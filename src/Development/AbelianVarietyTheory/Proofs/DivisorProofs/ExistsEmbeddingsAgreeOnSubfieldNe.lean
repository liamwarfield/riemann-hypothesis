module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimit
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCohomologyContinuousOnConeOfLevelwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
open TensorProduct

namespace GlobalTheory

theorem exists_embeddings_agree_on_subfield_ne (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω]
    [CharZero L] (a : Ω) (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F),
      i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω
  have he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0 := by
    intro h
    have h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a := sub_eq_zero.mp h
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)
    have h2 := congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2
    apply ha
    refine ⟨(φ 1)⁻¹ * φ a, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  have hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) :=
    fun h => he h.eq_zero
  rw [nilpotent_iff_mem_prime] at hn
  push_neg at hn
  obtain ⟨J, hJ, heJ⟩ := hn
  haveI := hJ
  let g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J) :=
    (algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)
  refine ⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance,
    g.comp (Algebra.TensorProduct.includeLeftRingHom),
    g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩
  · ext l
    simp only [RingHom.comp_apply]
    congr 1
    show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro h
    apply heJ
    have h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a) := h
    have h4 := IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3
    exact Ideal.Quotient.eq.mp h4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNeStatement
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range : ∀ (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] (a : Ω), a ∉ Set.range (algebraMap L Ω) → ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F), i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  first | exact @GlobalTheory.exists_embeddings_agree_on_subfield_ne | exact GlobalTheory.exists_embeddings_agree_on_subfield_ne | (intros; apply GlobalTheory.exists_embeddings_agree_on_subfield_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

theorem pull2_restrict_injective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G hsep hglue hvan
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨y0, hy0⟩ := hc
  obtain ⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t')
      (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b
        = z.1 _ _ _ (G.map a) (G.map b) := ⟨y0, fun t t' t'' a b ↦
    congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩
  have hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u)
        = z.1 _ _ _ u (G.map a) - y t t' a := fun T ↦
    hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by
      have k1 := z.2 u (G.map a) (G.map b)
      have k2 := hy' t t' t'' a b
      rw [Functor.map_comp]
      simp only [map_sub]
      linear_combination k2 - k1
  choose g hg using hg
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t),
      mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := z.2 φ u (G.map a)
    have k2 := hg T t t' (φ ≫ u) a
    have k3 := hg T' t t' u a
    rw [Category.assoc] at k2
    simp only [map_sub, map_add (f := _)]
    linear_combination -k1 - k2 + k3
  choose x hx using hx
  refine H2.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' T'' φ ψ
  refine sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)
  have k1 := z.2 φ ψ u
  have k2 := hx T T' φ t (ψ ≫ u)
  have k3 := hx T T'' (φ ≫ ψ) t u
  have k4 := hx T' T'' ψ t u
  rw [mp_comp] at k2
  rw [d1_apply]
  simp only [map_sub, map_add (f := _), Category.assoc] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1

end GlobalTheory.CatCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentInjectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_descent_injective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | exact GlobalTheory.CatCoh.pull2_restrict_injective_of_comma | (intros; apply GlobalTheory.CatCoh.pull2_restrict_injective_of_comma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquiv
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem pull2_surjective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G sep glue van1 van2 c
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ c
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ t t' t'' : C', (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t''),
      ∀ t t' t'' a b, Y t t' t'' a b = y.1 t t' t'' a b := ⟨y.1, fun _ _ _ _ _ ↦ rfl⟩
  have hy : ∀ t t' t'' t''' (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''),
      mp F (G.map c) (Y t t' t'' a b) + Y t t'' t''' (a ≫ b) c =
        Y t t' t''' a (b ≫ c) + Y t' t'' t''' b c := by
    intro t t' t'' t''' a b c
    simp only [hY]
    exact y.2 a b c
  choose h hh using fun T : C ↦ van2 T (fun t t' t'' _ a b ↦ Y t t' t'' a b)
    (fun t t' t'' t''' _ a b c ↦ hy t t' t'' t''' a b c)
  choose m hm using fun (T T' : C) (φ : T ⟶ T') ↦
    van1 T' (fun t t' u a ↦ h T t t' (φ ≫ u) a - h T' t t' u a) (fun t t' t'' u a b ↦ by
      have k1 := hh T t t' t'' (φ ≫ u) a b
      have k2 := hh T' t t' t'' u a b
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k2 - k1)
  choose x hx using fun (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦
    glue T'' (fun t u ↦ m T T' φ t (ψ ≫ u) + m T' T'' ψ t u - m T T'' (φ ≫ ψ) t u)
      (fun t t' u a ↦ by
        have k1 := hm T T' φ t t' (ψ ≫ u) a
        have k2 := hm T' T'' ψ t t' u a
        have k3 := hm T T'' (φ ≫ ψ) t t' u a
        simp only [map_sub, map_add (f := _), Category.assoc] at k1 k3 ⊢
        linear_combination k1 + k2 - k3)
  refine ⟨H2.mk F ⟨fun T T' T'' φ ψ ↦ x T T' T'' φ ψ,
    fun T T' T'' T''' φ ψ χ ↦ sub_eq_zero.1 (sep T''' _ fun t u ↦ ?_)⟩, ?_⟩
  · have k1 := hx _ _ _ φ ψ t (χ ≫ u)
    have k2 := hx _ _ _ (φ ≫ ψ) χ t u
    have k3 := hx _ _ _ φ (ψ ≫ χ) t u
    have k4 := hx _ _ _ ψ χ t u
    simp only [map_sub, map_add (f := _), Category.assoc, mp_comp] at k1 k2 k3 k4 ⊢
    linear_combination k1 + k2 - k3 - k4
  · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a, ?_⟩
    funext t t' t'' a b
    simp only [Pi.sub_apply]
    rw [← hY]
    have k1 := hx _ _ _ (G.map a) (G.map b) t'' (𝟙 _)
    have k2 := hm _ _ (G.map a) t' t'' (𝟙 _) b
    have k3 := hh _ t t' t'' (𝟙 _) a b
    simp only [mp_id, Category.id_comp, Category.comp_id] at k1 k2 k3
    change mp F (G.map b) (m _ _ (G.map a) t' (𝟙 _) - h _ t t' (𝟙 _) a) -
        (m _ _ (G.map (a ≫ b)) t'' (𝟙 _) - h _ t t'' (𝟙 _) (a ≫ b)) +
        (m _ _ (G.map b) t'' (𝟙 _) - h _ t' t'' (𝟙 _) b) =
      x _ _ _ (G.map a) (G.map b) - Y t t' t'' a b
    rw [G.map_comp]
    simp only [map_sub]
    linear_combination -k1 - k2 - k3

end GlobalTheory.CatCoh.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquivStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_descent_restriction_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | exact GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | (intros; apply GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimit
open IsLocalRing Polynomial CategoryTheory Limits

namespace GlobalTheory.TorsorColimElem

theorem exists_torsor_model_of_elements : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  intro ι _ _ _ R _ f hid hcomp B _ g hcompat hsurj hinj q hq D _ _ act hT
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (R i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le)
      map_id := fun i => by
        ext x
        simp [hid]
      map_comp := fun {i j k} a b => by
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply]
        exact (RingHom.congr_fun (hcomp i j k a.le b.le) x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of B
      ι := { app := fun i => CommRingCat.ofHom (g i)
             naturality := fun i j h => by
               ext x
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                 CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, F]
               exact RingHom.congr_fun (hcompat i j h.le) x } }
  have hc : IsColimit c := by
    haveI : ReflectsColimit F (forget CommRingCat) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      have hxy' : g i x = g j y := hxy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      have h0 : g k (f i k hik x - f j k hjk y) = 0 := by
        have e1 : g k (f i k hik x) = g i x := by rw [← hcompat i k hik]; rfl
        have e2 : g k (f j k hjk y) = g j y := by rw [← hcompat j k hjk]; rfl
        rw [map_sub, e1, e2, hxy', sub_self]
      obtain ⟨l, hkl, hl⟩ := hinj k _ h0
      refine ⟨l, homOfLE (hik.trans hkl), homOfLE (hjk.trans hkl), ?_⟩
      change f i l _ x = f j l _ y
      rw [map_sub, sub_eq_zero] at hl
      rw [← hcomp i k l hik hkl, ← hcomp j k l hjk hkl]
      exact hl
  have hT' : GlobalTheory.LocAcyc.IsZModTorsor B D q act := hT
  obtain ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩ :=
    @GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit ι _ _ F c hc q hq D _ ‹Algebra B D› act hT'
  exact ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩

end GlobalTheory.TorsorColimElem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimitStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsor_model_filtered_colimit : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  first | (exact @GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (exact GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (intros; apply GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfFibres
noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.CMVal.Fibre

variable {E : Type} [Field E] [NumberField E]


open Classical in
theorem tendsto_of_cut (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | a v ∈ v.adicCompletionIntegers E}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 E)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  have h2 := ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf
  have h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f :=
    funext fun T => Subtype.ext (funext fun v => hg T v)
  rw [h3]
  exact h2


open Classical in
theorem prod_single_apply (y : (Af E)ˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = if v ∈ T then (y : Af E) v else 1 := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, if_neg (Finset.notMem_empty v)]; rfl
  | insert u T hu ih =>
    rw [Finset.prod_insert hu, Units.val_mul]
    change (single u (coord u y) : Af E) v * ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = _
    rw [ih]
    by_cases h : v = u
    · subst h
      rw [single_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one, coe_coord]
    · rw [suppAt_single u _ v h, one_mul]; simp [h]

theorem coord_inv' (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := Units.ext rfl

theorem hasProd_single (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by
  have h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) =>
      ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E)) := fun y =>
    tendsto_of_cut _ _ (prod_single_apply y)
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h y).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h y⁻¹
  simp only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2
  exact h2

theorem continuous_finPart (χ : HChar E) : Continuous (finPart χ) :=
  χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))

theorem hasProd_loc (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) :=
  (hasProd_single y).map (finPart χ) (continuous_finPart χ)

theorem finPart_eq_one_of_fibres (E : Type) [Field E] [NumberField E] (χ : HChar E) (y : (Af E)ˣ)
    (h : ∀ v : HeightOneSpectrum (OF E),
      ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, χ.loc P (coord P y) = 1) : finPart χ y = 1 := by
  classical
  let U : Finset (HeightOneSpectrum (OF E)) → Finset (HeightOneSpectrum (𝓞 E)) :=
    fun S => S.biUnion (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E))
  have hmem : ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)),
      P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := fun v P => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]; rfl
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun S S' hS => Finset.biUnion_subset_biUnion_of_subset_left _ hS) fun P => ?_
    exact ⟨{P.under (OF E)}, Finset.mem_biUnion.2 ⟨_, Finset.mem_singleton_self _, (hmem _ _).2 rfl⟩⟩
  have h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) atTop (𝓝 (finPart χ y)) :=
    hasProd_loc χ y
  have h2 := h1.comp hU
  have h3 : ((fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) ∘ U) = fun _ => 1 := by
    funext S
    change ∏ P ∈ S.biUnion _, _ = 1
    rw [Finset.prod_biUnion]
    · exact Finset.prod_eq_one fun v _ => h v
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (hmem _ _).1 hv, ← (hmem _ _).1 hw]
  rw [h3] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

end GlobalTheory.CMVal.Fibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLv
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.BcLevel

set_option synthInstance.maxHeartbeats 200000 in
def bcIsoOfIso {E E' : Spc} {S : Scheme.{0}} (α : E ≅ E') (p : E' ⟶ sch.obj S) : bc (α.hom ≫ p) ≅ bc p :=
  haveI : ∀ U, IsIso ((bcMap α.hom p).app U) := fun U => by
    dsimp only [bcMap]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  haveI : IsIso (bcMap α.hom p) := NatIso.isIso_of_isIso_app _
  asIso (bcMap α.hom p)

def dq {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) : disc.obj (E.obj k) ⟶ sch.obj S :=
  disc.map (p.app k)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.isPullback_lv {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    IsPullback (_root_.GlobalTheory.EtC.disc.map ((pullback.fst p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj (E.obj k))
      (_root_.GlobalTheory.EtC.disc.map ((pullback.snd p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.sch.obj U.left)
      (_root_.GlobalTheory.EtC.BcLevel.dq p k) (_root_.GlobalTheory.EtC.sch.map U.hom) := by
  have h := (IsPullback.of_hasPullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).map
    ((evaluation SimplexCategoryᵒᵖ _root_.GlobalTheory.EtC.PSh).obj k)
  exact h.map _root_.GlobalTheory.EtC.disc

def lvIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    disc.obj ((pullback p (sch.map U.hom)).obj k) ≅ pullback (dq p k) (sch.map U.hom) :=
  (isPullback_lv p k U).isoPullback

set_option synthInstance.maxHeartbeats 200000 in
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.lv_nat {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) {U V : Over S} (g : U ⟶ V) :
    (_root_.GlobalTheory.EtC.disc.map (((_root_.GlobalTheory.EtC.bc p).map g).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map V.hom)).obj k)) ≫
      (_root_.GlobalTheory.EtC.BcLevel.lvIso p k V).hom = (_root_.GlobalTheory.EtC.BcLevel.lvIso p k U).hom ≫ (_root_.GlobalTheory.EtC.bc (_root_.GlobalTheory.EtC.BcLevel.dq p k)).map g := by
  have hV₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_fst
  have hV₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_snd
  have hU₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_fst
  have hU₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_snd
  unfold _root_.GlobalTheory.EtC.BcLevel.lvIso
  dsimp only [_root_.GlobalTheory.EtC.bc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [hV₁, pullback.lift_fst, Category.comp_id, hU₁]
    rw [← Functor.map_comp, ← NatTrans.comp_app, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc]
    erw [hV₂, pullback.lift_snd, ← Category.assoc, hU₂]
    change _ = _root_.GlobalTheory.EtC.disc.map _ ≫
      _root_.GlobalTheory.EtC.disc.map ((_root_.GlobalTheory.EtC.sch.map g.left).app k)
    rw [← Functor.map_comp]
    erw [← Functor.map_comp]
    congr 1
    rw [← NatTrans.comp_app]
    erw [← NatTrans.comp_app, pullback.lift_snd]

def bcDiscIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) :
    bc p ⋙ (evaluation _ PSh).obj k ⋙ disc ≅ bc (dq p k) :=
  NatIso.ofComponents (lvIso p k) (fun g => lv_nat p k g)

theorem bc_level : ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (r : X ⟶ S)
    (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r →
    Nonempty (bc (sch.map r) ≅ bc p ⋙ (evaluation _ PSh).obj k ⋙ disc) := by
  intro S E p k X r e h
  have heq : sch.map r = (disc.mapIso e : sch.obj X ≅ disc.obj (E.obj k)).hom ≫ dq p k := by
    change disc.map (yoneda.map r) = disc.map e.hom ≫ disc.map (p.app k)
    rw [← h]
    exact disc.map_comp _ _
  rw [heq]
  exact ⟨bcIsoOfIso _ (dq p k) ≪≫ (bcDiscIso p k).symm⟩

end GlobalTheory.EtC.BcLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevels
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CcStep

theorem cc_step : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  intro R _ F S E p I _ _ G c h
  apply GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F I (G ⋙ bc p) ((bc p).mapCone c)
  intro k
  obtain ⟨X, r, e, he, hc⟩ := h k
  obtain ⟨φ⟩ := GlobalTheory.EtC.BcLevel.bc_level S E p k X r e he
  have hiso := (GlobalTheory.EtC.eqv_basic R F).1
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ bc (sch.map r)) ((G ⋙ bc p) ⋙ (evaluation _ PSh).obj k ⋙ disc)
    ((bc (sch.map r)).mapCone c) (((evaluation _ PSh).obj k ⋙ disc).mapCone ((bc p).mapCone c))
    (Functor.whiskerLeft G φ.hom) (φ.hom.app c.pt) ?_ ?_ ?_).1 hc
  · intro i
    exact φ.hom.naturality (c.π.app i)
  · intro i
    exact hiso _ _ _ inferInstance
  · exact hiso _ _ _ inferInstance

end GlobalTheory.EtC.CcStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevelsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_base_change_of_levels : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  first | (exact @GlobalTheory.EtC.CcStep.cc_step) | (exact GlobalTheory.EtC.CcStep.cc_step) | (intros; apply GlobalTheory.EtC.CcStep.cc_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSection
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.PullBdd

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem castFrame_mem_GG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E}
    {p0 : ℕ} {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

theorem castFrame_mem_Bor {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) : castFrame h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem bchar_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) (b : Frame Ψ r) :
    bchar la (castFrame h b) = bchar (castWt h la) b := by
  subst h; rfl

theorem castFrame_rmul {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFrame h (rmul x b) = rmul (castFrame h x) (castFrame h b) := rfl

theorem castFrame_lact {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (β : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact β x) = lact β (castFrame h x) := rfl

theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (β : GL (Fin r) E) (x b : Frame Ψ r) :
    lact β (rmul x b) = rmul (lact β x) b := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_lact {Ψ : Finset (E →+* ℂ)} (β γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact β (lact γ x) = lact (β * γ) x := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
      Matrix (Fin r) (Fin r) ℂ) =
    ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem dmin_lact {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by
  have e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]
  unfold dmin
  rw [e2]

theorem nfac_cast {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E)
    (la : Wt Ψ' r) (x : Frame Ψ r) :
    (∏ τ : Ψ', ∏ i : Fin r, ‖dmin G (castFrame h x) τ i.succ / dmin G (castFrame h x) τ i.castSucc‖ ^
      (-(la τ i : ℝ) / 2)) =
    ∏ τ : Ψ, ∏ i : Fin r, ‖dmin G x τ i.succ / dmin G x τ i.castSucc‖ ^
      (-(castWt h la τ i : ℝ) / 2) := by
  subst h; rfl

theorem isBddSec_transport (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0)
    (β : GL (Fin r) E)
    (hβ : ∀ u v, herm Y.Gm ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm Y.Gm u v)
    (hΓ : ∀ γ ∈ X.Γ, β * γ * β⁻¹ ∈ Y.Γ) (la : Wt Y.Ψ r)
    (hχX : ∀ γ ∈ X.Γ, X.χ (castWt hΨ la) γ = 1) (hχY : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (Q : Frame Y.Ψ r → ℂ) (hQ : Y.IsBddSec la Q) :
    X.IsBddSec (castWt hΨ la) (fun x => Q (lact β (castFrame hΨ x))) := by
  obtain ⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩ := hQ
  have hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom := by
    intro x hx
    have h1 := castFrame_mem_GG hΨ hx
    rw [hG, hp] at h1
    exact GlobalTheory.FrameFibre.lact_mem_GG hβ h1
  refine ⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩
  · have hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x)) := by
      rw [differentiable_pi]; intro τ; rw [differentiable_pi]; intro a; rw [differentiable_pi]; intro b
      simp only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      fun_prop
    exact hQd.comp hd.differentiableOn hmaps
  · intro x hx b hb
    simp only
    rw [castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]
  · intro γ hγ x hx
    simp only
    rw [hχX γ hγ, one_mul, castFrame_lact, lact_lact,
      show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx),
      hχY _ (hΓ γ hγ), one_mul]
  · refine le_trans (le_of_eq ?_) (hC _ (hmaps x hx))
    unfold Data.pnorm
    congr 1
    simp only [dmin_lact hβ]
    rw [← hG]
    exact (nfac_cast hΨ X.Gm la x).symm

end

theorem pull_isBddSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type)
    [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ),
    F ∈ M.SS la → ∀ (h : U) (c : C),
      (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  intro E _ _ _ r U C _ _ M la F hF h c
  have hY := (hF (h • c)).1
  exact isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData
    ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm])
    (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c)
    (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt (M.comp_Ψ (h • c)) la)
    (fun γ hγ => M.χ_one c _ γ hγ) (fun γ hγ => M.χ_one (h • c) _ γ hγ) _ hY

end GlobalTheory.PullBdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormPullbackIsBoundedSectionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_pullback_isBoundedSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → ∀ (h : U) (c : C), (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  first | exact @GlobalTheory.PullBdd.pull_isBddSec | exact GlobalTheory.PullBdd.pull_isBddSec | (intros; apply GlobalTheory.PullBdd.pull_isBddSec <;> assumption)
end
end
