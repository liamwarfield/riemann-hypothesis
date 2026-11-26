module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    (p : Y ⟶ X) (hp : IsOpenMap p) : IsDominant (pullback.fst p j) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact j.denseRange.preimage hp

theorem _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints {T : Type*} [TopologicalSpace T] [T0Space T]
    {x y : T} (hx : x ∈ genericPoints T) (h : y ⤳ x) : y = x := by
  have h1 : closure ({y} : Set T) ⊆ closure {x} :=
    hx.2 isIrreducible_singleton.closure h.closure_subset
  exact (h.antisymm (specializes_iff_closure_subset.2 h1)).eq

theorem _root_.GlobalTheory.genericPoints_subset_range_of_isDominant {X U : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    [QuasiCompact j] : genericPoints X ⊆ Set.range j := by
  intro ξ hξ
  obtain ⟨V, hV, hξV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show ξ ∈ (⊤ : X.Opens) from trivial)
  replace hV : IsAffineOpen V := hV
  have hc : IsCompact (j ⁻¹' (V : Set X)) :=
    QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
  obtain ⟨s, hs, hW⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hc, V.isOpen.preimage j.continuous⟩
  have hcl : ξ ∈ closure (j '' (j ⁻¹' (V : Set X))) := by
    rw [Set.image_preimage_eq_inter_range]
    exact j.denseRange.open_subset_closure_inter V.isOpen hξV
  rw [hW, Set.image_iUnion₂, hs.closure_biUnion, Set.mem_iUnion₂] at hcl
  obtain ⟨W, hWs, hξW⟩ := hcl
  have hWV : (W : Set U) ⊆ j ⁻¹' (V : Set X) := by
    rw [hW]
    exact Set.subset_biUnion_of_mem (u := fun i : U.affineOpens => ((i : U.Opens) : Set U)) hWs
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  set g := hWa.fromSpec ≫ j with hg
  have hrg : Set.range g = j '' (W : Set U) := by
    rw [hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hWa.range_fromSpec]
  have hsub : Set.range g ⊆ Set.range hV.fromSpec := by
    rw [hrg, hV.range_fromSpec]
    rintro _ ⟨x, hx, rfl⟩
    exact hWV hx
  set k := IsOpenImmersion.lift hV.fromSpec g hsub with hk
  have hkg : k ≫ hV.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  set φ := Spec.preimage k
  have hφ : Spec.map φ = k := Spec.map_preimage k
  obtain ⟨p, hp⟩ : ξ ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hξV
  have hinj : Function.Injective hV.fromSpec := hV.fromSpec.isOpenEmbedding.injective
  have hpcl₀ : p ∈ closure (Set.range (Spec.map φ)) := by
    rw [hV.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.mem_preimage, hp]
    convert hξW using 2
    rw [← hrg, ← hkg, ← hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hpcl₁ : (p : PrimeSpectrum Γ(X, V)) ∈ closure (Set.range (PrimeSpectrum.comap φ.hom)) :=
    hpcl₀
  rw [PrimeSpectrum.closure_range_comap] at hpcl₁
  have hpcl : RingHom.ker φ.hom ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hpcl₁
  have hmin : p.asIdeal ∈ (Ideal.comap φ.hom ⊥).minimalPrimes := by
    rw [← RingHom.ker_eq_comap_bot]
    refine ⟨⟨p.2, hpcl⟩, fun q hq hqp => ?_⟩
    have hspec : (⟨q, hq.1⟩ : PrimeSpectrum _) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    have heq := _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints (hp ▸ hξ)
      (hspec.map hV.fromSpec.continuous)
    have heq' := hinj heq
    rw [← heq']
  obtain ⟨q, hq, -, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ.hom _ hmin
  refine ⟨hWa.fromSpec ⟨q, hq⟩, ?_⟩
  rw [← hp]
  change g ⟨q, hq⟩ = _
  have hgq : g ⟨q, hq⟩ = hV.fromSpec (Spec.map φ ⟨q, hq⟩) := by rw [← hkg, ← hφ]; rfl
  rw [hgq]
  congr 1
  exact PrimeSpectrum.ext hqp

theorem _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks {X U : Scheme.{0}} (j : U ⟶ X) [Flat j]
    [SurjectiveOnStalks j] (u : U) : IsIso (j.stalkMap u) := by
  have hs := j.stalkMap_surjective u
  letI := (j.stalkMap u).hom.toAlgebra
  haveI : Module.Flat _ _ := Flat.stalkMap j u
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (j u)) (U.presheaf.stalk u)) :=
    inferInstanceAs (IsLocalHom (j.stalkMap u).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (j u)) (B := U.presheaf.stalk u)
  have hi : Function.Injective (j.stalkMap u).hom :=
    FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j u)) (U.presheaf.stalk u)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, hs⟩

theorem _root_.GlobalTheory.densePart_basic : ∀ (X U : Scheme.{0}) (j : U ⟶ X), IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → genericPoints X ⊆ Set.range j ∧ (∀ u : U, IsIso (j.stalkMap u)) ∧ (IsReduced X → IsSchemeTheoreticallyDominant j) ∧ ∀ (Y : Scheme.{0}) (p : Y ⟶ X), UniversallyOpen p → IsDominant (pullback.fst p j) := by
  intro X U j _ _ _ _
  refine ⟨_root_.GlobalTheory.genericPoints_subset_range_of_isDominant j,
    fun u => _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks j u,
    fun _ => (isSchemeTheoreticallyDominant_iff_isDominant j).2 inferInstance,
    fun Y p _ => _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap j p p.isOpenMap⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS
section Basic
variable {Y Z : Scheme.{0}}

theorem rsT_of_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem pbT_of_le (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) :
    pbT f s O = (f.appLE O₀ O h).hom s := dif_pos h

theorem rsT_add {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_zero {O₀ : Y.Opens} (O : Y.Opens) : rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT; split_ifs <;> simp

theorem rsT_one {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (1 : Γ(Y, O₀)) O = 1 := by
  rw [rsT_of_le h, map_one]

theorem rsT_sum {J : Type*} (S : Finset J) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Y.Opens) :
    rsT (∑ a ∈ S, s a) O = ∑ a ∈ S, rsT (s a) O := by
  unfold rsT; split_ifs <;> simp

theorem pbT_add (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s + t) O = pbT f s O + pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_sub (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s - t) O = pbT f s O - pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_neg (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : pbT f (-s) O = -pbT f s O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_mul (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s * t) O = pbT f s O * pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_zero (f : Z ⟶ Y) {O₀ : Y.Opens} (O : Z.Opens) : pbT f (0 : Γ(Y, O₀)) O = 0 := by
  unfold pbT; split_ifs <;> simp

theorem pbT_one (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : pbT f (1 : Γ(Y, O₀)) O = 1 := by
  rw [pbT_of_le f h, map_one]

theorem pbT_sum {J : Type*} (S : Finset J) (f : Z ⟶ Y) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (∑ a ∈ S, s a) O = ∑ a ∈ S, pbT f (s a) O := by
  unfold pbT; split_ifs <;> simp

theorem rsT_self {O : Y.Opens} (s : Γ(Y, O)) : rsT s O = s := by
  rw [rsT_of_le le_rfl]
  simp [resG]

theorem rsT_rsT {O₀ O₁ O₂ : Y.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h₁, rsT_of_le h₂, rsT_of_le (h₂.trans h₁)]
  exact (congrArg (fun φ => φ.hom s)
    (Y.presheaf.map_comp (homOfLE h₁).op (homOfLE h₂).op)).symm

theorem rsT_pbT (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O₀)) : rsT (pbT f s O₁) O₂ = pbT f s O₂ := by
  rw [pbT_of_le f h₁, rsT_of_le h₂, pbT_of_le f (h₂.trans h₁)]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_map f h₁ (homOfLE h₂).op)

theorem pbT_rsT (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁)
    (s : Γ(Y, O₀)) : pbT f (rsT s O₁) O₂ = pbT f s O₂ := by
  rw [rsT_of_le h₁, pbT_of_le f h₂, pbT_of_le f (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE f h₂ (homOfLE h₁).op)

theorem rsT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) {O₀ O : Y.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn q O₀ a) O = constFn q O a := by
  rw [rsT_of_le h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem pbT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (a : R) : pbT f (constFn q O₀ a) O = constFn (f ≫ q) O a := by
  rw [pbT_of_le f h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O₀ O (fun _ _ => trivial) h)

theorem eq_of_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s t : Γ(Y, O)) (h : ∀ k, rsT s (V k) = rsT t (V k)) : s = t := by
  refine Y.sheaf.eq_of_locally_eq' V O (fun k => homOfLE (hV k)) hc s t fun k => ?_
  have := h k
  rw [rsT_of_le (hV k), rsT_of_le (hV k)] at this
  exact this

theorem exists_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s : ∀ k, Γ(Y, V k)) (h : ∀ k l, rsT (s k) (V k ⊓ V l) = rsT (s l) (V k ⊓ V l)) :
    ∃ t : Γ(Y, O), ∀ k, rsT t (V k) = s k := by
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' V O (fun k => homOfLE (hV k)) hc s (fun k l => by
    have := h k l
    rw [rsT_of_le inf_le_left, rsT_of_le inf_le_right] at this
    exact this)
  exact ⟨t, fun k => (rsT_of_le (hV k) _).trans (ht k)⟩

theorem le_iSup_inf_preimage (f : Z ⟶ Y) {I : Type} (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤) (O : Z.Opens) :
    O ≤ ⨆ k, O ⊓ f ⁻¹ᵁ U k := by
  intro x hx
  have : f x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩

end Basic

variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}

theorem IsCob.add {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c + c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i + b' i, fun i j => ?_⟩
  simp only [Pi.add_apply, rsT_add, hb, hb']
  ring

theorem IsCob.sub {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c - c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i - b' i, fun i j => ?_⟩
  simp only [Pi.sub_apply, rsT_sub, hb, hb']
  ring

theorem isCob_lc (q : Y ⟶ Sp K) {g : ℕ} (a : Fin g → K) (c : Fin g → C1 U) (h : ∀ x, IsCob U (c x)) :
    IsCob U (lc q a c) := by
  choose b hb using h
  refine ⟨fun i => ∑ x, constFn q (U i) (a x) * b x i, fun i j => ?_⟩
  simp only [lc, rsT_sum, rsT_mul, hb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rsT_constFn q inf_le_left, rsT_constFn q inf_le_right]
  ring

theorem cohom_lc (q : Y ⟶ Sp K) (f : Y ⟶ Y) (hf : f ≫ q = q) {g : ℕ} (a : Fin g → K) (c c' : Fin g → C1 U)
    (h : ∀ x, Cohom f U (c x) (c' x)) : Cohom f U (lc q a c) (lc q a c') := by
  choose b hb hb' using h
  refine ⟨fun i k => ∑ x, constFn q (U i ⊓ f ⁻¹ᵁ U k) (a x) * b x i k, fun i i' k => ?_, fun i k k' => ?_⟩
  · simp only [lc, rsT_sum, rsT_mul, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rsT_constFn q (inf_le_inf_right _ inf_le_left), rsT_constFn q (inf_le_inf_right _ inf_le_right),
      rsT_constFn q inf_le_left]
    ring
  · simp only [lc, rsT_sum, rsT_mul, pbT_sum, pbT_mul, ← hb', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ f ⁻¹ᵁ (U k ⊓ U k') := fun y hy => ⟨hy.1.2, hy.2⟩
    have e' : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ U i ⊓ f ⁻¹ᵁ U k' := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [rsT_constFn q inf_le_left, rsT_constFn q e', pbT_constFn q f e, hf]
    ring

theorem Cohom.isCob_sub (f : Y ⟶ Y) (hU : ⨆ i, U i = ⊤) {c c₁ c' c₁' : C1 U} (h : Cohom f U c c')
    (h₁ : Cohom f U c₁ c₁') (hc : IsCob U (c' - c₁')) : IsCob U (c - c₁) := by
  obtain ⟨b, hb, hb'⟩ := h
  obtain ⟨b₁, hb₁, hb₁'⟩ := h₁
  obtain ⟨β, hβ⟩ := hc
  have glue : ∀ i, ∃ t : Γ(Y, U i), ∀ k, rsT t (U i ⊓ f ⁻¹ᵁ U k) =
      b i k - b₁ i k + pbT f (β k) (U i ⊓ f ⁻¹ᵁ U k) := by
    intro i
    refine exists_rsT_eq (fun k => U i ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
      (le_iSup_inf_preimage f U hU _) _ fun k l => ?_
    have e : (U i ⊓ f ⁻¹ᵁ U k) ⊓ (U i ⊓ f ⁻¹ᵁ U l) ≤ U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l :=
      fun y hy => ⟨hy.1, hy.2.2⟩
    have e₁ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U k ⊓ U l) := fun y hy => ⟨hy.1.2, hy.2⟩
    have e₂ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ U i ⊓ f ⁻¹ᵁ U l := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [← rsT_rsT inf_le_left e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => pbT f s (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l)) (hβ k l)
    simp only [Pi.sub_apply, pbT_sub] at k₀
    rw [pbT_rsT f inf_le_right e₁, pbT_rsT f inf_le_left e₁, ← hb', ← hb₁'] at k₀
    simp only [rsT_add, rsT_sub]
    rw [rsT_pbT f inf_le_right inf_le_left, rsT_pbT f inf_le_right e₂]
    linear_combination k₀
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun k => U i ⊓ U j ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
    (le_iSup_inf_preimage f U hU _) _ _ fun k => ?_
  have e₁ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U i ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_left
  have e₂ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U j ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_right
  simp only [Pi.sub_apply, rsT_sub]
  rw [rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (t j), ← rsT_rsT inf_le_left e₁ (t i), ht, ht, ← hb, ← hb₁]
  simp only [rsT_add, rsT_sub]
  rw [rsT_pbT f inf_le_right e₁, rsT_pbT f inf_le_right e₂]
  ring

end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

private lemma comap_algebraMap_fractionRing_specializes (O F : Type) [CommRing O] [IsDomain O] [Field F]
    [Algebra O F] [IsFractionRing O F] (x : PrimeSpectrum F) (y : PrimeSpectrum O) :
    PrimeSpectrum.comap (algebraMap O F) x ⤳ y := by
  rw [← PrimeSpectrum.le_iff_specializes]
  intro a ha
  have h0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O F)] at ha
  rw [Ideal.mem_bot.mp ha]
  exact zero_mem _

theorem _root_.GlobalTheory.genericPart_dense_proOpen : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by
  intro O F _ _ _ _ _ X U s jQ hflat hproj hopen hdense
  obtain ⟨N, i, hi, hsi⟩ := hproj
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  have hprop : IsProper s := by rw [← hsi]; infer_instance
  have hnO : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hnF : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcF : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hcO : CompactSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hsepO : IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O).toSpecΓ := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hflg : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat F (nonZeroDivisors O)
  have hnP : IsLocallyNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have hcP : CompactSpace ↥(pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)))
  have : IsNoetherian (pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := jQ.isOpenEmbedding.isInducing.noetherianSpace
  have hdomj : IsDominant jQ := ⟨hdense⟩
  have hdomf : IsDominant (pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))) := by
    constructor
    intro x
    obtain ⟨p⟩ : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp F) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
    have hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F) p ⤳ s x := comap_algebraMap_fractionRing_specializes O F p (s x)
    obtain ⟨x', hx', hsx'⟩ := Flat.generalizingMap s hp
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F)) x' p hsx'
    exact closure_mono (show {x'} ⊆ Set.range _ from Set.singleton_subset_iff.mpr ⟨z, hz⟩)
      (specializes_iff_mem_closure.mp hx')
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian s, QuasiCompact.compactSpace_of_compactSpace s,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance⟩
  constructor
  rw [← terminal.comp_from s]
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.ConstThickening

theorem existsUnique_of_isPushout {K : Type} [Field K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra K A := c.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber K) A' := s.toAlgebra
  let _ : Algebra K A' := (s.comp (algebraMap K (DualNumber K))).toAlgebra
  have : IsScalarTower K (DualNumber K) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout K A (DualNumber K) A' := CommRingCat.isPushout_iff_isPushout.mp H
  let b : Module.Basis (Fin 2) K (DualNumber K) := Module.Basis.finTwoProd K
  have b0 : b 0 = 1 := Module.Basis.finTwoProd_zero K
  have b1 : b 1 = DualNumber.eps := Module.Basis.finTwoProd_one K
  let B := h.out.basis b
  have B0 : B 0 = 1 := by
    rw [h.out.basis_apply, b0]; exact map_one s
  have B1 : B 1 = s DualNumber.eps := by
    rw [h.out.basis_apply, b1]; rfl
  have key : ∀ x y : A, p.hom x + s DualNumber.eps * p.hom y = B.equivFun.symm ![x, y] := fun x y => by
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, B0, B1, Algebra.smul_def, Algebra.smul_def, _root_.mul_one,
      _root_.mul_comm (s _)]
    rfl
  refine ⟨(B.equivFun F 0, B.equivFun F 1), ?_, fun ab hab => ?_⟩
  · change F = _
    rw [key, LinearEquiv.eq_symm_apply]
    ext i; fin_cases i <;> rfl
  · replace hab : F = _ := hab
    rw [key, LinearEquiv.eq_symm_apply] at hab
    rw [hab]; rfl

variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem existsUnique_affine (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {U : Y.Opens}
    (hU : IsAffineOpen U) (F : Γ(Y', ρ ⁻¹ᵁ U)) : ∃! ab : Γ(Y, U) × Γ(Y, U),
      F = (ρ.app U).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app U).hom ab.2 := by
  refine existsUnique_of_isPushout (constHom q U) (ρ.app U) (constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ DualNumber.eps * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ DualNumber.eps * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add (f := _), map_mul, res_app ρ h, res_app ρ h, res_constFn]

theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem unique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {O : Y.Opens} {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (existsUnique_affine H U.2.1 _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

theorem existsUnique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (existsUnique_affine H U.2.1 ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber K)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem structure_dualNumber : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro K _ Y Y' q π ρ j H hj hq
  have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hp : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hq H
    rw [hj, e]
    exact IsPullback.id_horiz q
  refine ⟨fun O => ?_, hp, existsUnique_comb H⟩
  have hs : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) hp.flip surjective_spMap_fst
  ext x
  obtain ⟨y, rfl⟩ := hs.surj x
  change j (ρ (j y)) ∈ O ↔ j y ∈ O
  rw [← Scheme.Hom.comp_apply j ρ, hj]
  rfl

end GlobalTheory.ConstThickening
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.const_thickening_field_structure : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.ConstThickening.structure_dualNumber | exact GlobalTheory.ConstThickening.structure_dualNumber | (intros; apply GlobalTheory.ConstThickening.structure_dualNumber <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_smul_apply_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by
  classical
  have := Fintype.ofFinite G
  set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hmap : P.map x = P.map y := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hinvP]
  have hb : P.eval b = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have h0 : (P.map y).eval (y b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  rw [← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd] at h0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0
  obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨g, sub_eq_zero.mp hg⟩

theorem exists_smul_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) : ∃ g : G, ∀ b, y b = x (g • b) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc using hne
  have := Fintype.ofFinite G
  let e := Fintype.equivFin G
  let p : Polynomial B := ∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)
  have hcoef : ∀ g, p.coeff (e g) = c g := by
    intro g
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm))
      (by simp), if_pos rfl]
  have hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) →
      Polynomial.mapRingHom x q = Polynomial.mapRingHom y q := by
    intro q hq
    ext n
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hq]
  obtain ⟨g, hg⟩ := exists_smul_apply_eq_of_eq_on_invariants (G := G)
    (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p
  have hgc := congrArg (fun q => q.coeff (e g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc
  exact hc g hgc

theorem exists_aut_of_comp_eq_of_invariant {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).asIso.hom := by
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).asIso.hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).asIso.hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  have hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W
    rw [← hxy]
    exact hx
  have key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W),
      f.appLE W ⊤ h1 = f'.appLE W ⊤ h2 := by
    rintro f f' rfl h1 h2
    rfl
  have hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) →
      (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s := by
    intro s hs
    have hinv' : IsInvariantSection ρ _ s := by
      intro g
      refine ⟨hU g, ?_⟩
      have := hs g⁻¹
      rw [hact] at this
      simpa only [inv_inv] using this
    obtain ⟨t, rfl⟩ := hinv s hinv'
    have e1 := Scheme.Hom.comp_appLE x π W ⊤ hx
    have e2 := Scheme.Hom.comp_appLE y π W ⊤ hy
    have := congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)
    rw [e1, e2] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree
  refine ⟨g⁻¹, ?_⟩
  have h' : ⊤ ≤ (x ≫ (ρ g⁻¹).asIso.hom) ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W)
    exact hx.trans (x.preimage_mono (hU g⁻¹))
  have heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).asIso.hom).appLE (π ⁻¹ᵁ W) ⊤ h' := by
    ext s
    rw [← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).asIso.hom _ _ _ (hU g⁻¹) hx]
    rw [hg s, hact]
    rfl
  have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).asIso.hom) hA (isAffineOpen_top T) h'
  rw [heq] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  exact (cancel_epi _).1 (h1.symm.trans h2)

theorem isIntegralHom_of_invariant {G : Type*} [Group G] [Finite G] {X X' : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) : IsIntegralHom π := by
  rw [isIntegralHom_iff]
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).asIso.hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).asIso.hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  classical
  have := Fintype.ofFinite G
  intro s
  rcases subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt
  · rw [Subsingleton.elim s 0]
    exact RingHom.isIntegralElem_zero _
  set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hlift : P ∈ Polynomial.lifts (π.app W).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hinv W hW
    intro g
    refine ⟨hU g, ?_⟩
    have := congrArg (fun q => q.coeff n) (hinvP g⁻¹)
    simp only [Polynomial.coeff_smul] at this
    rw [hact] at this
    simpa only [inv_inv] using this
  have hmonic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

theorem quotient_isIntegral_surjective_orbits :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsIntegralHom π ∧ Surjective π ∧ (∀ x y : X, π x = π y → ∃ g, y = (ρ g).asIso.hom x) ∧ (∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).asIso.hom) ∧ ∀ U : X.Opens, (∀ g, (ρ g).asIso.hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
  intro Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩
  have hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
    intro W _ s hs
    apply (hV W).2 s
    intro g h
    obtain ⟨h', e⟩ := hs g
    exact e
  have hInt : IsIntegralHom π := isIntegralHom_of_invariant ρ π hπ hinvAll
  have hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π →
      ∃ g, y = x ≫ (ρ g).asIso.hom := by
    intro k _ x y hxy
    let p₀ : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial
    refine exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_
    intro p _
    have hp : p = p₀ := Subsingleton.elim _ _
    subst hp
    exact hmem
  have hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).asIso.hom x := by
    intro x y hxy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π =
        (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := hfield ((pullback π π).residueField z) _ _ hab
    refine ⟨g, ?_⟩
    let s : Spec ((pullback π π).residueField z) := ⟨⊥, Ideal.isPrime_bot⟩
    have ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x := by
      show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x
      rw [Scheme.fromSpecResidueField_apply]
      exact hz1
    have hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y := by
      show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y
      rw [Scheme.fromSpecResidueField_apply]
      exact hz2
    rw [← hb, hg, ← ha]
    rfl
  have hsurj : Surjective π := by
    rw [surjective_iff]
    intro y
    obtain ⟨W, hW, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
    have heq := IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl
    have hmem' : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hmem
    obtain ⟨p, rfl⟩ := hmem'
    have hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hInt.isIntegral_app W hW
    have hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact (hV W).1
    obtain ⟨q, hq⟩ := hint.comap_surjective hinj p
    refine ⟨hA.fromSpec q, ?_⟩
    have := congrArg (fun f => f q) heq
    rw [← hq]
    exact this.symm
  have hopen : ∀ U : X.Opens, (∀ g, (ρ g).asIso.hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
    intro U hU
    have hcl : IsClosed (π '' (U : Set X)ᶜ) := π.isClosedMap _ U.isOpen.isClosed_compl
    refine ⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩
    ext x
    show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · rintro hx ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := hpts x y hxy.symm
      apply hy
      have hx' : x ∈ (ρ g).asIso.hom ⁻¹ᵁ U := by
        rw [hU g]
        exact hx
      exact hx'
  exact ⟨hInt, hsurj, hpts, hfield, hopen⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_linear_lift_of_isMonHom_polAV :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro P P' L L' u u' f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom P.A P'.A P.3 P'.3 L L' P.g P'.g u u'
    (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).1 (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).2 f hf
  exact ⟨F, hF⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAVStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_linear_lift_of_isMonHom_uniformisation : ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.exists_linear_lift_of_isMonHom_polAV | exact GlobalTheory.exists_linear_lift_of_isMonHom_polAV | (intros; apply GlobalTheory.exists_linear_lift_of_isMonHom_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.DualRigidity

theorem eq_comp_section_of_const {X T Y : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y)
    (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) (y : Y) (hy : ∀ x : X, g x = y) :
    g = p ≫ ε ≫ g := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsAffine W := hW
  have hr : Set.range g ⊆ Set.range (Scheme.Opens.ι W) := by
    rintro _ ⟨x, rfl⟩
    rw [hy x, Scheme.Opens.range_ι]
    exact hyW
  have key := GlobalTheory.eq_comp_section_of_surjective_appTop p ε (IsOpenImmersion.lift (Scheme.Opens.ι W) g hr) h hs
  have := congrArg (· ≫ Scheme.Opens.ι W) key
  simpa only [Category.assoc, IsOpenImmersion.lift_fac] using this

end GlobalTheory.DualRigidity
end
