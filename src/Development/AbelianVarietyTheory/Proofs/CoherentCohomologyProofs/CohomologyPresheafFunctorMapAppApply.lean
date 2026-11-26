module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CohomologyPresheafFunctorMapAppApply
open CategoryTheory Abelian Opposite Limits TopologicalSpace

universe w v u

namespace GlobalTheory
namespace Flasque

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable abbrev freeSheafMap {V U : C} (i : V ⟶ U) : freeSheaf J V ⟶ freeSheaf J U :=
  (presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

instance mono_freeSheafMap {V U : C} (i : V ⟶ U) [Mono i] : Mono (freeSheafMap J i) := by
  infer_instance

variable {J}

noncomputable def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J _).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)
  map_add' f g := by
    rfl

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

lemma _root_.GlobalTheory.Flasque.subsingleton_H'_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (n : ℕ) (U : C) : Subsingleton (Sheaf.H'.{w} I (n + 1) U) :=
  Ext.subsingleton_of_injective (_root_.GlobalTheory.Flasque.freeSheaf J U) I n

section Shift

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

end Shift

end Site

section Injective

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable abbrev injectiveShortComplex [EnoughInjectives A] (F : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact [EnoughInjectives A] (F : A) :
    (_root_.GlobalTheory.Flasque.injectiveShortComplex F).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

lemma _root_.GlobalTheory.Flasque.exists_hom_τ₁_eq {S T : ShortComplex A} (hS : S.ShortExact)
    [Injective T.X₂] (f : S.X₁ ⟶ T.X₁) : ∃ φ : S ⟶ T, φ.τ₁ = f := by
  have := hS.mono_f
  let τ₂ : S.X₂ ⟶ T.X₂ := Injective.factorThru (f ≫ T.f) S.f
  have h₂ : S.f ≫ τ₂ = f ≫ T.f := Injective.comp_factorThru _ _
  have hw : S.f ≫ τ₂ ≫ T.g = 0 := by
    rw [reassoc_of% h₂, T.zero, comp_zero]
  let τ₃ : S.X₃ ⟶ T.X₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ hw)
  have h₃ : S.g ≫ τ₃ = τ₂ ≫ T.g :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ _ hw) WalkingParallelPair.one
  exact ⟨{ τ₁ := f, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₂.symm, comm₂₃ := h₃.symm }, rfl⟩

end Injective

section Space

variable {X : TopCat.{u}}

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_eq_yonedaEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h = yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
        ((sheafificationAdjunction J _).homEquiv _ _ h)) := rfl

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_freeSheafMap_comp' {V U : C} (i : V ⟶ U) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv V F (_root_.GlobalTheory.Flasque.freeSheafMap J i ≫ h) =
      F.obj.map i.op (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  rw [← yonedaEquiv_naturality]
  rfl

theorem _root_.GlobalTheory.Flasque.isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    I.IsFlasque := by
  let I' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := I
  haveI : Injective I' := hI
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : _root_.GlobalTheory.Flasque.freeSheaf _ (unop V) ⟶ I' :=
    (_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop V) I').symm s
  let h : _root_.GlobalTheory.Flasque.freeSheaf _ (unop U) ⟶ I' :=
    Injective.factorThru g (_root_.GlobalTheory.Flasque.freeSheafMap _ i.unop)
  refine ⟨_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop U) I' h, ?_⟩
  have key := freeSheafHomEquiv_freeSheafMap_comp' i.unop I' h
  rw [Injective.comp_factorThru] at key
  simpa [g] using key.symm

instance isFlasque_injectiveShortComplex_X₂ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (injectiveShortComplex F).X₂.IsFlasque :=
  isFlasque_of_injective _

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_comp' (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) (f : F ⟶ G) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U G (h ≫ f) =
      f.hom.app (op U) (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  rw [yonedaEquiv_comp]
  rfl

theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (n : ℕ) (U : Opens X) : Subsingleton (F.H' (n + 1) U) := by
  let Y : TopCat.Sheaf AddCommGrpCat.{u} X :=
    _root_.GlobalTheory.Flasque.freeSheaf (Opens.grothendieckTopology X) U
  letI : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X) := ‹HasExt.{w} (Sheaf _ _)›
  suffices h : ∀ x : Ext.{w} Y F (n + 1), x = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  induction n generalizing F with
  | zero =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x₃
    have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _ φ)
    let ψ : Y ⟶ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₂ :=
      (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).symm t
    have hψ : ψ ≫ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g = φ := by
      apply (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).injective
      refine (freeSheafHomEquiv_comp' U ψ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g).trans ?_
      simp only [ψ, AddEquiv.apply_symm_apply]
      exact ht
    rw [Ext.homEquiv₀_symm_apply, ← hψ, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by simp), hS.comp_extClass, Ext.comp_zero]
  | succ m ih =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    haveI : (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₃.IsFlasque :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    rw [ih _ x₃, Ext.zero_comp]

theorem _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque_of_pos (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] {n : ℕ} (hn : 0 < n) (U : Opens X) : Subsingleton (F.H' n U) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  exact _root_.GlobalTheory.Flasque.subsingleton_H'_of_isFlasque F m U

end Space

end Flasque

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Imports
universe u_1 u_2

namespace GlobalTheory.AdditiveValuationProduct

theorem addVal_prod : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ι : Type u_2} (s : Finset ι) (a : ι → R), (IsDiscreteValuationRing.addVal R : R → ℕ∞) (∏ i ∈ s, a i) = ∑ i ∈ s, (IsDiscreteValuationRing.addVal R : R → ℕ∞) (a i) := by
  intro R _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]

end GlobalTheory.AdditiveValuationProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneSubSmulPeirceCut
namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]

variable {A}

end GlobalTheory.PeirceDecompositionCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.StructureHomApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.SectionsCommRing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def structureHom (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom

theorem map_structureHom (s : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (structureHom s U r) = structureHom s V r := by
  show ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = _
  rw [← X.presheaf.map_comp]
  rfl

def Sections (_s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Type u := Γ(X, U)

namespace Sections

variable (s : X ⟶ Spec (CommRingCat.of R))

instance (U : X.Opens) : CommRing (Sections s U) := inferInstanceAs (CommRing Γ(X, U))

instance (U : X.Opens) : Algebra R (Sections s U) :=
  RingHom.toAlgebra (R := R) (S := Sections s U) (structureHom s U)

def restrict {U V : X.Opens} (h : V ≤ U) : Sections s U →ₐ[R] Sections s V where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := map_structureHom s h r

end Sections

end GlobalTheory.SectionsCommRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisMapOfLiftBaseChangeSurjective
open Module Function
open scoped TensorProduct Pointwise

namespace GlobalTheory

namespace Avoid

section Union

end Union

section Pick

theorem _root_.GlobalTheory.Avoid.exists_basis_map_one_tmul_of_surjective {K L V W ι : Type*} [CommRing K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [Module.Finite L W] {d : ℕ} (hd : finrank L W = d) (G : L ⊗[K] V →ₗ[L] W)
    (hG : Surjective G) (v : ι → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ (σ : Fin d → ι) (b : Basis (Fin d) L W), Injective σ ∧ ∀ k, b k = G (1 ⊗ₜ v (σ k)) := by
  classical
  have hspanT : Submodule.span L (Set.range fun i => (1 : L) ⊗ₜ[K] v i) = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul l y =>
      have hy : y ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
      have h1 : TensorProduct.mk K L V 1 y ∈
          Submodule.span K (TensorProduct.mk K L V 1 '' Set.range v) :=
        Submodule.apply_mem_span_image_of_mem_span _ hy
      have h2 := Submodule.span_le_restrictScalars K L _ h1
      rw [← Set.range_comp] at h2
      have h3 : l ⊗ₜ[K] y = l • ((1 : L) ⊗ₜ[K] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h3]
      exact Submodule.smul_mem _ l h2
    | add a b ha hb => exact add_mem ha hb
  have hw : Submodule.span L (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) = ⊤ := by
    have h : (Set.range fun i => G ((1 : L) ⊗ₜ[K] v i)) =
        G '' Set.range fun i => (1 : L) ⊗ₜ[K] v i := by
      rw [← Set.range_comp]; rfl
    rw [h, Submodule.span_image, hspanT, Submodule.map_top, LinearMap.range_eq_top.mpr hG]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' L fun i => G ((1 : L) ⊗ₜ[K] v i)
  let b := Basis.mk hli (hspan.trans hw).ge
  haveI : Finite κ := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by rw [← hd, Module.finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, b.reindex e.symm, ha.comp e.injective, fun k => ?_⟩
  simp [b, Basis.mk_apply]

end Pick

section Minor

open exteriorPower

theorem _root_.GlobalTheory.Avoid.exists_orderEmbedding_minor_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Fin r ↪o ι, pairingDual K V r (ιMulti K r fun k => c (J k)) x ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  have hall : ∀ φ : ⋀[K]^r (Dual K V), pairingDual K V r φ x = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span K (Set.range (ιMulti_family K r c)) := by
      rw [ιMulti_family_span_of_span K hc]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      exact hne (Set.powersetCard.ofFinEmbEquiv.symm s)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul t y _ hy => simp [hy]
  let b := Basis.ofVectorSpace K V
  letI : LinearOrder (Basis.ofVectorSpaceIndex K V) := IsWellOrder.linearOrder WellOrderingRel
  let B := b.exteriorPower r
  have hcoord : ∀ s, B.coord s = ιMultiDual K r b s := fun s => B.ext fun t => by
    have hBt : B t = ιMulti_family K r b t := by simp [B, Module.Basis.exteriorPower]
    rw [Basis.coord_apply, B.repr_self, hBt]
    by_cases hst : s = t
    · subst hst
      rw [ιMultiDual_apply_diag, Finsupp.single_eq_same]
    · rw [ιMultiDual_apply_nondiag K r b s t hst, Finsupp.single_eq_of_ne hst]
  apply hx
  refine B.ext_elem fun s => ?_
  rw [map_zero, Finsupp.zero_apply, ← B.coord_apply, hcoord]
  exact hall _

end Minor

end Avoid

universe u v w x y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries
namespace GlobalTheory.BoundedPowerSeriesDisc

open PowerSeries

section General

variable {K : Type*} [NormedField K]

theorem summable_norm_of_bounded {a : ℕ → K} {B : ℝ} (ha : ∀ n, ‖a n‖ ≤ B) {t : K}
    (ht : ‖t‖ < 1) : Summable fun n => ‖a n * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left B)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg t) n)

theorem tsum_coeff_mul [CompleteSpace K] (f g : K⟦X⟧) (t : K)
    (hf : Summable fun n => ‖coeff n f * t ^ n‖) (hg : Summable fun n => ‖coeff n g * t ^ n‖) :
    ∑' n, coeff n (f * g) * t ^ n = (∑' n, coeff n f * t ^ n) * ∑' n, coeff n g * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = n := by simpa using hp
  rw [pow_add]
  ring

theorem tsum_coeff_C (c t : K) : ∑' n, coeff n (C c : K⟦X⟧) * t ^ n = c := by
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]

end General

section Integral

variable {O : Type*} [Semiring O] {K : Type*} [NormedField K] [CompleteSpace K]

noncomputable def evalDisc (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) :
    O⟦X⟧ →+* K where
  toFun f := ∑' n, i (coeff n f) * t ^ n
  map_one' := by
    have := tsum_coeff_C (1 : K) t
    rw [map_one, ← map_one (PowerSeries.map i)] at this
    simpa only [coeff_map] using this
  map_mul' f g := by
    have := tsum_coeff_mul (PowerSeries.map i f) (PowerSeries.map i g) t
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n f)) ht)
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n g)) ht)
    rw [← map_mul] at this
    simpa only [coeff_map] using this
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_of_bounded (fun n => hi (coeff n f)) ht).of_norm.tsum_add
      (summable_norm_of_bounded (fun n => hi (coeff n g)) ht).of_norm]
    simp only [map_add (f := _), add_mul]

variable (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)

end Integral

section Bounded

def boundedSeries (F : Type*) [NormedField F] [IsUltrametricDist F] : Subring F⟦X⟧ where
  carrier := {f | ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨A * B, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA0 hB0)
      fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA _) (hB _) (norm_nonneg _) hA0
  one_mem' := ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, fun n => ?_⟩
    rw [map_add (f := _)]
    exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro f ⟨A, hA⟩
    exact ⟨A, fun n => by simpa using hA n⟩

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

theorem mem_boundedSeries {f : F⟦X⟧} :
    f ∈ boundedSeries F ↔ ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B := by exact Iff.rfl

theorem summable_norm_boundedSeries (f : boundedSeries F) {π : F} (hπ : ‖π‖ < 1) :
    Summable fun n => ‖coeff n (f : F⟦X⟧) * π ^ n‖ := by
  obtain ⟨B, hB⟩ := mem_boundedSeries.1 f.2
  exact summable_norm_of_bounded hB hπ

variable [CompleteSpace F]

noncomputable def evalBounded (π : F) (hπ : ‖π‖ < 1) : boundedSeries F →+* F where
  toFun f := ∑' n, coeff n (f : F⟦X⟧) * π ^ n
  map_one' := by simpa only [map_one, OneMemClass.coe_one] using tsum_coeff_C (1 : F) π
  map_mul' f g := tsum_coeff_mul (f : F⟦X⟧) g π (summable_norm_boundedSeries f hπ)
    (summable_norm_boundedSeries g hπ)
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_boundedSeries f hπ).of_norm.tsum_add
      (summable_norm_boundedSeries g hπ).of_norm]
    simp only [Subring.coe_add, map_add (f := _), add_mul]

variable (π : F) (hπ : ‖π‖ < 1)

end Bounded

end GlobalTheory.BoundedPowerSeriesDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RootCharOfAddNatCast
namespace GlobalTheory.RootCharacter

open scoped BigOperators

variable {B : Type*} [CommMonoid B] {I : Type*} [Fintype I] {n : ℕ} [NeZero n]

theorem pow_val_add {x : B} (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

def rootChar (u : I → B) (hu : ∀ q, u q ^ n = 1) : Multiplicative (I → ZMod n) →* B where
  toFun a := ∏ q, u q ^ (Multiplicative.toAdd a q).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => pow_val_add (hu q) _ _

end GlobalTheory.RootCharacter
end
