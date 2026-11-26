module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

end General

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]


end Dedekind

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

end PID

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]


variable (R M) in
theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := N)

end Valuation

universe u

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
open TensorProduct Function

namespace GlobalTheory

section LinearAlgebra

variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem exact_lTensor_iff_of_faithfullyFlat (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by
  have h1 := Module.FaithfullyFlat.lTensor_exact_iff_exact k L (f.baseChange k) (g.baseChange k)
  have h2 : Exact (AlgebraTensorModule.lTensor k L f) (AlgebraTensorModule.lTensor k L g) ↔
      Exact ((f.baseChange k).lTensor L) ((g.baseChange k).lTensor L) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k L A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k L B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k L C)
      (by ext; simp) (by ext; simp)
  exact h2.trans h1

theorem exact_lTensor_iff_residueField (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let φ : p.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ p (Algebra.ofId R L) hL.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hL ▸ h0))
  letI : Algebra p.ResidueField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exact_lTensor_iff_of_faithfullyFlat p.ResidueField L f g

theorem split_injective_of_forall_lTensor_residueField_injective [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Injective ((l.baseChange (Localization.AtPrime m)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField C) ∘
          ((l.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (l.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField B) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) l) x).symm
    exact Injective.of_comp (e ▸ (h m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] C) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Injective l := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    refine Module.subsingleton_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] LinearMap.ker l)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).2 (hloc m)
    have h1 : Injective (l.lTensor (Localization.AtPrime m)) :=
      HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
    have h2 : Injective ((LinearMap.ker l).subtype.lTensor (Localization.AtPrime m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine (subsingleton_iff_forall_eq 0).2 fun y => h2 (h1 ?_)
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  have : Module.FinitePresentation R (C ⧸ LinearMap.range l) :=
    Module.finitePresentation_of_surjective (LinearMap.range l).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map l)
  have : Module.Projective R (C ⧸ LinearMap.range l) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (C ⧸ LinearMap.range l))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (l.baseChange (Localization.AtPrime m))
      ((LinearMap.range l).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ l.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have := (Exact.split_tfae l.exact_map_mkQ_range hinj (Submodule.mkQ_surjective _)).out 1 2
  rw [← this]
  exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

theorem lTensor_liftQ_injective_of_exact (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := (h y).1 hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem exists_homotopy_of_forall_exact_residueField [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hfg
  obtain ⟨r, hr⟩ := split_injective_of_forall_lTensor_residueField_injective
    ((LinearMap.range f).liftQ g hle) fun m _ => lTensor_liftQ_injective_of_exact _ hle (h m)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ r
    (Submodule.mkQ_surjective _)
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ g : B →ₗ[R] B) b ∈ LinearMap.range f := by
    intro b
    have h1 := LinearMap.congr_fun ht (g b)
    have h2 := LinearMap.congr_fun hr (Submodule.Quotient.mk b)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      LinearMap.id_apply] at h1 h2
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ← Submodule.Quotient.eq,
      h1, h2]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
  refine ⟨s, t, LinearMap.ext fun b => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hs b)
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.rangeRestrict] at this
  simp [this]

theorem forall_exact_residueField_of_isLocalRing [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) :=
  (exact_lTensor_iff_residueField m (IsLocalRing.ResidueField R)
    (IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal ‹_›).symm) f g).1 h

theorem exact_of_homotopy {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by
  intro x
  constructor
  · intro hx
    refine ⟨s x, ?_⟩
    simpa [hx] using LinearMap.congr_fun h x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hfg y

end LinearAlgebra

section Comparison

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D]

section ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable [PreservesColimitsOfShape WalkingParallelPair F]

end ShortComplex

section Complex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}

variable [PreservesColimitsOfShape WalkingParallelPair F]

end Complex

end Comparison

section Homotopy

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {ι : Type*} {c : ComplexShape ι}

end Homotopy

section Modules

open CategoryTheory Category Limits

universe u w

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem isZero_homology_extendScalars_iff (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* S, φ.toAlgebra = inst := ⟨_, toAlgebra_algebraMap⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p q r hp hr,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end Modules

section Explicit

open CategoryTheory Category Limits ChangeOfRings

universe u

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type*} {c : ComplexShape ι}

end Explicit

section Main

open CategoryTheory Category Limits

universe u

variable {R : Type u} [CommRing R]

end Main

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.QCoh.Qcqs

section Glue

variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)

theorem exists_smul_eq_zero_of_isCompact
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hbot : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (a : A W) (ha : φ W a = 0) :
    ∃ s ∈ S, s • a = 0 := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → ∀ a : A ⟨W, h⟩,
      φ ⟨W, h⟩ a = 0 → ∃ s ∈ S, s • a = 0) W hW ?_ ?_ hWU hW a ha
  · intro h _ a _
    have := hbot ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ a ha
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, e₁⟩ := ih T'.2 hT (rA h₁ a) (by rw [hφ, ha, map_zero])
    obtain ⟨s₂, hs₂, e₂⟩ := hker V' V.2 (rA h₂ a) (by rw [hφ, ha, map_zero])
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, sepA h₁ h₂ le_rfl _ ?_ ?_⟩
    · rw [map_smul, mul_comm, mul_smul, e₁, smul_zero]
    · rw [map_smul, mul_smul, e₂, smul_zero]

theorem exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hrB : ∀ {V₁ V₂ V₃} (h : V₁ ≤ V₂) (h' : V₂ ≤ V₃) (b : B V₃),
      rB h (rB h' b) = rB (h.trans h') b)
    (hbotA : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (hbotB : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (B V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (sepB : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ b : B W, rB h₁ b = 0 → rB h₂ b = 0 → b = 0)
    (glueA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ (a₁ : A V₁) (a₂ : A V₂), rA (inf_le_left : V₁ ⊓ V₂ ≤ V₁) a₁ = rA inf_le_right a₂ →
        ∃ a : A W, rA h₁ a = a₁ ∧ rA h₂ a = a₂)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (hsurj : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ b : B V, ∃ s ∈ S, ∃ a : A V, s • b = φ V a)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (hW' : IsQuasiSeparated (W.1 : Set X))
    (b : B W) : ∃ s ∈ S, ∃ a : A W, s • b = φ W a := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → IsQuasiSeparated (W : Set X) →
      ∀ b : B ⟨W, h⟩, ∃ s ∈ S, ∃ a : A ⟨W, h⟩, s • b = φ ⟨W, h⟩ a) W hW ?_ ?_ hWU hW hW' b
  · intro h _ _ b
    have := hbotB ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, 0, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ hqs b
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := ih T'.2 hT (hqs.of_subset Set.subset_union_left) (rB h₁ b)
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := hsurj V' V.2 (rB h₂ b)
    have hc : IsCompact ((T' ⊓ V').1 : Set X) :=
      hqs _ _ Set.subset_union_left T.2 hT Set.subset_union_right V.1.2 V.2.isCompact
    obtain ⟨s, hs, e⟩ := exists_smul_eq_zero_of_isCompact S U rA rB φ hφ hbotA sepA hker
      (T' ⊓ V') hc (s₂ • rA inf_le_left a₁ - s₁ • rA inf_le_right a₂) (by
        rw [map_sub, map_smul, map_smul, hφ, hφ, ← e₁, ← e₂, map_smul, map_smul, hrB, hrB,
          smul_comm, sub_self])
    obtain ⟨a, ha₁, ha₂⟩ := glueA h₁ h₂ le_rfl (s • s₂ • a₁) (s • s₁ • a₂) (by
      rw [smul_sub, sub_eq_zero] at e
      simpa only [map_smul] using e)
    refine ⟨s * (s₁ * s₂), mul_mem hs (mul_mem hs₁ hs₂), a, ?_⟩
    rw [← sub_eq_zero]
    refine sepB h₁ h₂ le_rfl _ ?_ ?_
    · rw [map_sub, ← hφ, ha₁, map_smul, map_smul, map_smul, ← e₁, mul_comm s₁, mul_smul, mul_smul,
        sub_self]
    · rw [map_sub, ← hφ, ha₂, map_smul, map_smul, map_smul, ← e₂, mul_smul, mul_smul, sub_self]

end Glue

section Sheaf

variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}

theorem subsingleton_sections_of_eq_bot (h : W = ⊥) : Subsingleton Γ(F, W) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{u + 1} ↦ i.elim) W (fun i ↦ i.elim) (by simp [h]) s t (fun i ↦ i.elim)

theorem section_eq_zero_of_res₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s : Γ(F, W))
    (e₁ : F.presheaf.map (homOfLE h₁).op s = 0) (e₂ : F.presheaf.map (homOfLE h₂).op s = 0) :
    s = 0 :=
  TopCat.Sheaf.eq_of_locally_eq₂ (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ (homOfLE h₁) (homOfLE h₂)
    h s 0 (e₁.trans (map_zero _).symm) (e₂.trans (map_zero _).symm)

theorem exists_section_glue₂ (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s₁ : Γ(F, V₁))
    (s₂ : Γ(F, V₂))
    (e : F.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.presheaf.map (homOfLE inf_le_right).op s₂) :
    ∃ s : Γ(F, W), F.presheaf.map (homOfLE h₁).op s = s₁ ∧
      F.presheaf.map (homOfLE h₂).op s = s₂ := by
  let 𝒰 : Bool → X.Opens := fun b ↦ Bool.rec V₁ V₂ b
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    𝒰 W (fun b ↦ Bool.rec (homOfLE h₁) (homOfLE h₂) b)
    (h.trans (sup_le (le_iSup 𝒰 false) (le_iSup 𝒰 true)))
    (fun b ↦ Bool.rec s₁ s₂ b) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact e
      · have := congr(F.presheaf.map (homOfLE (inf_comm V₂ V₁).le).op $e)
        rw [res_res, res_res] at this
        exact this.symm
      · rfl)
  exact ⟨s, hs false, hs true⟩

end Sheaf

section BasicOpen

variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

def resLinearOver (hW : W ≤ U) (hV : V ≤ U) (h : V ≤ W) :
    letI := resModule F hW
    letI := resModule F hV
    Γ(F, W) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F hW
  letI := resModule F hV
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ by
      change F.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE hW).op r • s) =
        X.presheaf.map (homOfLE hV).op r • F.presheaf.map (homOfLE h).op s
      rw [F.map_smul, res_res_ring hW h] }

variable [F.IsQuasicoherent]

theorem exists_pow_smul_eq_zero_of_isCompact (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : V ≤ U) (hV : V = X.basicOpen f) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE h).op t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, e⟩ := exists_smul_eq_zero_of_isCompact (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU t (by
      change F.presheaf.map (homOfLE inf_le_left).op t = 0
      rw [← res_res F h inf_le_right, ht, map_zero])
  refine ⟨n, ?_⟩
  rw [← res_self_ring le_rfl (f ^ n)]
  exact e

theorem exists_pow_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f)
    (s : Γ(F, V)) : ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1) := resModule F W.2
  letI (W : Set.Iic U) : Module Γ(X, U) Γ(F, W.1 ⊓ V) := resModule F (inf_le_right.trans h)
  obtain ⟨_, ⟨n, rfl⟩, t, e⟩ := exists_smul_eq_map_of_isCompact_of_isQuasiSeparated (.powers f) U
    (A := fun W ↦ Γ(F, W.1)) (B := fun W ↦ Γ(F, W.1 ⊓ V))
    (fun {W₁ W₂} h' ↦ resLinearOver F W₂.2 W₁.2 h')
    (fun {W₁ W₂} h' ↦ resLinearOver F _ _ (inf_le_inf_right V h'))
    (fun W ↦ resLinearOver F W.2 _ inf_le_left)
    (fun h' a ↦ (res_res F _ _ a).trans (res_res F _ _ a).symm)
    (fun h₁ h₂ b ↦ res_res F _ _ b)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F hW)
    (fun W hW ↦ subsingleton_sections_of_eq_bot F (by simp [hW]))
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F h₁ h₂ h₃)
    (fun h₁ h₂ h₃ ↦ section_eq_zero_of_res₂ F (inf_le_inf_right V h₁) (inf_le_inf_right V h₂)
      ((inf_le_inf_right V h₃).trans (inf_sup_right _ _ _).le))
    (fun h₁ h₂ h₃ ↦ exists_section_glue₂ F h₁ h₂ h₃)
    (fun W hW a ha ↦ by
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        inf_le_left (by rw [X.basicOpen_res, hV]) a ha
      exact ⟨f ^ n, ⟨n, rfl⟩, by rw [← map_pow] at hn; exact hn⟩)
    (fun W hW b ↦ by
      obtain ⟨n, a, hn⟩ := exists_pow_smul_eq_res F hW (X.presheaf.map (homOfLE (W.2 : W.1 ≤ U)).op f)
        (V := W.1 ⊓ V) inf_le_left (by rw [X.basicOpen_res, hV]) b
      exact ⟨f ^ n, ⟨n, rfl⟩, a, by rw [res_res_ring (show W.1 ≤ U from W.2), ← map_pow] at hn; exact hn⟩)
    ⟨U, Set.self_mem_Iic⟩ hU hU' (F.presheaf.map (homOfLE inf_le_right).op s)
  refine ⟨n, t, ?_⟩
  have e' : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (f ^ n) •
      F.presheaf.map (homOfLE inf_le_right).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := e
  have := congr(F.presheaf.map (homOfLE (le_inf h le_rfl)).op $e')
  rwa [F.map_smul, res_res, res_res, res_res_ring, res_self, map_pow] at this

theorem isLocalizedModule_resBasicOpen_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isLocalizedModule_resBasicOpen_iff F f).mpr
    ⟨exists_pow_smul_eq_res_of_qcqs F hU hU' f _ rfl,
      exists_pow_smul_eq_zero_of_isCompact F hU f _ rfl⟩

end BasicOpen

section Hom

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}

end Hom

end GlobalTheory.QCoh.Qcqs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
open IsDedekindDomain Function

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R]

theorem isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

section Submodules

variable (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Submodules

end General

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

section Torsion

variable {X : Type*} [AddCommGroup X] [Module O X] [Module.Finite O X]

variable [Ring.HasFiniteQuotients O]

variable [Module.Free ℤ O]

end Torsion

section Lattices

variable [Ring.HasFiniteQuotients O] [Module.Free ℤ O]

end Lattices

end Dedekind

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop
open Pointwise

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem nonempty_quotient_smul_top_equiv_pi {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (a : R) :
    Nonempty ((M ⧸ (a • ⊤ : Submodule R M)) ≃ₗ[R] (ι → R ⧸ Ideal.span {a})) := by
  let g : M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a} : Ideal R).mkQ ∘ₗ b.coord i
  have hg : ∀ x i, g x i = Ideal.Quotient.mk (Ideal.span {a}) (b.repr x i) := fun _ _ => rfl
  have hs : Function.Surjective g := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, funext fun i => ?_⟩
    rw [hg, ← hc i, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hk : (a • ⊤ : Submodule R M) = LinearMap.ker g := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, funext_iff]
    simp only [hg, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨b.repr y i, by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨b.equivFun.symm c, trivial, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply, b.equivFun_apply, ← hc i, Pi.smul_apply,
        smul_eq_mul, mul_comm]
  exact ⟨Submodule.quotEquivOfEq _ _ hk ≪≫ₗ g.quotKerEquivOfSurjective hs⟩

theorem length_quotient_smul_top_of_free [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) =
      Module.length R (R ⧸ Ideal.span {a}) * (Module.finrank R M : ℕ∞) := by
  rw [(nonempty_quotient_smul_top_equiv_pi (Module.finBasis R M) a).some.length_eq,
    Module.length_pi, mul_comm]
  simp

theorem submoduleOf_smul_self (A : Submodule R M) (a : R) :
    (a • A).submoduleOf A = (a • ⊤ : Submodule R A) := by
  ext x
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩

theorem relLength_smul_self_eq_length (A : Submodule R M) (a : R) :
    relLength A (a • A) = Module.length R (A ⧸ (a • ⊤ : Submodule R A)) := by
  rw [relLength_def, submoduleOf_smul_self]

end General

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quotient_span_singleton_dvr (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a :=
  Ring.ord_eq_addVal a

theorem addVal_irreducible_pow {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    addVal R (ϖ ^ e) = e := by
  rw [addVal_pow, addVal_uniformizer hϖ, nsmul_one]

section Free

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem length_quotient_smul_top_dvr (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) = addVal R a * (Module.finrank R M : ℕ∞) := by
  rw [length_quotient_smul_top_of_free, length_quotient_span_singleton_dvr]

end Free

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

theorem relLength_smul_self (hA : A.FG) (a : R) :
    relLength A (a • A) = addVal R a * (Module.finrank R A : ℕ∞) := by
  have : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  rw [relLength_smul_self_eq_length, length_quotient_smul_top_dvr]

theorem relLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    relLength A (a • A) = ((n * Module.finrank R A : ℕ) : ℕ∞) := by
  rw [relLength_smul_self hA, hn, Nat.cast_mul]

theorem relLength_irreducible_pow_smul_self (hA : A.FG) {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    relLength A (ϖ ^ e • A) = ((e * Module.finrank R A : ℕ) : ℕ∞) :=
  relLength_smul_self_of_addVal_eq hA (addVal_irreducible_pow hϖ e)

theorem relLength_smul_self_ne_top (hA : A.FG) {a : R} (ha : a ≠ 0) :
    relLength A (a • A) ≠ ⊤ := by
  rw [relLength_smul_self hA]
  exact WithTop.mul_ne_top (addVal_eq_top_iff.not.mpr ha) (ENat.coe_ne_top _)

theorem lengthCommensurable_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    LengthCommensurable A (a • A) :=
  (lengthCommensurable_iff_of_ge (Submodule.smul_le_self_of_tower a A)).mpr
    (relLength_smul_self_ne_top hA ha)

theorem signedLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by
  have ha : a ≠ 0 := addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)
  rw [← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge
    (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]

theorem signedLength_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) :=
  signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm

end DVR

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
namespace GlobalTheory

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

section Chain

theorem relLength_eq_add_of_le {A B C : Submodule R V} (hCB : C ≤ B) (hBA : B ≤ A) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
    (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
    (LinearMap.exact_subtype_ker_map _)
  have hker : LinearMap.ker (Submodule.factor hle) =
      (B.submoduleOf A).map (C.submoduleOf A).mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [hker, ← relLength_eq_length_map_mkQ, relLength_submoduleOf hBA] at hex
  rw [add_comm]
  exact hex

theorem relLength_inf_eq_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) = relLength A B + relLength (A ⊓ B) C := by
  have h := relLength_eq_add_of_le (A := A) (B := A ⊓ B) (C := A ⊓ B ⊓ C) inf_le_left inf_le_left
  rwa [relLength_inf_right, relLength_inf_right, inf_assoc, relLength_inf_right] at h

theorem relLength_le_add (A B C : Submodule R V) :
    relLength A C ≤ relLength A B + relLength B C :=
  calc relLength A C ≤ relLength A (B ⊓ C) := relLength_anti_right A inf_le_right
    _ = relLength A B + relLength (A ⊓ B) C := relLength_inf_eq_add A B C
    _ ≤ relLength A B + relLength B C := by
      gcongr
      exact inf_le_right

theorem relLength_inf_le_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) ≤ relLength A B + relLength A C := by
  rw [relLength_inf_eq_add]
  gcongr
  exact inf_le_left

theorem relLength_ne_top_trans {A B C : Submodule R V} (hAB : relLength A B ≠ ⊤)
    (hBC : relLength B C ≠ ⊤) : relLength A C ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hAB, hBC⟩) (relLength_le_add A B C)

theorem relLength_inf_ne_top_iff {A B C : Submodule R V} :
    relLength A (B ⊓ C) ≠ ⊤ ↔ relLength A B ≠ ⊤ ∧ relLength A C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_anti_right A inf_le_left),
      ne_top_of_le_ne_top h (relLength_anti_right A inf_le_right)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_inf_le_add A B C)⟩

end Chain

section Commensurable

variable {A A' B B' C : Submodule R V}

@[trans] theorem LengthCommensurable.trans (hAB : LengthCommensurable A B)
    (hBC : LengthCommensurable B C) : LengthCommensurable A C :=
  ⟨relLength_ne_top_trans hAB.1 hBC.1, relLength_ne_top_trans hBC.2 hAB.2⟩

theorem lengthCommensurable_iff_of_le_of_le (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by
  rw [lengthCommensurable_iff_of_ge hCB, lengthCommensurable_iff_of_ge hBA,
    lengthCommensurable_iff_of_ge (hCB.trans hBA), relLength_eq_add_of_le hCB hBA]
  exact WithTop.add_ne_top

namespace LengthCommensurable

theorem of_between_left (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).1

theorem of_between_right (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable B C :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).2

theorem inf_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) :=
  ⟨relLength_inf_ne_top_iff.mpr ⟨hAB.1, hAC.1⟩,
    ne_top_of_le_ne_top hAB.2 (relLength_mono_left inf_le_left A)⟩

theorem toNat_relLength_eq_add_of_le (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by
  rw [relLength_eq_add_of_le hCB hBA,
    ENat.toNat_add (h.of_between_left hCB hBA).1 (h.of_between_right hCB hBA).1]

theorem signedLength_eq_toNat_sub_of_le {D : Submodule R V} (h : LengthCommensurable A B)
    (hAD : LengthCommensurable A D) (hDA : D ≤ A) (hDB : D ≤ B) :
    signedLength A B = ((relLength A D).toNat : ℤ) - ((relLength B D).toNat : ℤ) := by
  have hBD : LengthCommensurable B D := h.symm.trans hAD
  have h₁ := hAD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_left
  have h₂ := hBD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_right
  rw [relLength_inf_right] at h₁
  rw [relLength_inf_right'] at h₂
  rw [h₁, h₂, signedLength]
  push_cast
  ring

theorem signedLength_eq_add (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A C = signedLength A B + signedLength B C := by
  have hAC := hAB.trans hBC
  have hAD : LengthCommensurable A (A ⊓ B ⊓ C) := ((refl A).inf_right hAB).inf_right hAC
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  have hC : A ⊓ B ⊓ C ≤ C := inf_le_right
  rw [hAB.signedLength_eq_toNat_sub_of_le hAD hA hB, hAC.signedLength_eq_toNat_sub_of_le hAD hA hC,
    hBC.signedLength_eq_toNat_sub_of_le (hAB.symm.trans hAD) hB hC]
  ring

end LengthCommensurable

end Commensurable

end GlobalTheory
end
