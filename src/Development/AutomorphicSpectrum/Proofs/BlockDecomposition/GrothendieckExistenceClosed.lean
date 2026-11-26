module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforward
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedAltBis

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem killed_restrictSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData)
    (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ)
    (h : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U) (e : ℕ) :
    Killed J (restrictSys I D S c e) := by
  intro U a ha x
  have hle : (Subobject.pullback D.arrow).obj (S (e + c)) ≤ GlobalTheory.CompanionTheory.GE.restrictSys I D S c e := by
    unfold GlobalTheory.CompanionTheory.GE.restrictSys
    exact le_sup_left
  have hmem : a • x ∈ GlobalTheory.CompanionTheory.GE.secs ((Subobject.pullback D.arrow).obj (S (e + c))) U := by
    rw [GlobalTheory.T.subobject_pullback_sections, Set.mem_preimage, Scheme.Modules.Hom.app_smul]
    exact h (e + c) U a ha _ (by unfold GlobalTheory.CompanionTheory.GE.secs; exact Set.mem_range_self x)
  unfold GlobalTheory.CompanionTheory.GE.secs at hmem ⊢
  obtain ⟨y, hy⟩ := hmem
  refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (Subobject.ofLE _ _ hle) U) y, ?_⟩
  rw [← hy, ← Subobject.ofLE_arrow hle, Scheme.Modules.Hom.comp_app] <;> rfl

end GlobalTheory.CompanionTheory.GE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedSystemKilledByIdealStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_system_killed_by_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules} (J : X.IdealSheafData) (D : Subobject E) (S : ℕ → Subobject E) (c : ℕ), (∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U) → ∀ e, Killed J (restrictSys I D S c e) := by
  exact @GlobalTheory.CompanionTheory.GE.killed_restrictSys
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.NonPrime

variable {X : Scheme.{0}}

lemma secs_mk {E F : X.Modules} (f : F ⟶ E) [Mono f] (V : X.Opens) :
    secs (Subobject.mk f) V = Set.range (f.app V) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro ⟨t, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.app V t, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.underlyingIso_arrow]

lemma smul_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} (a : Γ(X, V)) {x : Γ(E, V)}
    (hx : x ∈ secs S V) : a • x ∈ secs S V := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨a • t, Scheme.Modules.Hom.app_smul S.arrow a t⟩

lemma add_mem_secs {E : X.Modules} (S : Subobject E) {V : X.Opens} {x y : Γ(E, V)}
    (hx : x ∈ secs S V) (hy : y ∈ secs S V) : x + y ∈ secs S V := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨s + t, map_add _ s t⟩

def idealSub (J : X.IdealSheafData) (E : X.Modules) : Subobject E :=
  Subobject.mk (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))

lemma secs_idealSub (J : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (U : X.affineOpens) :
    secs (idealSub J E) U = ((J.ideal U • ⊤ : Submodule Γ(X, U) Γ(E, U)) : Set Γ(E, U)) := by
  rw [idealSub, secs_mk, ← (GlobalTheory.surjective_and_ker_unit_subschemeι J E U).2,
    ← GlobalTheory.QCoh.range_kernel_ι_app]
  rfl

lemma isQuasicoherent_idealSub (J : X.IdealSheafData) {E : X.Modules} (hE : IsCoherent E) :
    ((idealSub J E : Subobject E) : X.Modules).IsQuasicoherent := by
  have := hE.1
  have := (isCoherent_pullback J.subschemeι hE).1
  have h₀ : ((𝟭 X.Modules).obj E).IsQuasicoherent := hE.1
  have h₁ : ((Scheme.Modules.pullback J.subschemeι ⋙ Scheme.Modules.pushforward J.subschemeι).obj
      E).IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom J.subschemeι
    ((Scheme.Modules.pullback J.subschemeι).obj E)
  have hk : (kernel ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app
      E)).IsQuasicoherent := GlobalTheory.QCoh.isQuasicoherent_kernel _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app E))).symm hk

lemma propSupp_mono {A : Type} [CommRing A] [X.Over (Spec (.of A))] {E : X.Modules}
    {S S' : Subobject E} (h : S ≤ S') (hS : PropSupp A S) : PropSupp A S' := by
  obtain ⟨T, hT, hsupp⟩ := hS
  refine ⟨T, hT, ?_⟩
  have w : S.arrow ≫ cokernel.π S'.arrow = 0 := by
    rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  have : Epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) :=
    epi_of_epi_fac (cokernel.π_desc S.arrow (cokernel.π S'.arrow) w)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc S.arrow (cokernel.π S'.arrow) w) hsupp

theorem statement_of_mul_mem : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J J₁ J₂ : X.IdealSheafData),
    (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) →
    Statement I J₁ → Statement I J₂ → Statement I J := by
  intro A _ _ I X _ _ _ _ J J₁ J₂ hm h₁ h₂ E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hEq : E.IsQuasicoherent := hE.1
  set K : Subobject E := idealSub J₁ E with hKdef
  have hKq : (K : X.Modules).IsQuasicoherent := isQuasicoherent_idealSub J₁ hE
  have hS1 : ClosedSys I E (fun e => S e ⊔ K) :=
    { qcoh := fun e => (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh e) hKq).1
      pow_le := fun e => (hS.pow_le e).trans le_sup_left
      succ := fun e => by
        conv_lhs => rw [hS.succ e]
        exact sup_right_comm _ _ _ }
  have hK1 : ∀ e, Killed J₁ (S e ⊔ K) := by
    intro e U a ha x
    have hax : a • x ∈ secs K U := by
      rw [hKdef, secs_idealSub]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact (GlobalTheory.T.subobject_le_iff_affine_sections K (S e ⊔ K)).1 le_sup_right U hax
  obtain ⟨B, hBq, hBP, hB⟩ := h₁ E hE _ hS1 hK1 (propSupp_mono le_sup_left hP)
  have hDq : ((B ⊔ K : Subobject E) : X.Modules).IsQuasicoherent :=
    (GlobalTheory.T.quasicoherent_sup_sections hEq _ _ hBq hKq).1
  have hDP : PropSupp A (B ⊔ K) := propSupp_mono le_sup_left hBP
  have hc : ∀ e, S (e + 0) ≤ (B ⊔ K) ⊔ powSub I E (e + 1) := fun e =>
    (le_sup_left : S e ≤ S e ⊔ K).trans ((hB e).symm.le.trans (sup_le_sup_right le_sup_left _))
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP (B ⊔ K) hDq 0 hc
  have hkill : ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J₂.ideal U →
      ∀ x ∈ secs (B ⊔ K) U, a • x ∈ secs (S n) U := by
    intro n U a ha x hx
    have hle : B ⊔ K ≤ S n ⊔ K :=
      sup_le ((le_sup_left : B ≤ B ⊔ powSub I E (n + 1)).trans (hB n).le) le_sup_right
    have hx' := (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 hle U hx
    rw [(GlobalTheory.T.quasicoherent_sup_sections hEq _ _ (hS.qcoh n) hKq).2 U U.2] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    rw [smul_add]
    refine add_mem_secs _ (smul_mem_secs _ a hs) ?_
    rw [hKdef, secs_idealSub] at hk
    refine Submodule.smul_induction_on (p := fun k => a • k ∈ secs (S n) U) hk
      (fun b hb y _ => ?_) (fun y z hy hz => ?_)
    · rw [smul_smul, mul_comm]
      exact hK n U _ (hm U b a hb ha) y
    · rw [smul_add]
      exact add_mem_secs _ hy hz
  exact halg (h₂ _ (GlobalTheory.T.coherent_subobject_coherent hE _ hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J₂ _ S c' hkill) hP') hDP

end GlobalTheory.CompanionTheory.GE.NonPrime
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdealStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_product_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J J₁ J₂ : X.IdealSheafData), (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) → Statement I J₁ → Statement I J₂ → Statement I J := by
  first | exact @GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem | exact GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem | (intros; apply GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdeal
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdealStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_top_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))], Statement I (⊤ : X.IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Unit.statement_top | exact GlobalTheory.CompanionTheory.GE.Unit.statement_top | (intros; apply GlobalTheory.CompanionTheory.GE.Unit.statement_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGt
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem idealSheafData_wellFoundedGT :
    ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  intro X _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, hUt, hxU⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  have hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1)) := fun i => by
    have : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) :=
      IsLocallyNoetherian.component_noetherian i.1
    infer_instance
  let φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) :=
    fun I i => I.ideal i.1
  have hφ : StrictMono φ := by
    refine Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_
    intro I J h
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov
      (fun i => congrFun h i)
  have h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) := h1
  exact hφ.wellFoundedGT

end GlobalTheory.CompanionTheory.GE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSheafWellFoundedGtStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_sheaf_well_founded_gt : ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  first | exact @GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | exact GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT | (intros; apply GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Dich

open TopologicalSpace Scheme.IdealSheafData

theorem isReduced_subscheme_of_radical_eq {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : J.radical = J) : IsReduced J.subscheme := by
  have : ∀ U, IsReduced (J.subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ J.ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    have e : (J.ideal U).radical = J.ideal U := congr($(h).ideal U)
    exact Ideal.radical_eq_iff.mp e
  exact IsReduced.of_openCover _ J.subschemeCover.openCover

theorem irreducibleSpace_subscheme {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : IsIrreducible (J.support : Set X)) : IrreducibleSpace J.subscheme := by
  have hr : Set.range J.subschemeι = (J.support : Set X) := J.range_subschemeι
  have hirr : IsIrreducible (Set.range J.subschemeι) := hr ▸ h
  have : IrreducibleSpace (Set.range J.subschemeι) :=
    { toPreirreducibleSpace := Subtype.preirreducibleSpace hirr.2
      toNonempty := hirr.1.to_subtype }
  exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this

theorem exists_radical_pow_le {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData) :
    ∃ k : ℕ, J.radical ^ k ≤ J := by
  have hU : ∀ U : X.affineOpens, ∃ k : ℕ, (J.ideal U).radical ^ k ≤ J.ideal U := fun U => by
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose k hk using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.sup k, le_of_iSup_eq_top (fun i : t => i.1) ?_ fun i => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change (J.ideal i.1).radical ^ t.sup k ≤ J.ideal i.1
    exact (Ideal.pow_le_pow_right (Finset.le_sup i.2)).trans (hk i.1)

theorem exists_of_radical_ne {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData)
    (hJ : J ≠ ⊤) (hr : J.radical ≠ J) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  classical
  have hex := exists_radical_pow_le J
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, J.radical ^ (m + 1) ≤ J ∧ ¬ J.radical ^ m ≤ J := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · have hs := Nat.find_spec hex
      rw [hk, pow_zero] at hs
      exact absurd (top_le_iff.mp hs) hJ
    · refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
      rw [Nat.sub_add_cancel hk]
      exact Nat.find_spec hex
  refine ⟨J.radical, J ⊔ J.radical ^ m, lt_of_le_of_ne J.le_radical hr.symm,
    left_lt_sup.mpr hm₂, fun U a b ha hb => ?_⟩
  have hle : J.radical.ideal U * (J ⊔ J.radical ^ m).ideal U ≤ J.ideal U := by
    change J.radical.ideal U * (J.ideal U ⊔ (J.radical.ideal U) ^ m) ≤ J.ideal U
    rw [Ideal.mul_sup]
    refine sup_le Ideal.mul_le_right ?_
    rw [← pow_succ']
    exact hm₁ U
  exact hle (Ideal.mul_mem_mul ha hb)

theorem exists_of_not_preirreducible {X : Scheme.{0}} (J : X.IdealSheafData)
    (hr : J.radical = J) (hirr : ¬ IsPreirreducible (J.support : Set X)) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  push_neg at hirr
  obtain ⟨Z₁, Z₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hirr
  let C₁ : Closeds X := J.support ⊓ ⟨Z₁, h₁⟩
  let C₂ : Closeds X := J.support ⊓ ⟨Z₂, h₂⟩
  have hsup : C₁ ⊔ C₂ = J.support := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hlt : ∀ (C : Closeds X) (Z : Set X), C ≤ J.support → (C : Set X) ⊆ Z →
      ¬ (J.support : Set X) ⊆ Z → J < vanishingIdeal C := by
    intro C Z hC hCZ hn
    refine lt_of_le_not_ge (le_support_iff_le_vanishingIdeal.mp hC) fun hle => hn ?_
    intro x hx
    have hx' : x ∈ ((vanishingIdeal C).support : Set X) := support_antitone hle hx
    rw [coe_support_vanishingIdeal] at hx'
    exact hCZ hx'
  refine ⟨vanishingIdeal C₁, vanishingIdeal C₂, hlt C₁ Z₁ inf_le_left (fun x hx => hx.2) hn₁,
    hlt C₂ Z₂ inf_le_left (fun x hx => hx.2) hn₂, fun U a b ha hb => ?_⟩
  have e : vanishingIdeal C₁ ⊓ vanishingIdeal C₂ = J := by
    rw [← vanishingIdeal_sup, hsup, vanishingIdeal_support, hr]
  have hm : a * b ∈ (vanishingIdeal C₁ ⊓ vanishingIdeal C₂).ideal U :=
    ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩
  rwa [e] at hm

theorem isIntegral_or_exists_mul_mem : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData),
    J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧
      ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U →
        a * b ∈ J.ideal U := by
  intro X _ J hJ
  by_cases hr : J.radical = J
  · by_cases hirr : IsPreirreducible (J.support : Set X)
    · left
      have hne : (J.support : Set X).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        exact hJ (J.support_eq_bot_iff.mp (SetLike.coe_injective h))
      haveI := isReduced_subscheme_of_radical_eq J hr
      haveI := irreducibleSpace_subscheme J ⟨hne, hirr⟩
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    · exact Or.inr (exists_of_not_preirreducible J hr hirr)
  · exact Or.inr (exists_of_radical_ne J hJ hr)

end GlobalTheory.CompanionTheory.GE.Dich
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplitStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_ideal_integral_or_split : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData), J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  first | exact @GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | exact GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | (intros; apply GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegral
set_option autoImplicit false
set_option maxSynthPendingDepth 1

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  TopologicalSpace

namespace GlobalTheory.CompanionTheory.GE.ChowOpen

lemma isClosedImmersion_restrict_iSup {T Z : Scheme.{0}} (f : T ⟶ Z) {ι : Type} (V : ι → Z.Opens)
    (h : ∀ i, IsClosedImmersion (f ∣_ V i)) : IsClosedImmersion (f ∣_ (⨆ i, V i)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => (⨆ i, V i).ι ⁻¹ᵁ V i) ?_ ?_
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · intro i
    have hV : (⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i) = V i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup V i)
    have e := morphismRestrictRestrict f (⨆ i, V i) ((⨆ i, V i).ι ⁻¹ᵁ V i)
    have h' : IsClosedImmersion (f ∣_ ((⨆ i, V i).ι ''ᵁ ((⨆ i, V i).ι ⁻¹ᵁ V i))) := by
      rw [hV]; exact h i
    exact (MorphismProperty.arrow_mk_iso_iff (@IsClosedImmersion) e).2 h'

theorem exists_image_open {T Z : Scheme.{0}} (f : T ⟶ Z) [QuasiCompact f] (S : Z.Opens)
    [IsClosedImmersion (f ∣_ S)] (hS : f ⁻¹ᵁ S = ⊤) :
    ∃ (O : f.image.Opens) (φ : O.toScheme ⟶ T), IsIso φ ∧ φ ≫ f = O.ι ≫ f.imageι := by
  have hι : IsIso (f ⁻¹ᵁ S).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    exact ⟨inferInstance, ⟨by rw [← Set.range_eq_univ, Scheme.Opens.range_ι, hS]; rfl⟩⟩
  refine ⟨f.imageι ⁻¹ᵁ S, SchemeImage.imageRestrictLift f S ≫ (f ⁻¹ᵁ S).ι, inferInstance, ?_⟩
  rw [Category.assoc, ← morphismRestrict_ι, SchemeImage.imageRestrictLift_fac_assoc,
    morphismRestrict_ι]

theorem exists_chow_open_projective {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (s : X ⟶ Spec (.of A)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    [IrreducibleSpace X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ s ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian X := ⟨⟩
  have hex : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := htne.card_pos; omega⟩
  let e : Fin (k + 1) ≃ t := (Fintype.equivFinOfCardEq (by simpa using hk)).symm
  let U : Fin (k + 1) → X.Opens := fun j => V (e j)
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hVaff _
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨e.symm ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hc := fun j => ProjSpace.exists_closedImmersion_stdOpen (A := A) s (hUaff j)
  choose n c hccl hcc using hc
  have : ∀ j, IsClosedImmersion (c j) := hccl
  have hη : genericPoint X ∈ ChowGraph.W U := by
    rw [ChowGraph.W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ((genericPoint_spec X).mem_open_set_iff (U j).2).2
      ⟨e j, Set.mem_univ _, hxV _⟩
  have : NoetherianSpace (ChowGraph.W U).toScheme :=
    NoetherianSpace.set ((ChowGraph.W U : X.Opens) : Set X)
  have : QuasiCompact (ChowGraph.g s n U c hcc) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hqc : QuasiCompact (ChowGraph.q s n U c hcc) := by
    unfold ChowGraph.q; infer_instance
  have hcl : IsClosedImmersion
      (ChowGraph.q s n U c hcc ∣_ (⨆ i, ChowGraph.V (A := A) n i)) :=
    isClosedImmersion_restrict_iSup _ _ fun i =>
      ChowGraph.isClosedImmersion_q_restrict s n U c hcc i
  have hS : ChowGraph.q s n U c hcc ⁻¹ᵁ (⨆ i, ChowGraph.V (A := A) n i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : ChowGraph.π s n U c hcc y ∈ (⊤ : X.Opens) := trivial
    rw [← hU] at hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, ChowGraph.q_mem_V s n U c hcc i y hi⟩
  obtain ⟨O, φ, hφ, hφq⟩ := exists_image_open (ChowGraph.q s n U c hcc) _ hS
  have hπ : IsProper (ChowGraph.π s n U c hcc) := by
    unfold ChowGraph.π; infer_instance
  refine ⟨ProjSpace.multiProjDim k n, (ChowGraph.q s n U c hcc).image,
    (ChowGraph.q s n U c hcc).imageι ≫ ProjSpace.multiProjEmb A k n, O,
    φ ≫ ChowGraph.π s n U c hcc, ChowGraph.W U, inferInstance, inferInstance, ?_, ⟨_, hη⟩, ?_⟩
  · rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, ← Category.assoc, ← hφq]
    simp only [ChowGraph.q, ChowGraph.π, Category.assoc, pullback.condition]
  · rw [morphismRestrict_comp]
    have := ChowGraph.isIso_π_restrict s n U c hcc
    have h1 : IsIso (φ ∣_ (ChowGraph.π s n U c hcc ⁻¹ᵁ ChowGraph.W U)) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hφ _
    exact IsIso.comp_isIso' h1 this

theorem exists_chow_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X] :
    ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens)
      (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧
      O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧
      IsIso (ψ ∣_ W) :=
  exists_chow_open_projective (X ↘ Spec (.of A))

end GlobalTheory.CompanionTheory.GE.ChowOpen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChowCoverIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chow_cover_integral : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] [IsIntegral X], ∃ (N : ℕ) (Y : Scheme.{0}) (i : Y ⟶ projectiveSpace A N) (O : Y.Opens) (ψ : (O : Scheme.{0}) ⟶ X) (W : X.Opens), IsClosedImmersion i ∧ IsProper ψ ∧ O.ι ≫ i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)) ∧ (W : Set X).Nonempty ∧ IsIso (ψ ∣_ W) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | exact GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open | (intros; apply GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosed
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GroundTheory.Arith.SchemeCoh
namespace GlobalTheory.CompanionTheory.GE

theorem step_integral {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (IH : ∀ J' : X.IdealSheafData, J < J' → Statement I J') : Statement I J := by
  intro E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  letI : J.subscheme.Over (Spec (.of A)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of A))⟩
  have h1 : IsSeparated (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : IsSeparated (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h2 : LocallyOfFiniteType (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : LocallyOfFiniteType (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h3 : QuasiCompact (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : QuasiCompact (J.subschemeι ≫ (X ↘ Spec (.of A))))
  obtain ⟨N, Y, i, O, ψ, W, hi, hψ, hcomm, hW, hiso⟩ := GlobalTheory.T.exists_chow_cover_integral (A := A) (X := J.subscheme)
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩
  have hZ : Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := GlobalTheory.T.formal_existence_projective_open I hI i hi O
  have hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = ((O : Scheme.{0}) ↘ Spec (.of A)) := by
    change (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = O.ι ≫ i ≫ ProjSpace.toSpecBase A N
    rw [hcomm, Category.assoc]
    rfl
  obtain ⟨D, c, J', hDq, hDP, hc, hJ, hkill⟩ := GlobalTheory.T.formal_existence_proper_pushforward I hI J hZ ψ hψ hover W hW hiso hE hS hK hP
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP D hDq c hc
  exact halg (IH J' hJ _ (GlobalTheory.T.coherent_subobject_coherent hE D hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J' D S c' hkill) hP') hDP

theorem statement_bot {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    (X : Scheme.{0}) [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] :
    Statement I (⊥ : X.IdealSheafData) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hwf : WellFoundedGT X.IdealSheafData := GlobalTheory.T.ideal_sheaf_well_founded_gt
  refine WellFoundedGT.induction (motive := fun J : X.IdealSheafData => Statement I J) ⊥ ?_
  intro J IH
  by_cases hJ : J = ⊤
  · subst hJ
    exact GlobalTheory.T.formal_existence_top_ideal I
  rcases GlobalTheory.T.noetherian_ideal_integral_or_split J hJ with h | ⟨J₁, J₂, h₁, h₂, hm⟩
  · exact step_integral I hI J IH
  · exact GlobalTheory.T.formal_existence_product_ideal I J J₁ J₂ hm (IH _ h₁) (IH _ h₂)

theorem geClosed : GEClosed :=
  GlobalTheory.T.geClosed_of_statement_bot fun _ _ _ I hI X _ _ _ _ => statement_bot I hI X

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closed : GEClosed := by
  first | exact @GlobalTheory.CompanionTheory.GE.geClosed | exact GlobalTheory.CompanionTheory.GE.geClosed | (intros; apply GlobalTheory.CompanionTheory.GE.geClosed <;> assumption)
end
