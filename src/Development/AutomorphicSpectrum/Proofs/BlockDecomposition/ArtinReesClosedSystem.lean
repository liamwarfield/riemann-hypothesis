module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecsMapArrow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem secs_map_arrow {X : Scheme.{0}} {E : X.Modules} (D : Subobject E)
    (B : Subobject (D : X.Modules)) (V : X.Opens) :
    secs ((Subobject.map D.arrow).obj B) V = (D.arrow.app V) '' secs B V := by
  have hmk : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    exact Subobject.map_mk _ _
  let e := Subobject.isoOfEqMk _ _ hmk
  have he : e.hom ≫ (B.arrow ≫ D.arrow) = ((Subobject.map D.arrow).obj B).arrow := by
    simp only [e, Subobject.isoOfEqMk_hom, Subobject.ofLEMk_comp]
  have he' : e.inv ≫ ((Subobject.map D.arrow).obj B).arrow = B.arrow ≫ D.arrow := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  ext y
  simp only [GlobalTheory.CompanionTheory.GE.secs]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(B.arrow.app V) ((e.hom.app V) x), ⟨_, rfl⟩, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(e.inv.app V) x, ?_⟩
    have h := congrArg (fun φ => ConcreteCategory.hom (Scheme.Modules.Hom.app φ V) x) he'
    simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h

end GlobalTheory.CompanionTheory.GE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobject
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobject
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}}

theorem hom_eq_zero_of_basis {M N : X.Modules} (φ : M ⟶ N) (P : X.Opens → Prop)
    (hP : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ B, P B ∧ B ≤ W ∧ x ∈ B)
    (h : ∀ B, P B → ∀ s : Γ(M, B), φ.app B s = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov : W ≤ ⨆ B : {B : X.Opens // P B ∧ B ≤ W}, B.1 := by
    intro x hx
    obtain ⟨B, hB, hBW, hxB⟩ := hP W x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨B, hB, hBW⟩, hxB⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun B : {B : X.Opens // P B ∧ B ≤ W} ↦ B.1) W
    (fun B ↦ homOfLE B.2.2) hcov _ _ fun B ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE B.2.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE B.2.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h B.1 B.2.1 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

theorem le_of_secs_basicOpen {E : X.Modules} (S T : Subobject E) (t : Set X.affineOpens)
    (ht : ∀ x : X, ∃ U ∈ t, x ∈ (U : X.Opens))
    (h : ∀ U ∈ t, ∀ f : Γ(X, (U : X.Opens)), secs S (X.basicOpen f) ⊆ secs T (X.basicOpen f)) :
    S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basis _
      (fun B ↦ ∃ U ∈ t, ∃ f : Γ(X, (U : X.Opens)), B = X.basicOpen f) ?_ ?_
    · intro W x hx
      obtain ⟨U, hU, hxU⟩ := ht x
      obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le (V := W) ⟨x, hx⟩ hxU
      exact ⟨X.basicOpen f, ⟨U, hU, f, rfl⟩, hfW, hxf⟩
    · rintro B ⟨U, hU, f, rfl⟩ s
      obtain ⟨y, hy⟩ := h U hU f ⟨s, rfl⟩
      have hz : (T.arrow ≫ cokernel.π T.arrow).app (X.basicOpen f) y = 0 := by
        rw [cokernel.condition]; rfl
      change (cokernel.π T.arrow).app _ (S.arrow.app _ s) = 0
      rw [← hy]
      exact hz
  refine Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) ?_
  exact Abelian.monoLift_comp _ _ _

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

lemma toFunctions_res {U V : X.Opens} (h : V ≤ U) (a : A) :
    resO h (toFunctions (A := A) U a) = toFunctions (A := A) V a := by
  change resO h (resO le_top _) = resO le_top _
  rw [resO_resO]

lemma map_toFunctions_res {U V : X.Opens} (h : V ≤ U) (J : Ideal A) :
    Ideal.map (resO h) (Ideal.map (toFunctions (A := A) U) J) = Ideal.map (toFunctions (A := A) V) J := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (toFunctions_res h)

lemma resF_mem_pow (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) (m : Γ(F, U))
    (hm : m ∈ (Ideal.map (toFunctions (A := A) U) (I ^ n) • ⊤ : Submodule Γ(X, U) Γ(F, U))) :
    resF F h m ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha z _
    rw [resF_smul]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← map_toFunctions_res h]
    exact Ideal.mem_map_of_mem _ ha
  · intro x y hx hy
    rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

lemma sat_add (F : X.Modules) {V : X.Opens} (f : Γ(X, V)) (P : Submodule Γ(X, V) Γ(F, V))
    (y₁ y₂ : Γ(F, X.basicOpen f))
    (h₁ : ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y₁)
    (h₂ : ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y₂) :
    ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • (y₁ + y₂) := by
  obtain ⟨e₁, z₁, hz₁, hr₁⟩ := h₁
  obtain ⟨e₂, z₂, hz₂, hr₂⟩ := h₂
  refine ⟨e₁ + e₂, f ^ e₂ • z₁ + f ^ e₁ • z₂, add_mem (P.smul_mem _ hz₁) (P.smul_mem _ hz₂), ?_⟩
  rw [map_add (f := _), resF_smul, resF_smul, hr₁, hr₂, smul_smul, smul_smul, smul_add, map_pow, map_pow,
    pow_add, mul_comm (resO (X.basicOpen_le f) f ^ e₂)]

lemma exists_res_eq_of_mem_pow (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Γ(X, V)) (n : ℕ) (y : Γ(F, X.basicOpen f))
    (hy : y ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ(F, X.basicOpen f))) :
    ∃ (e : ℕ) (y' : Γ(F, V)),
      y' ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ∧
      resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • y := by
  set P : Submodule Γ(X, V) Γ(F, V) := Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ with hPdef
  have key : ∀ a ∈ Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n),
      ∀ z : Γ(F, X.basicOpen f), ∃ (e : ℕ) (y' : Γ(F, V)), y' ∈ P ∧
        resF F (X.basicOpen_le f) y' = resO (X.basicOpen_le f) f ^ e • (a • z) := by
    intro a ha
    rw [← map_toFunctions_res (X.basicOpen_le f)] at ha
    change a ∈ Ideal.span _ at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨b, hb, rfl⟩ := ha
      intro z
      obtain ⟨e, z', hz'⟩ := qcoh_exists_res_eq F hV f z
      refine ⟨e, b • z', Submodule.smul_mem_smul hb Submodule.mem_top, ?_⟩
      rw [resF_smul, hz', smul_comm]
    | zero =>
      intro z
      exact ⟨0, 0, P.zero_mem, by simp⟩
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro z
      rw [add_smul]
      exact sat_add F f P _ _ (h₁ z) (h₂ z)
    | smul s a _ h =>
      intro z
      rw [smul_eq_mul, mul_smul, smul_comm s a]
      exact h (s • z)
  refine Submodule.smul_induction_on hy (fun a ha z _ ↦ key a ha z) ?_
  intro y₁ y₂ h₁ h₂
  exact sat_add F f P _ _ h₁ h₂

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

lemma isUnit_resO_basicOpen {V : X.Opens} (f : Γ(X, V)) : IsUnit (resO (X.basicOpen_le f) f) :=
  X.toRingedSpace.isUnit_res_basicOpen f

theorem local_step {E : X.Modules} [E.IsQuasicoherent] (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) (k : ℕ)
    (hk : ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)))
    (f : Γ(X, V)) (n : ℕ) (x : Γ((D : X.Modules), X.basicOpen f))
    (hx : D.arrow.app _ x ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ (n + k)) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ(E, X.basicOpen f))) :
    x ∈ (Ideal.map (toFunctions (A := A) (X.basicOpen f)) (I ^ n) • ⊤ :
      Submodule Γ(X, X.basicOpen f) Γ((D : X.Modules), X.basicOpen f)) := by
  set u := resO (X.basicOpen_le f) f with hu
  obtain ⟨e₁, y', hy', hr₁⟩ := exists_res_eq_of_mem_pow I E hV f (n + k) _ hx
  obtain ⟨e₂, d', hd'⟩ := qcoh_exists_res_eq (D : X.Modules) hV f x
  have h0 : resF E (X.basicOpen_le f) (f ^ e₁ • D.arrow.app V d' - f ^ e₂ • y') = 0 := by
    rw [map_sub, resF_smul, resF_smul, resF_app, hd', Scheme.Modules.Hom.app_smul, hr₁, map_pow,
      map_pow, ← hu, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨e₃, he₃⟩ := qcoh_exists_pow_smul_eq_zero E hV f _ h0
  rw [smul_sub, sub_eq_zero] at he₃
  have hmem : D.arrow.app V (f ^ e₃ • f ^ e₁ • d') ∈
      (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, he₃]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy')
  have h2 := resF_mem_pow I (D : X.Modules) (X.basicOpen_le f) n _ (hk n _ hmem)
  rw [resF_smul, resF_smul, hd', map_pow, map_pow, ← hu] at h2
  have hU : IsUnit (u ^ e₃ * u ^ e₁ * u ^ e₂) :=
    (((isUnit_resO_basicOpen f).pow e₃).mul ((isUnit_resO_basicOpen f).pow e₁)).mul
      ((isUnit_resO_basicOpen f).pow e₂)
  rw [smul_smul, smul_smul] at h2
  exact (Submodule.smul_mem_iff_of_isUnit _ hU).mp h2

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE.ArtinRees

variable {X : Scheme.{0}} {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

theorem exists_const_of_finite {E : X.Modules} (D : Subobject E) (V : X.Opens)
    [IsNoetherianRing Γ(X, V)] [Module.Finite Γ(X, V) Γ(E, V)] :
    ∃ k : ℕ, ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)) := by
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul D.arrow }
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.map (toFunctions (A := A) V) I)
    (LinearMap.range φ)
  refine ⟨k, fun n x hx ↦ ?_⟩
  rw [Ideal.map_pow] at hx ⊢
  have h1 : φ x ∈ (Ideal.map (toFunctions (A := A) V) I) ^ (n + k) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓
      LinearMap.range φ := ⟨hx, ⟨x, rfl⟩⟩
  rw [hk (n + k) (by omega), Nat.add_sub_cancel] at h1
  have h2 : (Ideal.map (toFunctions (A := A) V) I) ^ n •
      ((Ideal.map (toFunctions (A := A) V) I) ^ k • (⊤ : Submodule Γ(X, V) Γ(E, V)) ⊓ LinearMap.range φ) ≤
      ((Ideal.map (toFunctions (A := A) V) I) ^ n • (⊤ : Submodule Γ(X, V) Γ((D : X.Modules), V))).map φ := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨y, hy, hyx⟩ := h2 h1
  rwa [injective_app_of_mono D.arrow V hyx] at hy

lemma const_mono {E : X.Modules} (D : Subobject E) (V : X.Opens) {k k' : ℕ} (hkk : k ≤ k')
    (hk : ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k)) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V))) :
    ∀ (n : ℕ) (x : Γ((D : X.Modules), V)), D.arrow.app V x ∈
        (Ideal.map (toFunctions (A := A) V) (I ^ (n + k')) • ⊤ : Submodule Γ(X, V) Γ(E, V)) →
      x ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ :
        Submodule Γ(X, V) Γ((D : X.Modules), V)) := by
  intro n x hx
  refine hk n x (Submodule.smul_mono_left (Ideal.map_mono (Ideal.pow_le_pow_right ?_)) hx)
  omega

end GlobalTheory.CompanionTheory.GE.ArtinRees

namespace GlobalTheory.CompanionTheory.GE


open GlobalTheory.CompanionTheory.GE.ArtinRees in
theorem artinRees_uniform {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  haveI : E.IsQuasicoherent := hE.1
  have hc : ∀ U : X.affineOpens, ∃ k : ℕ, ∀ (n : ℕ) (x : Γ((D : X.Modules), (U : X.Opens))),
      D.arrow.app (U : X.Opens) x ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ (n + k)) • ⊤ :
        Submodule Γ(X, (U : X.Opens)) Γ(E, (U : X.Opens))) →
      x ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ n) • ⊤ :
        Submodule Γ(X, (U : X.Opens)) Γ((D : X.Modules), (U : X.Opens))) := fun U ↦ by
    haveI := hE.2 (U : X.Opens) U.2
    haveI := IsLocallyNoetherian.component_noetherian U
    exact exists_const_of_finite I D (U : X.Opens)
  choose c hc using hc
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := by
    intro x _
    obtain ⟨U, ⟨V, hV, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen) hcov
  refine ⟨t.sup c, fun n ↦ ?_⟩
  rw [Subobject.inf_eq_map_pullback]
  refine leOfHom ((Subobject.map D.arrow).map (homOfLE ?_))
  refine le_of_secs_basicOpen _ _ (↑t : Set X.affineOpens) ?_ ?_
  · intro x
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨U, hU, hxU⟩
  · intro U hU f y hy
    rw [secs_pullback_arrow, secs_powSub I E inferInstance _ _ (U.2.basicOpen f)] at hy
    rw [secs_powSub I (D : X.Modules) hD _ _ (U.2.basicOpen f)]
    haveI := hD
    exact local_step I D U.2 (t.sup c)
      (const_mono I D (U : X.Opens) (Finset.le_sup (f := c) hU) (hc U)) f n y hy

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobjectStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_subobject : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  first | exact @GlobalTheory.CompanionTheory.GE.artinRees_uniform | exact GlobalTheory.CompanionTheory.GE.artinRees_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.artinRees_uniform <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Union

theorem support_inf_subset {X : Scheme.{0}} (T₁ T₂ : X.IdealSheafData) :
    ((T₁ ⊓ T₂).support : Set X) ⊆ (T₁.support : Set X) ∪ T₂.support := by
  have hle : T₁ * T₂ ≤ T₁ ⊓ T₂ := fun U => Ideal.mul_le_inf
  have h := Scheme.IdealSheafData.support_antitone hle
  intro x hx
  have hx' : x ∈ (T₁ * T₂).support := h hx
  rw [Scheme.IdealSheafData.support_mul] at hx'
  exact hx'

theorem universallyClosed_of_cover {Z₁ Z₂ Z S : Scheme.{0}} (p₁ : Z₁ ⟶ Z) (p₂ : Z₂ ⟶ Z)
    (h : Z ⟶ S) (h₁ : UniversallyClosed (p₁ ≫ h)) (h₂ : UniversallyClosed (p₂ ≫ h))
    (hc : ∀ z : Z, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂) : UniversallyClosed h := by
  rw [universallyClosed_iff]
  intro X' Y' i₁ i₂ f' H
  have key : ∀ {W : Scheme.{0}} (p : W ⟶ Z), UniversallyClosed (p ≫ h) →
      IsClosedMap (pullback.fst i₁ p ≫ f') := by
    intro W p hp
    have H' : IsPullback (pullback.fst i₁ p ≫ f') (pullback.snd i₁ p) i₂ (p ≫ h) :=
      (IsPullback.of_hasPullback i₁ p).paste_horiz H
    exact (universallyClosed_iff _).mp hp _ _ _ H'
  have lift : ∀ {W : Scheme.{0}} (p : W ⟶ Z) (x : X'), i₁ x ∈ Set.range p →
      ∃ z : ↑(pullback i₁ p), pullback.fst i₁ p z = x := by
    rintro W p x ⟨w, hw⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨z, hz⟩
  show IsClosedMap f'
  intro C hC
  have hEq : f' '' C = (pullback.fst i₁ p₁ ≫ f') '' (pullback.fst i₁ p₁ ⁻¹' C) ∪
      (pullback.fst i₁ p₂ ≫ f') '' (pullback.fst i₁ p₂ ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hc (i₁ x) with hr | hr
      · obtain ⟨z, hz⟩ := lift p₁ x hr
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz⟩ := lift p₂ x hr
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨_, hz, by simp⟩
      · exact ⟨_, hz, by simp⟩
  rw [hEq]
  exact (key p₁ h₁ _ (hC.preimage (pullback.fst i₁ p₁).continuous)).union
    (key p₂ h₂ _ (hC.preimage (pullback.fst i₁ p₂).continuous))

theorem isProper_inf : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) →
    IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  intro X S f _ _ T₁ T₂ hT₁ hT₂
  let K : X.IdealSheafData := T₁ ⊓ T₂
  let p₁ : T₁.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₁.subschemeι
    (by simpa [K] using (inf_le_left : T₁ ⊓ T₂ ≤ T₁))
  let p₂ : T₂.subscheme ⟶ K.subscheme := IsClosedImmersion.lift K.subschemeι T₂.subschemeι
    (by simpa [K] using (inf_le_right : T₁ ⊓ T₂ ≤ T₂))
  have e₁ : p₁ ≫ K.subschemeι = T₁.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have e₂ : p₂ ≫ K.subschemeι = T₂.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have u₁ : UniversallyClosed (p₁ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₁]; infer_instance
  have u₂ : UniversallyClosed (p₂ ≫ K.subschemeι ≫ f) := by
    rw [← Category.assoc, e₂]; infer_instance
  have cover : ∀ {T : X.IdealSheafData} (p : T.subscheme ⟶ K.subscheme),
      p ≫ K.subschemeι = T.subschemeι → ∀ z : K.subscheme, K.subschemeι z ∈ (T.support : Set X) →
      z ∈ Set.range p := by
    intro T p e z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    refine ⟨w, K.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← e]
    rfl
  have hc : ∀ z : K.subscheme, z ∈ Set.range p₁ ∨ z ∈ Set.range p₂ := by
    intro z
    have hz : K.subschemeι z ∈ (K.support : Set X) := K.range_subschemeι.le ⟨z, rfl⟩
    rcases support_inf_subset T₁ T₂ hz with h | h
    · exact Or.inl (cover p₁ e₁ z h)
    · exact Or.inr (cover p₂ e₂ z h)
  have : UniversallyClosed (K.subschemeι ≫ f) :=
    universallyClosed_of_cover p₁ p₂ _ u₁ u₂ hc
  exact ⟨⟩

end GlobalTheory.CompanionTheory.GE.Union
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheavesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_inf_ideal_sheaves : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) → IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Union.isProper_inf | exact GlobalTheory.CompanionTheory.GE.Union.isProper_inf | (intros; apply GlobalTheory.CompanionTheory.GE.Union.isProper_inf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.Comb

noncomputable section

variable {X : Scheme.{0}} {E : X.Modules}

abbrev QC (S : Subobject E) : Prop := (S : X.Modules).IsQuasicoherent

lemma secs_add {S : Subobject E} {V : X.Opens} {x y : Γ(E, V)} (hx : x ∈ secs S V) (hy : y ∈ secs S V) :
    x + y ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ _ _⟩

lemma secs_sub {S : Subobject E} {V : X.Opens} {x y : Γ(E, V)} (hx : x ∈ secs S V) (hy : y ∈ secs S V) :
    x - y ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ _ _⟩

lemma secs_smul {S : Subobject E} {V : X.Opens} (r : Γ(X, V)) {x : Γ(E, V)} (hx : x ∈ secs S V) :
    r • x ∈ secs S V := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

lemma secs_mono {S T : Subobject E} (h : S ≤ T) (V : X.Opens) : secs S V ⊆ secs T V := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(Subobject.ofLE S T h).app V a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]

lemma secs_inf (S T : Subobject E) (V : X.Opens) : secs (S ⊓ T) V = secs S V ∩ secs T V := by
  have h : S ⊓ T = (Subobject.map S.arrow).obj ((Subobject.pullback S.arrow).obj T) :=
    Subobject.inf_eq_map_pullback S T
  rw [h, GlobalTheory.CompanionTheory.GE.secs_map_arrow, GlobalTheory.CompanionTheory.GE.secs_pullback_arrow]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, hy, rfl⟩

lemma modular (hE : E.IsQuasicoherent) {a b c : Subobject E} (ha : QC a) (hb : QC b) (hac : a ≤ c) :
    (a ⊔ b) ⊓ c ≤ a ⊔ (b ⊓ c) := by
  rw [GlobalTheory.CompanionTheory.GE.le_iff_secs_subset]
  intro U x hx
  rw [secs_inf, (GlobalTheory.CompanionTheory.GE.supsecs hE a b ha hb).2 _ U.2] at hx
  obtain ⟨⟨s, hs, t, ht, rfl⟩, hxc⟩ := hx
  have hsc := secs_mono hac _ hs
  have htc : t ∈ secs c U := by
    have := secs_sub hxc hsc
    simpa using this
  exact secs_add (secs_mono le_sup_left _ hs)
    (secs_mono le_sup_right _ ((secs_inf b c U).symm ▸ ⟨ht, htc⟩))

lemma pullback_eq_kernel (D S : Subobject E) :
    (Subobject.pullback D.arrow).obj S = Subobject.mk (kernel.ι (D.arrow ≫ cokernel.π S.arrow)) := by
  have hp := Subobject.isPullback D.arrow S
  apply le_antisymm
  · refine Subobject.le_mk_of_comm (kernel.lift _ ((Subobject.pullback D.arrow).obj S).arrow ?_) ?_
    · rw [← Category.assoc, ← hp.w, Category.assoc, cokernel.condition, comp_zero]
    · simp
  · have hw : (kernel.ι (D.arrow ≫ cokernel.π S.arrow) ≫ D.arrow) ≫ cokernel.π S.arrow = 0 := by
      rw [Category.assoc, kernel.condition]
    let l := Abelian.monoLift S.arrow (kernel.ι (D.arrow ≫ cokernel.π S.arrow) ≫ D.arrow) hw
    refine Subobject.mk_le_of_comm (hp.lift l (kernel.ι _) ?_) (hp.lift_snd _ _ _)
    exact Abelian.monoLift_comp _ _ _

lemma qc_pullback (hE : E.IsQuasicoherent) {D S : Subobject E} (hD : QC D) (hS : QC S) :
    QC ((Subobject.pullback D.arrow).obj S) := by
  haveI : E.IsQuasicoherent := hE
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI : (S : X.Modules).IsQuasicoherent := hS
  rw [QC, pullback_eq_kernel]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι (D.arrow ≫ cokernel.π S.arrow))).symm inferInstance

lemma qc_map {D : Subobject E} {B : Subobject (D : X.Modules)} (hB : QC B) :
    QC ((Subobject.map D.arrow).obj B) := by
  have hm : (Subobject.map D.arrow).obj B = Subobject.mk (B.arrow ≫ D.arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    rfl
  rw [QC, hm]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (B.arrow ≫ D.arrow)).symm hB

lemma qc_inf (hE : E.IsQuasicoherent) {S T : Subobject E} (hS : QC S) (hT : QC T) : QC (S ⊓ T) := by
  rw [Subobject.inf_eq_map_pullback]
  exact qc_map (qc_pullback hE hS hT)

lemma map_sup' (D : Subobject E) (a b : Subobject (D : X.Modules)) :
    (Subobject.map D.arrow).obj (a ⊔ b) =
      (Subobject.map D.arrow).obj a ⊔ (Subobject.map D.arrow).obj b :=
  (Subobject.mapPullbackAdj D.arrow).gc.l_sup

lemma secs_eq_univ_of_supportedIn (hE : E.IsQuasicoherent) {S : Subobject E} (hS : QC S) {T : Set X}
    (h : Scheme.Modules.SupportedIn (cokernel S.arrow) T) {U : X.Opens} (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) T) : secs S U = Set.univ := by
  haveI : E.IsQuasicoherent := hE
  haveI : (S : X.Modules).IsQuasicoherent := hS
  refine Set.eq_univ_of_forall fun x => ?_
  exact (mem_range_app_iff S.arrow hU x).2 (h U hd _)

lemma supportedIn_of_secs_eq_univ (hE : E.IsQuasicoherent) {S : Subobject E} (hS : QC S) {T : Set X}
    (h : ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) T → secs S U = Set.univ) :
    Scheme.Modules.SupportedIn (cokernel S.arrow) T := by
  haveI : E.IsQuasicoherent := hE
  haveI : (S : X.Modules).IsQuasicoherent := hS
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {W : X.affineOpens // (W : X.Opens) ≤ U} => (i.1 : X.Opens)) U
    (fun i => homOfLE i.2) ?_ s 0 ?_
  · intro x hx
    obtain ⟨W, ⟨V, hV, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hWU⟩, hxW⟩
  · intro i
    rw [map_zero]
    have hd : Disjoint ((i.1 : X.Opens) : Set X) T := hU.mono_left i.2
    obtain ⟨y, hy⟩ := surjective_cokernel_π_app S.arrow i.1.2
      ((cokernel S.arrow).presheaf.map (homOfLE i.2).op s)
    have hmem : y ∈ secs S i.1 := by rw [h _ i.1.2 hd]; trivial
    rw [← hy]
    exact (mem_range_app_iff S.arrow i.1.2 y).1 hmem

lemma eq_top_of_sup_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (J : Ideal R)
    (N : Submodule R M) (h1 : N ⊔ J • ⊤ = ⊤) (m : ℕ) (h2 : J ^ m • (⊤ : Submodule R M) ≤ N) :
    N = ⊤ := by
  have key : ∀ j : ℕ, N ⊔ J ^ j • (⊤ : Submodule R M) = ⊤ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      apply le_antisymm le_top
      calc (⊤ : Submodule R M) = N ⊔ J ^ j • (⊤ : Submodule R M) := ih.symm
        _ ≤ N ⊔ J ^ (j + 1) • (⊤ : Submodule R M) := by
          refine sup_le le_sup_left ?_
          have h3 : J ^ j • (⊤ : Submodule R M) = J ^ j • (N ⊔ J • ⊤) := by rw [h1]
          rw [h3, Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          exact sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right
  exact ((key m).symm.trans (sup_eq_left.2 h2)).symm

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]

lemma qc_pow (hE : E.IsQuasicoherent) (n : ℕ) : QC (powSub I E n) :=
  haveI : E.IsQuasicoherent := hE
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealPowι I E n)).symm inferInstance

lemma powSub_anti (E : X.Modules) {m n : ℕ} (h : m ≤ n) : powSub I E n ≤ powSub I E m := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (powSub_succ_le I E n).trans ih

lemma map_pow_le (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D) (n : ℕ) :
    (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) ≤ powSub I E n := by
  rw [GlobalTheory.CompanionTheory.GE.le_iff_secs_subset]
  intro U
  rw [GlobalTheory.CompanionTheory.GE.secs_map_arrow, GlobalTheory.CompanionTheory.GE.secs_powSub I _ hD n _ U.2, GlobalTheory.CompanionTheory.GE.secs_powSub I _ hE n _ U.2]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ (Ideal.map (toFunctions (A := A) (U : X.Opens)) (I ^ n) • ⊤ :
      Submodule Γ(X, U) Γ((D : X.Modules), U)) := hy
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr m _
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

variable {I} {S : ℕ → Subobject E}

lemma sys_anti (hS : ClosedSys I E S) : Antitone S :=
  antitone_nat_of_succ_le fun e => le_sup_left.trans_eq (hS.succ e).symm

lemma sys_iter (hS : ClosedSys I E S) (e j : ℕ) : S e ≤ S (e + j) ⊔ powSub I E (e + 1) := by
  induction j with
  | zero => exact le_sup_left
  | succ j ih =>
    refine ih.trans (sup_le ((hS.succ (e + j)).le.trans (sup_le le_sup_left ?_)) le_sup_right)
    exact (powSub_anti I E (by omega)).trans le_sup_right

lemma sys_le (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D) {c : ℕ}
    (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) (e : ℕ) :
    S (e + c) ≤ (D ⊓ S e) ⊔ powSub I E (e + 1) := by
  have h1 : S (e + c) ≤ (powSub I E (e + 1) ⊔ D) ⊓ S e :=
    le_inf (by rw [sup_comm]; exact hc e) (sys_anti hS (by omega))
  refine h1.trans ((modular hE (qc_pow I hE _) hD (hS.pow_le e)).trans ?_)
  rw [sup_comm]

lemma map_restrict (D : Subobject E) (c e : ℕ) :
    (Subobject.map D.arrow).obj (restrictSys I D S c e) =
      (D ⊓ S (e + c)) ⊔ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) := by
  rw [restrictSys, map_sup', Subobject.inf_eq_map_pullback]

lemma map_inj (D : Subobject E) : Function.Injective (Subobject.map D.arrow).obj :=
  Subobject.map_obj_injective D.arrow

lemma restrict_succ (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {D : Subobject E} (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (ar : ∀ n, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n))
    (e : ℕ) :
    restrictSys I D S k e = restrictSys I D S k (e + 1) ⊔ powSub I (D : X.Modules) (e + 1) := by
  apply map_inj D
  rw [map_sup', map_restrict, map_restrict]
  have hQ : (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1 + 1)) ≤
      (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) :=
    (Subobject.map D.arrow).monotone (powSub_succ_le I _ _)
  have hs : e + 1 + k = e + k + 1 := by omega
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    set W := D ⊓ S (e + k + 1) with hW
    have hWq : QC W := qc_inf hE hD (hS.qcoh _)
    have h1 : S (e + k) ≤ W ⊔ powSub I E (e + k + 1) := by
      refine (sys_iter hS (e + k) (1 + c)).trans (sup_le ?_ le_sup_right)
      rw [← add_assoc]
      refine (sys_le hS hE hD hc (e + k + 1)).trans (sup_le le_sup_left ?_)
      exact (powSub_anti I E (by omega)).trans le_sup_right
    have h2 : D ⊓ S (e + k) ≤ (W ⊔ powSub I E (e + k + 1)) ⊓ D :=
      le_inf (inf_le_right.trans h1) inf_le_left
    refine h2.trans ((modular hE hWq (qc_pow I hE _) inf_le_left).trans (sup_le ?_ ?_))
    · rw [hs]
      exact le_sup_left.trans le_sup_left
    · refine le_trans ?_ le_sup_right
      rw [inf_comm, ← hs]
      exact ar (e + 1)
  · rw [hs]
    refine sup_le (sup_le (le_inf inf_le_left ?_ |>.trans le_sup_left) (hQ.trans le_sup_right)) le_sup_right
    exact inf_le_right.trans (sys_anti hS (by omega))

variable {D : Subobject E}

lemma qc_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D) (c e : ℕ) :
    QC (restrictSys I D S c e) :=
  (GlobalTheory.CompanionTheory.GE.supsecs hD _ _ (qc_pullback hE hD (hS.qcoh _)) (qc_pow I hD _)).1

lemma closedSys_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (ar : ∀ n, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n)) :
    ClosedSys I (D : X.Modules) (restrictSys I D S k) :=
  ⟨qc_restrict hS hE hD k, fun _ => le_sup_right, restrict_succ hS hE hD hc ar⟩

lemma secs_sys_univ (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U)
    (h0 : secs (S 0) U = Set.univ) (n : ℕ) : secs (S n) U = Set.univ := by
  let J : Ideal Γ(X, U) := Ideal.map (toFunctions (A := A) U) I
  let N : Submodule Γ(X, U) Γ(E, U) :=
    { carrier := secs (S n) U
      add_mem' := fun hx hy => secs_add hx hy
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := fun r _ hx => secs_smul r hx }
  have hp : ∀ m, Ideal.map (toFunctions (A := A) U) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  have h1 : N ⊔ J • ⊤ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ secs (S 0) U := by rw [h0]; trivial
    have hle := sys_iter hS 0 n
    rw [zero_add, zero_add] at hle
    have h2 := secs_mono hle U hx
    rw [(GlobalTheory.CompanionTheory.GE.supsecs hE _ _ (hS.qcoh _) (qc_pow I hE _)).2 U hU, GlobalTheory.CompanionTheory.GE.secs_powSub I E hE _ U hU, hp,
      pow_one] at h2
    obtain ⟨s, hs, t, ht, rfl⟩ := h2
    exact Submodule.add_mem_sup hs ht
  have h2 : J ^ (n + 1) • (⊤ : Submodule Γ(X, U) Γ(E, U)) ≤ N := by
    intro x hx
    have := secs_mono (hS.pow_le n) U
    rw [GlobalTheory.CompanionTheory.GE.secs_powSub I E hE _ U hU, hp] at this
    exact this hx
  have h3 := eq_top_of_sup_smul J N h1 (n + 1) h2
  refine Set.eq_univ_of_forall fun x => ?_
  change x ∈ N
  rw [h3]
  trivial

lemma propSupp_restrict (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    (hP : PropSupp A (S 0)) (c : ℕ) : PropSupp A (restrictSys I D S c 0) := by
  obtain ⟨T, hT, hsupp⟩ := hP
  refine ⟨T, hT, supportedIn_of_secs_eq_univ hD (qc_restrict hS hE hD c 0) fun U hU hd => ?_⟩
  have h := secs_sys_univ hS hE hU (secs_eq_univ_of_supportedIn hE (hS.qcoh 0) hsupp hU hd) (0 + c)
  refine Set.eq_univ_of_forall fun x => secs_mono le_sup_left U ?_
  rw [GlobalTheory.CompanionTheory.GE.secs_pullback_arrow]
  change D.arrow.app U x ∈ secs (S (0 + c)) U
  rw [h]
  trivial

lemma alg_of (hS : ClosedSys I E S) (hE : E.IsQuasicoherent) (hD : QC D)
    {c k : ℕ} (hc : ∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1))
    (hprop : ∀ T₁ T₂ : X.IdealSheafData, IsProper (T₁.subschemeι ≫ (X ↘ Spec (.of A))) →
      IsProper (T₂.subschemeι ≫ (X ↘ Spec (.of A))) →
      IsProper ((T₁ ⊓ T₂).subschemeι ≫ (X ↘ Spec (.of A))))
    (halg : Alg I (D : X.Modules) (restrictSys I D S k)) (hPD : PropSupp A D) : Alg I E S := by
  obtain ⟨B', hB'q, hB'P, hB'⟩ := halg
  refine ⟨(Subobject.map D.arrow).obj B', qc_map hB'q, ?_, fun e => ?_⟩
  · obtain ⟨T₁, h1, s1⟩ := hPD
    obtain ⟨T₂, h2, s2⟩ := hB'P
    refine ⟨T₁ ⊓ T₂, hprop T₁ T₂ h1 h2, supportedIn_of_secs_eq_univ hE (qc_map hB'q) fun U hU hd => ?_⟩
    have d1 : Disjoint (U : Set X) (T₁.support : Set X) :=
      hd.mono_right (Scheme.IdealSheafData.support_antitone inf_le_left)
    have d2 : Disjoint (U : Set X) (T₂.support : Set X) :=
      hd.mono_right (Scheme.IdealSheafData.support_antitone inf_le_right)
    have e1 := secs_eq_univ_of_supportedIn hE hD s1 hU d1
    have e2 := secs_eq_univ_of_supportedIn hD hB'q s2 hU d2
    rw [GlobalTheory.CompanionTheory.GE.secs_map_arrow, e2, Set.image_univ]
    exact e1
  · have hmap : (Subobject.map D.arrow).obj B' ⊔
        (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) =
        (D ⊓ S (e + k)) ⊔ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) (e + 1)) := by
      rw [← map_sup', hB' e, map_restrict]
    have hQ := map_pow_le I hE hD (e + 1)
    apply le_antisymm
    · refine sup_le ?_ (hS.pow_le e)
      refine le_sup_left.trans (hmap.le.trans (sup_le ?_ (hQ.trans (hS.pow_le e))))
      exact inf_le_right.trans (sys_anti hS (by omega))
    · refine (sys_iter hS e (k + c)).trans (sup_le ?_ le_sup_right)
      rw [← add_assoc]
      refine (sys_le hS hE hD hc (e + k)).trans (sup_le ?_ ?_)
      · refine (le_sup_left.trans hmap.ge).trans (sup_le le_sup_left (hQ.trans le_sup_right))
      · exact (powSub_anti I E (by omega)).trans le_sup_right

end

theorem restrict_alg : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  intro A _ _ I X _ _ _ _ E hE S hS hP D hD c hc
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  obtain ⟨k, ar⟩ := GlobalTheory.T.artin_rees_subobject I hE D hD
  exact ⟨k, closedSys_restrict hS hE.1 hD hc ar, propSupp_restrict hS hE.1 hD hP k,
    fun halg hPD => alg_of hS hE.1 hD hc (fun T₁ T₂ => GlobalTheory.T.proper_inf_ideal_sheaves _ T₁ T₂) halg hPD⟩

end GlobalTheory.CompanionTheory.GE.Comb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  exact @GlobalTheory.CompanionTheory.GE.Comb.restrict_alg
end
