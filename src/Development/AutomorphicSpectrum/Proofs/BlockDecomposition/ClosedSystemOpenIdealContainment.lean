module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedMissingClosedFibreEmpty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.ClosedFibre

theorem closed_missing_closedFibre_empty : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X : Over (Spec (CommRingCat.of R))), UniversallyClosed X.hom →
  ∀ Z : Set X.left, IsClosed Z → (∀ x ∈ Z, ¬ (I ≤ (X.hom.base x).asIdeal)) → Z = ∅ := by
  intro R _ I hI X hX Z hZ h
  haveI := hI
  haveI := hX
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hcl : IsClosed (X.hom.base '' Z) := X.hom.isClosedMap _ hZ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (X.hom.base x).asIdeal (X.hom.base x).isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hsp : (X.hom.base x) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have hq : q ∈ X.hom.base '' Z := hsp.mem_closed hcl ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyq⟩ := hq
  apply h y hy
  rw [hyq]
  exact (IsAdicComplete.le_jacobson_bot (I := I)).trans (sInf_le ⟨bot_le, hm⟩)

end GlobalTheory.CompanionTheory.ClosedFibre
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.PSupp

def badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : Set X :=
  {x | ∀ V : X.affineOpens, secs S (V : X.Opens) = Set.univ → x ∉ (V : X.Opens)}

lemma badSet_compl_eq {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) :
    (badSet S)ᶜ = ⋃ V ∈ {V : X.affineOpens | secs S (V : X.Opens) = Set.univ}, ((V : X.Opens) : Set X) := by
  ext x
  simp only [badSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop, Set.mem_iUnion]
  constructor
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mp hx⟩
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mpr hx⟩

lemma isClosed_badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : IsClosed (badSet S) := by
  rw [← isOpen_compl_iff, badSet_compl_eq]
  exact isOpen_biUnion fun V _ => (V : X.Opens).isOpen

theorem subset_of_closedFibre {A : Type} [CommRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X)
    (hC : IsClosed C) (h : ∀ x ∈ C, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ (O : Set X)) :
    C ⊆ O := by

  have hZ := GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty A I hI
    (Over.mk (X ↘ Spec (.of A))) (inferInstanceAs (UniversallyClosed (X ↘ Spec (.of A))))
    (C ∩ (O : Set X)ᶜ) (hC.inter O.isOpen.isClosed_compl) (by
      rintro x ⟨hxC, hxO⟩ hIx
      exact hxO (h x hxC hIx))
  intro x hx
  by_contra hxO
  have hx' : x ∈ C ∩ (O : Set X)ᶜ := ⟨hx, hxO⟩
  rw [hZ] at hx'
  exact hx'

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSubsetSupportProper
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ClosedSub

theorem closed_subset_support_proper {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X) (hC : IsClosed C)
    (hCO : C ⊆ (O : Set X)) :
    ∃ T' : (O : Scheme.{0}).IdealSheafData,
      (T'.support : Set (O : Scheme.{0})) = O.ι.base ⁻¹' C ∧
        IsProper (T'.subschemeι ≫ O.ι ≫ (X ↘ Spec (.of A))) := by
  have hC' : IsClosed (O.ι.base ⁻¹' C) := hC.preimage O.ι.continuous
  refine ⟨Scheme.IdealSheafData.vanishingIdeal ⟨_, hC'⟩, by simp, ?_⟩
  set T' := Scheme.IdealSheafData.vanishingIdeal (X := (O : Scheme.{0})) ⟨_, hC'⟩
  have hrange : Set.range (T'.subschemeι ≫ O.ι) = C := by
    have h : Set.range (T'.subschemeι ≫ O.ι) = O.ι '' Set.range T'.subschemeι := by
      rw [← Set.range_comp]
      rfl
    rw [h, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change O.ι '' (O.ι ⁻¹' C) = C
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr hCO
  have : IsClosedImmersion (T'.subschemeι ≫ O.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hC)
  rw [← Category.assoc]
  infer_instance

end GlobalTheory.CompanionTheory.GE.ClosedSub
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.PSupp

noncomputable section

variable {X : Scheme.{0}}

lemma eq_zero_basicOpen_of_affine (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)) :
    m = 0 := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV f m
  refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
  rw [← hm', h0 m', map_zero]

lemma eq_zero_of_le_affine (F : X.Modules) [F.IsQuasicoherent] {V W : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (hW : W ≤ V) (m : Γ(F, W)) : m = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, V) // X.basicOpen f ≤ W} => X.basicOpen i.1) W
    (fun i => homOfLE i.2) ?_ m 0 ?_
  · intro x hx
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hW hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfW⟩, hxf⟩
  · intro i
    rw [map_zero]
    exact eq_zero_basicOpen_of_affine F hV h0 i.1 _

lemma cokernel_sections_eq_zero {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (hS : secs S V = Set.univ) (s : Γ(cokernel S.arrow, V)) : s = 0 := by
  obtain ⟨y, rfl⟩ := surjective_cokernel_π_app S.arrow hV s
  have hmem : y ∈ secs S V := by rw [hS]; trivial
  exact (mem_range_app_iff S.arrow hV y).1 hmem

lemma supportedIn_badSet {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] :
    Scheme.Modules.SupportedIn (cokernel S.arrow) (badSet S) := by
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {V : X.affineOpens // secs S (V : X.Opens) = Set.univ} => U ⊓ (i.1 : X.Opens)) U
    (fun i => homOfLE inf_le_left) ?_ s 0 ?_
  · intro x hx
    have hxb : x ∉ badSet S := fun hb => Set.disjoint_left.1 hU hx hb
    have hxc : x ∈ (badSet S)ᶜ := hxb
    rw [badSet_compl_eq] at hxc
    simp only [Set.mem_iUnion, exists_prop] at hxc
    obtain ⟨V, hV, hxV⟩ := hxc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
  · intro i
    rw [map_zero]
    exact eq_zero_of_le_affine _ i.1.2 (cokernel_sections_eq_zero S i.1.2 i.2) inf_le_right _

theorem secs_eq_univ_of_disjoint_badSet {X : Scheme.{0}} {P : X.Modules} (hP : P.IsQuasicoherent)
    (S : Subobject P) (hS : (S : X.Modules).IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) (badSet S)) : secs S U = Set.univ := by
  haveI : P.IsQuasicoherent := hP
  haveI : (S : X.Modules).IsQuasicoherent := hS
  exact GlobalTheory.CompanionTheory.GE.Comb.secs_eq_univ_of_supportedIn hP hS (supportedIn_badSet S) hU hd

end

end GlobalTheory.CompanionTheory.GE.PSupp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupportStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_eq_univ_off_bad_support : ∀ {X : Scheme.{0}} {P : X.Modules}, P.IsQuasicoherent → ∀ (S : Subobject P), (S : X.Modules).IsQuasicoherent → ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) (GlobalTheory.CompanionTheory.GE.PSupp.badSet S) → secs S U = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | exact GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfBadSetClosedFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.PSupp

lemma fromSpec_appTop_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
  have h := hV.fromSpec_app_of_le ⊤ le_top
  have e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]
    simp
  refine h.trans ?_
  erw [e, Category.comp_id]
  rfl

lemma fromSpec_comp_base {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (.of A)) = Spec.map (CommRingCat.ofHom (toFunctions (A := A) V)) := by
  have key : (Scheme.ΓSpecIso (.of A)).inv ≫ (X ↘ Spec (.of A)).appTop ≫
      X.presheaf.map (homOfLE le_top).op = CommRingCat.ofHom (toFunctions (A := A) V) := by
    ext r
    rfl
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop_eq,
    ← cancel_epi (Scheme.ΓSpecIso (.of A)).inv, ← Scheme.ΓSpecIso_inv_naturality, ← key]
  simp only [Category.assoc]
  rfl

lemma basicOpen_of_sub_one_mem {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (hI : I ≤ ((X ↘ Spec (.of A)).base x).asIdeal) {r : Γ(X, V)}
    (hr : r - 1 ∈ Ideal.map (toFunctions (A := A) V) I) : x ∈ X.basicOpen r := by
  set p := hV.primeIdealOf ⟨x, hxV⟩ with hp
  have hpx : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hcomp : (X ↘ Spec (.of A)).base x =
      (Spec.map (CommRingCat.ofHom (toFunctions (A := A) V))).base p := by
    rw [← fromSpec_comp_base hV, ← hpx]
    rfl
  have hle : Ideal.map (toFunctions (A := A) V) I ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have := hI ha
    rw [hcomp] at this
    exact this
  have hrp : r ∉ p.asIdeal := fun h => p.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.sub_mem h (hle hr)))
  rw [← hV.fromSpec_image_basicOpen r]
  exact ⟨p, hrp, hpx⟩

theorem mem_of_badSet_closedFibre : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, IsCoherent P → ∀ (Bb : Subobject P), (Bb : X.Modules).IsQuasicoherent → ∀ (K : Set X), IsClosed K → (∀ V : X.Opens, Disjoint (V : Set X) K → secs (Bb ⊔ powSub I P 1) V = Set.univ) → ∀ x ∈ GlobalTheory.CompanionTheory.GE.PSupp.badSet Bb, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ K := by
  intro A _ _ I X _ P hP Bb hBq K hK h x hx hI
  by_contra hxK
  obtain ⟨W, ⟨V, hV, rfl⟩, hxV, hVK⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ Kᶜ from hxK) hK.isOpen_compl
  have hV' : IsAffineOpen V := hV
  have hdisj : Disjoint (V : Set X) K := Set.disjoint_left.2 fun y hy hyK => hVK hy hyK
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  let N : Submodule Γ(X, V) Γ(P, V) :=
    { carrier := secs Bb V
      add_mem' := fun hx hy => GlobalTheory.CompanionTheory.GE.Comb.secs_add hx hy
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := fun r _ hx => GlobalTheory.CompanionTheory.GE.Comb.secs_smul r hx }
  have hsum : ∀ m : Γ(P, V), ∃ s ∈ N, ∃ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)), m = s + t := by
    intro m
    have hm : m ∈ secs (Bb ⊔ powSub I P 1) V := by rw [h V hdisj]; trivial
    rw [(GlobalTheory.T.quasicoherent_sup_sections hP.1 Bb (powSub I P 1) hBq (GlobalTheory.CompanionTheory.GE.Comb.qc_pow I hP.1 1)).2 V hV',
      GlobalTheory.T.ideal_power_subobject_sections I P hP.1 1 V hV', pow_one] at hm
    obtain ⟨s, hs, t, ht, rfl⟩ := hm
    exact ⟨s, hs, t, ht, rfl⟩
  haveI : Module.Finite Γ(X, V) Γ(P, V) := hP.2 V hV'
  have hfg : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)) ≤ J • ⊤ := by
    intro z _
    obtain ⟨m, rfl⟩ := N.mkQ_surjective z
    obtain ⟨s, hs, t, ht, rfl⟩ := hsum m
    have h1 : N.mkQ (s + t) = N.mkQ t := by
      have h0 : N.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero N).2 hs
      rw [map_add (f := _), h0, zero_add]
    rw [h1]
    have h2 : N.mkQ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)).map N.mkQ := ⟨t, ht, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤ hfg hle
  have hrN : ∀ m : Γ(P, V), r • m ∈ N := fun m => by
    have := hr (N.mkQ m) trivial
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this
  have hxD : x ∈ X.basicOpen r := basicOpen_of_sub_one_mem I hV' hxV hI hr1
  have hD : IsAffineOpen (X.basicOpen r) := hV'.basicOpen r
  refine hx ⟨X.basicOpen r, hD⟩ ?_ hxD
  refine Set.eq_univ_of_forall fun m => ?_
  haveI : P.IsQuasicoherent := hP.1
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq P hV' r m
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le r) r) := X.toRingedSpace.isUnit_res_basicOpen r
  obtain ⟨b, hb⟩ := hrN m'
  have h3 : resF P (X.basicOpen_le r) (r • m') ∈ secs Bb (X.basicOpen r) := by
    rw [← hb]
    exact ⟨resF _ (X.basicOpen_le r) b, (resF_app Bb.arrow (X.basicOpen_le r) b).symm⟩
  rw [resF_smul, hm', ← hu, smul_smul, ← pow_succ'] at h3
  have h4 := GlobalTheory.CompanionTheory.GE.Comb.secs_smul (((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) : Γ(X, X.basicOpen r)) ^ (e + 1)) h3
  rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h4

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSupportedInPreimage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem cokernel_supportedIn_preimage : ∀ {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ Bb : Subobject P, ∀ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent → (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → ∀ (C : Set X), (∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) C → secs Bb U = Set.univ) → Scheme.Modules.SupportedIn (cokernel B.arrow) (O.ι.base ⁻¹' C) := by
  intro X O P E hP hE f hf Bb B hB hsec C hC
  haveI : P.IsQuasicoherent := hP
  haveI : E.IsQuasicoherent := hE
  haveI : Epi f := hf
  refine GlobalTheory.CompanionTheory.GE.Comb.supportedIn_of_secs_eq_univ hE hB fun W hW hd => ?_
  have hWi : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  have hdis : Disjoint ((O.ι ''ᵁ W : X.Opens) : Set X) C := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyC
    exact Set.disjoint_left.1 hd hy hyC
  rw [hsec W hW, hC _ hWi hdis, Set.image_univ]
  refine Function.Surjective.range_eq fun y => ?_
  obtain ⟨z, rfl⟩ := surjective_app_of_epi f hW y
  refine ⟨(P.restrictAppIso O.ι W).hom z, ?_⟩
  simp

end GlobalTheory.CompanionTheory.GE.PSupp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuasicoherentOfSecsImage
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (i : F ⟶ E) [Mono i] (V : X.Opens) :
    secs (Subobject.mk i) V = Set.range (i.app V) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).hom.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso i).inv.app V x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma restrict_map_app {X : Scheme.{0}} (O : X.Opens) {Q P : X.Modules} (a : Q ⟶ P)
    (W : (O : Scheme.{0}).Opens) (y : Γ(Q.restrict O.ι, W)) :
    ((Scheme.Modules.restrictFunctor O.ι).map a).app W y =
      (P.restrictAppIso O.ι W).inv (a.app (O.ι ''ᵁ W) ((Q.restrictAppIso O.ι W).hom y)) :=
  rfl

theorem isQuasicoherent_of_secs_image {X : Scheme.{0}} (O : X.Opens) {P : X.Modules}
    {E : (O : Scheme.{0}).Modules} (hP : P.IsQuasicoherent) (hE : E.IsQuasicoherent)
    (f : P.restrict O.ι ⟶ E) (Bb : Subobject P) (hBb : (Bb : X.Modules).IsQuasicoherent)
    (B : Subobject E)
    (hB : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) :
    (B : (O : Scheme.{0}).Modules).IsQuasicoherent := by
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  have hBr : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor O.ι _
  have hs : ∀ U : (O : Scheme.{0}).affineOpens,
      secs B (U : (O : Scheme.{0}).Opens) =
        secs (Subobject.mk (kernel.ι (cokernel.π g))) (U : (O : Scheme.{0}).Opens) := by
    intro U
    rw [secs_mk, range_kernel_ι_cokernel_π_app g U.2, hB _ U.2]
    ext m
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).inv y, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app, Iso.inv_hom_id_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨((Bb : X.Modules).restrictAppIso O.ι (U : (O : Scheme.{0}).Opens)).hom y, rfl⟩, ?_⟩
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, restrict_map_app]
  have hEq : B = Subobject.mk (kernel.ι (cokernel.π g)) :=
    le_antisymm ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).subset)
      ((GlobalTheory.T.subobject_le_iff_affine_sections _ _).2 fun U => (hs U).symm.subset)
  have hK : (kernel (cokernel.π g)).IsQuasicoherent := inferInstance
  rw [hEq]
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainment
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem propSupp_of_closed_image : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  intro A _ _ I hI X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf Sb T hTc hSb Bb hBq hBS B hB
  have hC : IsClosed (badSet Bb) := isClosed_badSet Bb
  have hCO : badSet Bb ⊆ (O : Set X) := subset_of_closedFibre I hI O (badSet Bb) hC
    (fun x hx hIx => by
      obtain ⟨y, _, rfl⟩ := mem_of_badSet_closedFibre I hP Bb hBq _ hTc
        (fun V hV => by rw [hBS]; exact hSb V hV) x hx hIx
      rw [← Scheme.Opens.range_ι O]
      exact ⟨y, rfl⟩)
  obtain ⟨T', hT'supp, hT'prop⟩ := ClosedSub.closed_subset_support_proper (A := A) O (badSet Bb) hC hCO
  have hBqc := isQuasicoherent_of_secs_image O hP.1 hE.1 f Bb hBq B hB
  refine ⟨T', hT'prop, ?_⟩
  rw [hT'supp]
  exact cokernel_supportedIn_preimage O hP.1 hE.1 f hf Bb B hBqc hB (badSet Bb)
    (fun U hU hd => GlobalTheory.T.sections_eq_univ_off_bad_support hP.1 Bb hBq U hU hd)

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemOpenIdealContainmentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_open_ideal_containment : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ (Sb : Subobject P) (T : (O : Scheme.{0}).IdealSheafData), IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) → (∀ V : X.Opens, Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs Sb V = Set.univ) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → Bb ⊔ powSub I P 1 = Sb → ∀ B : Subobject E, (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → PropSupp A B := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | exact GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.propSupp_of_closed_image <;> assumption)
end
