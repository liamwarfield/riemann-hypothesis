module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditive
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanMul

abbrev red (C : Type) [CommRing C] : Sp C ⟶ Sp (DualNumber C) :=
  spMap (TrivSqZeroExt.fstHom C C C).toRingHom

theorem red_surj (C : Type) [CommRing C] (p : Sp (DualNumber C)) : ∃ q : Sp C, red C q = p := by
  let P : PrimeSpectrum (DualNumber C) := p
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ P.asIdeal := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : a * a ∈ P.asIdeal := by rw [h2]; exact zero_mem _
    rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  haveI := P.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨_, hprime⟩ : PrimeSpectrum C), ?_⟩
  have e : PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom ⟨_, hprime⟩ = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom P.asIdeal) = P.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  exact e

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)


include hU in
theorem top_le {C : Type} [CommRing C] (t : Sp (DualNumber C) ⟶ X) (u : Γ(X, U) →+* C)
    (h : red C ≫ t = spMap u ≫ hU.fromSpec) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surj C p
  show t (red C q) ∈ U
  have e : t (red C q) = hU.fromSpec (spMap u q) := by
    have := congrArg (fun f : Sp C ⟶ X => f q) h
    simpa using this
  rw [e]
  exact hU.range_fromSpec.subset (Set.mem_range_self _)

def ringOf {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem ringOf_spec {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) :
    spMap (ringOf t h) ≫ hU.fromSpec = t := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec t hU (isAffineOpen_top (Spec (CommRingCat.of A))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : spMap (ringOf t h) = Spec.map (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) := by
    unfold ringOf spMap
    rw [CommRingCat.ofHom_hom]
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

include hU in
theorem ring_inj {A : Type} [CommRing A] {f g : Γ(X, U) →+* A}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g := by
  rw [cancel_mono] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem ringOf_eq {A : Type} [CommRing A] {t : Sp A ⟶ X} (h : ⊤ ≤ t ⁻¹ᵁ U) {f : Γ(X, U) →+* A}
    (e : t = spMap f ≫ hU.fromSpec) : ringOf t h = f :=
  ring_inj hU ((ringOf_spec hU t h).trans e)

variable {S : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ S)

def redO : Over.mk y ⟶ epsAt y :=
  Over.homMk (red C) (by
    have h : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      ext a; simp
    show red C ≫ spMap (algebraMap C (DualNumber C)) ≫ y = y
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    simp)

def projO : epsAt y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

theorem comp_one_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_mul_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) (a b : T ⟶ G) :
    f ≫ (a * b) = (f ≫ a) * (f ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have rv : redO y ≫ v = 1 := Over.OverMorphism.ext hv
  have rw' : redO y ≫ w = 1 := Over.OverMorphism.ext hw
  have rvw : redO y ≫ (v * w) = 1 := by rw [comp_mul_O, rv, rw', _root_.one_mul]
  have r1 : redO y ≫ (1 : epsAt y ⟶ G) = 1 := comp_one_O _
  have lv : red C ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans hu
  have lw : red C ≫ w.left = spMap u ≫ hU.fromSpec := hw.trans hu
  have lvw : red C ≫ (v * w).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) rvw).trans hu
  have l1 : red C ≫ (1 : epsAt y ⟶ G).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) r1).trans hu
  have hv' := top_le hU _ u lv
  have hw' := top_le hU _ u lw
  have hvw := top_le hU _ u lvw
  have h1 := top_le hU _ u l1
  have e1 : (1 : epsAt y ⟶ G).left = spMap ((algebraMap C (DualNumber C)).comp u) ≫ hU.fromSpec := by
    have p1 : projO y ≫ (1 : Over.mk y ⟶ G) = 1 := comp_one_O _
    have p2 : spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left = (1 : epsAt y ⟶ G).left :=
      congrArg (fun f => CommaMorphism.left f) p1
    rw [← p2, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw) = u := by
    apply ring_inj hU
    have : spMap ((TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw)) =
        red C ≫ spMap (ringOf (v * w).left hvw) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc, ringOf_spec hU, lvw]
  have hχ' : ringOf (v * w).left hvw = χ := by
    ext s
    · rw [hχ]
      exact RingHom.congr_fun hfst s
    · have key := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom
        (GlobalTheory.T.tangent_section_additive S G C y v w hv hw U hv' hw' hvw h1 s)
      rw [map_add (f := _), map_add (f := _)] at key
      change ringOf (v * w).left hvw s + ringOf (1 : epsAt y ⟶ G).left h1 s =
        ringOf v.left hv' s + ringOf w.left hw' s at key
      rw [ringOf_eq hU h1 e1, ringOf_eq hU hv' ev, ringOf_eq hU hw' ew] at key
      have := congrArg TrivSqZeroExt.snd key
      have h0 : TrivSqZeroExt.snd (((algebraMap C (DualNumber C)).comp u) s) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h0, add_zero] at this
      rw [hs, this]
  rw [← hχ', ringOf_spec hU]

end GlobalTheory.CompanionTheory.Ar.TanMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumberStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_sum_dual_number : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | exact GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanChart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem spMap_fromSpec_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {D : Type} [CommRing D]
    (ψ : Γ(X, U) →+* D) :
    spMap ψ ≫ hU.fromSpec ≫ f = spMap (ψ.comp (f.appLE V U hUV).hom) ≫ hV.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ringHom_eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    {ψ ψ' : Γ(X, U) →+* D} (h : spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec) : ψ = ψ' := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_ringHom_of_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    (x : Sp D ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* D, x = spMap φ ≫ hU.fromSpec := by
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec (CommRingCat.of D))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change x = Spec.map (CommRingCat.ofHom (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem le_preimage_of_fst {X : Scheme.{0}} {U : X.Opens} {C : Type} [CommRing C] (x : Sp (DualNumber C) ⟶ X)
    (h : ∀ p, (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ x) p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom := fun c => ⟨TrivSqZeroExt.inl c, by simp⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ p.asIdeal := fun a ha => by
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  haveI := p.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  let p₀ : ↥(Sp C) := (⟨p.asIdeal.map (TrivSqZeroExt.fstHom C C C).toRingHom, hprime⟩ : PrimeSpectrum C)
  have hp : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  have e := h p₀
  simp only [Scheme.Hom.comp_apply] at e
  show x p ∈ U
  rw [← hp]
  exact e

theorem tan_iff_der (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C) :
    (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
    (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
       ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
    (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  intro h1
  have hal : ∀ c : C, algebraMap C (DualNumber C) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hy : y = spMap (u.comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    have hw := Over.w (1 : Over.mk y ⟶ G)
    rw [h1, Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV u] at hw
    exact hw.symm
  have hbase : spMap (algebraMap C (DualNumber C)) ≫ y =
      spMap (((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    rw [hy, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun φ hφ hb => ?_, fun v hv => ?_⟩
  · have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      ext b
      · simpa [hal] using hφ _
      · simpa [hal] using hb b
    refine ⟨Over.homMk (spMap φ ≫ hU.fromSpec) ?_, ?_, rfl⟩
    · change (spMap φ ≫ hU.fromSpec) ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y
      rw [Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV φ, hbase, hcomp]
    · have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
        ext a
        exact hφ a
      change spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap φ ≫ hU.fromSpec = _
      rw [h1, ← Category.assoc, ← Spec.map_comp, ← hfst]
      rfl
  · have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans h1
    have hle : ⊤ ≤ v.left ⁻¹ᵁ U := by
      refine le_preimage_of_fst v.left fun p => ?_
      rw [hv']
      simp only [Scheme.Hom.comp_apply]
      exact hU.range_fromSpec.subset (Set.mem_range_self _)
    obtain ⟨φ, hφ⟩ := exists_ringHom_of_le hU v.left hle
    have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
      apply ringHom_eq_of_fromSpec hU
      rw [← hv', hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      apply ringHom_eq_of_fromSpec hV
      rw [← hbase, ← spMap_fromSpec_hom G.hom hU hV hUV φ, ← Category.assoc, ← hφ]
      exact Over.w v
    refine ⟨φ, fun a => RingHom.congr_fun hfst a, fun b => ?_, hφ⟩
    have := RingHom.congr_fun hcomp b
    simpa [hal] using congrArg TrivSqZeroExt.snd this

end GlobalTheory.CompanionTheory.Ar.TanChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_of_dual_hom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
     ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
  (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
     (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | exact GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der | (intros; apply GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartDer

open scoped TensorProduct

theorem exists_diffModule {A B : Type} [CommRing A] [CommRing B] (g : B →+* A) (hg : g.Smooth)
    {R : Type} [CommRing R] (f : R) (u : A →+* Localization.Away f) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
      (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
      (_ : Module.Projective (Localization.Away f) P) (d : A → P),
      (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = u a • d b + u b • d a) ∧ (∀ b, d (g b) = 0) ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
        κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
        (∀ (w : P →ₗ[R] C) (r : Localization.Away f) (p : P), w (r • p) = κ r * w p) ∧
        (∀ w w' : P →ₗ[R] C, (∀ a, w (d a) = w' (d a)) → w = w') ∧
        (∀ δ : A → C, (∀ a b, δ (a + b) = δ a + δ b) →
          (∀ a b, δ (a * b) = κ (u a) * δ b + κ (u b) * δ a) → (∀ b, δ (g b) = 0) →
          ∃ w : P →ₗ[R] C, ∀ a, w (d a) = δ a) := by
  letI iB : Algebra B A := g.toAlgebra
  haveI : Algebra.Smooth B A := hg
  letI iA : Algebra A (Localization.Away f) := u.toAlgebra
  haveI tw : IsScalarTower R (Localization.Away f) (Localization.Away f ⊗[A] Ω[A⁄B]) := inferInstance
  have hsmul : ∀ (a : A) (x : Ω[A⁄B]), (1 : Localization.Away f) ⊗ₜ[A] (a • x) =
      u a • ((1 : Localization.Away f) ⊗ₜ[A] x) := fun a x => by
    have e : a • (1 : Localization.Away f) = u a := by
      rw [Algebra.smul_def, _root_.mul_one]; rfl
    rw [← TensorProduct.smul_tmul, e, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  refine ⟨Localization.Away f ⊗[A] Ω[A⁄B], inferInstance, inferInstance, inferInstance, tw,
    Module.Finite.base_change A _ _, inferInstance, fun a => 1 ⊗ₜ[A] KaehlerDifferential.D B A a,
    fun a b => by simp [TensorProduct.tmul_add], fun a b => ?_, fun b => ?_, ?_⟩
  · simp only [Derivation.leibniz, TensorProduct.tmul_add, hsmul]
  · have : g b = algebraMap B A b := rfl
    simp [this]
  intro C _ _ κ hκ
  letI aC : Algebra (Localization.Away f) C := κ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' hκ.symm
  have lin : ∀ (w : (Localization.Away f ⊗[A] Ω[A⁄B]) →ₗ[R] C) (r : Localization.Away f) p,
      w (r • p) = κ r * w p := fun w r p => by
    have h : w (r • p) = r • w p :=
      (w.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).map_smul r p
    rw [h, Algebra.smul_def]
    rfl
  refine ⟨lin, fun w w' h => LinearMap.ext fun p => ?_, fun δ h1 h2 h3 => ?_⟩
  · have hD : ∀ x : Ω[A⁄B], w ((1 : Localization.Away f) ⊗ₜ[A] x) = w' ((1 : Localization.Away f) ⊗ₜ[A] x) := by
      intro x
      have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D B A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
      | smul a x _ ih => rw [hsmul, lin, lin, ih]
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add (f := _), hx, hy]
    | tmul r x =>
      have e : r ⊗ₜ[A] x = r • ((1 : Localization.Away f) ⊗ₜ[A] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, lin, lin, hD]
  · letI aA : Algebra A C := (κ.comp u).toAlgebra
    haveI : IsScalarTower A (Localization.Away f) C := IsScalarTower.of_algebraMap_eq' rfl
    letI aB : Algebra B C := ((κ.comp u).comp g).toAlgebra
    haveI : IsScalarTower B A C := IsScalarTower.of_algebraMap_eq' rfl
    let L : A →ₗ[B] C :=
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          change δ (g b * a) = κ (u (g b)) * δ a
          rw [h2, h3, mul_zero, add_zero] }
    let Dv : Derivation B A C := Derivation.mk' L fun a b => by
      change δ (a * b) = κ (u a) * δ b + κ (u b) * δ a
      exact h2 a b
    refine ⟨(Dv.liftKaehlerDifferential.liftBaseChange (Localization.Away f)).restrictScalars R, fun a => ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl

def dualOf {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C)
    (h1 : ∀ a b, δ (a + b) = δ a + δ b) (h2 : ∀ a b, δ (a * b) = v a * δ b + v b * δ a) :
    A →+* DualNumber C where
  toFun a := TrivSqZeroExt.inl (v a) + TrivSqZeroExt.inr (δ a)
  map_one' := by
    have h : δ 1 = 0 := by simpa using h2 1 1
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [h2, TrivSqZeroExt.snd_mul]
      ring
  map_zero' := by
    have h : δ 0 = 0 := by simpa using h1 0 0
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [h1]

theorem dualOf_fst {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).fst = v a := by
  simp [dualOf]

theorem dualOf_snd {A C : Type} [CommRing A] [CommRing C] (v : A →+* C) (δ : A → C) (h1 h2) (a : A) :
    (dualOf v δ h1 h2 a).snd = δ a := by
  simp [dualOf]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem one_left {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [GlobalTheory.T.tangent_vector_sum_dual_number S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add (f := _), l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.ChartDer
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartDer

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have hv' : LieEx.zsec y ≫ (v : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G v).1 hv
  have hw' : LieEx.zsec y ≫ (w : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G w).1 hw
  have z : ∀ t : LieEx.ob y C ⟶ G, LieEx.zsec y ≫ t = 1 → LieEx.hom y (0 : C →ₗ[C] C) ≫ t = 1 := fun t ht => by
    rw [LieEx.hom_zero, Category.assoc, ht, MonObj.comp_one]
  obtain ⟨t, ht⟩ : ∃ t : LieEx.ob y (C × C) ⟶ G, t = (LieEx.hom y (LinearMap.inl C C C) ≫ (v : LieEx.ob y C ⟶ G)) *
    (LieEx.hom y (LinearMap.inr C C C) ≫ (w : LieEx.ob y C ⟶ G)) := ⟨_, rfl⟩
  have hz : LieEx.zsec y ≫ t = 1 := by
    rw [ht, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv', hw',
      _root_.mul_one]
  have h1 : LieEx.hom y (LinearMap.fst C C C) ≫ t = v := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z w hw', _root_.mul_one]
  have h2 : LieEx.hom y (LinearMap.snd C C C) ≫ t = w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv', _root_.one_mul]
  have h3 : LieEx.hom y (LinearMap.fst C C C + LinearMap.snd C C C) ≫ t = v * w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      add_zero, zero_add, LieEx.hom_id, Category.id_comp]
  have hzl : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) ≫ t.left =
      spMap u ≫ hU.fromSpec := (congrArg CommaMorphism.left hz).trans hu
  have hle : ⊤ ≤ t.left ⁻¹ᵁ U := by
    intro p _
    obtain ⟨q, rfl⟩ := LieVB.surj_fst (T := C) (M := C × C) p
    have e : t.left (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) q) =
        hU.fromSpec (spMap u q) := congrArg (fun f : Sp C ⟶ G.left => f q) hzl
    show t.left _ ∈ U
    rw [e]
    exact hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ(G.left, U) →+* TrivSqZeroExt C (C × C), spMap Φ ≫ hU.fromSpec = t.left :=
    ⟨_, TanMul.ringOf_spec (A := TrivSqZeroExt C (C × C)) hU t.left hle⟩
  have key : ∀ (l : C × C →ₗ[C] C), (LieEx.hom y l ≫ t).left =
      spMap ((TrivSqZeroExt.map l).toRingHom.comp Φ) ≫ hU.fromSpec := fun l => by
    rw [spMap_comp, Category.assoc, hΦ]
    rfl
  have e1 := TanMul.ring_inj hU (ev.symm.trans ((congrArg CommaMorphism.left h1).symm.trans (key _)))
  have e2 := TanMul.ring_inj hU (ew.symm.trans ((congrArg CommaMorphism.left h2).symm.trans (key _)))
  have e3 : χ = (TrivSqZeroExt.map (LinearMap.fst C C C + LinearMap.snd C C C)).toRingHom.comp Φ := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [hχ, ← hφ, e1]
      simp
    · rw [hs, e1, e2]
      simp
  rw [e3]
  exact (congrArg CommaMorphism.left h3).symm.trans (key _)

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add (f := _), l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end PositivityTheory.HtPt.Htat.Lie
