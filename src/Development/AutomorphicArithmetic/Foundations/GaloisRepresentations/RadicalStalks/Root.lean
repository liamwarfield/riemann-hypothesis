module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OneLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpenStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonvanishingPoint
theorem UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (B : Type)
    [inst_2 : CommRing B] [inst_3 : Algebra k B] [Algebra.FiniteType k B] [IsReduced B] {c : B},
    c ≠ (0 : B) → ∃ (x : B →ₐ[k] k), (x : B → k) c ≠ (0 : k) := by
  intro k _ _ B _ _ _ _ c hc
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal B).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    exact (Ideal.mem_bot).2 (IsNilpotent.eq_zero ⟨n, (Ideal.mem_bot).1 hn⟩)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out ‹_› hrad
  have hcj : c ∉ (⊥ : Ideal B).jacobson := by
    rw [hj]
    exact fun h => hc ((Ideal.mem_bot).1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hcj
  push Not at hcj
  obtain ⟨m, ⟨-, hm⟩, hcm⟩ := hcj
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  let f : (B ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  intro h
  apply hcm
  have h1 : f (Ideal.Quotient.mk m c) = 0 := h
  have h2 : Ideal.Quotient.mk m c = 0 := (map_eq_zero f).1 h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Transl
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.transl :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left), SMor A σ ψ →
      (∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ)) → ∀ v : epsR k ⟶ A, IsConst (v.left ≫ ψ) := by
  intro k _ A _ σ ψ m hT v
  let z : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  let r : Sp (DualNumber k) ⟶ Sp k := spMap (algebraMap k (DualNumber k))
  have hq : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = r ≫ z := by
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hzr : z ≫ r = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; simp
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have hqq : (r ≫ z) ≫ r ≫ z = r ≫ z := by
    rw [Category.assoc, reassoc_of% hzr]
  let c : epsR k ⟶ epsR k := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r = r
    rw [Category.assoc, hzr, Category.comp_id])
  let zz : 𝟙_ (Over (Sp k)) ⟶ epsR k := Over.homMk z hzr
  have hzc : zz ≫ c = zz := Over.OverMorphism.ext (by
    show z ≫ r ≫ z = z
    rw [reassoc_of% hzr])
  let v0 : epsR k ⟶ A := c ≫ v
  let t : epsR k ⟶ A := v0⁻¹ * v
  have hvt : v = v0 * t := by simp [t]
  have hzt : zz ≫ t = 1 := by
    have a : zz ≫ v0 = zz ≫ v := by simp only [v0, ← Category.assoc, hzc]
    calc zz ≫ t = (zz ≫ v0⁻¹) * (zz ≫ v) := MonObj.comp_mul _ _ _
      _ = (zz ≫ v0⁻¹) * (zz ≫ v0) := by rw [a]
      _ = zz ≫ (v0⁻¹ * v0) := (MonObj.comp_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, MonObj.comp_one]
  have htan : IsTangent t := by
    have e1 : (1 : 𝟙_ (Over (Sp k)) ⟶ A) = η[A] := by
      show toUnit _ ≫ η[A] = _
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    show z ≫ t.left = η[A].left
    rw [← e1, ← hzt]
    rfl
  let Y : Over (Sp k) := Over.mk ((epsR k).hom ≫ spMap σ)
  let Q : Y ⟶ Y := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r ≫ spMap σ = r ≫ spMap σ
    rw [Category.assoc, reassoc_of% hzr])
  let down (x : epsR k ⟶ A) : Y ⟶ A :=
    Over.homMk (x.left ≫ ψ) (by simp [Y, m.w])
  have down_mul (x y : epsR k ⟶ A) : down (x * y) = down x * down y :=
    Over.OverMorphism.ext (m.mul (epsR k) x y (down x) (down y) rfl rfl).symm
  have h0 : Q ≫ down v0 = down v0 := Over.OverMorphism.ext (by
    show (r ≫ z) ≫ ((r ≫ z) ≫ v.left) ≫ ψ = ((r ≫ z) ≫ v.left) ≫ ψ
    simp only [← Category.assoc]
    rw [show ((r ≫ z) ≫ r) ≫ z = r ≫ z by simpa using hqq])
  have h1 : Q ≫ down t = down t := Over.OverMorphism.ext (by
    have := hT t htan
    unfold IsConst at this
    rw [hq] at this
    exact this)
  have key : Q ≫ down v = down v := by
    rw [hvt, down_mul, MonObj.comp_mul, h0, h1]
  unfold IsConst
  rw [hq]
  exact congrArg (fun u => u.left) key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FromSpecEv
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RootGlue
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma rootGlue_uniq {R : Type*} [CommRing R] [IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (hab : a ^ p = b ^ p) : a = b := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim a b
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    haveI : Fact p.Prime := ⟨hp⟩
    apply frobenius_inj R p
    simpa [frobenius_def] using hab

theorem UpperTheory.Gal.Ord.rootGlue :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X], (p : Γ(X, ⊤)) = 0 → ∀ (U : X.Opens) (s : Γ(X, U)),
      (∀ (V : X.Opens) (hV : V ≤ U), IsAffineOpen V → ∃ r : Γ(X, V), r ^ p = X.presheaf.map (homOfLE hV).op s) → ∃ r : Γ(X, U), r ^ p = s := by
  intro p _ X _ hp U s hloc
  have hpr : p.Prime := Fact.out
  have hpV : ∀ V : X.Opens, (p : Γ(X, V)) = 0 := by
    intro V
    have h0 := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) hp
    rwa [map_natCast, map_zero] at h0
  let Idx := {V : X.Opens // V ≤ U ∧ IsAffineOpen V}
  choose r hr using fun i : Idx => hloc i.1 i.2.1 i.2.2
  have hcover : U ≤ ⨆ i : Idx, i.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hxV⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun i : Idx => i.1) r := by
    intro i j
    apply rootGlue_uniq hpr (hpV _)
    change (X.presheaf.map _ (r i)) ^ p = (X.presheaf.map _ (r j)) ^ p
    rw [← map_pow, ← map_pow, hr i, hr j, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, U), ∀ i : Idx, X.presheaf.map (homOfLE i.2.1).op t = r i :=
    X.sheaf.existsUnique_gluing' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover r hcomp
  refine ⟨t, ?_⟩
  have key : ∀ i : Idx,
      X.presheaf.map (homOfLE i.2.1).op (t ^ p) = X.presheaf.map (homOfLE i.2.1).op s := by
    intro i
    rw [map_pow, ht i, hr i]
  exact X.sheaf.eq_of_locally_eq' (fun i : Idx => i.1) U (fun i => homOfLE i.2.1) hcover _ _ key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsFunctionalNeZeroProjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_functional_ne_zero_projective {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] {m : M} (hm : m ≠ 0) : ∃ l : M →ₗ[B] B, l m ≠ 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B M)
  by_contra hall
  push_neg at hall
  apply hm
  have h0 : s m = 0 := by
    ext a
    simpa using hall (Finsupp.lapply a ∘ₗ s)
  have := LinearMap.congr_fun hs m
  simpa [h0] using this.symm

private theorem exists_point_nonvanishing_reduced (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [IsReduced B] {c : B} (hc : c ≠ 0) :
    ∃ x : B →ₐ[k] k, x c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced k B hc

theorem UpperTheory.Gal.Ord.dz1 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] [Module.Projective B Ω[B⁄k]] (r : B),
      (∀ v : B →ₐ[k] DualNumber k, TrivSqZeroExt.snd (v r) = 0) → KaehlerDifferential.D k B r = 0 := by
  intro k _ _ B _ _ _ _ _ r hv
  by_contra hne
  obtain ⟨l, hl⟩ := exists_functional_ne_zero_projective (B := B) hne
  obtain ⟨x, hx⟩ := exists_point_nonvanishing_reduced k B hl
  let d : B →ₗ[k] k := x.toLinearMap ∘ₗ (l.restrictScalars k) ∘ₗ (KaehlerDifferential.D k B).toLinearMap
  have hd : ∀ b, d b = x (l (KaehlerDifferential.D k B b)) := fun _ => rfl
  let f : B →ₗ[k] DualNumber k :=
    Algebra.linearMap k (DualNumber k) ∘ₗ x.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ d
  have hal : ∀ c : k, algebraMap k (DualNumber k) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hfst : ∀ b, TrivSqZeroExt.fst (f b) = x b := fun b => by simp [f, hal]
  have hsnd : ∀ b, TrivSqZeroExt.snd (f b) = d b := fun b => by simp [f, hal]
  let v : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap f
    (by
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hsnd, hd])
    (by
      intro a b
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hfst, hsnd, hd, Derivation.leibniz, mul_comm, add_comm])
  apply hx
  have := hv v
  simpa [v, hsnd, hd] using this
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma ev_comp {T T' : Type} [CommRing T] [CommRing T'] (g : T →+* T') {Y : Scheme.{0}} (U : Y.Opens)
    (f : Sp T ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U) :
    (spMap g ≫ f).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of T')).hom =
      (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ CommRingCat.ofHom g := by
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h (by simp), Category.assoc, Category.assoc]
  congr 1
  have hh : (spMap g).appLE ⊤ ⊤ (by simp) = (spMap g).appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [hh]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

private lemma fromSpec_ev {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ W)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ W) :
    hV.fromSpec.appLE W ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = X.presheaf.map (homOfLE hVW).op := by
  have e' : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  rw [← Scheme.Hom.map_appLE hV.fromSpec e' (homOfLE hVW).op, Category.assoc]
  have key : hV.fromSpec.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hid : ∀ i : Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤, i = 𝟙 _ :=
      fun i => Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hid (_ ≫ _), CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rw [key, Category.comp_id]

private lemma snd_zero {k : Type} [Field k] {X Y : Scheme.{0}} (ψ : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hV : V ≤ ψ ⁻¹ᵁ U) (hA : IsAffineOpen V) (φ : Γ(X, V) →+* DualNumber k)
    (hc : IsConst (spMap φ ≫ hA.fromSpec ≫ ψ)) (t : Γ(Y, U)) :
    TrivSqZeroExt.snd (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) = 0 := by
  have h0 : ⊤ ≤ hA.fromSpec ⁻¹ᵁ (ψ ⁻¹ᵁ U) :=
    hA.fromSpec_preimage_self.ge.trans
      ((TopologicalSpace.Opens.map hA.fromSpec.base).map (homOfLE hV)).le
  have h1 : ⊤ ≤ (hA.fromSpec ≫ ψ) ⁻¹ᵁ U := h0
  have h2 : ⊤ ≤ (spMap φ ≫ hA.fromSpec ≫ ψ) ⁻¹ᵁ U := fun x _ => h1 (Set.mem_univ _)
  have hc' : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap φ ≫ hA.fromSpec ≫ ψ = spMap φ ≫ hA.fromSpec ≫ ψ := hc
  have hcongr : ∀ (w₁ w₂ : Sp (DualNumber k) ⟶ Y), w₁ = w₂ → ∀ (e₁ : ⊤ ≤ w₁ ⁻¹ᵁ U)
      (e₂ : ⊤ ≤ w₂ ⁻¹ᵁ U), w₁.appLE U ⊤ e₁ = w₂.appLE U ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have A := ev_comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
    U (spMap φ ≫ hA.fromSpec ≫ ψ) h2 (hc'.symm ▸ h2)
  rw [hcongr _ _ hc' _ h2] at A
  have B := ev_comp φ U (hA.fromSpec ≫ ψ) h1 h2
  have C := fromSpec_ev hA hV h0
  have B' : (spMap φ ≫ hA.fromSpec ≫ ψ).appLE U ⊤ h2 ≫
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom =
      ψ.app U ≫ X.presheaf.map (homOfLE hV).op ≫ CommRingCat.ofHom φ := by
    rw [B, Scheme.Hom.comp_appLE, Category.assoc, Category.assoc]
    erw [← Category.assoc (hA.fromSpec.appLE _ _ _), C]
  have A' := ConcreteCategory.congr_hom A t
  rw [B'] at A'
  have hxx : φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)) =
      ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
        (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) := by
    simpa using A'
  rw [hxx, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

theorem UpperTheory.Gal.Ord.dzero :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X Y : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (ψ : X ⟶ Y),
      (∀ v : Sp (DualNumber k) ⟶ X, v ≫ s = spMap (algebraMap k (DualNumber k)) → IsConst (v ≫ ψ)) →
      ∀ (U : Y.Opens) (t : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U t := by
  intro p _ k _ _ hk X Y _ s _ ψ hψ U t
  have hp : (p : Γ(X, ⊤)) = 0 := by
    have h := congrArg (GlobalTheory.CechDR.secMap s ⊤).hom hk
    rwa [map_natCast, map_zero] at h
  refine rootGlue p X hp (ψ ⁻¹ᵁ U) (ψ.app U t) ?_
  intro V hV hA
  let V' : X.affineOpens := ⟨V, hA⟩
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s V) := by
    have hi : Smooth hA.fromSpec := inferInstance
    have h0 : Smooth (hA.fromSpec ≫ s) := MorphismProperty.comp_mem _ _ _ hi ‹Smooth s›
    have h1 : Smooth (GlobalTheory.CechDR.affPt s V' ≫ s) := h0
    rw [GlobalTheory.CechDR.affPt_w] at h1
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h1)
  haveI : _root_.IsReduced (GlobalTheory.CechDR.Sec s V) := IsReduced.component_reduced V
  have hD := dz1 k (GlobalTheory.CechDR.Sec s V) (X.presheaf.map (homOfLE hV).op (ψ.app U t)) ?_
  · exact GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen p k hk X s V' _ hD
  intro v
  have hw : (spMap v.toRingHom ≫ hA.fromSpec) ≫ s = spMap (algebraMap k (DualNumber k)) := by
    change spMap v.toRingHom ≫ GlobalTheory.CechDR.affPt s V' ≫ s = _
    rw [GlobalTheory.CechDR.affPt_w, ← Geo.Tor.spMap_comp]
    exact congrArg spMap v.comp_algebraMap
  have hc : IsConst (spMap v.toRingHom ≫ hA.fromSpec ≫ ψ) := by
    convert hψ _ hw using 1
    exact (Category.assoc _ _ _).symm
  exact snd_zero ψ hV hA v.toRingHom hc t
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RootMor
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.rootMor :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ σ' : k →+* k) (ψ ψ' : A.left ⟶ A.left), SMor A σ ψ → (∀ x, σ' x ^ p = σ x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ → SMor A σ' ψ' := by
  intro p _ k _ _ hk A _ _ hAb σ σ' ψ ψ' hS hpow hfr
  haveI := hAb
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  haveI hP : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hAb hAb
  haveI : Smooth (A ⊗ A).hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced (A ⊗ A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (A ⊗ A).hom
  haveI : Epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A)) := (epi p A.left (cast_left p k hk A)).1
  haveI : Epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) :=
    (epi p (A ⊗ A).left (cast_left p k hk (A ⊗ A))).1
  have hσ : spMap (frobR p k hk) ≫ spMap σ' = spMap σ := by
    rw [← Geo.Tor.spMap_comp]
    congr 1
    ext x
    rw [RingHom.comp_apply, GlobalTheory.ConjSeq.frobR_apply, hpow]
  have hw' : ψ' ≫ A.hom = A.hom ≫ spMap σ' := by
    apply (cancel_epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A))).mp
    rw [← Category.assoc, hfr, hS.w, ← Category.assoc,
      GlobalTheory.ConjSeq.frob_comp_hom p k hk A.hom (cast_left p k hk A), Category.assoc, hσ]
  have hnat : ∀ f : (A ⊗ A).left ⟶ A.left,
      GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)) ≫ f ≫ ψ' = f ≫ ψ := by
    intro f
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p (cast_left p k hk A) f (cast_left p k hk (A ⊗ A)),
      Category.assoc, hfr]
  let F : Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) (by
      simp only [Over.mk_hom]
      rw [← Category.assoc,
        GlobalTheory.ConjSeq.frob_comp_hom p k hk (A ⊗ A).hom (cast_left p k hk (A ⊗ A)), Category.assoc, hσ])
  let u : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ') ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ') (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hw', ← Category.assoc, Over.w g])
  let v : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hS.w, ← Category.assoc, Over.w g])
  have hFu : ∀ g : A ⊗ A ⟶ A, F ≫ u g = v g := by
    intro g
    apply Over.OverMorphism.ext
    simp only [F, u, v, Over.comp_left, Over.homMk_left]
    exact hnat g.left
  have huniv : (u (fst A A) * u (snd A A)).left = (fst A A * snd A A).left ≫ ψ' := by
    apply (cancel_epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)))).mp
    rw [hnat]
    have e1 : (F ≫ (u (fst A A) * u (snd A A))).left = (v (fst A A) * v (snd A A)).left := by
      rw [MonObj.comp_mul, hFu, hFu]
    rw [Over.comp_left] at e1
    exact e1.trans (hS.mul (A ⊗ A) (fst A A) (snd A A) (v (fst A A)) (v (snd A A)) rfl rfl)
  refine GlobalTheory.DeRham.GrpMor.mk (isDPMorphism_of_eq_bot (dp0 k) rfl (dp0 k) σ') (by simp) hw' ?_
  intro T x y x₀ y₀ hx0 hy0
  let h : T ⟶ A ⊗ A := lift x y
  let hh : Over.mk (T.hom ≫ spMap σ') ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk h.left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w h])
  have ex : x₀ = hh ≫ u (fst A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hx0, ← Category.assoc, ← Over.comp_left, lift_fst]
  have ey : y₀ = hh ≫ u (snd A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hy0, ← Category.assoc, ← Over.comp_left, lift_snd]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left, huniv]
  simp only [hh, Over.homMk_left]
  rw [← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobRootMor
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.RootBuild

variable {p : ℕ} [hp : Fact p.Prime] {X Y : Scheme.{0}} [IsReduced X]

private theorem pow_inj (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) {a b : Γ(X, U)} (e : a ^ p = b ^ p) :
    a = b := by
  have hU := GlobalTheory.SS.FrobField.cast_zero h U
  have hs := map_sub (GlobalTheory.SS.FrobField.powHom Γ(X, U) p 1 hp.out hU) a b
  have e2 : (a - b) ^ p = 0 := by
    simpa [GlobalTheory.SS.FrobField.powHom, e] using hs
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨p, e2⟩)

variable (ψ : X ⟶ Y)
  (H : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s)

private def rt (U : Y.Opens) (s : Γ(Y, U)) : Γ(X, ψ ⁻¹ᵁ U) := (H U s).choose

private theorem rt_pow (U : Y.Opens) (s : Γ(Y, U)) : rt ψ H U s ^ p = ψ.app U s := (H U s).choose_spec

private def rtHom (h : (p : Γ(X, ⊤)) = 0) (U : Y.Opens) : Γ(Y, U) →+* Γ(X, ψ ⁻¹ᵁ U) where
  toFun := rt ψ H U
  map_one' := pow_inj h _ (by rw [rt_pow, map_one, one_pow])
  map_mul' a b := pow_inj h _ (by rw [mul_pow, rt_pow, rt_pow, rt_pow, map_mul])
  map_zero' := pow_inj h _ (by rw [rt_pow, map_zero, zero_pow hp.out.ne_zero])
  map_add' a b := pow_inj h _ (by
    have hU := GlobalTheory.SS.FrobField.cast_zero h (ψ ⁻¹ᵁ U)
    have := map_add (GlobalTheory.SS.FrobField.powHom Γ(X, ψ ⁻¹ᵁ U) p 1 hp.out hU) (rt ψ H U a) (rt ψ H U b)
    have e : (rt ψ H U a + rt ψ H U b) ^ p = rt ψ H U a ^ p + rt ψ H U b ^ p := by
      simpa [GlobalTheory.SS.FrobField.powHom] using this
    rw [e, rt_pow, rt_pow, rt_pow, map_add (f := _)])

private def rootPre (h : (p : Γ(X, ⊤)) = 0) : X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  base := ψ.base
  c := { app := fun U => CommRingCat.ofHom (rtHom ψ H h U.unop)
         naturality := fun U V i => by
           ext s
           refine pow_inj h _ ?_
           have e := congrArg (fun φ => φ.hom s) (ψ.naturality i)
           show (rt ψ H V.unop ((Y.presheaf.map i).hom s)) ^ p =
             ((X.presheaf.map ((TopologicalSpace.Opens.map ψ.base).map i.unop).op).hom (rt ψ H U.unop s)) ^ p
           rw [rt_pow, ← map_pow, rt_pow]
           exact e }

private def rootMor (h : (p : Γ(X, ⊤)) = 0) : X ⟶ Y :=
  ⟨⟨rootPre ψ H h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := ψ.base x) a
    have e := PresheafedSpace.stalkMap_germ_apply (rootPre ψ H h) U x hU s
    erw [e] at ha
    have ha' : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s)) := ha
    have e2 : (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s) =
        (X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (rt ψ H U s) ^ p := by
      rw [← rt_pow ψ H U s, map_pow]
    have hu : IsUnit ((X.presheaf.germ (ψ ⁻¹ᵁ U) x hU).hom (ψ.app U s)) := e2 ▸ ha'.pow p
    have e3 := Scheme.Hom.germ_stalkMap_apply ψ U x hU s
    rw [← e3] at hu
    exact isUnit_of_map_unit (ψ.stalkMap x).hom _ hu⟩⟩⟩

private theorem frob_rootMor (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ rootMor ψ H h = ψ := by
  refine Scheme.Hom.ext rfl ?_
  intro U
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  have e := GlobalTheory.VB.frob_app p h (rootMor ψ H h ⁻¹ᵁ U) (rt ψ H U s)
  refine Eq.trans ?_ (rt_pow ψ H U s)
  exact e

end UpperTheory.Gal.Ord.RootBuild

theorem UpperTheory.Gal.Ord.root0 :
    ∀ (p : ℕ) [Fact p.Prime] (X Y : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0) (ψ : X ⟶ Y),
      (∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U s) → ∃ ψ' : X ⟶ Y, GlobalTheory.VB.frob X p h ≫ ψ' = ψ :=
  fun _ _ _ _ _ h ψ H => ⟨UpperTheory.Gal.Ord.RootBuild.rootMor ψ H h, UpperTheory.Gal.Ord.RootBuild.frob_rootMor ψ H h⟩

end
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.root :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : A.left ⟶ A.left) (m : SMor A σ ψ), (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) →
      ∃ (σ' : k →+* k) (ψ' : A.left ⟶ A.left), Function.Bijective σ' ∧ SMor A σ' ψ' ∧ (∀ x, σ' x ^ p = σ x) ∧ GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ := by
  intro p _ k _ _ hk A _ _ hab σ hσ ψ m hm
  haveI : IsAbelianScheme A := hab
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hk
  haveI : AlgebraicGeometry.IsIntegral A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hab
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hab
  have hLie : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hab hg).1
  have hT : ∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ) := by
    intro v hv
    refine (tan k A hab σ ψ m hσ.2 v hv).mp ?_
    intro f hf
    obtain ⟨h, hh⟩ := hLie.2 v hv
    have hcl : Form.cl _ ((GrpMor.isMor m).pullForm f) = 0 := by
      rw [IsMor.cl_pullForm]
      have hF : (⟨Form.cl _ f, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
        show Form.cl _ f ∈ F1 _
        rw [hodgeFiltration_eq_range]
        exact ⟨f, rfl⟩
      exact congrArg Subtype.val (hm _ hF)
    have hmem : Form.cl _ ((GrpMor.isMor m).pullForm f) ∈ primDR A := hcl ▸ (primDR A).zero_mem
    rw [← hh.2 _ hmem]
    have he : (⟨Form.cl _ ((GrpMor.isMor m).pullForm f), hmem⟩ : primDR A) = 0 := Subtype.ext hcl
    rw [he]
    exact map_zero h
  have hall := transl k A σ ψ m hT
  have hroot := dzero p k hk A.left A.left A.hom ψ (fun v hv => hall (Over.homMk v hv))
  obtain ⟨ψ', hψ'⟩ := root0 p A.left A.left (cast_left p k hk A) ψ hroot
  refine ⟨((frobeniusEquiv k p).symm : k →+* k).comp σ, ψ', ?_, ?_, ?_, hψ'⟩
  · exact (frobeniusEquiv k p).symm.bijective.comp hσ
  · exact rootMor p k hk A hab σ _ ψ ψ' m (fun x => frobeniusEquiv_symm_pow_p k p (σ x)) hψ'
  · exact fun x => frobeniusEquiv_symm_pow_p k p (σ x)
