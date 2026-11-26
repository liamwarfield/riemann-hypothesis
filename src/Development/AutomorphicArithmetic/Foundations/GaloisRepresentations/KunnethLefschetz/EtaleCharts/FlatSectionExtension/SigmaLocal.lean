module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {V : Scheme.{0}} (a : V ⟶ ∐ X) (x : V), ∃ (U : V.Opens) (p : σ) (a₁ : (U : Scheme.{0}) ⟶ X p), x ∈ U ∧ U.ι ≫ a = a₁ ≫ Sigma.ι X p := by
  intro σ X V a x
  obtain ⟨⟨p, z⟩, hz⟩ := (sigmaMk X).surjective (a x)
  rw [sigmaMk_mk] at hz
  have hr : Set.range ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) ⊆ Set.range (Sigma.ι X p) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  refine ⟨a ⁻¹ᵁ (Sigma.ι X p).opensRange, p,
    IsOpenImmersion.lift (Sigma.ι X p) ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) hr, ?_, ?_⟩
  · show a x ∈ (Sigma.ι X p).opensRange
    exact ⟨z, hz⟩
  · exact (IsOpenImmersion.lift_fac _ _ _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt :
    ∀ {V : Scheme.{0}} (s s' : Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι.appTop.hom s = U.ι.appTop.hom s') → s = s' := by
  intro V s s' h
  choose U hxU hU using h
  refine TopCat.Sheaf.eq_of_locally_eq' V.sheaf (fun x => (U x).ι ''ᵁ ⊤) ⊤
    (fun x => homOfLE le_top) ?_ s s' ?_
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ⟨⟨y, hxU y⟩, trivial, rfl⟩⟩
  · intro x
    exact hU x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {S : Scheme.{0}} {p p' : σ} (f : S ⟶ X p) (f' : S ⟶ X p') (_ : S), f ≫ Sigma.ι X p = f' ≫ Sigma.ι X p' → p = p' := by
  intro σ X S p p' f f' s h
  have e : Sigma.ι X p (f s) = Sigma.ι X p' (f' s) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact congrArg Sigma.fst ((sigmaι_eq_iff X p p' _ _).mp e)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α) → LocMat B α α p 1 := by
  intro K _ W Z Y q i π D d B α V p h x
  have hU : ⊤ ≤ (((⊤ : V.Opens).ι ≫ p ≫ i) ⁻¹ᵁ B.V α) := by
    intro y _
    exact h y.1
  refine ⟨⊤, B.V α, trivial, (B.c α).affine, le_rfl, le_rfl, hU, 1, ?_, ?_⟩
  · intro m
    simp [Matrix.one_apply]
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.coverComm :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i), rhoP B j r hw ≫ cP B = eP B j ≫ r ∧ tauP B j ≫ D.f = eP B j ≫ j := by
  intro K _ W Z Y q i π D d B T j r hw
  constructor
  · refine Sigma.hom_ext _ _ fun p => ?_
    have h1 : wI B p.1 ≫ cP B = (oW B p.1).ι := by
      simp only [wI, cP, Sigma.ι_desc]
    have h2 : rhoC B j r hw p ≫ (oW B p.1).ι = (oT B j p).ι ≫ r := by
      simp only [rhoC, IsOpenImmersion.lift_fac]
    simp only [rhoP, eP, Sigma.ι_desc_assoc, Category.assoc, h1, h2]
  · refine Sigma.hom_ext _ _ fun p => ?_
    simp only [tauP, eP, Sigma.ι_desc_assoc, secOf_f]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.uSelf :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k), uV B α k y h k = 1 := by
  intro K _ W Z Y q i π D d B α k V y h
  have hmem : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hu : (B.c α).u k k = 1 := by
    have h0 := RingHom.mem_ker.mp hmem
    rw [map_sub, map_one, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at h0
    exact sub_eq_zero.mp h0
  unfold uV
  rw [hu, map_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNat
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V' V : Scheme.{0}} (s : V' ⟶ V) (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k), (∀ m, uV B α k (s ≫ y) h' m = s.appTop.hom (uV B α k y h m)) ∧ secOf B α k (s ≫ y) h' = s ≫ secOf B α k y h := by
  intro K _ W Z Y q i π D d B α k V' V s y h h'
  constructor
  · intro m
    have hs : (⊤ : V'.Opens) ≤ s ⁻¹ᵁ (⊤ : V.Opens) := le_rfl
    have key : (s ≫ y).appLE ((B.c α).C k) ⊤ h' = y.appLE ((B.c α).C k) ⊤ h ≫ s.appTop := by
      have h1 := Scheme.Hom.appLE_comp_appLE s y ((B.c α).C k) ⊤ ⊤ h hs
      rw [← h1]
      congr 1
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change _ ≫ V'.presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    unfold uV
    rw [key]
    rfl
  · unfold secOf
    rw [← Category.assoc]
    congr 1
    symm
    apply IsOpenImmersion.lift_uniq
    rw [Category.assoc, IsOpenImmersion.lift_fac]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.EtaleSplit
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι), (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).Etale := by
  intro K _ W Z Y q i π D d B α
  let E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K ≃ₐ[K] MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) :=
    (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin (B.c α).n) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv K (Fin d) (Fin (B.c α).n))
  have h : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).comp
        (E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K →+* MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K)) =
      MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, MvPolynomial.sumAlgEquiv_C_inl]
    · rintro (m | m) <;> simp [E, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have h' : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)) =
      (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t)).comp
        (E.symm : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* MvPolynomial (Fin (B.c α).n ⊕ Fin d) K) := by
    rw [← h]
    ext x
    all_goals simp
  rw [h']
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective E.symm.bijective) (B.c α).etale
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_top_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  change _ = f.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

private theorem appLE_comp_appTop' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ N) (h' : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ N) :
    (f ≫ g).appLE N ⊤ h' = g.appLE N ⊤ h ≫ f.appTop := by
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial
  rw [← appLE_top_eq f e]
  exact (Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V' V : Scheme.{0}} (s : V' ⟶ V) (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β (s ≫ p) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B α β V' V s p M h x'
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩ := h (s x')
  have e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i := by
    rw [← Category.assoc (s ∣_ U), morphismRestrict_ι]
    simp only [Category.assoc]
  have hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N := by
    rw [e]
    intro y _
    exact hU (Set.mem_univ ((s ∣_ U) y))
  refine ⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩
  have gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ hf = g.appLE N ⊤ hg := by
    rintro f g rfl _ _
    rfl
  have h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop :=
    (gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)
  have h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a) := by
    intro a
    have e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop := by rw [morphismRestrict_ι]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e2
    exact congrArg (fun φ => φ.hom a) e2
  ext m l
  have h1 := congrFun (congrFun hM m) l
  simp only [Matrix.map_apply] at h1 ⊢
  rw [h3, ← h4, h1]
  rfl
end
