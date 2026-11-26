module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B (s ≫ a) (s ≫ b) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B V' V s a b M h x'
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h (s x')
  have hι : (s ∣_ U) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
  refine ⟨s ⁻¹ᵁ U, α, β, (s ∣_ U) ≫ a₁, (s ∣_ U) ≫ b₁, hx, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, reassoc_of% hι]
  · rw [Category.assoc, ← hb, reassoc_of% hι]
  · have h2 := locMatNat B α β (s ∣_ U) _ _ hL
    have e1 : (s ∣_ U) ≫ U.ι ≫ a ≫ cP B = (s ⁻¹ᵁ U).ι ≫ (s ≫ a) ≫ cP B := by
      rw [← Category.assoc, hι]; simp only [Category.assoc]
    have e2 : ((M.map U.ι.appTop.hom).map (s ∣_ U).appTop.hom) =
        ((M.map s.appTop.hom).map (s ⁻¹ᵁ U).ι.appTop.hom) := by
      ext m l
      simp only [Matrix.map_apply]
      have h3 : U.ι.appTop ≫ (s ∣_ U).appTop = s.appTop ≫ (s ⁻¹ᵁ U).ι.appTop := by
        rw [← Scheme.Hom.comp_appTop, hι, Scheme.Hom.comp_appTop]
      exact congrArg (fun f => f.hom (M m l)) h3
    rw [e1, e2] at h2
    exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem e1 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ eP B j = (oT B j p).ι := by
  unfold tI eP
  rw [Sigma.ι_desc]

private theorem e2 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ tauP B j = secOf B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) := by
  unfold tI tauP
  rw [Sigma.ι_desc]

private theorem e3 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (p : B.ι × Fin d) :
    tI B j p ≫ rhoP B j r hw = rhoC B j r hw p ≫ wI B p.1 := by
  unfold tI rhoP
  rw [Sigma.ι_desc]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ (p : B.ι × Fin d) {V : Scheme.{0}} (a₁ : V ⟶ (oT B j p : Scheme.{0})), ∃ h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2, (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ rhoP B j r hw = (a₁ ≫ rhoC B j r hw p) ≫ wI B p.1 := by
  intro K _ W Z Y q i π D d B T j r hw v hv p V a₁
  have ey : (a₁ ≫ tI B j p) ≫ eP B j ≫ j = a₁ ≫ (oT B j p).ι ≫ j := by
    rw [Category.assoc, ← Category.assoc (tI B j p), e1]
  have hle : ⊤ ≤ (a₁ ≫ (oT B j p).ι ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    intro x _
    have := oT_le B j p (Set.mem_univ (a₁ x))
    simpa using this
  have key : ∀ (y' : V ⟶ Y) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c p.1).C p.2), y' = a₁ ≫ (oT B j p).ι ≫ j →
      (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 y' h' ∧
        (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 y' h' := by
    rintro y' h' rfl
    obtain ⟨n1, n2⟩ := chartNat B p.1 p.2 a₁ ((oT B j p).ι ≫ j) (oT_le B j p) h'
    refine ⟨?_, ?_⟩
    · funext m
      rw [n1 m, ← hv p m]
      rw [Function.comp_apply, Scheme.Hom.comp_appTop]
      rfl
    · rw [n2, Category.assoc, e2]
  have h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    rw [ey]; exact hle
  obtain ⟨k1, k2⟩ := key _ h ey
  exact ⟨h, k1, k2, by rw [Category.assoc, e3, Category.assoc]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatLoc
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatLocal
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ LocMat B α β (U.ι ≫ p) (M.map U.ι.appTop.hom)) → LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p M h x
  obtain ⟨U, hxU, hL⟩ := h x
  obtain ⟨U', N, hx', hN, h₁, h₂, hU', G, hT, hM⟩ := hL ⟨x, hxU⟩
  have he : (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι = U'.ι ≫ U.ι := U.ι.isoImage_hom_ι U'
  have hU'' : ⊤ ≤ ((U.ι ''ᵁ U').ι ≫ p ≫ i) ⁻¹ᵁ N := by
    rintro ⟨y, z, hz, rfl⟩ _
    have := @hU' (⟨z, hz⟩ : U'.toScheme) trivial
    exact this
  refine ⟨U.ι ''ᵁ U', N, ⟨⟨x, hxU⟩, hx', rfl⟩, hN, h₁, h₂, hU'', G, hT, ?_⟩
  ext a b
  have hinj : ∀ {A C : Scheme.{0}} (e : A ≅ C), Function.Injective e.hom.appTop.hom := by
    intro A C e
    have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
  apply hinj (U.ι.isoImage U')
  have hab := congrFun (congrFun hM a) b
  simp only [Matrix.map_apply] at hab ⊢
  have e₁ : (U.ι.isoImage U').hom.appTop.hom (((U.ι ''ᵁ U').ι).appTop.hom (M a b)) = U'.ι.appTop.hom (U.ι.appTop.hom (M a b)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, he]
  have e₂ : (U.ι.isoImage U').hom.appTop.hom ((((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'').hom (G a b)) = ((U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU').hom (G a b) := by
    have : ((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'' ≫ (U.ι.isoImage U').hom.appTop = (U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU' := by
      have hc : U'.ι ≫ (U.ι ≫ p) ≫ i = (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι ≫ p ≫ i := by
        rw [reassoc_of% he]; simp
      simp only [hc]
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => f.hom (G a b)) this
  rw [e₁, e₂, hab]
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (α β : B.ι) (a₁ : V ⟶ (oW B α : Scheme.{0})) (b₁ : V ⟶ (oW B β : Scheme.{0})), a = a₁ ≫ wI B α → b = b₁ ≫ wI B β → GMat B a b M → LocMat B α β (a ≫ cP B) M := by
  intro K _ W Z Y q i π D d B V a b M α β a₁ b₁ ha hb hG
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal B α β (a ≫ cP B) M fun x => ?_
  obtain ⟨U, α', β', a', b', hx, h1, h2, hL⟩ := hG x
  have e1 : α' = α := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) a' (U.ι ≫ a₁) (⟨x, hx⟩ : U) ?_
    have h : a' ≫ wI B α' = (U.ι ≫ a₁) ≫ wI B α := by
      rw [← h1, ha, Category.assoc]
    exact h
  have e2 : β' = β := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) b' (U.ι ≫ b₁) (⟨x, hx⟩ : U) ?_
    have h : b' ≫ wI B β' = (U.ι ≫ b₁) ≫ wI B β := by
      rw [← h2, hb, Category.assoc]
    exact h
  subst e1 e2
  exact ⟨U, hx, hL⟩
end
