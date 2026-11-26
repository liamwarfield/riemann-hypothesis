module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvField
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem uV_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : uV B α k y h = uV B α k y' h' := by
  subst e; rfl

private theorem secOf_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : secOf B α k y h = secOf B α k y' h' := by
  subst e; rfl

private theorem u_eq' {Y : Scheme.{0}} (D : E.LineData Y) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ea : a = a') (eb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ea eb; rfl

private theorem rho_c {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) : rhoP B j r hw ≫ cP B = eP B j ≫ r := by
  refine Sigma.hom_ext _ _ fun p => ?_
  simp only [rhoP, cP, eP, wI, Category.assoc, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as,
    rhoC, IsOpenImmersion.lift_fac]

private theorem core {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (hab : (a₁ ≫ tI B j p) ≫ eP B j = (b₁ ≫ tI B j p') ≫ eP B j)
    (hh : ((a₁ ≫ tI B j p) ≫ tauP B j) ≫ D.f = ((b₁ ≫ tI B j p') ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ((b₁ ≫ tI B j p') ≫ rhoP B j r hsq.w) M) :
    M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) =
      (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v) := by
  obtain ⟨h₁, e1, e2, e3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p a₁
  obtain ⟨h₂, f1, f2, f3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p' b₁
  have hy : (b₁ ≫ tI B j p') ≫ eP B j ≫ j = (a₁ ≫ tI B j p) ≫ eP B j ≫ j := by
    rw [← Category.assoc, ← hab, Category.assoc]
  have h₂' : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C p'.2 := hy ▸ h₂
  have hL := UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc B _ _ M p.1 p'.1 (a₁ ≫ rhoC B j r hsq.w p) (b₁ ≫ rhoC B j r hsq.w p') e3 f3 hG
  have hc : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ≫ cP B) ≫ i := by
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hsq.w,
      ← Category.assoc (rhoP B j r hsq.w), rho_c B j r hsq.w]
    simp only [Category.assoc]
  have key := UpperTheory.Gal.KunnethLefschetz.G.PX.gvChart B _ _ hc p.1 p'.1 p.2 p'.2 h₁ h₂' M hL
  rw [e1, f1, uV_eq' B p'.1 p'.2 hy h₂ h₂',
    u_eq' D e2 (f2.trans (secOf_eq' B p'.1 p'.2 hy h₂ h₂')) hh
      ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 p'.2 _ h₂').symm)]
  exact key

private theorem core' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (a b : V ⟶ TP B j) (ea : a = a₁ ≫ tI B j p) (eb : b = b₁ ≫ tI B j p')
    (hab : a ≫ eP B j = b ≫ eP B j) (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M) :
    M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  subst ea eb
  exact core B j r hsq v hv p p' a₁ b₁ hab hh M hG

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j → ∀ (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b hab hh M hG
  funext m
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x
  let U : V.Opens := U₁ ⊓ U₂
  have hU₁ : U ≤ U₁ := inf_le_left
  have hU₂ : U ≤ U₂ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p := by
    have : (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p = V.homOfLE hU₁ ≫ (U₁.ι ≫ a) := by
      rw [ha]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  have eb : U.ι ≫ b = (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' := by
    have : (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' = V.homOfLE hU₂ ≫ (U₂.ι ≫ b) := by
      rw [hb]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨U, ⟨hx₁, hx₂⟩, ?_⟩
  have hG' : GMat B ((U.ι ≫ a) ≫ rhoP B j r hsq.w) ((U.ι ≫ b) ≫ rhoP B j r hsq.w) (M.map U.ι.appTop.hom) := by
    simpa only [Category.assoc] using UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat B U.ι _ _ M hG
  have hab' : (U.ι ≫ a) ≫ eP B j = (U.ι ≫ b) ≫ eP B j := by
    rw [Category.assoc, Category.assoc, hab]
  have hh' : ((U.ι ≫ a) ≫ tauP B j) ≫ D.f = ((U.ι ≫ b) ≫ tauP B j) ≫ D.f := by
    simp only [Category.assoc] at hh ⊢
    rw [hh]
  have res := core' B j r hsq v hv p p' _ _ (U.ι ≫ a) (U.ι ≫ b) ea eb hab' hh' _ hG'
  have hc : ∀ g : V ⟶ TP B j, (U.ι ≫ g).appTop.hom ∘ v = U.ι.appTop.hom ∘ (g.appTop.hom ∘ v) := by
    intro g
    funext l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Scheme.Hom.comp_appTop]
    rfl
  have hu : D.u ((U.ι ≫ a) ≫ tauP B j) ((U.ι ≫ b) ≫ tauP B j) hh' =
      Units.map U.ι.appTop.hom.toMonoidHom (D.u _ _ hh) := by
    rw [← D.nat]
    exact u_eq' D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  rw [hc a, hc b, hu] at res
  have e := congrFun res m
  rw [RingHom.map_mulVec, e]
  simp [Pi.smul_apply, smul_eq_mul, map_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.OntoField
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartLift
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) : hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _ using 2
  exact CategoryTheory.Functor.map_id _ _

private theorem appLE_top_top {V X : Scheme.{0}} (a : V ⟶ X) (e : (⊤ : V.Opens) ≤ a ⁻¹ᵁ ⊤) :
    a.appLE ⊤ ⊤ e = a.appTop := by
  change a.app ⊤ ≫ V.presheaf.map (homOfLE e).op = a.app ⊤
  exact (congrArg (a.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)

private theorem exists_hom_of_ring {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U) ⟶ Γ(V, ⊤)) :
    ∃ (y : V ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ U), y.appLE U ⊤ h = f := by
  have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₂ : (⊤ : V.Opens) ≤ (V.toSpecΓ ≫ Spec.map f) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨(V.toSpecΓ ≫ Spec.map f) ≫ hU.fromSpec, ?_, ?_⟩
  · exact e₂.trans (Scheme.Hom.preimage_mono _ e₁)
  · rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂, fromSpec_appLE_top]
    have : (V.toSpecΓ ≫ Spec.map f).appLE ⊤ ⊤ e₂ = (Spec.map f).appTop ≫ (Scheme.ΓSpecIso Γ(V, ⊤)).hom := by
      rw [appLE_top_top, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [this, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private theorem hom_eq_of_appLE {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (a b : V ⟶ X)
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b := by
  have key : ∀ (c : V ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ U), ∃ c' : V ⟶ Spec Γ(X, U), c' ≫ hU.fromSpec = c ∧
      c'.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ c.appLE U ⊤ hc := by
    intro c hc
    have hr : Set.range c ⊆ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact hc (Set.mem_univ x)
    refine ⟨IsOpenImmersion.lift hU.fromSpec c hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have e₂ : (⊤ : V.Opens) ≤ (IsOpenImmersion.lift hU.fromSpec c hr) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have := Scheme.Hom.appLE_comp_appLE (IsOpenImmersion.lift hU.fromSpec c hr) hU.fromSpec U ⊤ ⊤ e₁ e₂
    rw [fromSpec_appLE_top, appLE_top_top] at this
    have h2 : (IsOpenImmersion.lift hU.fromSpec c hr ≫ hU.fromSpec).appLE U ⊤
        (by rw [IsOpenImmersion.lift_fac]; exact hc) = c.appLE U ⊤ hc := by
      simp only [IsOpenImmersion.lift_fac]
    rw [← this.trans h2, Iso.hom_inv_id_assoc]
  obtain ⟨a', ha', ea⟩ := key a ha
  obtain ⟨b', hb', eb⟩ := key b hb
  rw [← ha', ← hb', ext_of_isAffine (f := a') (g := b') (by rw [ea, eb, h])]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartLift :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ (α : B.ι) (k : Fin d) {V : Scheme.{0}} (p : V ⟶ W), ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α → ∀ (w : Fin d → Γ(V, ⊤)), w k = 1 → ∃ (y : V ⟶ T) (h : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.c α).C k), y ≫ r = p ∧ uV B α k (y ≫ j) h = w := by
  intro K _ W Z Y q i π D d B T j r hpb α k V p hp w hk
  have ht : ∀ m, ((p ≫ i).appLE (B.V α) ⊤ hp).hom ((B.c α).t m) = 0 := by
    intro m
    have hm : (B.c α).t m ∈ RingHom.ker (i.app (B.V α)).hom := by
      rw [(B.c α).ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.mem_ker.mp hm, map_zero]
  let ψ := MvPolynomial.eval₂Hom (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).u k)
  let φ : MvPolynomial (Fin d) Γ(Z, B.V α) →+* Γ(V, ⊤) :=
    MvPolynomial.eval₂Hom ((p ≫ i).appLE (B.V α) ⊤ hp).hom w
  have hφC : ∀ a, φ (MvPolynomial.C a) = ((p ≫ i).appLE (B.V α) ⊤ hp).hom a := fun a =>
    MvPolynomial.eval₂_C _ _ _
  have hker : RingHom.ker ψ ≤ RingHom.ker φ := by
    change RingHom.ker (MvPolynomial.eval₂Hom _ _) ≤ _
    rw [(B.c α).rel k, Ideal.span_le]
    rintro x (rfl | ⟨m, rfl⟩)
    · simp [φ, hk]
    · change φ _ = 0
      rw [map_sub, map_mul, hφC, hφC, ht, ht, zero_mul, sub_zero]
  let f : Γ(Y, (B.c α).C k) →+* Γ(V, ⊤) := RingHom.liftOfSurjective ψ ((B.c α).surj k) ⟨φ, hker⟩
  have hf : ∀ x, f (ψ x) = φ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φ, hker⟩ x
  obtain ⟨y₀, h₀, hy₀⟩ := exists_hom_of_ring ((B.c α).C_aff k) (CommRingCat.ofHom f)
  have hπ : ⊤ ≤ (y₀ ≫ π) ⁻¹ᵁ B.V α := h₀.trans (Scheme.Hom.preimage_mono _ ((B.c α).C_le k))
  have hc : y₀ ≫ π = p ≫ i := by
    refine hom_eq_of_appLE (B.c α).affine _ _ hπ hp ?_
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ ((B.c α).C_le k) h₀, hy₀]
    ext a
    have := hf (MvPolynomial.C a)
    simpa [ψ, φ] using this
  have hyj : hpb.lift y₀ p hc ≫ j = y₀ := hpb.lift_fst _ _ _
  refine ⟨hpb.lift y₀ p hc, by rw [hyj]; exact h₀, hpb.lift_snd _ _ _, ?_⟩
  have gen : ∀ (y' : V ⟶ Y) (e : y' = y₀) (h : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), uV B α k y' h = w := by
    intro y' e h
    have hy' : Scheme.Hom.appLE y' _ ⊤ h = CommRingCat.ofHom f := by
      subst e
      exact hy₀
    funext m
    have := hf (MvPolynomial.X m)
    simp only [ψ, φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    unfold uV
    rw [hy']
    exact this
  exact gen _ hyj _
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem exists_basicOpen_of_span {V : Scheme.{0}} {d : ℕ} (v : Fin d → Γ(V, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : V) : ∃ k, x ∈ V.basicOpen (v k) := by
  by_contra hn
  push_neg at hn
  let φ : Γ(V, ⊤) →+* V.presheaf.stalk x := (V.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have := hn k
    rw [Scheme.mem_basicOpen_top] at this
    exact (IsLocalRing.mem_maximalIdeal _).2 this
  rw [h] at hle
  have h1 : (1 : Γ(V, ⊤)) ∈ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := hle trivial
  have h2 : φ 1 ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk x) := h1
  rw [map_one] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 isUnit_one

private theorem isUnit_restrict {V : Scheme.{0}} (s : Γ(V, ⊤)) (U : V.Opens) (hU : U ≤ V.basicOpen s) :
    IsUnit (U.ι.appTop.hom s) := by
  have h0 : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le s)).op).hom s) :=
    RingedSpace.isUnit_res_basicOpen _ _
  have hle : ⊤ ≤ U.ι ⁻¹ᵁ V.basicOpen s := by
    intro z _
    exact hU z.2
  have h1 : U.ι.appTop = V.presheaf.map (homOfLE (V.basicOpen_le s)).op ≫ U.ι.appLE (V.basicOpen s) ⊤ hle := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE U.ι
  rw [h1]
  exact h0.map (U.ι.appLE (V.basicOpen s) ⊤ hle).hom

private theorem uV_congr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
    {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d)
    {V : Scheme.{0}} {f g : V ⟶ Y} (e : f = g) (h : ⊤ ≤ f ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ g ⁻¹ᵁ (B.c α).C k) :
    uV B α k f h = uV B α k g h' := by
  subst e; rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ontoField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a₀ : V ⟶ WP B) (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ TP B j) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧ a ≫ rhoP B j r hsq.w = U.ι ≫ a₀ ∧ a.appTop.hom ∘ v = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a₀ v₀ x
  obtain ⟨U₀, α, a₁, hx₀, ha₁⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a₀ x
  obtain ⟨k, hk⟩ := exists_basicOpen_of_span v₀.1 v₀.2 x
  let U : V.Opens := U₀ ⊓ V.basicOpen (v₀.1 k)
  obtain ⟨e, he⟩ := isUnit_restrict (v₀.1 k) U inf_le_right
  let a₂ : (U : Scheme.{0}) ⟶ (oW B α : Scheme.{0}) := V.homOfLE (inf_le_left : U ≤ U₀) ≫ a₁
  let p : (U : Scheme.{0}) ⟶ W := a₂ ≫ (oW B α).ι
  have hp : ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α := by
    intro z _
    have hz : (a₂ z).1 ∈ oW B α := (a₂ z).2
    exact hz
  let w : Fin d → Γ((U : Scheme.{0}), ⊤) := fun m => (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 m)
  have hwk : w k = 1 := by
    change (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 k) = 1
    rw [← he]; exact e.inv_mul
  obtain ⟨y, hy, hyr, huv⟩ := chartLift B j r hsq α k p hp w hwk
  have hrange : Set.range y ⊆ Set.range (oT B j (α, k)).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : (y ≫ j) z ∈ (B.c α).C k := hy (Set.mem_univ z)
    rw [Scheme.Hom.comp_apply] at hz
    exact hz
  let y₁ : (U : Scheme.{0}) ⟶ (oT B j (α, k) : Scheme.{0}) := IsOpenImmersion.lift (oT B j (α, k)).ι y hrange
  have hy₁ : y₁ ≫ (oT B j (α, k)).ι = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨h', hv', -, hrho⟩ := pieceFacts B j r hsq.w v hv (α, k) y₁
  have hpath : (y₁ ≫ tI B j (α, k)) ≫ eP B j ≫ j = y ≫ j := by
    have : tI B j (α, k) ≫ eP B j = (oT B j (α, k)).ι := by
      simp [tI, eP]
    rw [← hy₁, Category.assoc, reassoc_of% this, Category.assoc]
  have hmap : y₁ ≫ rhoC B j r hsq.w (α, k) = a₂ := by
    rw [← cancel_mono (oW B α).ι]
    have : rhoC B j r hsq.w (α, k) ≫ (oW B α).ι = (oT B j (α, k)).ι ≫ r := IsOpenImmersion.lift_fac _ _ _
    rw [Category.assoc, this, reassoc_of% hy₁, hyr]
  refine ⟨U, y₁ ≫ tI B j (α, k), e⁻¹, ⟨hx₀, hk⟩, ?_, ?_⟩
  · rw [hrho, hmap]
    have hι : U.ι ≫ a₀ = V.homOfLE (inf_le_left : U ≤ U₀) ≫ U₀.ι ≫ a₀ := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hι, ha₁]
    simp only [a₂, Category.assoc]
    rfl
  · rw [hv', uV_congr B α k hpath h' hy, huv]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.InjField
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.RatioInj
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartInj
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appLE_univ_congr_of_eq {V Z : Scheme.{0}} {f g : V ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ g ⁻¹ᵁ U) : f.appLE U ⊤ e = g.appLE U ⊤ e' := by
  subst hfg; rfl

private lemma appLE_lift_eq {Y V : Scheme.{0}} (C : Y.Opens) (l : V ⟶ (C : Scheme.{0}))
    (h : ⊤ ≤ (l ≫ C.ι) ⁻¹ᵁ C) : (l ≫ C.ι).appLE C ⊤ h = C.topIso.inv ≫ l.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE l C.ι C ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  simp
  congr 1

private lemma eq_of_appLE_eq {Y V : Scheme.{0}} (C : Y.Opens) (hC : IsAffineOpen C) (y y' : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (h' : ⊤ ≤ y' ⁻¹ᵁ C) (e : y.appLE C ⊤ h = y'.appLE C ⊤ h') : y = y' := by
  have r : ∀ z : V ⟶ Y, ⊤ ≤ z ⁻¹ᵁ C → Set.range z ⊆ Set.range C.ι := by
    rintro z hz _ ⟨x, rfl⟩
    simpa using hz (Set.mem_univ x)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ C.ι = y := ⟨_, IsOpenImmersion.lift_fac C.ι y (r y h)⟩
  obtain ⟨l', rfl⟩ : ∃ l, l ≫ C.ι = y' := ⟨_, IsOpenImmersion.lift_fac C.ι y' (r y' h')⟩
  haveI : IsAffine (C : Scheme.{0}) := hC
  rw [appLE_lift_eq, appLE_lift_eq] at e
  have e2 : l.appTop = l'.appTop := (cancel_epi C.topIso.inv).mp e
  rw [ext_of_isAffine e2]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), y ≫ π = y' ≫ π → uV B α k y h = uV B α k y' h' → y = y' := by
  intro K _ W Z Y q i π D d B α k V y y' h h' hπ hu
  have hle := (B.c α).C_le k
  refine eq_of_appLE_eq _ ((B.c α).C_aff k) y y' h h' ?_
  have hpi : ∀ r : Γ(Z, B.V α), (y.appLE _ ⊤ h).hom ((π.appLE (B.V α) _ hle).hom r) =
      (y'.appLE _ ⊤ h').hom ((π.appLE (B.V α) _ hle).hom r) := by
    intro r
    have e1 := Scheme.Hom.appLE_comp_appLE y π (B.V α) ((B.c α).C k) ⊤ hle h
    have e2 := Scheme.Hom.appLE_comp_appLE y' π (B.V α) ((B.c α).C k) ⊤ hle h'
    have e3 := e1.trans ((appLE_univ_congr_of_eq hπ (B.V α) _ _).trans e2.symm)
    exact congrArg (fun t => t.hom r) e3
  have hP := MvPolynomial.ringHom_ext
    (f := (y.appLE _ ⊤ h).hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (g := (y'.appLE _ ⊤ h').hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (fun r => by simpa using hpi r)
    (fun m => by simpa [uV] using congrFun hu m)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  obtain ⟨P, rfl⟩ := (B.c α).surj k s
  exact congrArg (fun t => t P) hP
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem mem_of_unit {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (hu : IsUnit (uV B β m y h l)) : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := by
  have h1 : V.basicOpen (uV B β m y h l) = ⊤ := Scheme.basicOpen_of_isUnit V hu
  have h2 : V.basicOpen (uV B β m y h l) ≤ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := by
    unfold uV
    rw [Scheme.Hom.appLE]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    exact inf_le_right
  intro x hx
  have h3 : x ∈ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := h2 (h1.ge hx)
  have h4 : y x ∈ Y.basicOpen ((B.c β).u m l) := h3
  rw [← (B.c β).inter m l] at h4
  exact h4.2

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ratioInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (p : V ⟶ W) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c β).C l) (s : (Γ(V, ⊤))ˣ), y ≫ π = p ≫ i → y' ≫ π = p ≫ i → uV B β m y h = (s : Γ(V, ⊤)) • uV B β l y' h' → y = y' := by
  intro K _ W Z Y q i π D d B β m l V y y' p h h' s hy hy' e
  have hl : uV B β m y h l = (s : Γ(V, ⊤)) := by
    have := congrFun e l
    simpa [uSelf B β l y' h'] using this
  have h'' : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := mem_of_unit B β m l y h (hl ▸ s.isUnit)
  have hV : ∀ x : V, (p ≫ i) x ∈ B.V β := by
    intro x
    rw [← hy, Scheme.Hom.comp_apply]
    exact (B.c β).C_le m (h (Set.mem_univ x))
  have hg := gvChart B y p hy β β m l h h'' 1 (locMatOne B β p hV)
  rw [Matrix.one_mulVec] at hg
  obtain ⟨c, hc⟩ : ∃ c : (Γ(V, ⊤))ˣ, uV B β m y h = (c : Γ(V, ⊤)) • uV B β l y h'' := ⟨_, hg⟩
  have hcs : (c : Γ(V, ⊤)) = s := by
    have := congrFun hc l
    rw [hl, Pi.smul_apply, uSelf B β l y h'', smul_eq_mul, mul_one] at this
    exact this.symm
  have hvv : uV B β l y h'' = uV B β l y' h' := by
    funext j
    have h1 := congrFun hc j
    have h2 := congrFun e j
    rw [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [hcs] at h1
    exact s.isUnit.mul_left_cancel (h1.symm.trans h2)
  exact chartInj B β l y y' h'' h' (hy.trans hy'.symm) hvv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.HomExt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.homExt :
    ∀ {V X : Scheme.{0}} (a b : V ⟶ X), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι ≫ a = U.ι ≫ b) → a = b := by
  intro V X a b h
  choose W hxW hW using h
  have hcov : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  exact (V.openCoverOfIsOpenCover W hcov).hom_ext _ _ hW
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem injKey {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}} (p p' : B.ι × Fin d)
    (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hp : ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B = ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) ≫ cP B)
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ((b₁ ≫ tI B j p') ≫ rhoP B j r hw) M)
    (u : (Γ(V, ⊤))ˣ)
    (hyp : M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) = (u : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v))
    (m : Fin d) (hm : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m) :
    (a₁ ≫ tI B j p) ≫ eP B j ≫ j = (b₁ ≫ tI B j p') ≫ eP B j ≫ j := by
  obtain ⟨h₁, e₁, -, r₁⟩ := pieceFacts B j r hw v hv p a₁
  obtain ⟨h₂, e₂, -, r₂⟩ := pieceFacts B j r hw v hv p' b₁
  have hL := gMatLoc B _ _ M p.1 p'.1 _ _ r₁ r₂ hG
  have hc := (coverComm B j r hw).1
  have hy : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [Category.assoc (a₁ ≫ tI B j p) (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hy' : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hw) ≫ cP B) ≫ i := by
    rw [hp, Category.assoc (b₁ ≫ tI B j p') (rhoP B j r hw) (cP B), hc]
    simp only [Category.assoc, hw]
  have hg := gvChart B _ _ hy p.1 p'.1 p.2 m h₁ hm M hL
  rw [e₁, e₂, hg] at hyp
  refine ratioInj B p'.1 m p'.2 _ _ _ hm h₂ ((D.u _ _ ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 m _ hm).symm)) * u) hy hy' ?_
  rw [Units.val_mul, mul_smul, ← hyp, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.injField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (a ≫ rhoP B j r hsq.w) ≫ cP B = (b ≫ rhoP B j r hsq.w) ≫ cP B → GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → ∀ u : (Γ(V, ⊤))ˣ, M.mulVec (a.appTop.hom ∘ v) = (u : Γ(V, ⊤)) • (b.appTop.hom ∘ v) → a ≫ eP B j = b ≫ eP B j := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b M hp hG u hyp
  have hc := (coverComm B j r hsq.w).1
  have hrr : a ≫ eP B j ≫ r = b ≫ eP B j ≫ r := by
    have h := hp
    simp only [Category.assoc] at h
    rwa [hc] at h
  have hππ : (a ≫ eP B j ≫ j) ≫ π = (b ≫ eP B j ≫ j) ≫ π := by
    simp only [Category.assoc, hsq.w]
    simp only [← Category.assoc] at hrr ⊢
    rw [hrr]
  refine hsq.hom_ext ?_ (by simpa only [Category.assoc] using hrr)
  refine homExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x

  have hbx : (b ≫ eP B j ≫ j) x ∈ (B.c p'.1).C p'.2 := by
    obtain ⟨h₂, -, -, -⟩ := pieceFacts B j r hsq.w v hv p' b₁
    have h3 : ((b₁ ≫ tI B j p') ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) ∈ (B.c p'.1).C p'.2 := h₂ (Set.mem_univ _)
    have h4 : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [h4] at h3
    have h6 : ((U₂.ι ≫ b) ≫ eP B j ≫ j) (⟨x, hx₂⟩ : U₂) = (b ≫ eP B j ≫ j) x := by
      rw [Category.assoc, Scheme.Hom.comp_apply]
      rfl
    rwa [h6] at h3
  have hπx : π ((a ≫ eP B j ≫ j) x) ∈ B.V p'.1 := by
    have h5 : π ((a ≫ eP B j ≫ j) x) = π ((b ≫ eP B j ≫ j) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hππ]
    rw [h5]
    exact (B.c p'.1).C_le p'.2 hbx
  obtain ⟨m, hmx⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c p'.1).C_cover hπx)
  let U₃ : V.Opens := (a ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C m
  let U : V.Opens := U₁ ⊓ U₂ ⊓ U₃
  have hxU : x ∈ U := ⟨⟨hx₁, hx₂⟩, hmx⟩
  have l₁ : U ≤ U₁ := inf_le_left.trans inf_le_left
  have l₂ : U ≤ U₂ := inf_le_left.trans inf_le_right
  have l₃ : U ≤ U₃ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE l₁ ≫ a₁) ≫ tI B j p := by
    have h : a₁ ≫ tI B j p = U₁.ι ≫ a := ha.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  have eb : U.ι ≫ b = (V.homOfLE l₂ ≫ b₁) ≫ tI B j p' := by
    have h : b₁ ≫ tI B j p' = U₂.ι ≫ b := hb.symm
    rw [Category.assoc, h, Scheme.homOfLE_ι_assoc]
  refine ⟨U, hxU, ?_⟩
  have hk := injKey B j r hsq.w v hv p p' (V.homOfLE l₁ ≫ a₁) (V.homOfLE l₂ ≫ b₁) (M.map U.ι.appTop.hom)
    (by rw [← ea, ← eb]; simp only [Category.assoc]; simp only [Category.assoc] at hp; rw [hp])
    (by
      rw [← ea, ← eb]
      have h := gMatNat B U.ι _ _ M hG
      simpa only [Category.assoc] using h)
    (Units.map (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)).toMonoidHom u)
    (by
      rw [← ea, ← eb]
      have hca : ∀ (c : V ⟶ TP B j), (U.ι ≫ c).appTop.hom ∘ v = U.ι.appTop.hom ∘ (c.appTop.hom ∘ v) := by
        intro c
        funext n
        rw [Scheme.Hom.comp_appTop]
        rfl
      rw [hca a, hca b]
      funext n
      have h2 := congrArg (U.ι.appTop.hom : Γ(V, ⊤) →+* Γ((U : Scheme.{0}), ⊤)) (congrFun hyp n)
      rw [RingHom.map_mulVec] at h2
      refine h2.trans ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_apply]
      rfl)
    m
    (by
      rw [← ea, Category.assoc U.ι a]
      intro z _
      exact l₃ z.2)
  rw [← ea, ← eb] at hk
  simpa only [Category.assoc] using hk
end
