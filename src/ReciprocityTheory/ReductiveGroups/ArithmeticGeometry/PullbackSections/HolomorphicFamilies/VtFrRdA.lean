module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdHol
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem vtf_closure_eq_top {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (h : IsPushout f g inl inr) :
    Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) = ⊤ := by
  set R := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom) with hR
  let l : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inl.hom.codRestrict R fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let r : C ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (inr.hom.codRestrict R fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ l = g ≫ r := by
    ext a
    have := congrArg (fun q : A ⟶ P => q.hom a) h.w
    simpa [l, r] using this
  let i : CommRingCat.of R ⟶ P := CommRingCat.ofHom R.subtype
  have hid : h.desc l r w ≫ i = 𝟙 P := by
    apply h.hom_ext
    · ext b
      simp [l, i]
    · ext c
      simp [r, i]
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (((h.desc l r w).hom x : R) : P) = x := by
    have := congrArg (fun q : P ⟶ P => q.hom x) hid
    simpa [i] using this
  rw [← hx]
  exact ((h.desc l r w).hom x).2

theorem vtf_pt_eq (q : Sp ℂ) : q = cpt := by
  have : Subsingleton (PrimeSpectrum ℂ) := inferInstance
  exact this.elim q cpt

theorem vtf_mem {Z : Scheme.{0}} {x : Sp ℂ ⟶ Z} {U : Z.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : x cpt ∈ U :=
  h trivial

theorem vtf_range {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Set.range x ⊆ Set.range U.ι := by
  rintro _ ⟨q, rfl⟩
  rw [Scheme.Opens.range_ι, vtf_pt_eq q]
  exact vtf_mem h

theorem vtf_top {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) : ⊤ ≤ x ⁻¹ᵁ (⊤ : Z.Opens) := le_top

section Fibre

variable {g : ℕ} {X Y : Scheme.{0}} (f : Y ⟶ X) (u : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
  (he : ∀ z, e z ≫ f = u)

def vtfLift (z : Fin g → ℂ) : Sp ℂ ⟶ pullback f u :=
  pullback.lift (e z) (𝟙 _) (by rw [he z, Category.id_comp])

set_option maxHeartbeats 800000 in
theorem vtf_local (hol : IsHolFam e) (V : (pullback f u).Opens) (φ : Γ(pullback f u, V))
    (z0 : Fin g → ℂ) (hz0 : ⊤ ≤ vtfLift f u e he z0 ⁻¹ᵁ V) :
    ∃ N : Set (Fin g → ℂ), IsOpen N ∧ z0 ∈ N ∧ (∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V) ∧
      DifferentiableOn ℂ (fun z => valAt' (vtfLift f u e he z) V φ) N := by
  classical
  obtain ⟨W, hW, huW, -⟩ := exists_isAffineOpen_mem_and_subset (x := u cpt) (U := ⊤) trivial
  have hfy : e z0 cpt ∈ f ⁻¹ᵁ W := by
    show f (e z0 cpt) ∈ W
    rw [← Scheme.Hom.comp_apply, he]
    exact huW
  obtain ⟨U, hU, hyU, hUW⟩ := exists_isAffineOpen_mem_and_subset hfy
  have : IsAffine U := hU
  have : IsAffine W := hW
  have hUr : Set.range (U.ι ≫ f) ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hUW y.2
  let fU : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U.ι ≫ f) hUr
  let uW : Sp ℂ ⟶ W.toScheme := IsOpenImmersion.lift W.ι u (vtf_range u W (top_le_of_mem huW))
  have hSU : IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} := (hol U 0).1
  have h0U : ⊤ ≤ e z0 ⁻¹ᵁ U := top_le_of_mem hyU
  let eU : (Fin g → ℂ) → (Sp ℂ ⟶ U.toScheme) := fun z =>
    if h : ⊤ ≤ e z ⁻¹ᵁ U then IsOpenImmersion.lift U.ι (e z) (vtf_range (e z) U h)
    else IsOpenImmersion.lift U.ι (e z0) (vtf_range (e z0) U h0U)
  have heU : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → eU z ≫ U.ι = e z := fun z h => by
    simp only [eU, dif_pos h, IsOpenImmersion.lift_fac]
  have heU' : ∀ z, eU z ≫ fU = uW := fun z => by
    rw [← cancel_mono W.ι]
    simp only [fU, uW, Category.assoc, IsOpenImmersion.lift_fac]
    by_cases h : ⊤ ≤ e z ⁻¹ᵁ U
    · rw [← Category.assoc, heU z h, he]
    · simp only [eU, dif_neg h, IsOpenImmersion.lift_fac_assoc, he]
  have hpb : IsPullback (pullback.fst fU uW) (pullback.snd fU uW) fU uW := IsPullback.of_hasPullback fU uW
  have hgen := vtf_closure_eq_top (isPushout_appTop_of_isPullback hpb)
  have hw' : (pullback.fst fU uW ≫ U.ι) ≫ f = pullback.snd fU uW ≫ u := by
    rw [Category.assoc, ← IsOpenImmersion.lift_fac W.ι (U.ι ≫ f) hUr, ← Category.assoc, pullback.condition,
      Category.assoc, IsOpenImmersion.lift_fac]
  let ι' : pullback fU uW ⟶ pullback f u := pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw'
  let pP : (Fin g → ℂ) → (Sp ℂ ⟶ pullback fU uW) := fun z =>
    pullback.lift (eU z) (𝟙 _) (by rw [heU' z, Category.id_comp])
  have hpP : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U → pP z ≫ ι' = vtfLift f u e he z := fun z h => by
    apply pullback.hom_ext
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.fst f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.fst f u
      rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, heU z h]
    · change pullback.lift (eU z) (𝟙 _) _ ≫ pullback.lift (pullback.fst fU uW ≫ U.ι) (pullback.snd fU uW) hw' ≫
        pullback.snd f u = pullback.lift (e z) (𝟙 _) _ ≫ pullback.snd f u
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have hUimg : U ≤ U.ι ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hfst : ∀ b : Γ(U.toScheme, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom b)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro b
    obtain ⟨b', rfl⟩ : ∃ b', (U.ι.appIso ⊤).hom.hom b' = b :=
      ⟨(U.ι.appIso ⊤).inv.hom b, by exact congrArg (fun q => q.hom b) (U.ι.appIso ⊤).inv_hom_id⟩
    have key : ∀ z, ⊤ ≤ e z ⁻¹ᵁ U →
        valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (e z) (U.ι ''ᵁ ⊤) b' := by
      intro z hz
      have e1 : valAt' (pP z) ⊤ ((pullback.fst fU uW).appTop.hom ((U.ι.appIso ⊤).hom.hom b')) =
          valAt' (pP z ≫ pullback.fst fU uW) ⊤ ((U.ι.appIso ⊤).hom.hom b') := by
        exact valAt'_comp (pP z) (pullback.fst fU uW) ⊤ _
      have e2 : pP z ≫ pullback.fst fU uW = eU z := pullback.lift_fst _ _ _
      rw [e1, e2, Scheme.Hom.appIso_hom', Scheme.Hom.appLE, CommRingCat.comp_apply,
        valAt'_res _ _ (vtf_top _), valAt'_comp, heU z hz]
    refine ((hol _ b').2.mono fun z hz => ?_).congr fun z hz => key z hz
    exact top_le_of_mem (hUimg (vtf_mem hz))
  have hsnd : ∀ c : Γ(Sp ℂ, ⊤), DifferentiableOn ℂ
      (fun z => valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c)) {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro c
    refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ c)).congr fun z _ => ?_
    have e1 : valAt' (pP z) ⊤ ((pullback.snd fU uW).appTop.hom c) =
        valAt' (pP z ≫ pullback.snd fU uW) ⊤ c := by
      exact valAt'_comp (pP z) (pullback.snd fU uW) ⊤ _
    have e2 : pP z ≫ pullback.snd fU uW = 𝟙 _ := pullback.lift_snd _ _ _
    rw [e1, e2]
  have hv : ∀ (x : Sp ℂ ⟶ pullback fU uW) (a : Γ(pullback fU uW, ⊤)),
      valHom x ⊤ (vtf_top x) a = valAt' x ⊤ a := fun _ _ => rfl
  have hall : ∀ a : Γ(pullback fU uW, ⊤), DifferentiableOn ℂ (fun z => valAt' (pP z) ⊤ a)
      {z | ⊤ ≤ e z ⁻¹ᵁ U} := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (pullback.fst fU uW).appTop.hom ∪
        Set.range (pullback.snd fU uW).appTop.hom) := by
      rw [hgen]; exact Subring.mem_top a
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact hfst b
      · exact hsnd c
    | zero => exact (differentiableOn_const 0).congr fun z _ => (hv _ _).symm.trans (map_zero _)
    | one => exact (differentiableOn_const 1).congr fun z _ => (hv _ _).symm.trans (map_one _)
    | add x y _ _ hx hy =>
      exact (hx.add hy).congr fun z _ => (hv _ _).symm.trans (map_add _ _ _)
    | neg x _ hx => exact hx.neg.congr fun z _ => (hv _ _).symm.trans (map_neg _ _)
    | mul x y _ _ hx hy =>
      exact (hx.mul hy).congr fun z _ => (hv _ _).symm.trans (map_mul _ _ _)
  have hz0' : pP z0 cpt ∈ ι' ⁻¹ᵁ V := by
    show ι' (pP z0 cpt) ∈ V
    rw [← Scheme.Hom.comp_apply, hpP z0 h0U]
    exact vtf_mem hz0
  obtain ⟨h, hle, hmem⟩ := (isAffineOpen_top (pullback fU uW)).exists_basicOpen_le ⟨pP z0 cpt, hz0'⟩ trivial
  haveI := (isAffineOpen_top (pullback fU uW)).isLocalization_basicOpen h
  let ψ : Γ(pullback fU uW, (pullback fU uW).basicOpen h) :=
    ((pullback fU uW).presheaf.map (homOfLE hle).op).hom ((ι'.app V).hom φ)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) ψ
  dsimp only at hs
  obtain ⟨n, hn⟩ := s.2
  have hpow : ∀ z, valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ h ^ n := fun z =>
    (hv _ _).symm.trans ((map_pow _ _ _).trans (congrArg (· ^ n) (hv _ _)))
  have hal : ∀ q : Γ(pullback fU uW, ⊤), algebraMap Γ(pullback fU uW, ⊤)
      Γ(pullback fU uW, (pullback fU uW).basicOpen h) q =
      ((pullback fU uW).presheaf.map (homOfLE ((pullback fU uW).basicOpen_le h)).op).hom q := fun _ => rfl
  let N : Set (Fin g → ℂ) := {z | ⊤ ≤ e z ⁻¹ᵁ U} ∩ (fun z => valAt' (pP z) ⊤ h) ⁻¹' {0}ᶜ
  have hN : IsOpen N := (hall h).continuousOn.isOpen_inter_preimage hSU isOpen_compl_singleton
  have hD : ∀ z ∈ N, ⊤ ≤ pP z ⁻¹ᵁ (pullback fU uW).basicOpen h := fun z hz =>
    top_le_of_mem ((valAt'_ne_zero_iff (pP z) ⊤ (vtf_top _) h cpt).1 hz.2)
  have hVz : ∀ z ∈ N, ⊤ ≤ vtfLift f u e he z ⁻¹ᵁ V := fun z hz => by
    apply top_le_of_mem
    rw [← hpP z hz.1, Scheme.Hom.comp_apply]
    exact hle (vtf_mem (hD z hz))
  have hval : ∀ z ∈ N, valAt' (vtfLift f u e he z) V φ =
      valAt' (pP z) ⊤ a * (valAt' (pP z) ⊤ (h ^ n))⁻¹ := by
    intro z hz
    have hne : valAt' (pP z) ⊤ h ≠ 0 := hz.2
    have e1 : valAt' (vtfLift f u e he z) V φ = valAt' (pP z) _ ψ := by
      rw [← hpP z hz.1, ← valAt'_comp]
      exact (valAt'_res _ hle (hD z hz) _).symm
    have e3 : valAt' (pP z) _ ψ * valAt' (pP z) ⊤ (h ^ n) = valAt' (pP z) ⊤ a := by
      have e2 := congrArg (valHom (pP z) _ (hD z hz)) hs
      rw [map_mul] at e2
      have ra : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ a) = valAt' (pP z) ⊤ a := by
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) a
      have rs : valHom (pP z) _ (hD z hz) (algebraMap Γ(pullback fU uW, ⊤) _ (s : Γ(pullback fU uW, ⊤))) =
          valAt' (pP z) ⊤ (h ^ n) := by
        rw [← hn]
        exact valAt'_res (pP z) ((pullback fU uW).basicOpen_le h) (hD z hz) _
      rw [ra, rs] at e2
      exact e2
    rw [e1, eq_mul_inv_iff_mul_eq₀ (by rw [hpow]; exact pow_ne_zero _ hne), e3]
  refine ⟨N, hN, ⟨h0U, ?_⟩, hVz, ?_⟩
  · exact (valAt'_ne_zero_iff (pP z0) ⊤ (vtf_top _) h cpt).2 hmem
  · refine (((hall a).mono Set.inter_subset_left).mul (((hall (h ^ n)).mono Set.inter_subset_left).inv
      fun z hz => ?_)).congr fun z hz => hval z hz
    rw [hpow]
    exact pow_ne_zero _ hz.2

theorem isHolFam_vtfLift (hol : IsHolFam e) : IsHolFam (vtfLift f u e he) := by
  intro V φ
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro z0 hz0
    obtain ⟨N, hN, hzN, hNS, -⟩ := vtf_local f u e he hol V φ z0 hz0
    exact Filter.mem_of_superset (hN.mem_nhds hzN) hNS
  · intro z0 hz0
    obtain ⟨N, hN, hzN, -, hd⟩ := vtf_local f u e he hol V φ z0 hz0
    exact ((hd z0 hzN).differentiableAt (hN.mem_nhds hzN)).differentiableWithinAt

end Fibre

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {Z Z' : Scheme.{0}}

private lemma ringHom_units_zpow_lemma {R S : Type*} [CommRing R] [Field S] (f : R →+* S) (u : Rˣ) (k : ℤ) :
    f ↑(u ^ k) = (f ↑u) ^ k := by
  have hk : ((Units.map (f : R →* S) (u ^ k) : Sˣ) : S) = ((Units.map (f : R →* S) u ^ k : Sˣ) : S) := by
    rw [map_zpow]
  rw [Units.val_zpow_eq_zpow_val] at hk
  exact hk

theorem vtf_valU (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) (k : ℤ) :
    valAt' p V ((u ^ k : Γ(Z, V)ˣ) : Γ(Z, V)) = valAt' p V (u : Γ(Z, V)) ^ k := by
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h]
  delta valAt
  exact ringHom_units_zpow_lemma ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (p.appLE V ⊤ h).hom) u k

theorem vtf_val_res (p : Sp ℂ ⟶ Z) {U V : Z.Opens} (hVU : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, U)ˣ) :
    valAt' p V (res hVU u : Γ(Z, V)) = valAt' p U (u : Γ(Z, U)) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ U := h.trans (fun x hx => hVU hx)
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h']
  delta valAt res
  congr 1
  first
  | (rw [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE])
  | simp [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem vtf_val_pullU (p : Sp ℂ ⟶ Z) (f : Z ⟶ Z') (U : Z'.Opens) (u : Γ(Z', U)ˣ) :
    valAt' p (f ⁻¹ᵁ U) (pullU f U u : Γ(Z, f ⁻¹ᵁ U)) = valAt' (p ≫ f) U (u : Γ(Z', U)) := by
  by_cases hc : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have hc' : ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun x hx => hc hx
    rw [valAt', valAt', dite_eq_left hc, dite_eq_left hc']
    delta valAt pullU
    congr 1
  · have hc' : ¬ ⊤ ≤ (p ≫ f) ⁻¹ᵁ U := fun h' => hc (fun x hx => h' hx)
    rw [valAt', valAt', dite_eq_right hc, dite_eq_right hc']

end Units

section Rd

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}

abbrev vtfQ (a : Over.mk x0 ⟶ A) : Over.mk x0 ⟶ Over.mk x0 ⊗ A := lift (𝟙 _) a

theorem vtfQ_snd (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (snd (Over.mk x0) A).left = a.left := by
  show (lift (𝟙 _) a ≫ snd (Over.mk x0) A).left = a.left
  rw [lift_snd]

theorem vtfQ_fst (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (fst (Over.mk x0) A).left = 𝟙 _ := by
  show (lift (𝟙 _) a ≫ fst (Over.mk x0) A).left = 𝟙 _
  rw [lift_fst]
  rfl

theorem vtf_pt_uniq (a : Over.mk x0 ⟶ A) (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)
    (h1 : pt ≫ (snd (Over.mk x0) A).left = a.left) (h2 : pt ≫ (fst (Over.mk x0) A).left = 𝟙 _) :
    pt = (vtfQ A a).left := by
  have hw : pt ≫ (Over.mk x0 ⊗ A).hom = x0 := by
    rw [← Over.w (fst (Over.mk x0) A), ← Category.assoc, h2, Category.id_comp]
    rfl
  let q : Over.mk x0 ⟶ Over.mk x0 ⊗ A := Over.homMk pt hw
  have hq : q = vtfQ A a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [vtfQ, lift_fst]
      ext
      exact h2
    · simp only [vtfQ, lift_snd]
      ext
      exact h1
  exact congrArg CommaMorphism.left hq

theorem vtf_chart (k : ℤ) (a : Over.mk x0 ⟶ A) (i : Fin 1 → L.ι) (h : ⊤ ≤ a.left ⁻¹ᵁ L.U (i 0)) :
    ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ (LPow A L k (Over.mk x0)).U i := by
  intro x _
  have hx : a.left.base x ∈ L.U (i 0) := h (by trivial)
  have hx' : (snd (Over.mk x0) A).left.base ((vtfQ A a).left.base x) ∈ L.U (i 0) := by
    have e : ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x = a.left.base x := by
      rw [vtfQ_snd]
    change ((vtfQ A a).left ≫ (snd (Over.mk x0) A).left).base x ∈ L.U (i 0)
    rw [e]
    exact hx
  refine Set.mem_iInter.mpr fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact hx'

theorem vtf_val_g {k : ℤ} (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (i i' : Fin 1 → L.ι)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U i ⊓ (LPow A L k (Over.mk x0)).U i')) :
    valAt' p _ ((LPow A L k (Over.mk x0)).g i i').val =
      valAt' (p ≫ (snd (Over.mk x0) A).left) (L.U (i 0) ⊓ L.U (i' 0)) (L.g (i 0) (i' 0)).val ^ k := by
  delta LPow LB.LinComb at h ⊢
  dsimp only at h ⊢
  rw [Fin.prod_univ_one, vtf_valU p h]
  congr 1
  exact (vtf_val_res p _ h _).trans (vtf_val_pullU p (snd (Over.mk x0) A).left _ (L.g (i 0) (i' 0)))

theorem vtf_read {k : ℤ} (F : LB.Sec (LPow A L k (Over.mk x0))) (a : Over.mk x0 ⟶ A) (fr : L.ι → ℂ)
    (hfr : ∀ j j', ⊤ ≤ a.left ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j = valAt' a.left _ (L.g j j' : Γ(A.left, L.U j ⊓ L.U j')) * fr j')
    (j j' : L.ι) (hj : ⊤ ≤ a.left ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ a.left ⁻¹ᵁ L.U j') (θ : ℂ)
    (h : valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ * fr j ^ k) :
    valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j')) (F.f (fun _ => j')) = θ * fr j' ^ k := by
  have hjj : ⊤ ≤ a.left ⁻¹ᵁ (L.U j' ⊓ L.U j) := fun q hq => ⟨hj' hq, hj hq⟩
  have hp : ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U (fun _ => j') ⊓
      (LPow A L k (Over.mk x0)).U (fun _ => j)) :=
    fun q hq => ⟨vtf_chart A L k a _ hj' hq, vtf_chart A L k a _ hj hq⟩
  have e := congrArg (valAt' (vtfQ A a).left _) (F.compat (fun _ => j') (fun _ => j))
  rw [valAt'_mul] at e
  have e1 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_left :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j'))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j')) := by
    exact valAt'_res _ _ hp _
  have e2 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_right :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j)) := by
    exact valAt'_res _ _ hp _
  rw [e1, e2, vtf_val_g A L _ _ _ hp, vtfQ_snd, h] at e
  rw [e, hfr j' j hjj, mul_zpow]
  ring

theorem vtf_twist {a b : ℤ} {ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A} {m : Over.mk x0 ⊗ A ⟶ A}
    {hm : ψ ≫ snd (Over.mk x0) A = m}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b (Over.mk x0))} {s' : LB.Sec (LPow A L a (Over.mk x0))}
    (h : IsTwistPull A L ψ m hm a b α s s') (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (j : Fin 2 → L.ι)
    (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) :
    valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0)) =
      valAt' p _ (α.s j).val *
        valAt' (p ≫ ψ.left) ((LPow A L b (Over.mk x0)).U (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  calc valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0))
      = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom
            (s'.f (fun _ => j 0))) := by
        exact (valAt'_res p (chart_le_zero A L m j) hp _).symm
    _ = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          ((show Γ((Over.mk x0 ⊗ A).left, LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) from (α.s j).val) *
            ((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
              ((ψ.left.app _).hom (s.f (fun _ => j 1)))) := by rw [h j]
    _ = _ := by
        rw [valAt'_mul]
        refine congrArg₂ (· * ·) rfl ?_
        calc _ = valAt' p (ψ.left ⁻¹ᵁ (LPow A L b (Over.mk x0)).U (fun _ => j 1))
              ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
              exact valAt'_res p (chart_le_pull A L ψ m hm j) hp _
          _ = _ := by exact valAt'_comp p ψ.left _ _

end Rd

end ReciprocityTheory.ChartRestriction.G.PullbackSections
