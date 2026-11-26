module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibres
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOut

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem triv_of_invariant_gen : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  intro P Q f hfl hlf hsu D hD t ht hinv
  have hle : ∀ i : D.ι, f ⁻¹ᵁ D.U i ≤ (D.pull f).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  have hex : ∀ i : D.ι, ∃ s : Γ(Q, D.U i)ˣ, pullU f (D.U i) s = res (hle i) (t.s fun _ => i) := by
    intro i
    refine (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i)).2 _ ?_
    intro W b c hbc w hw
    have hw' : f (c w) ∈ D.U i := by
      have : f (b w) = f (c w) := by
        have := congrArg (fun q : W ⟶ Q => q w) hbc
        simpa using this
      exact this ▸ hw
    rw [gm_res b w (hle i) hw, gm_res c w (hle i) hw']
    exact hinv W b c hbc w i hw
  choose s hs using hex
  have key : ∀ (i : D.ι) (x : P) (hx : f x ∈ D.U i),
      gm (𝟙 P ≫ f) x (D.U i) (s i) = gm (𝟙 P) x ((D.pull f).U fun _ => i) (t.s fun _ => i) := by
    intro i x hx
    rw [← gm_pull (𝟙 P) f x (D.U i) hx, hs i]
    exact gm_res (𝟙 P) x (hle i) hx _
  refine ⟨⟨s⟩, fun i j => ?_⟩
  apply (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i ⊓ D.U j)).1
  apply unit_ext
  intro x hx
  have hi : f x ∈ D.U i := hx.1
  have hj : f x ∈ D.U j := hx.2
  have hij : f x ∈ D.U i ⊓ D.U j := hx
  have hm : x ∈ (D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have e := congrArg (gm (𝟙 P) x _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res (𝟙 P) x _ hm, gm_res (𝟙 P) x _ hm] at e
  have eg : gm (𝟙 P) x ((D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j)) ((D.pull f).g (fun _ => i) (fun _ => j)) =
      gm (𝟙 P ≫ f) x _ (D.g i j) := by
    show gm (𝟙 P) x _ (∏ _k : PUnit, (res _ (pullU f _ (D.g i j))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 P) x _ hm _).trans (gm_pull (𝟙 P) f x (D.U i ⊓ D.U j) hij _)
  rw [eg, ← key i x hi, ← key j x hj] at e
  rw [gm_pull (𝟙 P) f x _ hij, gm_pull (𝟙 P) f x _ hij, map_mul,
    gm_res (𝟙 P ≫ f) x _ hij, gm_res (𝟙 P ≫ f) x _ hij]
  exact e

end GlobalTheory.CompanionTheory.FnDesc
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGeneratorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_trivial_of_descended_generator : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | exact GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | (intros; apply GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PolSpread

def good {S : Type} [CommRing S] (B : Over (Sp S)) (M : LB B.left) : Set S :=
  {r | Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))).obj B)
    (M.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp S) (PrimeSpectrum.basicOpen r))))}

theorem exists_good_notMem {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) (p : Ideal R) [p.IsPrime] :
    ∃ r ∈ good B M, σ r ∉ p := by
  let p₀ : Ideal S := p.comap σ
  have : p₀.IsPrime := Ideal.IsPrime.comap σ
  let a := algebraMap S p₀.ResidueField
  let b := algebraMap R p.ResidueField
  let i : p₀.ResidueField →+* p.ResidueField := Ideal.ResidueField.map p₀ p σ rfl
  have hw : spMap b ≫ spMap σ = spMap i ≫ spMap a := by
    have : i.comp a = b.comp σ := RingHom.ext fun r => Ideal.ResidueField.map_algebraMap p₀ p σ rfl r
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  have hX := (IsPullback.of_hasPullback A.hom (spMap b)).paste_horiz h
  have h₂ : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap b))) (M.pull (pullback.fst A.hom (spMap b) ≫ φ)) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM h hX (spMap b) rfl hL e hA
  rw [hw] at hX
  have h₀ : Out.RelAmple ((Over.pullback (spMap a)).obj B) (M.pull (pullback.fst B.hom (spMap a))) :=
    GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback B.hom (spMap a)) hX
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) h₂
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hM a
    (GlobalTheory.FibreAmple.residueField_fraction p₀) h₀
  exact ⟨r, hr', fun hp => hr (Ideal.algebraMap_residueField_eq_zero.2 hp)⟩

theorem span_good {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S] (σ : S →+* R)
    (A : Over (Sp R)) (B : Over (Sp S)) [IsProper B.hom] [Flat B.hom] {M : LB B.left} (hM : M.IsLB)
    {L : LB A.left} (hL : L.IsLB) {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom (spMap σ))
    (e : LBIso L (M.pull φ)) (hA : Out.RelAmple A L) : Ideal.span (σ '' good B M) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have := hm.isPrime
  obtain ⟨r, hr, hr'⟩ := exists_good_notMem σ A B hM hL h e hA m
  exact hr' (hle (Ideal.subset_span ⟨r, hr, rfl⟩))

theorem relAmple_of_span {S S' : Type} [CommRing S] [CommRing S'] (τ : S →+* S') (B : Over (Sp S)) [IsProper B.hom]
    {M : LB B.left} (hM : M.IsLB) (T : Set S) (hT : T ⊆ good B M) (h : Ideal.span (τ '' T) = ⊤) :
    Out.RelAmple (Over.mk (pullback.snd B.hom (spMap τ))) (M.pull (pullback.fst B.hom (spMap τ))) := by
  let f := pullback.snd B.hom (spMap τ)
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have : IsProper f := inferInstance
  have hB := IsPullback.of_hasPullback B.hom (spMap τ)
  refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S') (Over.mk f) _ (pull_isLB hM _) inferInstance inferInstance
    fun s => ?_
  let s' : PrimeSpectrum S' := s
  obtain ⟨r, hr, hs⟩ : ∃ r ∈ T, τ r ∉ s'.asIdeal := by
    by_contra hc
    push_neg at hc
    refine s'.isPrime.ne_top (top_le_iff.1 (h ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨r, hr, rfl⟩
    exact hc r hr
  let U : (Sp S').Opens := PrimeSpectrum.basicOpen (τ r)
  let D : (Sp S).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range (U.ι ≫ spMap τ) ⊆ Set.range D.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact x.2
  let u := IsOpenImmersion.lift D.ι (U.ι ≫ spMap τ) hrange
  have hu : u ≫ D.ι = U.ι ≫ spMap τ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hs, ?_⟩
  have hU := (isPullback_morphismRestrict f U).flip
  have a₁ : Out.RelAmple (Over.mk (f ∣_ U)) (M.pull ((f ⁻¹ᵁ U).ι ≫ pullback.fst B.hom (spMap τ))) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback B.hom D.ι) (hU.paste_horiz hB) u hu
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) (hT hr)
  exact GlobalTheory.FibreAmple.relAmple_of_factor (pull_isLB hM _) hU hU (𝟙 _) (Category.id_comp _) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _).symm a₁

end GlobalTheory.CompanionTheory.PolSpread
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSections
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjTotal

theorem acyclic_over_affineOpen {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}}
    (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T) (H : IsPullback p q a b)
    (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y →
      FibAc a (G.pull σ))
    {κ : Type} [LinearOrder κ] [Fintype κ] (B : κ → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hc : ⨆ i, B i = ⊤) {V : T.Opens} (hV : IsAffineOpen V) :
    (cechLB (p ≫ a) G fun i => p ⁻¹ᵁ B i ⊓ q ⁻¹ᵁ V).Acyclic := by
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen_of_isPullback a b p q H hV B hB hc G hG
  have h := fibAc_of_closed_fibres a b p q H ha G hG Γ(T, V) hV.fromSpec Y π f Hy
    (fun s σ h₁ h₂ h₃ => hfib (s ≫ hV.fromSpec) σ (by simpa using h₁) h₂ (by simpa using h₃))
    κ E hE hEc
  exact fun m => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h m).of_iso i₁

theorem fibAc_comp_of_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG hfib κ _ _ D hD hc n
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  obtain ⟨m, B, hB, hBc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover X
  obtain ⟨r, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover T
  let V : Fin (r + 1) → T.Opens := Fin.cons ⊥ E
  have hV : ∀ j, IsAffineOpen (V j) := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact isAffineOpen_bot T
    · exact hE j
  have hVc : ⨆ j, V j = ⊤ := by
    rw [← top_le_iff, ← hEc]
    exact iSup_le fun j => le_iSup V j.succ
  have hsep : IsSeparated (p ≫ a) := by
    have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) H.flip inferInstance
    infer_instance
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G κ D (Fin m) (fun i => p ⁻¹ᵁ B i)
    (Fin (r + 1)) (fun j => q ⁻¹ᵁ V j) hG hsep hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
    (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
    (fun i j => (over_affineOpen_of_isPullback a b p q H (hV j) B hB hBc G hG).1 i) n
  have e₂ := trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (p ≫ a) G
    fun u : Fin m ⊕ₗ Fin (r + 1) =>
      Sum.elim (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) (ofLex u))
    (fun t ht _ => by
      have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
        IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j
      obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
        (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) t _ (preimage_biInf V q t)
      exact fun l => (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc hVt l).of_iso i₂) n
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
    (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) {0} (q ⁻¹ᵁ V 0) (by simp)
  have h₀ := (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc (hV 0) n).of_iso i₂
  have z := h₀.isZero_homology.of_iso e₂
  have : Subsingleton _ := ModuleCat.subsingleton_of_isZero z
  have := e₁.toEquiv.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _)

end GlobalTheory.CompanionTheory.PointSurjTotal
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_acyclicity_of_sections : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | exact GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres <;> assumption)
end
end
