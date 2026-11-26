module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivRep

theorem eq_zero_of_away {S : Type} [CommRing S] (x : S)
    (h : ∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, algebraMap S (Localization.Away s) x = 0) : x = 0 := by
  by_contra hx
  have hne : LinearMap.ker (LinearMap.mulRight S x) ≠ ⊤ := fun e => hx (by
    have : (1 : S) ∈ LinearMap.ker (LinearMap.mulRight S x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, h0⟩ := h ⟨m, hm.isPrime⟩
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ x).1 h0
  exact hs (hm.isPrime.mem_of_pow_mem n (hle hc))

theorem exists_ideal {R : Type} [CommRing R] (P : ∀ (S : Type) [CommRing S], (R →+* S) → Prop)
    (hP : ∀ (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T), P S g → P T (h.comp g))
    (H : ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      IsUnit (g r) → (P S g ↔ I ≤ RingHom.ker g)) :
    ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      (∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, P _ ((algebraMap S (Localization.Away s)).comp g)) ↔
        I ≤ RingHom.ker g := by
  classical
  choose r hr J hJ using H
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) (fun p _ => Set.mem_iUnion.2 ⟨p, hr p⟩)
  have ht' : ∀ (S : Type) [CommRing S] (g : R →+* S) (q : PrimeSpectrum S), ∃ i ∈ t, g (r i) ∉ q.asIdeal := by
    intro S _ g q
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (PrimeSpectrum.comap g q)))
    exact ⟨i, hi, h⟩
  let T := fun i => Localization.Away (r i) ⧸ (J i).map (algebraMap R (Localization.Away (r i)))
  let φ : ∀ i, R →+* T i := fun i => (Ideal.Quotient.mk _).comp (algebraMap R (Localization.Away (r i)))
  have hφ : ∀ i, P _ (φ i) := fun i =>
    (hJ i _ (φ i) ((IsLocalization.Away.algebraMap_isUnit (r i)).map (Ideal.Quotient.mk _))).2 fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have hk : ∀ i (S : Type) [CommRing S] (g : R →+* S), IsUnit (g (r i)) → P S g →
      RingHom.ker (φ i) ≤ RingHom.ker g := by
    intro i S _ g hu hg a ha
    have h₁ : (J i).map (algebraMap R (Localization.Away (r i))) ≤
        RingHom.ker (IsLocalization.Away.lift (S := Localization.Away (r i)) (r i) hu) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]
      exact (hJ i S g hu).1 hg hb
    have h₂ := h₁ (Ideal.Quotient.eq_zero_iff_mem.1 ha)
    rwa [RingHom.mem_ker, IsLocalization.Away.lift_eq] at h₂
  refine ⟨⨅ i ∈ t, RingHom.ker (φ i), fun S _ g => ⟨fun h a ha => ?_, fun h q => ?_⟩⟩
  · refine eq_zero_of_away (g a) fun q => ?_
    obtain ⟨s, hs, hPs⟩ := h q
    obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (s * g (r i))) (s * g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul, IsUnit.mul_iff] at hu
    have h₁ := hP _ _ _ (IsLocalization.Away.lift (S := Localization.Away s) s hu.1) hPs
    rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp] at h₁
    refine ⟨s * g (r i), fun hm => (q.isPrime.mem_or_mem hm).elim hs hq, ?_⟩
    exact hk i _ _ hu.2 h₁ ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ha i) hi)
  · obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (g (r i))) (g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    refine ⟨g (r i), hq, (hJ i _ _ hu).2 fun a ha => ?_⟩
    have h₁ : ∀ j, ∃ n : ℕ, φ j (r i ^ n * a) = 0 := fun j => by
      have h₂ := (hJ i _ _ (IsLocalization.Away.algebraMap_isUnit (φ j (r i)))).1
        (hP _ _ _ (algebraMap (T j) (Localization.Away (φ j (r i)))) (hφ j)) ha
      obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ j (r i))) _ _).1 h₂
      exact ⟨n, by rw [map_mul, map_pow]; exact hc⟩
    choose n hn using h₁
    have h₃ : r i ^ (∑ j ∈ t, n j) * a ∈ ⨅ i ∈ t, RingHom.ker (φ i) := by
      refine (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => ?_
      rw [← Finset.add_sum_erase t n hj, add_comm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn j)
    have h₄ : g (r i ^ (∑ j ∈ t, n j) * a) = 0 := h h₃
    rw [RingHom.mem_ker, RingHom.comp_apply, ← (hu.pow (∑ j ∈ t, n j)).mul_right_eq_zero, ← map_pow,
      ← map_mul, ← map_pow, ← map_mul, h₄, map_zero]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (F : LB X)

def TrivOn (S : Type) [CommRing S] (g : R →+* S) : Prop :=
  Triv (F.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g))))

theorem TrivOn.comp (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T)
    (H : TrivOn f F S g) : TrivOn f F T (h.comp g) :=
  CubeOpen.triv_comp (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom h))
    (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]))
    (pullback.lift_fst _ _ _) H

theorem trivOn_of_subsingleton (S : Type) [CommRing S] [Subsingleton S] (g : R →+* S) : TrivOn f F S g := by
  have he : IsEmpty (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}) :=
    ⟨fun x => (inferInstance : IsEmpty (PrimeSpectrum S)).elim
      ((pullback.snd f (Spec.map (CommRingCat.ofHom g))) x)⟩
  have hs : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}).Opens,
      Subsingleton Γ(pullback f (Spec.map (CommRingCat.ofHom g)), U) := fun U => by
    have : U = ⊥ := TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
    subst this
    infer_instance
  exact ⟨⟨fun _ => 1⟩, fun i j => Units.ext (Subsingleton.elim _ _)⟩

theorem loc_iff {S : Type} [CommRing S] {g : R →+* S} {X' : Scheme.{0}} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of S)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (q : PrimeSpectrum S) :
    (∃ U : (Spec (CommRingCat.of S)).Opens, q ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔
      ∃ s ∉ q.asIdeal, TrivOn f F _ ((algebraMap S (Localization.Away s)).comp g) := by
  have hr : ∀ s : S, Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) =
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) := fun s =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  constructor
  · rintro ⟨U, hq, t, ht⟩
    obtain ⟨_, ⟨s, rfl⟩, hs, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (u := U.1) hq U.isOpen
    refine ⟨s, hs, ?_⟩
    have ht' : Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := exists_isGen_linComb_of_pull F _ _ _ t ht
    let l := h.lift (pullback.fst f (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp g))))
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hl : Set.range l ⊆ Set.range (f' ⁻¹ᵁ U).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply hU
      change (l ≫ f') y ∈ _
      rw [h.lift_snd]
      exact (hr s).le ⟨_, rfl⟩
    refine CubeOpen.triv_comp (IsOpenImmersion.lift _ l hl) ?_ ht'
    rw [IsOpenImmersion.lift_fac_assoc]
    exact h.lift_fst _ _ _
  · rintro ⟨s, hs, ht⟩
    refine ⟨PrimeSpectrum.basicOpen s, hs, CubeOpen.triv_pull_pull _ _ ?_⟩
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) :=
      IsOpenImmersion.of_isLocalization s
    have hsub : Set.range ((f' ⁻¹ᵁ (PrimeSpectrum.basicOpen s)).ι ≫ f') ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) := by
      rintro _ ⟨y, rfl⟩
      rw [hr]
      exact y.2
    refine CubeOpen.triv_comp (pullback.lift _ (IsOpenImmersion.lift _ _ hsub) ?_) (pullback.lift_fst _ _ _) ht
    rw [CommRingCat.ofHom_comp g, Spec.map_comp, IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, h.w]

theorem exists_ideal_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB B.left, F.IsLB → ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) → ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  intro hG R _ B _ hB hproj F hF
  haveI := hB.proper
  haveI := hB.geomConnected
  have hP := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj F hF
  have hQ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj _ (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := exists_ideal (TrivOn B.hom F) (TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => loc_iff B.hom F h q

end GlobalTheory.TrivRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PolAVNonzeroLocusCoverAffine
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_nonzeroLocus_cover_affine (hA : AmpleSt) {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    (P : PolAV S) {N : ℕ} (hN : 4 ≤ N) :
    (∀ x : P.A.left, ∃ s : H0 P.L N, x ∈ nonzeroLocus s) ∧ ∀ s : H0 P.L N, IsAffineOpen (nonzeroLocus s) := by
  classical
  have := P.isAb.proper
  let := P.grp
  obtain ⟨M, s, hs⟩ := AmpleSpan.exists_embedsBy_of_isPullback P.A P.isLB (hA S P N hN).2 (isAffineOpen_top S)
    (φ := 𝟙 P.A.left) (f' := P.A.hom) (g := 𝟙 S ≫ S.topIso.inv)
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  refine ⟨fun x => ?_, fun t => (hs.affine_and_surjective (t := s) (fun j => ⟨Pi.single j 1, fun k => ?_⟩) t).1⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.1.ge (Set.mem_univ x))
    exact ⟨s i, hi⟩
  · rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, map_one, _root_.one_mul]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem exists_iso_of_polAV_sectionRing : Laws → ∀ (K : Type) [Field K] (P P' : PolAV (Spec (CommRingCat.of K))), ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 P'.L n), (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)), (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from d.f j) = (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from a.f j) * (show Γ(P'.A.left, LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) j) from b.f j)) → ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ n hn a).f j) * (show Γ(P.A.left, LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : P'.A ≅ P.A, ∃ w : LB.Iso P'.L (P.L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (p : Fin 1 → P.L.ι) (q : Fin 1 → P'.L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z)) ∈ P.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 P'.A.left) κ (r z) ∈ P'.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 P'.A.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart P'.L (fun _ : Fin 1 => 𝟙 P'.A.left) q) ((a).f q)) := by
  intro hL K _ P P' θ hlin hmul
  have := P.isAb.proper
  have := P'.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace P'.A.left := QuasiCompact.compactSpace_of_compactSpace P'.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  have : QuasiSeparatedSpace P'.A.left := quasiSeparatedSpace_of_quasiSeparated P'.A.hom
  obtain ⟨c, a⟩ := polAV_nonzeroLocus_cover_affine hL.ample P (le_refl 4)
  obtain ⟨c', a'⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (le_refl 4)
  obtain ⟨c₅, -⟩ := polAV_nonzeroLocus_cover_affine hL.ample P' (N := 4 + 1) (by norm_num)
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, by norm_num, H0 P'.L 4, id, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (c' x),
      top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (by
        obtain ⟨s, hs⟩ := c x
        obtain ⟨t, rfl⟩ := (θ 4 (by norm_num)).surjective s
        exact ⟨t, hs⟩), fun i => ⟨a' _, a _⟩⟩
  refine ⟨Φ, exists_iso_of_sectionRing K P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Φ.hom.left hΦ fun x => ?_⟩
  obtain ⟨s, hs⟩ := c' x
  obtain ⟨t, ht⟩ := c₅ x
  exact ⟨4, by norm_num, s, t, hs, ht⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GeometricallyConnectedOfClosedFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ConnFibre

open GlobalTheory.AbLaw.Seesaw

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_functions Y H

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_line (R := R) (F := F) (f := f) (g := g) (π := π) (f' := f') P h v hv

theorem geometricallyConnected_of_closedFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))), Smooth B.hom → IsProjBy B.hom → ∀ (Y₀ : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1))))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (thick V (IsLocalRing.maximalIdeal V) 0) → GeometricallyConnected Y₀.hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B hs hp Y₀ b hb hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj V B.left B.hom hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hp
  let L := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* L := (algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)
  have hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V := fun a =>
    (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)
  let q : V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1) →+* L :=
    Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (by simpa using ha)
  let y₀ : Spec (CommRingCat.of L) ⟶ _ := Spec.map (CommRingCat.ofHom q)
  have h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb
    rwa [← Spec.map_comp] at this
  have hs₀ : Smooth Y₀.hom := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc
  have hint : IsIntegral (pullback Y₀.hom y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)
  have hpr₀ : IsProper (pullback.snd Y₀.hom y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hδ' : IsUnit δ := by
    by_contra hn
    exact hδ ((hg₀ δ).2 hn)
  have hsurj : Surjective B.hom := by
    let O : (Spec (CommRingCat.of V)).Opens := ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩
    have hO : O = ⊤ := by
      refine (IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩
      have e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext ?_)
      refine ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top
        fun a ha => ?_).symm
      change g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal
      rw [(hg₀ a).2 ha]
      exact zero_mem _
    exact ⟨fun z => hO.ge (Set.mem_univ z)⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback h hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnFibre
end
end
