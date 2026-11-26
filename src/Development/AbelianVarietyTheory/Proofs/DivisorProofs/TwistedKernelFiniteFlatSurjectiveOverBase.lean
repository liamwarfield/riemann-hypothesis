module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasRepOfPublished
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem Fam.ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hN' : (GlobalTheory.AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hN', (isAdditive_iff hN').2 fun Z a a' t => ?_⟩
  simp only [evc_ev h.isLB (fst A Y) (snd A Y ≫ y) hN', lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' (t ≫ y)


end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isProjBy :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ L : LB A.left, L.IsLB → ∃ t : LB.Gen (Theta A L), t.IsGen := by
  intro k _ _ A _ hA hP L hL
  have := hA.comm
  have := hA.geomConnected
  have gi : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have conn : ConnectedSpace A.left := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have x : (Sp k : Scheme.{0}) := (default : PrimeSpectrum k)
    have h := A.hom.isConnected_preimage_singleton x
    have e : A.hom ⁻¹' {x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [e] at h
    exact connectedSpace_iff_univ.2 h
  have face : ∀ {Z : Over (Sp k)} (r : Z ⟶ G3 A) (i : Fin 3), r ≫ x3 A i = toUnit Z ≫ η[A] →
      Triv ((Theta A L).pull r.left) := fun {Z} r i h =>
    (CubeGen.triv_pull_iff L (thφ A (x3 A)) thε r.left).2
      (CubeGen.trivAt_of_formal hL _ (CubeGen.prod_face _ i (toUnit Z).left (congrArg (fun q => q.left) h)))
  exact GlobalTheory.T.theorem_of_cube_two_projective_factors k A A A η[A] η[A] η[A] hA.smooth hA.smooth hA.proper hA.proper hP hP gi gi conn
    (Theta A L) (DVR.linComb_isLB _ hL _ _) (face _ 0 (by simp [x3])) (face _ 1 (by simp [x3]))
    (face _ 2 (by simp [x3]))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclicFin

open GlobalTheory.Cube HomologicalComplex

theorem cech_sliceFst_singleton_acyclic {𝔦 𝔧 : Type} [LinearOrder 𝔦] [LinearOrder 𝔧] [Finite 𝔧]
    {R : Type} [Ring R] (A : GlobalTheory.Cube.{0} (𝔦 ⊕ₗ 𝔧) R)
    (h₀ : ∀ n, IsZero ((cubeComplex (trunc₂ A)).homology (n + 2)))
    (hA : ∀ t : Finset 𝔧, 2 ≤ t.card → (cechComplex (sliceFst A t)).Acyclic) (k : 𝔧) :
    (cechComplex (sliceFst A {k})).Acyclic := by
  have hc := isCompl_range_inlEmb_inrEmb 𝔦 𝔧
  have hQ : Set.OrdConnected {s : Finset 𝔦 | s.Nonempty} := ordConnected_nonempty
  have hU₁ : IsUpperSet {t : Finset 𝔧 | 2 ≤ t.card} :=
    fun s t hst (hs : 2 ≤ s.card) => le_trans hs (Finset.card_le_card hst)
  have hT₁ : Set.OrdConnected {t : Finset 𝔧 | 2 ≤ t.card} := hU₁.ordConnected
  have hT₂ : Set.OrdConnected {t : Finset 𝔧 | t.card = 1} := ⟨fun a (ha : a.card = 1) b
    (hb : b.card = 1) x hx => by
      have h1 := Finset.card_le_card hx.1
      have h2 := Finset.card_le_card hx.2
      show x.card = 1
      omega⟩
  have hTk : Set.OrdConnected ({{k}} : Set (Finset 𝔧)) := Set.ordConnected_singleton
  have hS := cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₁)
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ ordConnected_nonempty)
    (ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₂)
    (fun u => by
      simp only [mem_partsIn, Set.mem_setOf_eq, ← Finset.card_pos]
      constructor <;> intro h <;> omega)
    (fun u hu hu' => by
      simp only [mem_partsIn, Set.mem_setOf_eq] at hu hu'
      omega)
    (fun _ _ hst hs ht => ⟨ht.1, le_trans hs.2 (Finset.card_le_card (monotone_part _ hst))⟩))

  have h₁ : (cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) {s | s.Nonempty}
      {t | 2 ≤ t.card}) (ordConnected_partsIn _ _ hQ hT₁))).Acyclic := by
    rw [supp_partsIn_comm hQ hT₁ A]
    refine cubeComplex_supp_partsIn_acyclic hc.symm hT₁ hQ A fun t ht => ?_
    rw [← sliceFst_eq_slice]
    exact (cubeComplex_trunc₁_acyclic_iff _).2 (hA t ht)

  have h₂ : (cubeComplex (trunc₂ A)).Acyclic := by
    intro n
    match n with
    | n + 2 => exact (exactAt_iff_isZero_homology _ _).2 (h₀ n)
    | 0 | 1 =>
      refine ExactAt.of_isZero (isZero_cubeComplex_X_of_subsingleton _ _ fun u hu => ?_)
      refine subsingleton_supp A (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty) fun hmem => ?_
      simp only [mem_partsIn, Set.mem_setOf_eq] at hmem
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hmem
      rw [mem_part] at hi hj
      have : 1 < u.card := Finset.one_lt_card.2 ⟨_, hi, _, hj, by simp⟩
      omega

  have h₃ : ∀ n, IsZero ((cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧)
      {s | s.Nonempty} {t | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₂))).homology n) := by
    intro n
    have hx := hS.homology_exact₃ n (n + 1) rfl
    exact hx.isZero_X₂ (((exactAt_iff_isZero_homology _ _).1 (h₂ n)).eq_of_src _ _)
      (((exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))).eq_of_tgt _ _)

  have hPk := ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hTk
  have hP₂ := ordConnected_partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) hQ hT₂
  let ι₁ := suppMap (𝟙 A) hPk hP₂ fun s t hst hs ht => by
    simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ht ⊢
    refine iff_of_true ⟨ht.1, ?_⟩ ⟨hs.1, by rw [hs.2]; rfl⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 ht.2
    have : k ∈ part (inrEmb 𝔦 𝔧) t := monotone_part _ hst (by rw [hs.2]; exact Finset.mem_singleton_self k)
    rw [ha, Finset.mem_singleton] at this
    rw [ha, this]
  let ρ₁ := suppMap (𝟙 A) hP₂ hPk fun s t hst hs ht => by
    simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ht ⊢
    refine iff_of_true ⟨ht.1, by rw [ht.2]; rfl⟩ ⟨hs.1, ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hs.2
    have : a ∈ part (inrEmb 𝔦 𝔧) t := monotone_part _ hst (by rw [ha]; exact Finset.mem_singleton_self a)
    rw [ht.2, Finset.mem_singleton] at this
    rw [ha, this]
  have hr : ι₁ ≫ ρ₁ = 𝟙 _ := by
    ext s x
    refine supp_ext fun hs => ?_
    have hs₂ : s ∈ partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧) {s | s.Nonempty} {t | t.card = 1} := by
      simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs ⊢
      exact ⟨hs.1, by rw [hs.2]; rfl⟩
    change suppEquiv A hPk hs (suppMapApp (𝟙 A) hP₂ hPk s (suppMapApp (𝟙 A) hPk hP₂ s x)) =
      suppEquiv A hPk hs x
    rw [suppEquiv_suppMapApp (𝟙 A) hs₂ hs, suppEquiv_suppMapApp (𝟙 A) hs hs₂]
    rfl
  have h₄ : ∀ n, IsZero ((cubeComplex (supp A (partsIn (inlEmb 𝔦 𝔧) (inrEmb 𝔦 𝔧)
      {s | s.Nonempty} {{k}}) hPk)).homology n) := by
    intro n
    rw [IsZero.iff_id_eq_zero]
    have := congrArg (fun φ => homologyMap ((cubeFunctor _ R).map φ) n) hr
    simp only [Functor.map_comp, Functor.map_id, homologyMap_comp, homologyMap_id] at this
    have h0 : homologyMap ((cubeFunctor _ R).map ρ₁) n = 0 := (h₃ n).eq_of_src _ _
    rw [h0, comp_zero, CategoryTheory.Functor.map_id, homologyMap_id] at this
    exact this.symm
  have h₅ : (cubeComplex (supp (slice (inlEmb 𝔦 𝔧) (({k} : Finset 𝔧).map (inrEmb 𝔦 𝔧).toEmbedding) A)
      {s | s.Nonempty} hQ)).Acyclic := fun n =>
    (exactAt_iff_isZero_homology _ _).2 ((h₄ (n + 1)).of_iso (suppSingletonHomologyIso hc hQ k A n).symm)
  rw [← cubeComplex_trunc₁_acyclic_iff, trunc₁, sliceFst_eq_slice]
  exact h₅

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

theorem acyclic_over_of_pairs (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j j', j ≠ j' → (∀ y, t y ∈ V j ⊓ V j') →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤)
    (hac : ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (D i)) →
      ⨆ i, D i = ⊤ → (cechLB (p ≫ g) F D).Acyclic) (k : σ) :
    (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).Acyclic := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  let P : ν ×ₗ σ → Z.Opens := fun u => q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
  have hP (u) : IsAffineOpen (P u) := GlobalTheory.ProductAcyclic.isAffineOpen_prod sq hF (hV _) B hB hBc _
  have hPc : ⨆ u, P u = ⊤ := by
    refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
    exact ⟨toLex (i, j), hi, hj⟩
  have h₀ : ∀ n, IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F _ P _
      (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hP hPc
      (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ hW => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
      (fun j _ hW => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
      (fun i j => GlobalTheory.ProductAcyclic.isAffineOpen_prod sq hF (hV j) B hB hBc i) n
    have h₁ := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac _ P hP hPc n)
    rw [ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e₁.symm.injective.subsingleton
  have hs : ∀ s : Finset σ, 2 ≤ s.card → (cechComplex (Cube.sliceFst (secCube (p ≫ g) F
      fun u : ν ⊕ₗ σ => Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u)) s)).Acyclic := by
    intro s hs
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.1 hs
    have hne : s.Nonempty := ⟨j, hj⟩
    have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
      IsAffineOpen.biInf _ s.finite_toSet hne fun j _ => hV j
    have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
    have h₁ := (GlobalTheory.ProductAcyclic.over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀
      hVs.opensRange_fromSpec B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j j' hjj
        fun y => le_inf (biInf_le V hj) (biInf_le V hj') (hVs.range_fromSpec.le ⟨y, rfl⟩))
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
      (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
    exact fun m => (h₁ m).of_iso i₂
  have hk := cech_sliceFst_singleton_acyclic _ h₀ hs k
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact fun m => (hk m).of_iso i₂.symm

end GlobalTheory.ProductAcyclicFin

namespace GlobalTheory.ProductAcyclicFin

theorem acyclic_over_affine_of_finite_closed : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ∀ S : Finset T, (∀ s ∈ S, IsClosed ({s} : Set T)) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ∉ S) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF S hS H hac R _ t Y π f H₀ ht
  classical
  haveI := ht
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ :=
    GlobalTheory.ProductAcyclic.exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial

  have hU : ∀ s ∈ S, ∃ U : T.Opens, IsAffineOpen U ∧ s ∈ U ∧ ∀ x ∈ S, x ∈ U → x = s := by
    intro s hs
    have hC : IsClosed (⋃ x ∈ S.erase s, ({x} : Set T)) :=
      Set.Finite.isClosed_biUnion (S.erase s).finite_toSet fun x hx =>
        hS x (Finset.mem_of_mem_erase hx)
    have hsC : s ∈ (⋃ x ∈ S.erase s, ({x} : Set T))ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, not_exists]
      intro x hx hsx
      exact Finset.ne_of_mem_erase hx hsx.symm
    obtain ⟨_, ⟨U, hUa, rfl⟩, hsU, hUC⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hsC hC.isOpen_compl
    refine ⟨U, hUa, hsU, fun x hx hxU => by_contra fun hne => hUC hxU ?_⟩
    exact Set.mem_iUnion₂.2 ⟨x, Finset.mem_erase.2 ⟨hne, hx⟩, rfl⟩
  choose! U hUa hUs hUS using hU
  let S' := S.filter (fun s => s ∉ t.opensRange)
  let pt : Fin S'.card → T := fun j => (S'.equivFin.symm j).1
  have hpt (j) : pt j ∈ S ∧ pt j ∉ t.opensRange := Finset.mem_filter.1 (S'.equivFin.symm j).2
  let G : Fin (S'.card + 1) → T.Opens := Fin.cons t.opensRange fun j => U (pt j)
  have hGa : ∀ a, IsAffineOpen (G a) :=
    Fin.cases (isAffineOpen_opensRange t) fun j => hUa _ (hpt j).1
  have hGS : ∀ a b, a ≠ b → ∀ x ∈ S, x ∈ G a → x ∈ G b → False := by
    have h₁ : ∀ j, ∀ x ∈ S, x ∈ t.opensRange → x ∈ U (pt j) → False := fun j x hx hx₁ hx₂ =>
      (hpt j).2 (hUS _ (hpt j).1 x hx hx₂ ▸ hx₁)
    intro a b hab x hx ha hb
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact hab rfl
      | succ j => exact h₁ j x hx ha hb
    | succ i =>
      induction b using Fin.cases with
      | zero => exact h₁ i x hx hb ha
      | succ j =>
        refine hab (congrArg Fin.succ (S'.equivFin.symm.injective (Subtype.ext ?_)))
        exact (hUS _ (hpt i).1 x hx ha).symm.trans (hUS _ (hpt j).1 x hx hb)
  have hGc : ∀ x ∈ S, x ∈ ⨆ a, G a := by
    intro x hx
    refine TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hxt : x ∈ t.opensRange
    · exact ⟨0, hxt⟩
    · have hx' : x ∈ S' := Finset.mem_filter.2 ⟨hx, hxt⟩
      refine ⟨(S'.equivFin ⟨x, hx'⟩).succ, ?_⟩
      have : pt (S'.equivFin ⟨x, hx'⟩) = x := by simp [pt]
      simp only [G, Fin.cons_succ]
      rw [this]
      exact hUs x hx

  obtain ⟨r, V', hV'a, hV'S, hV'c⟩ : ∃ (r : ℕ) (V' : Fin r → T.Opens), (∀ j, IsAffineOpen (V' j)) ∧
      (∀ j, ∀ x ∈ V' j, x ∉ S) ∧ ∀ x, x ∉ ⨆ a, G a → ∃ j, x ∈ V' j := by
    have hSc : IsOpen (↑S : Set T)ᶜ := by
      have := Set.Finite.isClosed_biUnion S.finite_toSet fun x hx => hS x hx
      rw [Set.biUnion_of_singleton] at this
      exact this.isOpen_compl
    have hc : IsCompact (↑(⨆ a, G a) : Set T)ᶜ := (⨆ a, G a).isOpen.isClosed_compl.isCompact
    obtain ⟨s, hs⟩ := hc.elim_finite_subcover
      (fun W : {W : T.Opens // IsAffineOpen W ∧ (W : Set T) ⊆ (↑S)ᶜ} => (W.1 : Set T))
      (fun W => W.1.isOpen) (by
        intro x hx
        have hxS : x ∈ (↑S : Set T)ᶜ := fun hxS => hx (hGc x hxS)
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
          T.isBasis_affineOpens.exists_subset_of_mem_open hxS hSc
        exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
    refine ⟨s.card, fun j => (s.equivFin.symm j).1.1, fun j => (s.equivFin.symm j).1.2.1,
      fun j x hx => (s.equivFin.symm j).1.2.2 hx, fun x hx => ?_⟩
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
    exact ⟨s.equivFin ⟨W, hW⟩, by simpa using hxW⟩
  let V : Fin (S'.card + 1 + r) → T.Opens := Fin.append G V'
  have hV : ∀ j, IsAffineOpen (V j) := Fin.addCases (fun a => by simpa [V] using hGa a)
    (fun j => by simpa [V] using hV'a j)
  have hVc : ⨆ j, V j = ⊤ := by
    refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ ⨆ a, G a
    · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨Fin.castAdd r a, by simpa [V] using ha⟩
    · obtain ⟨j, hj⟩ := hV'c x hx
      exact ⟨Fin.natAdd _ j, by simpa [V] using hj⟩
  have hVS : ∀ j j', j ≠ j' → ∀ x, x ∈ V j → x ∈ V j' → x ∉ S := by
    intro j j' hjj x hx hx' hxS
    induction j using Fin.addCases with
    | left a =>
      induction j' using Fin.addCases with
      | left b =>
        simp only [V, Fin.append_left] at hx hx'
        exact hGS a b (fun hab => hjj (hab ▸ rfl)) x hxS hx hx'
      | right c =>
        simp only [V, Fin.append_right] at hx'
        exact hV'S c x hx' hxS
    | right c =>
      simp only [V, Fin.append_right] at hx
      exact hV'S c x hx hxS
  have hk : V (Fin.castAdd r 0) = t.opensRange := by simp [V, G]
  have h₁ := GlobalTheory.ProductAcyclicFin.acyclic_over_of_pairs sq hF V hV hVc
    (fun R _ t Y π f H₁ ht j j' hjj hy => H R t Y π f H₁ ht fun y hyS =>
      hVS j j' hjj _ (hy y).1 (hy y).2 hyS)
    B hB hBc hac (Fin.castAdd r 0)
  exact (GlobalTheory.ProductAcyclic.over_affineOpen sq hF H₀ hk.symm B hB hBc).2.2 h₁

end GlobalTheory.ProductAcyclicFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_product_acyclic_over_affine_finite_closed : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ∀ S : Finset T, (∀ s ∈ S, IsClosed ({s} : Set T)) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ∉ S) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  first | exact @GlobalTheory.ProductAcyclicFin.acyclic_over_affine_of_finite_closed | exact GlobalTheory.ProductAcyclicFin.acyclic_over_affine_of_finite_closed | (intros; apply GlobalTheory.ProductAcyclicFin.acyclic_over_affine_of_finite_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KLFinite

theorem finite_of_isFinite {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite Z := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  letI : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hmod : Module.Finite K Γ(Z, ⊤) := by
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.Finite
    rw [CommRingCat.hom_comp]
    exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite K _
  have : Finite (Spec (.of Γ(Z, ⊤))) := inferInstanceAs (Finite (PrimeSpectrum _))
  exact Finite.of_injective _ Z.isoSpec.hom.isOpenEmbedding.injective

theorem memKL_of_lam_eq_zero {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (x : 𝟙_ _ ⟶ A) (h : lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0) : MemKL A L x := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  have e := congrArg (CechPic.pull (snd (𝟙_ _) A).left) h
  rw [pull_lam, map_zero, Category.comp_id, ← Category.assoc, comp_toUnit, GlobalTheory.PrimitiveOverField.lam_const,
    toUnit_unique (toUnit _) (fst (𝟙_ _) A)] at e
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ e)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

theorem isClosed_point {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [IsSeparated A.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set A.left) := by
  have hx : x.left ≫ A.hom = 𝟙 _ := Over.w x
  have : IsClosedImmersion (x.left ≫ A.hom) := by rw [hx]; infer_instance
  have : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left A.hom
  have h := x.left.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
    (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
      Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
  exact (congrArg IsClosed Set.image_singleton).mp h

end GlobalTheory.KLFinite

theorem GlobalTheory.KLFinite.kl_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  intro K _ _ A _ hA L hL ha
  obtain ⟨Z, i, -, hfin, -, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds K A hA L hL ha
  have : Finite Z.left := GlobalTheory.KLFinite.finite_of_isFinite Z.hom
  have : IsProper A.hom := hA.proper
  have hr : (Set.range i.left).Finite := Set.finite_range _
  classical
  refine ⟨hr.toFinset.filter (fun s => IsClosed ({s} : Set A.left)), fun s hs => (Finset.mem_filter.1 hs).2,
    fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hZ _ x).1 (GlobalTheory.KLFinite.memKL_of_lam_eq_zero hL x hx)
  refine Finset.mem_filter.2 ⟨hr.mem_toFinset.2 ⟨z.left (IsLocalRing.closedPoint K), ?_⟩,
    GlobalTheory.KLFinite.isClosed_point x⟩
  rw [← hz, Over.comp_left]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  first | exact @GlobalTheory.KLFinite.kl_finite | exact GlobalTheory.KLFinite.kl_finite | (intros; apply GlobalTheory.KLFinite.kl_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AddLineField


open GlobalTheory.PrimitiveOverField in
theorem additive_eq_lam_of_ample : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  intro K _ _ A _ hA L hL hamp N hN
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have hpr : IsProjBy A.hom := by
    obtain ⟨_, _, m, s, hH, hv⟩ := veryAmpleBy_of_relAmple hL hamp (𝟙 A.left) (Category.id_comp _)
      (pull_isLB hL (𝟙 A.left)) (GlobalTheory.lbIso_self (pull_isLB hL _))
    exact ⟨_, hH, m, s, hv⟩
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f A.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.exists_gen_theta_of_isProjBy K A hA hpr L hL
  obtain ⟨S, hS, hSK⟩ := GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed K A hA L hL hamp
  let O : LB A.left := ev N (𝟙 A) (toUnit A)
  have hO : O.IsLB := pull_isLB hN.isLB _
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have pO : ∀ {Y : Over (Sp K)} (u : Y ⟶ A), CechPic.pull u.left (cls O hO) = evc hN.isLB u (toUnit Y) := by
    intro Y u
    rw [cls_ev hN.isLB, pull_evc, Category.comp_id, comp_toUnit]
  have lamO : lam (cls O hO) (fst A A) (snd A A) = 0 := by
    have e := (isAdditive_iff hN.isLB).1 hN.add (A ⊗ A) (fst A A) (snd A A) (toUnit _)
    have e1 := hN.add.evc_one hN.isLB (toUnit (A ⊗ A))
    simp only [lam, pO, e, e1]
    abel
  have key : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO = lam (cls L hL) (toUnit A ≫ x) (𝟙 A) →
      Same A N (abelian₂ A L) (𝟙 _) x := by
    intro x hx
    rw [same_iff hN.isLB hLam]
    have e1 : evc hN.isLB (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ 𝟙 _) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (cls O hO) := by
      rw [pO, Category.comp_id, toUnit_unique (toUnit _) (snd A _)]
    have e2 : evc hLam (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ x) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (lam (cls L hL) (toUnit A ≫ x) (𝟙 A)) := by
      have cL : cls (abelian₂ A L) hLam = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hLam
      rw [evc, cL, pull_lam, pull_lam, lift_fst,
        lift_snd, Category.comp_id, ← Category.assoc, toUnit_unique (fst A _ ≫ toUnit A) (snd A _), lam_comm]
    rw [e1, e2, hx]
  by_contra hno
  have hno' : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO ≠ lam (cls L hL) (toUnit A ≫ x) (𝟙 A) :=
    fun x e => hno ⟨x, key x e⟩
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst A A) (snd A A) - CechPic.pull (snd A A).left (cls O hO))
  have hpq : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ A, (toUnit A ≫ x).left = A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (toUnit A ≫ x) (𝟙 A)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (𝟙 A) (toUnit A ≫ x)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst A A).left ≫ A.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
    refine ⟨(lift (toUnit A ≫ x') (𝟙 A)).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit A ≫ x') (𝟙 A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit A ≫ x') (𝟙 A))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno' x' e.symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ A.left := η[A].left
  have ho : o ≫ A.hom = 𝟙 _ := Over.w η[A]
  have all := GlobalTheory.T.lineBundle_product_acyclic_over_affine_finite_closed K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance
    inferInstance F hF S hS (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
      refine ⟨(lift (𝟙 A) (toUnit A ≫ x')).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have hm := hSK x' e
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (by rw [hy]; exact hm)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 A) (toUnit A ≫ η[A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (cst_left η[A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ η[A])))
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : Nonempty A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.AddLineField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgCloseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  first | exact @GlobalTheory.AddLineField.additive_eq_lam_of_ample | exact GlobalTheory.AddLineField.additive_eq_lam_of_ample | (intros; apply GlobalTheory.AddLineField.additive_eq_lam_of_ample <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamily
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerSurj

theorem exists_point_geom : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S) (M : LB (A ⊗ Over.mk ξ).left), Fam A M → ∃ a : Over.mk ξ ⟶ A, Same A (abelian₂ A L) M a (𝟙 _) := by
  intro S A _ hA L hL hAmp K _ _ ξ M hM
  obtain ⟨A', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A ξ
  have := hA
  have : IsProper A.hom := IsAbelianScheme.proper
  have hA' : IsAbelianScheme A' := by
    have : IsCommMonObj A := hA.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hA.geomConnected⟩
  have := hA'
  have : IsCommMonObj A := IsAbelianScheme.comm
  have : IsCommMonObj A' := IsAbelianScheme.comm
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  have hAmp' : Out.RelAmple A' (L.pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hAmp hφ.1
  have hs : 𝟙 (Sp K) ≫ ξ = ξ := Category.id_comp ξ
  have hN' : Fam A' (M.pull (BaseChange.toBase hφ hs)) := BaseChange.fam_toBase hφ hs hM
  obtain ⟨a', ha'⟩ := GlobalTheory.T.additiveLineBundle_eq_mumfordLambda_of_ample_algClosed K A' hA' (L.pull φ) hL' hAmp' _ hN'
  refine ⟨GlobalTheory.AbDual.pushP hφ hs a', ?_⟩

  obtain hsq := GlobalTheory.LamPull.exists_isSquare (G := A) (G' := A') (f := ξ) (φ := φ) hφ.1.w
  have hLam : (abelian₂ A L).IsLB := FullSiegel.isLB_lam hL
  have hLam' : (abelian₂ A' (L.pull φ)).IsLB := FullSiegel.isLB_lam hL'
  have eLam := (GlobalTheory.LamPull.lbIso_lam_pull hφ hL hL' (GlobalTheory.lbIso_self hL') hsq).symm
  have h0 := (same_iff hN'.isLB hLam' _ _).mp ha'
  have e1 : evc hN'.isLB (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) =
      GlobalTheory.CechPic.pull (BaseChange.toBase hφ hs) (evc hM.isLB (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _)) := by
    simp only [GlobalTheory.AbDual.evc]
    rw [show lift (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ 𝟙 _) = 𝟙 _ by simp,
      show lift (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ 𝟙 _) = 𝟙 _ by simp,
      Over.id_left, Over.id_left, GlobalTheory.CechPic.pull_id]
    exact (GlobalTheory.CechPic.pull_id _).trans (GlobalTheory.CechPic.cls_pull hM.isLB _ hN'.isLB)
  rw [same_iff hLam hM.isLB]
  rw [BaseChange.pull_inj_iff (BaseChange.toBase hφ hs) (BaseChange.ofBase hφ hs)
    (BaseChange.ofBase_toBase hφ hs), ← e1]
  unfold BaseChange.toBase
  rw [pull_evc]
  refine Eq.trans (GlobalTheory.AbDual.evc_eq (f := φ) (g := φ) hsq.1 hsq.2 hLam hLam' eLam
      (s := (A' ⊗ 𝟙_ (Over (Sp K))).hom) (s₀ := (A' ⊗ 𝟙_ (Over (Sp K))).hom ≫ ξ)
      (fst A' (𝟙_ (Over (Sp K)))) (snd A' (𝟙_ (Over (Sp K))) ≫ a') _ _ ?_ ?_).symm h0.symm
  · rw [Over.comp_left, GlobalTheory.AbDual.lift_left_fst]; rfl
  · simp only [Over.comp_left]
    rw [← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
    simp [GlobalTheory.AbDual.pushP]

theorem surjective_twist_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL hAmp T _ _ N hN H h _ hiff
  refine ⟨fun x => ?_⟩

  let Ω := AlgebraicClosure (T.left.residueField x)
  let p : Sp Ω ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) Ω)) ≫ T.left.fromSpecResidueField x
  let tpt : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p rfl
  have hMf := Fam.ev hN tpt
  obtain ⟨a, ha⟩ := exists_point_geom (Sp R) A hA L hL hAmp Ω (p ≫ T.hom) _ hMf
  have hs : Same A (abelian₂ A L) N a tpt := by
    rw [same_iff (FullSiegel.isLB_lam hL) hN.isLB]
    rw [same_iff (FullSiegel.isLB_lam hL) hMf.isLB] at ha
    rw [ha, GlobalTheory.AbDual.evc_ev hN.isLB]
    simp
  obtain ⟨z, hz⟩ := (hiff (Over.mk (p ≫ T.hom)) a tpt).mp hs
  have e : z.left ≫ (h ≫ snd A T).left = p := by
    rw [← Over.comp_left, ← Category.assoc, hz, lift_snd]
    rfl
  let q : Sp Ω := IsLocalRing.closedPoint Ω
  refine ⟨z.left.base q, ?_⟩
  have e2 : (h ≫ snd A T).left.base (z.left.base q) = p.base q :=
    (Scheme.Hom.comp_apply z.left (h ≫ snd A T).left q).symm.trans
      (congrArg (fun f : Sp Ω ⟶ T.left => f.base q) e)
  exact e2.trans ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _))

end GlobalTheory.TwistKerSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveTwistedKernelAdditiveLineBundleFamilyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → Surjective (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistKerSurj.surjective_twist_kernel | exact GlobalTheory.TwistKerSurj.surjective_twist_kernel | (intros; apply GlobalTheory.TwistKerSurj.surjective_twist_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambda
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambda
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistKerFinite

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    (x y : Y ⟶ A) : evc hP x y = lam (cls L hL) x y := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem add_inv_eq_of_same {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a a' : Y ⟶ A) (t : Y ⟶ T)
    (h₁ : Same A (abelian₂ A L) N a t) (h₂ : Same A (abelian₂ A L) N a' t) :
    CechPic.pull a.left (cls L hL) + CechPic.pull (a⁻¹).left (cls L hL) =
      CechPic.pull a'.left (cls L hL) + CechPic.pull (a'⁻¹).left (cls L hL) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e := ((same_iff hP hN a t).1 h₁).trans ((same_iff hP hN a' t).1 h₂).symm
  rw [evc_lam hL hP, evc_lam hL hP] at e
  have e' := congrArg (CechPic.pull (lift (a⁻¹ * a'⁻¹) (𝟙 Y)).left) e
  simp only [pull_lam, lift_fst, lift_snd_assoc, Category.id_comp] at e'
  simp only [lam] at e'
  rw [show a⁻¹ * a'⁻¹ * a = a'⁻¹ by rw [mul_right_comm, inv_mul_cancel, _root_.one_mul],
    show a⁻¹ * a'⁻¹ * a' = a⁻¹ from inv_mul_cancel_right _ _] at e'
  linear_combination (norm := abel) e'.symm

theorem isFinite_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  intro R _ _ A _ hB L hL hA T _ _ N hN H h hh hH
  haveI := hB.comm
  have := hB.proper
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A L hL).1 hA
  have hAT : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback A.hom T.hom
  have : IsProper (snd A T).left := MorphismProperty.of_isPullback hAT inferInstance
  have : IsAffineHom (fst A T).left := MorphismProperty.of_isPullback hAT.flip inferInstance
  let f : H.left ⟶ T.left := (h ≫ snd A T).left
  have hf : f ≫ T.hom = H.hom := Over.w (h ≫ snd A T)
  have : IsProper f := inferInstanceAs (IsProper (h.left ≫ (snd A T).left))
  change IsFinite f
  suffices LocallyQuasiFinite f from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (f ⁻¹' {z}) with h0 | ⟨x₀, hx₀⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField x₀
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField x₀
  let g : Spec (CommRingCat.of K) ⟶ T.left := y₀ ≫ f
  let π : pullback f g ⟶ H.left := pullback.fst f g
  let q : pullback f g ⟶ Spec (CommRingCat.of K) := pullback.snd f g
  let Z : Scheme.{0} := pullback f g
  have hpb : IsPullback π q f g := IsPullback.of_hasPullback f g
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  let P : Over (Sp R) := Over.mk (y₀ ≫ H.hom)
  let Q : Over (Sp R) := Over.mk (π ≫ H.hom)
  let yo : P ⟶ H := Over.homMk y₀ rfl
  let qo : Q ⟶ P := Over.homMk q (by
    show q ≫ y₀ ≫ H.hom = π ≫ H.hom
    rw [← hf, ← Category.assoc π, hpb.w]
    simp only [g, Category.assoc])
  let p₁ : Q ⟶ H := Over.homMk π rfl
  have hpt : p₁ ≫ h ≫ snd A T = qo ≫ yo ≫ h ≫ snd A T := by
    ext
    exact hpb.w
  let w : H ⟶ A := h ≫ fst A T
  have hs₁ : Same A (abelian₂ A L) N (p₁ ≫ w) (p₁ ≫ h ≫ snd A T) :=
    (hH _ _ _).2 ⟨p₁, by ext <;> simp [w]⟩
  have hs₂ : Same A (abelian₂ A L) N (qo ≫ yo ≫ w) (p₁ ≫ h ≫ snd A T) := by
    rw [hpt]
    exact (hH _ _ _).2 ⟨qo ≫ yo, by ext <;> simp [w]⟩
  have key := add_inv_eq_of_same hL hN.isLB _ _ _ hs₁ hs₂
  rw [← GrpObj.comp_inv qo, Over.comp_left _ _ _ qo, Over.comp_left _ _ _ qo, pull_comp qo.left,
    pull_comp qo.left, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w).left,
    GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) (yo ≫ w)⁻¹.left, map_zero, add_zero] at key
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (p₁ ≫ w).left := inferInstanceAs (IsAffineHom (π ≫ h.left ≫ (fst A T).left))
  have : Z.IsQuasiAffine := GlobalTheory.AmpleStabFinite.quasiAffine_of_pull_add (p₁ ≫ w).left ((p₁ ≫ w)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [GlobalTheory.AmpleStabFinite.cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add]
      exact (congrArg _ key).trans (zsmul_zero _))
  have : IsAffine Z := GlobalTheory.AmpleStabFinite.isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set Z).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun v hv => ?_
  have e : f v = g (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = x₀ := Scheme.fromSpecResidueField_apply x₀ _
    exact (show f v = z from hv).trans ((show f x₀ = z from hx₀).symm.trans (congrArg f e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.TwistKerFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteTwistedKernelCubeLambdaStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_twisted_kernel_cubeLambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | exact GlobalTheory.TwistKerFinite.isFinite_twisted_kernel | (intros; apply GlobalTheory.TwistKerFinite.isFinite_twisted_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBase
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistKernel

theorem twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL ha T _ hT N hN
  have := hA.proper
  have : LocallyOfFiniteType (A ⊗ T).hom := by
    have := hT
    first
    | infer_instance
    | (show LocallyOfFiniteType (pullback.fst A.hom T.hom ≫ A.hom); infer_instance)
    | (show LocallyOfFiniteType (pullback.snd A.hom T.hom ≫ T.hom); infer_instance)
  have : IsLocallyNoetherian (A ⊗ T).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ T).hom
  have hΛ : Fam A (abelian₂ A L) := ⟨LB.isLB_linComb hL _ _,
    (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL (LB.isLB_linComb hL _ _)).1⟩
  obtain ⟨H, h, hh, hH⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp R) A (A ⊗ T) hA
    (ev (abelian₂ A L) (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T)) (ev N (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
    (hΛ.ev (fst A T)) (hN.ev (snd A T))
  have rep : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T),
      Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
    intro Y a t
    rw [← hH Y (lift a t), same_iff hΛ.isLB hN.isLB, same_iff (hΛ.ev (fst A T)).isLB (hN.ev (snd A T)).isLB,
      evc_ev hΛ.isLB, evc_ev hN.isLB]
    simp
  exact ⟨H, h, hh, GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep,
    GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter R A hA L hL ha T hT N hN H h hh rep (GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep),
    GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily R A hA L hL ha T hT N hN H h hh rep, rep⟩

end GlobalTheory.TwistKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedKernel_finite_flat_surjective_over_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  first | exact @GlobalTheory.TwistKernel.twisted_kernel | exact GlobalTheory.TwistKernel.twisted_kernel | (intros; apply GlobalTheory.TwistKernel.twisted_kernel <;> assumption)
end
