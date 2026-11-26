module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicGluing.ExistsOpenSubgroupRightInvariantFiniteAdelicGL
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem locally_constant_right_invariant_open_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) [CompactSpace K₀] [TotallyDisconnectedSpace K₀]
    (e : G → ℂ) (he : IsLocallyConstant e) (hc : HasCompactSupport e) :
    ∃ W : Subgroup G, IsOpen (W : Set G) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  letI : Inv (Set G) := Set.inv
  have hF : IsLocallyConstant fun p : G × G => e (p.1 * p.2) - e p.1 :=
    (he.comp_continuous (continuous_fst.mul continuous_snd)).sub (he.comp_continuous continuous_fst)
  have hN : IsOpen {p : G × G | e (p.1 * p.2) - e p.1 = 0} := hF.isOpen_fiber 0
  obtain ⟨A, V, -, hVo, hCA, h1V, hAV⟩ := generalized_tube_lemma (s := tsupport e) hc
    (isCompact_singleton (x := (1 : G))) hN (by
      rintro ⟨x, k⟩ ⟨-, hk⟩
      have hk' : k = 1 := hk
      simp [hk'])
  have h1 : (1 : G) ∈ V := h1V rfl
  have hinv : ∀ x ∈ tsupport e, ∀ k ∈ V, e (x * k) = e x :=
    fun x hx k hk => sub_eq_zero.1 (hAV (Set.mk_mem_prod (hCA hx) hk))
  have hVi : IsOpen (V ∩ V⁻¹) := hVo.inter hVo.inv
  have hUo : IsOpen ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := hVi.preimage continuous_subtype_val
  have hU1 : (1 : K₀) ∈ ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := by
    simp [h1]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨(H.toOpenSubgroup.toSubgroup).map K₀.subtype, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.isOpenEmbedding_subtypeVal.isOpenMap _ H.toOpenSubgroup.isOpen
  · rintro _ ⟨u, hu, rfl⟩ x
    have hV : (u : G) ∈ V ∩ V⁻¹ := hH hu
    by_cases hx : x ∈ tsupport e
    · exact hinv x hx _ hV.1
    by_cases hxk : x * u ∈ tsupport e
    · have := hinv _ hxk _ hV.2
      simpa using this.symm
    · change e (x * u) = e x
      rw [image_eq_zero_of_notMem_tsupport hxk, image_eq_zero_of_notMem_tsupport hx]

theorem UpperTheory.exists_open_subgroup_rightInvariant_finiteAdelicGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (e : TF K n), IsLocallyConstant e →
      ∃ W : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (W : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  intro K _ _ n e he
  exact locally_constant_right_invariant_open_subgroup (AdelicGLn.integralFiniteGL K n) (AdelicGLn.isOpen_integralFiniteGL K n) e he e.hasCompactSupport
end

section -- merged from Development.AutomorphicArithmetic.AdelicGluing.LevFIsOpenIsCompactLeIntegral
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

theorem UpperTheory.levF_isOpen_isCompact_le_integral :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (lev : ∀ v : Pl K, Subgroup (GL (Fin n) (v.adicCompletion K))) (S : Finset (Pl K)),
      (∀ v ∈ S, IsOpen (lev v : Set (GL (Fin n) (v.adicCompletion K))) ∧ lev v ≤ GLnLocal.integralGL (v.adicCompletion K) n) →
      (∀ v, v ∉ S → lev v = GLnLocal.integralGL (v.adicCompletion K) n) →
      IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
        levF lev ≤ AdelicGLn.integralFiniteGL K n ∧
        ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), J ≤ lev w → J.map (AdelicGLn.localEmbedding w) ≤ levF lev := by
  classical
  intro K _ _ n lev S hS hS'
  have hmem : ∀ h : AdelicGLn.FiniteAdelicGL K n,
      h ∈ levF lev ↔ ∀ v, AdelicGLn.finiteRestrictedEquiv K n h v ∈ lev v := fun h => Iff.rfl
  have hint : levF lev ≤ AdelicGLn.integralFiniteGL K n := by
    intro h hh
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro v
    have hv := (hmem h).1 hh v
    by_cases hvS : v ∈ S
    · exact (hS v hvS).2 hv
    · rwa [hS' v hvS] at hv
  have hev : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n =>
      (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K)) := fun v =>
    (_root_.RestrictedProduct.continuous_eval v).comp (AdelicGLn.finiteRestrictedEquiv K n).continuous
  have hVo : IsOpen ((AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
      ⋂ v ∈ S, (fun h : AdelicGLn.FiniteAdelicGL K n =>
        (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K))) ⁻¹'
          (lev v : Set (GL (Fin n) (v.adicCompletion K)))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (isOpen_biInter_finset fun v hv => (hS v hv).1.preimage (hev v))
  have hopen : IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levF lev) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨one_mem _, ?_⟩
      simp only [Set.mem_iInter]
      intro v _
      exact (levF lev).one_mem v
    · rintro h ⟨h1, h2⟩
      simp only [Set.mem_iInter] at h2
      refine (hmem h).2 fun v => ?_
      by_cases hvS : v ∈ S
      · exact h2 v hvS
      · rw [hS' v hvS]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1 v
  refine ⟨hopen, ?_, hint, ?_⟩
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w J hJ _ ⟨x, hx, rfl⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1
    have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hJ hx
    · rw [h2 v hv]
      exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.AdelicGluing.BaseChangeLevelIsOpenIsCompactContainsIwahori
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_atFin {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

private theorem fin_above (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem eq_one_of_cmp {v : Pl F} (g : GL (Fin n) (CompletionsOver E v))
    (h : ∀ w : PlacesOver E v, cmp w g = 1) : g = 1 := by
  apply Units.ext
  ext i j w
  have h1 : (g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i j w =
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j :=
    congrArg (fun x : GL (Fin n) (w.1.adicCompletion E) => (x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) (h w)
  rw [h1]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem cont_fin (w : Pl E) : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
    (finAt w (finEmb E n h) : GL (Fin n) (w.adicCompletion E)) :=
  (_root_.RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous

private theorem cont_above (v : Pl F) : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
    mapGL n (atFin (E := E) v) (finEmb E n h) := by
  have hval : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
      Units.val (mapGL n (atFin (E := E) v) (finEmb E n h)) := by
    refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.comp (cont_fin w.1)).matrix_elem i j
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have h2 := hval.comp (continuous_inv (G := AdelicGLn.FiniteAdelicGL E n))
  refine h2.congr fun h => ?_
  simp only [Function.comp, map_inv]

private theorem comp_mem (P : ∀ w : Pl E, Subgroup (GL (Fin n) (w.adicCompletion E))) (w : Pl E)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ P w) (w' : Pl E) :
    finAt w' (finEmb E n (AdelicGLn.localEmbedding w g)) ∈ P w' := by
  obtain ⟨-, h1, h2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  by_cases hw : w' = w
  · subst hw
    rw [h1]
    exact hg
  · rw [h2 w' hw]
    exact one_mem _

private theorem above_one (w : Pl E) (g : GL (Fin n) (w.adicCompletion E)) (v : Pl F)
    (hne : w.under (𝓞 F) ≠ v) :
    mapGL n (atFin (E := E) v) (finEmb E n (AdelicGLn.localEmbedding w g)) = 1 := by
  obtain ⟨-, -, h2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  refine eq_one_of_cmp _ fun w' => ?_
  rw [cmp_atFin]
  exact h2 w'.1 (fun h => hne (by rw [← h]; exact under_over w')) g

end SlopeTestRemainingChoices

theorem UpperTheory.baseChangeLevel_isOpen_isCompact_contains_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (q : Pl F) (w₀ : PlacesOver E q) (L : Loc σ n q w₀),
          {w : Pl E | w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q}.Finite ∧
          IsOpen (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) ∧ IsCompact (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) ∧
          levE L.UE ≤ AdelicGLn.integralFiniteGL E n ∧
          (∀ w : Pl E, ¬ (w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q) → (GLnLocal.integralGL (w.adicCompletion E) n).map (AdelicGLn.localEmbedding w) ≤ levE L.UE) ∧
          ∀ w : PlacesOver E q, (GLnLocal.iwahori (w.1.adicCompletion E) n).map (AdelicGLn.localEmbedding w.1) ≤ levE L.UE ∧
            ∀ u ∈ levE L.UE, finAt w.1 (finEmb E n u) ∈ GLnLocal.iwahori (w.1.adicCompletion E) n := by
  classical
  intro F E _ _ _ _ _ _ σ n hn q w₀ L
  have hmem : ∀ u : AdelicGLn.FiniteAdelicGL E n,
      u ∈ levE L.UE ↔ ∀ v, mapGL n (atFin (E := E) v) (finEmb E n u) ∈ L.UE v := by
    intro u
    simp only [levE, Subgroup.mem_iInf, Subgroup.mem_comap]
    rfl
  have hiq : ∀ g, g ∈ L.UE q ↔ ∀ w, cmp w g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n := L.at_q.2.2.1
  have hU : ∀ v, ∀ g ∈ L.UE v, g ∈ unitSet E n v := by
    intro v g hg
    by_cases hv : v ∈ L.S
    · exact (L.lev v hv).2.1 hg
    by_cases hvq : v = q
    · subst hvq
      intro w
      exact GLnLocal.iwahori_le_integralGL _ _ ((hiq g).1 hg w)
    · have h3 : g ∈ (L.UE v : Set _) := hg
      rwa [(L.off v hv hvq).2.2.1] at h3
  have hint : levE L.UE ≤ AdelicGLn.integralFiniteGL E n := by
    intro u hu
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro w
    have h2 : cmp (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F)))
        (mapGL n (atFin (E := E) (w.under (𝓞 F))) (finEmb E n u)) ∈ GLnLocal.integralGL (w.adicCompletion E) n :=
      hU _ _ ((hmem u).1 hu (w.under (𝓞 F))) ⟨w, ⟨rfl⟩⟩
    rw [cmp_atFin] at h2
    exact h2
  have hVo : IsOpen (((AdelicGLn.integralFiniteGL E n : Set (AdelicGLn.FiniteAdelicGL E n)) ∩
      ⋂ v ∈ L.S, (fun h : AdelicGLn.FiniteAdelicGL E n => mapGL n (atFin (E := E) v) (finEmb E n h)) ⁻¹'
        (L.UE v : Set (GL (Fin n) (CompletionsOver E v)))) ∩
      ⋂ w : PlacesOver E q, (fun h : AdelicGLn.FiniteAdelicGL E n =>
        (finAt w.1 (finEmb E n h) : GL (Fin n) (w.1.adicCompletion E))) ⁻¹'
          (GLnLocal.iwahori (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E)))) :=
    ((AdelicGLn.isOpen_integralFiniteGL E n).inter
      (isOpen_biInter_finset fun v hv => (L.lev v hv).1.preimage (cont_above v))).inter
      (isOpen_iInter_of_finite fun w => (GLnLocal.isOpen_iwahori _ n).preimage (cont_fin w.1))
  have hopen : IsOpen (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levE L.UE) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨⟨one_mem _, ?_⟩, ?_⟩
      · simp only [Set.mem_iInter]
        intro v _
        exact (hmem 1).1 (one_mem _) v
      · simp only [Set.mem_iInter]
        intro w
        have h1 : finAt w.1 (finEmb E n (1 : AdelicGLn.FiniteAdelicGL E n)) = 1 := by
          rw [map_one, finAt_one]
        simp only [Set.mem_preimage, h1]
        exact one_mem _
    · rintro h ⟨⟨h1, h2⟩, h3⟩
      simp only [Set.mem_iInter] at h2 h3
      refine (hmem h).2 fun v => ?_
      by_cases hv : v ∈ L.S
      · exact h2 v hv
      by_cases hvq : v = q
      · subst hvq
        refine (hiq _).2 fun w => ?_
        rw [cmp_atFin]
        exact h3 w
      · have h4 : mapGL n (atFin (E := E) v) (finEmb E n h) ∈ (L.UE v : Set _) := by
          rw [(L.off v hv hvq).2.2.1]
          intro w
          change cmp w _ ∈ _
          rw [cmp_atFin]
          exact (AdelicGLn.mem_integralFiniteGL_iff_forall E n).1 h1 w.1
        exact h4
  refine ⟨?_, hopen, ?_, hint, ?_, ?_⟩
  · refine (Set.Finite.biUnion (insert q L.S).finite_toSet
      (fun v _ => fin_above (E := E) v)).subset fun w hw => ?_
    simp only [Set.mem_iUnion]
    refine ⟨w.under (𝓞 F), ?_, rfl⟩
    rcases hw with h | h
    · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem h)
    · exact Finset.mem_coe.2 (Finset.mem_insert.2 (Or.inl h))
  · exact (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w hw _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe] at hg; rw [hmem]
    intro v
    by_cases hv : w.under (𝓞 F) = v
    · subst hv
      rw [not_or] at hw
      have h4 : mapGL n (atFin (E := E) (w.under (𝓞 F))) (finEmb E n (AdelicGLn.localEmbedding w g)) ∈
          (L.UE (w.under (𝓞 F)) : Set _) := by
        rw [(L.off _ hw.1 hw.2).2.2.1]
        intro w'
        change cmp w' _ ∈ _
        rw [cmp_atFin]
        exact comp_mem (fun w => GLnLocal.integralGL (w.adicCompletion E) n) w hg w'.1
      exact h4
    · rw [above_one w g v hv]
      exact one_mem _
  · intro w
    refine ⟨?_, fun u hu => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe] at hg; rw [hmem]
      intro v
      by_cases hv : v = q
      · subst hv
        refine (hiq _).2 fun w' => ?_
        rw [cmp_atFin]
        exact comp_mem (fun w => GLnLocal.iwahori (w.adicCompletion E) n) w.1 hg w'.1
      · rw [above_one w.1 g v (by rw [under_over]; exact Ne.symm hv)]
        exact one_mem _
    · have h5 := (hiq _).1 ((hmem u).1 hu q) w
      rwa [cmp_atFin] at h5
end
