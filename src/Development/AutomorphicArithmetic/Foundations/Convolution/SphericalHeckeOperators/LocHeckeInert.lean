module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DeepHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.PolyAlg
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem evalAt_polynomialEmbed {n : ℕ} (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb (n := n) Q) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) Q := by
  have h : (evalAt z).comp (polyEmb (n := n)) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact AlgHom.congr_fun h Q

private theorem baseChange_polynomialEmbed {n : ℕ} (l : ℕ) (Q : MvPolynomial (Fin n) ℂ) :
    bc l (polyEmb (n := n) Q) = polyEmb (n := n) (MvPolynomial.expand l Q) := by
  have h : (bc l).comp (polyEmb (n := n)) = (polyEmb (n := n)).comp (MvPolynomial.expand l) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.expand_X, map_pow, polyEmb_X,
      AddMonoidAlgebra.single_pow, one_pow]
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  exact AlgHom.congr_fun h Q

private theorem aeval_elemSymm_power {n : ℕ} (l : ℕ) (i : Fin n) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (powE l i) =
      MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
    ⟨MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)), fun w => by
      rw [MvPolynomial.rename_expand, MvPolynomial.esymm_isSymmetric]⟩
  have h2 := congrArg Subtype.val h
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact h2

private theorem aeval_aeval_elemSymm_power {n : ℕ} (l : ℕ) (γ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.aeval (powE l) γ) =
      MvPolynomial.expand l
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) := by
  have h : (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))).comp
        (MvPolynomial.aeval (powE l)) =
      (MvPolynomial.expand l).comp
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      aeval_elemSymm_power]
  exact AlgHom.congr_fun h γ

private theorem polynomialEmbed_symmetric_mem {n : ℕ} (γ : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) ∈
      symmetricLaurent (n := n) := by
  intro σ
  have h := (MvPolynomial.esymmAlgHom (Fin n) ℂ n γ).2
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.mem_symmetricSubalgebra] at h
  rw [← polyEmb_rename, h σ]

theorem UpperTheory.ConvolutionTheory.H.polyAlg :
    ∀ n : ℕ,
      (∀ g ∈ symmetricLaurent (n := n), g ∈ (polyEmb (n := n)).range → ∃ γ : MvPolynomial (Fin n) ℂ, polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) = g) ∧
      (∀ (γ : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂˣ), evalAt z (polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) =
        MvPolynomial.eval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) γ) ∧
      (∀ (l : ℕ) (γ : MvPolynomial (Fin n) ℂ), bc l (polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) = polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (MvPolynomial.aeval (powE l) γ))) ∧
      ∀ D : ℕ, ∃ P : Finset (LaurentRing n), (∀ y ∈ P, y ∈ symmetricLaurent (n := n)) ∧
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) ∈ Submodule.span ℂ (P : Set (LaurentRing n)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro g hg ⟨Q, rfl⟩
    have hQ : Q ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℂ := by
      rw [MvPolynomial.mem_symmetricSubalgebra]
      intro σ
      apply polyEmb_injective
      rw [polyEmb_rename]
      exact hg σ
    obtain ⟨γ, hγ⟩ := MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin n) (n := n)
      (Fintype.card_fin n).le ⟨Q, hQ⟩
    refine ⟨γ, ?_⟩
    rw [← MvPolynomial.esymmAlgHom_apply, hγ]
    rfl
  · intro γ z
    rw [evalAt_polynomialEmbed]
    have h : (MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))).comp
          (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) =
        MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_esymm_eq_multiset_esymm]
    have h2 := AlgHom.congr_fun h γ
    rw [AlgHom.comp_apply] at h2
    rw [h2, MvPolynomial.aeval_eq_eval]
  · intro l γ
    rw [baseChange_polynomialEmbed, aeval_aeval_elemSymm_power]
  · intro D
    classical
    let f : (Fin n → Fin (D + 1)) → LaurentRing n := fun c =>
      polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (c i : ℕ)) (1 : ℂ)))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro y hy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact polynomialEmbed_symmetric_mem _
    · intro p hp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [p.as_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hle : ∀ i, s i < D + 1 := fun i => by
        have h1 : s.degree ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s i ≤ s.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hm : MvPolynomial.monomial s (AddMonoidAlgebra.coeff p s) =
          AddMonoidAlgebra.coeff p s • MvPolynomial.monomial s (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hle i⟩, Finset.mem_univ _, ?_⟩)
      have hs' : (Finsupp.equivFunOnFinite.symm fun i => s i) = s := by
        ext i
        rfl
      simp only [f, hs']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SphIndep
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

theorem UpperTheory.ConvolutionTheory.H.sphIndep :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.adicCompletion K) → ℂ),
      GM.IsSph w p h → ∀ [MeasurableSpace (GL (Fin n) (w.adicCompletion K))] [BorelSpace (GL (Fin n) (w.adicCompletion K))]
        (m : Measure (GL (Fin n) (w.adicCompletion K))) [m.IsHaarMeasure], m (GLnLocal.integralGL (w.adicCompletion K) n) = 1 →
        ∃ H : SphericalHecke m (F := w.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧ satakeTransform m H = polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  intro K _ _ n w p h hs inst instB m instH hm
  obtain ⟨i', b', m', h', hm', H, hH⟩ := hs
  have e : i' = inst := (@BorelSpace.measurable_eq _ _ i' b').trans (@BorelSpace.measurable_eq _ _ inst instB).symm
  subst e
  have hmm : m' = m := by
    have h1 := Measure.isMulLeftInvariant_eq_smul m' m
    have h2 := congrArg (fun μ : Measure (GL (Fin n) (w.adicCompletion K)) => μ (GLnLocal.integralGL (w.adicCompletion K) n)) h1
    simp only [smul_apply, hm, hm'] at h2
    have h3 : Measure.haarScalarFactor m' m = 1 := by
      simpa [ENNReal.smul_def] using h2.symm
    rw [h1, h3, one_smul]
  subst hmm
  exact ⟨H, hH⟩
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem haar_eq {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (m m' : Measure G) [m.IsHaarMeasure] [m'.IsHaarMeasure]
    {A : Set G} (hm : m A = 1) (hm' : m' A = 1) : m' = m := by
  have h1 := Measure.isMulLeftInvariant_eq_smul m' m
  have h2 := congrArg (fun μ : Measure G => μ A) h1
  simp only [Measure.smul_apply, hm, hm'] at h2
  have h3 : Measure.haarScalarFactor m' m = 1 := by
    simpa [ENNReal.smul_def] using h2.symm
  rw [h1, h3, one_smul]

private theorem haar_ex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    simpa [ho.interior_eq] using (⟨1, K.one_mem⟩ : (K : Set G).Nonempty)⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

private theorem exists_point {n : ℕ} (t : Multiset ℂ) (ht : t.card = n) (h0 : 0 ∉ t) :
    ∃ z : Fin n → ℂˣ, (Finset.univ.val.map fun j => (z j : ℂ)) = t := by
  induction t using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := ht
    subst hl
    refine ⟨fun j => Units.mk0 (l.get j) fun e => h0 (e ▸ List.get_mem l j), ?_⟩
    simp only [Units.val_mk0, Fin.univ_val_map, List.ofFn_get]
    rfl

open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb in
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin) in
theorem UpperTheory.ConvolutionTheory.H.locHeckeInert :
    UpperTheory.ConvolutionTheory.GM.LocHeckeInert := by
  intro F E _ _ _ _ _ _ σ hσ hp n _ v hu hsp w t ht h0 D
  obtain ⟨w', hw'⟩ := placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  letI mv : MeasurableSpace (GL (Fin n) (v.adicCompletion F)) := borel _
  haveI bv : BorelSpace (GL (Fin n) (v.adicCompletion F)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨μE, hμE, vE⟩ := haar_ex _ (unitSB_holds (w.1.adicCompletion E) n).2.1 (unitSB_holds (w.1.adicCompletion E) n).1
  obtain ⟨μF, hμF, vF⟩ := haar_ex _ (unitSB_holds (v.adicCompletion F) n).2.1 (unitSB_holds (v.adicCompletion F) n).1
  obtain ⟨z, hz⟩ := exists_point t ht h0
  obtain ⟨a1, a2, a3, a4⟩ := polyAlg n
  obtain ⟨P, hP, hPD⟩ := a4 D
  obtain ⟨g, hg, hg', hgz, H⟩ := @deepHecke _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 (hu w)) s hs n _ _ _ _ μE μF hμE hμF
    vE vF P hP z
  obtain ⟨γ, rfl⟩ := a1 g hg hg'
  refine ⟨γ, by rwa [a2, hz] at hgz, fun p hpD h f hh hf => ?_⟩
  intro _ _ mv' bv' mE mF hE hF wE wF
  have e : mv' = mv := @BorelSpace.measurable_eq _ _ mv' bv'
  subst e
  obtain ⟨hH, hPl⟩ := @placeOfLocal_holds F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have eE := haar_eq μE (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w))) vE
    (by rw [Measure.map_apply hc.measurable (unitSB_holds _ n).1.measurableSet, ← placeInt_holds.2 F E v w hw n, wE])
  have eF := haar_eq μF mF vF (by rw [placeInt_holds.1 F v n, wF])
  obtain ⟨HE, hE1, hE2⟩ := sphIndep E n w.1 _ h hh μE (by rw [← placeInt_holds.1 E w.1 n, vE])
  obtain ⟨HF, hF1, hF2⟩ := sphIndep F n v _ f hf μF (by rw [← placeInt_holds.1 F v n, vF])
  have hm := H _ (hPD p hpD) HE HF (by rw [hE2, map_mul, map_mul]) (by rw [hF2, hr, ← a3, map_mul, map_mul])
  have e1 : (fun x => (HE : HeckeAlgebra μE) x) = h := funext hE1
  have e2 : (fun x => (HF : HeckeAlgebra μF) x) = f := funext hF1
  have m1 := (HE : HeckeAlgebra μE).mem
  have m2 := (HF : HeckeAlgebra μF).mem
  rw [e1, e2, ← eE, ← eF] at hm
  rw [show ((HE : HeckeAlgebra μE) : _ → ℂ) = h from e1] at m1
  rw [show ((HF : HeckeAlgebra μF) : _ → ℂ) = f from e2] at m2
  exact hPl h m1 f m2 hm
