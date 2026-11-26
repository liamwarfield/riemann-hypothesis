module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideBaseFieldOfAbsoluteConvergence
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory NumberField IsDedekindDomain Topology Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.orbitalSideBaseField_of_absoluteConvergence :
    SideAbs → RPF → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → InfF → SideF := by
  intro hS hRP hRC hUL hUO hTC hSep hCL hInf F _ _ n hn _ _ _ _ μ μi m hμ hμi hm γ hγ ν νi nv hν hνi hnv S a b ha hb hT hE
    fi f hfi hfc hf hloc
  have hcA : IsClosed ((TA γ : Subgroup (GA F n)) : Set (GA F n)) := Set.isClosed_centralizer _
  have hcI : IsClosed ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F))) :=
    Set.isClosed_centralizer _
  have hcF : ∀ v : Pl F, IsClosed ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) :
      Set (GL (Fin n) (v.adicCompletion F))) := fun v => Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (TA γ) := hcA.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := hcI.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) := fun v => (hcF v).locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology
    ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology
    ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))
  have hR := hRP F n
  have hRT := hRC _ _ _ _ (pI F n) (pF F n) (KF F n) hR (AdelicGLn.diagonal F n γ)
  obtain ⟨hc1, hc2, hc3, -⟩ := hTC F n γ hγ
  obtain ⟨hUi, hUv⟩ := hUL (Pl F) (GA F n) _ _ (pI F n) (pF F n) (KF F n) hR μ μi m hμ hμi hm
  have hP : Pair μ (TA γ).subtype ν := ⟨hμ, hcA.isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 hc1⟩
  have hPi : Pair μi (TI γ).subtype νi := ⟨hUi, hcI.isClosedEmbedding_subtypeVal, (hUO _ νi hνi).2 hc2⟩
  have hPv : ∀ v : Pl F, Pair (m v) (TF γ v).subtype (nv v) := fun v =>
    ⟨hUv v, (hcF v).isClosedEmbedding_subtypeVal, (hUO _ (nv v) (hnv v)).2 (hc3 v)⟩
  have hz : Continuous (zA F n) :=
    (continuous_centralSection (K := F) (n := n)).comp
      (Continuous.subtype_mk Real.continuous_exp fun s => Real.exp_pos s)
  have hzv : ∀ (v : Pl F) (s : ℝ), pF F n v (zA F n s) = 1 := fun v s => (hCL F n _).2.2.1 v
  have hfix : ∀ t : TA γ, ((TA γ).subtype t)⁻¹ * AdelicGLn.diagonal F n γ * (MonoidHom.id (GA F n)) ((TA γ).subtype t) =
      AdelicGLn.diagonal F n γ := by
    intro t
    have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
    simp only [Subgroup.subtype_apply, MonoidHom.id_apply]
    first
      | rw [mul_assoc, ← h, inv_mul_cancel_left]
      | rw [mul_assoc, h, inv_mul_cancel_left]
  have hcpt : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ C : Set (GL (Fin n) (InfiniteAdeleRing F)),
      IsCompact C ∧ ∀ x, x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ D →
        ∃ t : TI γ, ∃ y ∈ C, x = (TI γ).subtype t * y := by
    intro D hD
    obtain ⟨C, hC, h⟩ := (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).2 (hSep F n γ hγ).1 D hD
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := h x hx
    exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
  have hbd : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ B : Set ℝ, IsCompact B ∧
      ∀ s x, pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x) ∈ D → s ∈ B :=
    (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).1
  have hl : ∀ v ∉ S, f v = (KF F n v : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 ∧
      ∀ x, x⁻¹ * pF F n v (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ KF F n v ↔
        ∃ t : TF γ v, ∃ y ∈ KF F n v, x = (TF γ v).subtype t * y := by
    intro v hv
    refine ⟨(hloc v hv).1, fun x => ?_⟩
    refine ((hloc v hv).2 x).trans ⟨?_, ?_⟩
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
    · rintro ⟨t, y, hy, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
      exact ⟨t, by first | exact h | exact h.symm, y, hy, rfl⟩
  obtain ⟨hm1, hm2⟩ := hS (Pl F) (GA F n) (GL (Fin n) (InfiniteAdeleRing F)) (fun v => GL (Fin n) (v.adicCompletion F))
    (pI F n) (pF F n) (KF F n) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hR hRT (TA γ).subtype (TI γ).subtype (fun v => (TF γ v).subtype)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) μ μi m ν νi nv hP hPi hPv S a b ha hb hE hT
    (MonoidHom.id _) (MonoidHom.id _) (fun _ => MonoidHom.id _) (fun _ => rfl) (fun _ _ => rfl)
    continuous_id (fun _ => continuous_id) (AdelicGLn.diagonal F n γ) (zA F n) hz hzv hfix hcpt hbd fi f hfi hfc hf hl
  refine ⟨hm1, ?_⟩
  refine Eq.trans hm2 ?_
  congr 3
  funext s
  congr 1
  funext x
  have hc := (hCL F n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  congr 1
  change pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * x) =
    x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x
  rw [mul_assoc, mul_assoc, ← mul_assoc (pI F n (zA F n s)), hc x⁻¹, mul_assoc, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionContinuous
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_cont {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ : E ≃ₐ[F] E) {ι : Type*} [Fintype ι] (b : ι → E) (c : ι → B → A)
    (hc : ∀ i, Continuous (c i)) (hs : ∀ y, e.symm y = ∑ i, b i ⊗ₜ[F] c i y)
    (hm : Continuous fun a : A => e (1 ⊗ₜ a)) : Continuous (galOf e σ) := by
  have h : ∀ y, galOf e σ y = ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := by
    intro y
    change e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e.symm y)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have h' : (galOf e σ : B → B) = fun y => ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := funext h
  rw [h']
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hm.comp (hc i))

private theorem galAd_cont (σ : E ≃ₐ[F] E) : Continuous (galAd σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (adeleTensorEquiv F E) σ (Module.finBasis F E) (coord (Module.finBasis F E))
    (continuous_coord _) (adeleTensorEquiv_symm_apply _) ?_
  have h : (fun a : 𝔸[F] => adeleTensorEquiv F E ((1 : E) ⊗ₜ a)) = adeleMap F E := by
    funext a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h]
  exact continuous_adeleMap

private theorem galInf_cont (σ : E ≃ₐ[F] E) : Continuous (galInf σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
    (Module.finBasis F E) (GroundTheory.Global.InfinitePlace.adeleCoord (Module.finBasis F E))
    (GroundTheory.Global.InfinitePlace.continuous_adeleCoord _) (fun y => ?_) ?_
  · rw [AlgEquiv.symm_apply_eq]
    exact (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord _ y).symm
  · have h : (fun a : InfiniteAdeleRing F =>
        GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ a)) =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) := by
      funext a
      rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    rw [h]
    exact GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap

private theorem galFin_mul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (y : CompletionsOver E v) :
    galFin σ v (algebraMap (v.adicCompletion F) (CompletionsOver E v) a * y) =
      algebraMap (v.adicCompletion F) (CompletionsOver E v) a * galFin σ v y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  rw [← tensorEquiv'_tmul_mul]
  change tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 ⊗ₜ a) * t)))) =
    _ * tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v t)))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← tensorEquiv'_tmul_mul, map_mul,
    Algebra.TensorProduct.map_tmul]
  simp

private theorem galFin_cont (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun a y => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact galFin_mul σ v a y }
  exact IsModuleTopology.continuous_of_linearMap L

private theorem mapGL_cont {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (n : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

end

theorem UpperTheory.adele_galois_action_continuous :
    Compat → RPE → GalCont := by
  intro _ _ F E _ _ _ _ _ σ n
  exact ⟨mapGL_cont n _ (galAd_cont σ), mapGL_cont n _ (galInf_cont σ),
    fun v => mapGL_cont n _ (galFin_cont σ v)⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductFiniteAdelicGL
open NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open scoped NumberField.AdeleRing RestrictedProduct

namespace UpperTheory.OpenSubgroupProjection

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

private abbrev RF : Type :=
  Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]

private theorem fst_eq (g : GA K n) : (AdelicGLn.prodEquiv K n g).1 = pI K n g := by
  apply Units.ext; ext a b; rfl

private theorem opn (v : Pl K) : IsOpen (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isOpen_integralGL _ n

private theorem cpt (v : Pl K) : IsCompact (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isCompact_integralGL _ n

private noncomputable def phi : GA K n ≃ₜ GL (Fin n) (InfiniteAdeleRing K) × RF K n :=
  (AdelicGLn.prodEquiv K n).toHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.refl _) (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph)

private theorem phi_fst (g : GA K n) : (phi K n g).1 = pI K n g := fst_eq K n g

private theorem phi_snd (g : GA K n) (v : Pl K) : (phi K n g).2 v = pF K n v g := rfl

private theorem compact_box (C : ∀ v : Pl K, Set (GL (Fin n) (v.adicCompletion K)))
    (hC : ∀ v, IsCompact (C v))
    (hK : ∀ᶠ v in cofinite, C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))) :
    IsCompact {x : RF K n | ∀ v, x v ∈ C v} := by
  let A : Set (Pl K) := {v | C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))}
  have hle : (cofinite : Filter (Pl K)) ≤ 𝓟 A := le_principal_iff.2 hK
  have hemb : IsEmbedding (DFunLike.coe : (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := RestrictedProduct.isEmbedding_coe_of_principal
  have hT : IsCompact (Set.pi Set.univ C) := isCompact_univ_pi hC
  have hsub : Set.pi Set.univ C ⊆ Set.range (DFunLike.coe :
      (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := fun x hx =>
    ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v trivial)⟩, rfl⟩
  have h1 := (hemb.isInducing.isCompact_preimage_iff hsub).2 hT
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hle)
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v)⟩, fun v _ => hx v, rfl⟩
  · rintro ⟨y, hy, rfl⟩ v
    exact hy v trivial

private theorem opnU (S : Finset (Pl K)) :
    IsOpen (US (pF K n) (KF K n) S : Set (GA K n)) := by
  have h0 : IsOpen (US (pF K n) (KF K n) ∅ : Set (GA K n)) := by
    have : (US (pF K n) (KF K n) ∅ : Set (GA K n)) =
        (fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹'
          (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, AdelicGLn.mem_integralFiniteGL_iff_forall, mem_US]
      exact ⟨fun h v => h v (Finset.notMem_empty v), fun h v _ => h v⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).preimage
      (continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous)
  exact Subgroup.isOpen_mono (H₁ := US (pF K n) (KF K n) ∅) (H₂ := US (pF K n) (KF K n) S)
    (fun g hg v _ => hg v (Finset.notMem_empty v)) h0

end UpperTheory.OpenSubgroupProjection

open UpperTheory.OpenSubgroupProjection in
theorem UpperTheory.restrictedProduct_finite_adelicGL :
    RPF := by
  intro K _ _ n
  refine
    { cq := ?_
      cp := fun v => continuous_finAt v
      opn := opn K n
      cpt := cpt K n
      ae := fun g => AdelicGLn.eventually_mem_integralGL K n g
      opnU := opnU K n
      ext := ?_
      surj := ?_
      prop := ?_ }
  · have : (pI K n : GA K n → _) = fun g => (AdelicGLn.prodEquiv K n g).1 :=
      funext fun g => (fst_eq K n g).symm
    rw [this]
    exact continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous
  · intro g g' h1 h2
    apply (phi K n).injective
    refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
    · rw [phi_fst, phi_fst, h1]
    · exact h2 v
  · intro gi gv h
    refine ⟨(phi K n).symm (gi, ⟨gv, h⟩), ?_, fun v => ?_⟩
    · rw [← phi_fst, Homeomorph.apply_symm_apply]
    · rw [← phi_snd, Homeomorph.apply_symm_apply]
      rfl
  · intro Ci C hCi hC hK
    have h := (hCi.prod (compact_box K n C hC hK))
    have h2 := (phi K n).isCompact_preimage.2 h
    convert h2 using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, phi_fst, phi_snd]
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.SplitCentralizerOfSplitEquiv
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Core Topology GroundTheory.Global.AdeleBaseChange

private theorem mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) (t : Subgroup.centralizer {γ₁}) :
    ((t : G1 K n) : GA K n) ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← h]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 t.2)

private noncomputable def cenIn {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) : Subgroup.centralizer {γ₁} →* TA γ where
  toFun t := ⟨((t : G1 K n) : GA K n), mem_TA h t⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem cs_mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : GL (Fin n) K)
    (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact centralSection_mul_comm s _

private theorem isClosed_cen {K : Type} [Field K] [NumberField K] {n : ℕ} (γ₁ : G1 K n) :
    IsClosed (Subgroup.centralizer {γ₁} : Set (G1 K n)) := by
  have : (Subgroup.centralizer {γ₁} : Set (G1 K n)) = {x | x * γ₁ = γ₁ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem UpperTheory.splitCentralizer_of_splitEquiv :
    SplitEquiv → N5 → CentBC → Spl := by
  intro hS hN hC F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hcl, hmod, -⟩ := hN F E σ hσ n hn
  have hl : 0 < Module.finrank F E := Module.finrank_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hS (G1 E n) {r : ℝ // 0 < r} (GA E n) (normOneGL (K := E) (n := n)).subtype
      ((rpowHom ((Module.finrank F E : ℝ))⁻¹).comp (detModule E n))
      ((mapGL n (adeleMap F E)).comp (centralSection F n))
      IsEmbedding.subtypeVal
      ((continuous_rpowHom _).comp continuous_detModule)
      (hcl.continuous.comp continuous_centralSection)
      (fun s => by
        refine Subtype.ext ?_
        change ((detModule E n (mapGL n (adeleMap F E) (centralSection F n s)) : ℝ)) ^
          ((Module.finrank F E : ℝ))⁻¹ = s.1
        rw [hmod, detModule_centralSection hn]
        exact Real.pow_rpow_inv_natCast s.2.le hl.ne')
      (fun s g => by
        change mapGL n (adeleMap F E) (centralSection F n s) * g = g * mapGL n (adeleMap F E) (centralSection F n s)
        rw [hC F E n s]
        exact centralSection_mul_comm _ g)
      (fun g => by
        constructor
        · intro hg
          have h1 : ((detModule E n g : ℝ)) ^ ((Module.finrank F E : ℝ))⁻¹ = 1 := congrArg Subtype.val hg
          have h2 : (detModule E n g : ℝ) = 1 := by
            have h3 := Real.rpow_inv_natCast_pow (detModule E n g).2.le hl.ne'
            rw [h1, one_pow] at h3
            exact h3.symm
          exact ⟨⟨g, mem_normOneGL_iff_detModule.2 (Subtype.ext h2)⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          have h1 : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
          change rpowHom _ (detModule E n (x : GA E n)) = 1
          rw [h1, map_one])
    exact ⟨e, he⟩
  · intro γ γ₁ h
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hS (Subgroup.centralizer {γ₁}) {r : ℝ // 0 < r} (TA γ) (cenIn h)
        ((detModule F n).comp (TA γ).subtype)
        ((centralSection F n).codRestrict (TA γ) (cs_mem_TA γ))
        ((IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : TA γ → GA F n))).1
          (show IsEmbedding ((Subtype.val : G1 F n → GA F n) ∘ (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n)) from
            IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal))
        (continuous_detModule.comp continuous_subtype_val)
        (continuous_centralSection.subtype_mk _)
        (fun s => detModule_centralSection hn s)
        (fun s g => Subtype.ext (centralSection_mul_comm s _))
        (fun g => by
          constructor
          · intro hg
            have h1 : (g : GA F n) ∈ normOneGL (K := F) (n := n) := mem_normOneGL_iff_detModule.2 hg
            refine ⟨⟨⟨g, h1⟩, ?_⟩, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            refine Subtype.ext ?_
            change (g : GA F n) * (γ₁ : GA F n) = (γ₁ : GA F n) * g
            rw [h]
            exact Subgroup.mem_centralizer_singleton_iff.1 g.2
          · rintro ⟨x, rfl⟩
            exact mem_normOneGL_iff_detModule.1 x.1.2)
      exact ⟨e, fun x => congrArg Subtype.val (he x)⟩
    · have hmem : ∀ t : Subgroup.centralizer {γ₁},
          mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) ∈ normOneGL (K := E) (n := n) := fun t => by
        refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
        rw [hmod, mem_normOneGL_iff_detModule.1 (t : G1 F n).2]
        simp
      let j : Subgroup.centralizer {γ₁} →* G1 E n :=
        { toFun := fun t => ⟨mapGL n (adeleMap F E) ((t : G1 F n) : GA F n), hmem t⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine ⟨j, ?_, fun t => rfl⟩
      have hE : IsClosedEmbedding (Subtype.val : G1 E n → GA E n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hF : IsClosedEmbedding (Subtype.val : G1 F n → GA F n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hT : IsClosedEmbedding (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n) :=
        (isClosed_cen γ₁).isClosedEmbedding_subtypeVal
      exact (IsClosedEmbedding.of_comp_iff hE).1 (hcl.comp (hF.comp hT))
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdeleBaseChangeLocalIsClosedEmbedding
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Topology Filter

private theorem ce_of_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) (h : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hf (Function.Injective.of_comp h.injective)
    (isProperMap_of_comp_of_t2 hf hg h.isProperMap).isClosedMap

private theorem ce_reindex {V : Type*} {A : V → Type*} [∀ v, TopologicalSpace (A v)] (φ : V → V) (h : ∀ v, φ v = v) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => x (φ v)) := by
  obtain rfl : φ = id := funext h
  exact (Homeomorph.refl _).isClosedEmbedding

private theorem ce_piMap {V : Type*} {A B : V → Type*} [∀ v, TopologicalSpace (A v)] [∀ v, TopologicalSpace (B v)]
    (ι : ∀ v, A v → B v) (h : ∀ v, IsClosedEmbedding (ι v)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => ι v (x v)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_pi fun v => (h v).continuous.comp (continuous_apply v))
    (fun _ _ e => funext fun v => (h v).injective (congrFun e v))
    (IsProperMap.pi_map fun v => (h v).isProperMap).isClosedMap

private theorem ce_pi {V W : Type*} (c : W → V) (hc : Function.Surjective c) {A : V → Type*} {B : W → Type*}
    [∀ v, TopologicalSpace (A v)] [∀ w, TopologicalSpace (B w)] [∀ w, T2Space (B w)]
    (ι : ∀ w, A (c w) → B w) (h : ∀ w, IsClosedEmbedding (ι w)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (w : W) => ι w (x (c w))) := by
  choose s hs using hc
  refine ce_of_comp (g := fun (y : ∀ w, B w) (v : V) => y (s v))
    (continuous_pi fun w => (h w).continuous.comp (continuous_apply _))
    (continuous_pi fun v => continuous_apply _) ?_
  exact (ce_piMap (fun v => ι (s v)) fun v => h (s v)).comp (ce_reindex (A := A) (fun v => c (s v)) hs)

private theorem ce_gl {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [T2Space R] [T2Space S] (n : ℕ) (f : R →+* S) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mapGL n f) := by
  have h1 : IsClosedEmbedding (fun (x : Fin n → R) (j : Fin n) => f (x j)) := ce_piMap (fun _ => f) fun _ => hf
  have hM : IsClosedEmbedding (f.mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) S) :=
    ce_piMap (fun _ => fun (x : Fin n → R) (j : Fin n) => f (x j)) fun _ => h1
  exact @IsClosedEmbedding.units_map (Matrix (Fin n) (Fin n) R) (Matrix (Fin n) (Fin n) S)
    _ _ _ _ _ _ f.mapMatrix.toMonoidHom hM

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_small (v : HeightOneSpectrum (𝓞 F)) (g : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ a : v.adicCompletion F, a ≠ 0 ∧ Valued.v a < (g : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hπ
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) π) < 1 := by
    rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h2 g
  refine ⟨algebraMap F (v.adicCompletion F) π ^ k, pow_ne_zero _ ?_, by rwa [map_pow]⟩
  intro h0
  rw [h0, map_zero] at h1
  exact (WithZero.exp_ne_zero) h1.symm

private theorem ce_compl (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    IsClosedEmbedding (completionMap v w) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  have hind : IsInducing (completionMap v w) := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    · have := (continuous_completionMap v w).tendsto 0
      rw [map_zero] at this
      exact this.le_comap
    · intro s hs
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
      let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
      let emb : ν.ValueGroup₀ →*₀ WithZero (Multiplicative ℤ) :=
        MonoidWithZeroHom.ValueGroup₀.embedding (f := ν.toMonoidWithZeroHom)
      obtain ⟨a, ha0, ha⟩ := exists_small v (Units.map emb.toMonoidHom γ)
      have hfa : completionMap v w a ≠ 0 := (map_ne_zero_iff _ (completionMap v w).injective).2 ha0
      have hopen := Valued.isOpen_ball (w.adicCompletion E) ((Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a))
      have hmem : (0 : w.adicCompletion E) ∈ {x | (Valued.v : Valuation (w.adicCompletion E) _).restrict x < (Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a)} := by
        simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_zero]
        exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hfa)
      refine Filter.mem_comap.2 ⟨_, hopen.mem_nhds hmem, fun x hx => hγ ?_⟩
      have h1 : Valued.v (completionMap v w x) < Valued.v (completionMap v w a) := by
        simpa [Valuation.restrict_lt_iff] using hx
      rw [valued_completionMap, valued_completionMap] at h1
      have h2 := lt_of_pow_lt_pow_left₀ _ zero_le h1
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      exact h2.trans ha
  have hu : IsUniformInducing (completionMap v w) := AddMonoidHom.isUniformInducing_of_isInducing hind
  exact (IsUniformEmbedding.mk hu (completionMap v w).injective).isClosedEmbedding

omit [NumberField F] [NumberField E] in
private theorem ce_infComp (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] :
    IsClosedEmbedding (AbsoluteValue.Completion.map v.1 w.1) :=
  (AbsoluteValue.Completion.isometry_map v.1 w.1).isClosedEmbedding

private theorem ce_incFin (v : HeightOneSpectrum (𝓞 F)) : IsClosedEmbedding (incFin E v) := by
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  let w : PlacesOver E v := (placesOverEquiv E v).symm P
  exact ce_of_comp (g := fun y : CompletionsOver E v => y w)
    (continuous_pi fun u => continuous_completionMap v u.1) (continuous_apply w) (ce_compl v w.1)

open scoped NumberField.LiesOver in
private theorem ce_infMap : IsClosedEmbedding (infMap F E) := by
  have hs : Function.Surjective (fun w : InfinitePlace E => w.comap (algebraMap F E)) := InfinitePlace.comap_surjective
  have hmap : (infMap F E : InfiniteAdeleRing F → InfiniteAdeleRing E) =
      fun (x : InfiniteAdeleRing F) (w : InfinitePlace E) =>
        AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (x (w.comap (algebraMap F E))) := by
    funext x w
    exact (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w).trans
      (AbsoluteValue.Completion.algebraMap_apply_of_liesOver (w.comap (algebraMap F E)).1 w.1 _)
  rw [hmap]
  exact ce_pi (A := fun v : InfinitePlace F => v.Completion) (B := fun w : InfinitePlace E => w.Completion)
    (fun w : InfinitePlace E => w.comap (algebraMap F E)) hs
    (fun w => AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1) fun w => ce_infComp _ w
end

theorem UpperTheory.adele_baseChange_local_isClosedEmbedding :
    LocEmb := by
  intro F E _ _ _ _ _ n
  exact ⟨ce_gl n _ ce_infMap, fun v => ce_gl n _ (ce_incFin v)⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.GlobalOrbitalComparisonOfSplit
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc

private theorem cenClosed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | g * x = x * g} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem cenLC {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (g : G) : LocallyCompactSpace (Subgroup.centralizer {g} : Subgroup G) :=
  (cenClosed g).isClosedEmbedding_subtypeVal.locallyCompactSpace

private theorem diag_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (δ : GL (Fin n) E) :
    detModule E n (AdelicGLn.diagonal E n δ) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨δ, rfl⟩)

theorem UpperTheory.globalOrbitalComparison_of_split :
    QSub → SplitQ → UniOf → TComm → Spl → N3 → N5 → CentBC → Glob := by
  intro hQ hS hU hT hSpl hN3 hN5 _ F E _ _ _ _ _ _ σ hσ n hn μE μF hE hF
  obtain ⟨⟨eE, heE⟩, hG⟩ := hSpl F E σ hσ n hn
  let l : Measure {r : ℝ // 0 < r} := Measure.haar
  have hl : Uni l := (hU _ l inferInstance).2 mul_comm
  have hUE : Uni μE := (hU _ μE hE).1 inferInstance
  have hUF : Uni μF := (hU _ μF hF).1 inferInstance
  let eF : G1 F n × {r : ℝ // 0 < r} ≃ₜ* GA F n := (glNormOneSplitting (K := F) hn).symm
  refine ⟨(μE.prod l).map eE, (μF.prod l).map eF, ?_, ?_, ?_⟩
  · exact (hS (G1 E n) (G1 E n) _ (GA E n) (GA E n) μE (MonoidHom.id _) μE l
      ⟨hUE, Topology.IsClosedEmbedding.id, hUE⟩ hl eE eE (MonoidHom.id _) (fun _ => rfl)).1.1
  · exact (hS (G1 F n) (G1 F n) _ (GA F n) (GA F n) μF (MonoidHom.id _) μF l
      ⟨hUF, Topology.IsClosedEmbedding.id, hUF⟩ hl eF eF (MonoidHom.id _) (fun _ => rfl)).1.1
  intro γ γ₁ hγ hreg ν hν
  obtain ⟨⟨eT, heT⟩, j, hj, hjv⟩ := hG γ γ₁ hγ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) := cenLC γ₁
  haveI : SecondCountableTopology (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (TA γ) := cenLC _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hUν : Uni ν := (hU _ ν hν).2 ((hT F n γ hreg).2.2.2 γ₁ hγ)
  have hPF : Pair μF (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν :=
    ⟨hUF, (cenClosed γ₁).isClosedEmbedding_subtypeVal, hUν⟩
  have sF := hS (G1 F n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA F n) (TA γ) μF
    (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν l hPF hl eF eT (TA γ).subtype
    (fun x => heT x)
  have hPE : Pair μE j ν := ⟨hUE, hj, hUν⟩
  have sE := hS (G1 E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA E n) (TA γ) μE j ν l hPE hl eE eT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype)
    (fun x => by
      rw [heE, MonoidHom.comp_apply, Subgroup.subtype_apply, heT, map_mul, hjv])
  refine ⟨(ν.prod l).map eT, sF.1.2.2.1, ?_, ?_⟩
  · intro Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA F n), FF γ Φ ((TA γ).subtype t * g) = FF γ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have hc : ((t : GA F n) * g)⁻¹ * AdelicGLn.diagonal F n γ * ((t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal F n γ * g := by
        rw [_root_.mul_inv_rev, mul_assoc g⁻¹, mul_assoc g⁻¹, mul_assoc, ← mul_assoc _ (t : GA F n) g, ← ht]
        group
      simp only [FF, Subgroup.subtype_apply, hc]
    rw [← (sF.2 (FF γ Φ) hΦ inv)]
    have hx : (fun x : G1 F n => FF γ Φ (eF (x, 1))) = fun x => avg Φ (x⁻¹ * γ₁ * x) := by
      funext x
      have h1 : eF (x, 1) = (x : GA F n) := by
        change (x : GA F n) * centralSection F n 1 = x
        rw [map_one, mul_one]
      rw [h1]
      simp only [FF, avg, Subgroup.coe_mul, Subgroup.coe_inv, hγ]
    rw [hx]
    rfl
  · intro δ hδ Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA E n),
        FE σ δ Φ (((mapGL n (adeleMap F E)).comp (TA γ).subtype) t * g) = FE σ δ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have h3 := (hN3 F E σ hσ n hn δ γ hreg hδ (mapGL n (adeleMap F E) (t : GA F n))).2 ⟨t, ht, rfl⟩
      have hc : (mapGL n (adeleMap F E) (t : GA F n) * g)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) g := by
        rw [map_mul, _root_.mul_inv_rev]
        calc _ = g⁻¹ * ((mapGL n (adeleMap F E) (t : GA F n))⁻¹ * AdelicGLn.diagonal E n δ *
              mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n))) * mapGL n (galAd σ) g := by group
          _ = _ := by rw [h3]
      simp only [FE, MonoidHom.comp_apply, Subgroup.subtype_apply, hc]
    rw [← (sE.2 (FE σ δ Φ) hΦ inv)]
    have h1 : ∀ x : G1 E n, eE (x, 1) = (x : GA E n) := by
      intro x
      rw [heE]
      simp only [map_one, mul_one]
    have hm : ∀ x : G1 E n, (x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n) ∈
        normOneGL (K := E) (n := n) := by
      intro x
      have hx : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, (hN5 F E σ hσ n hn).2.2, hx, diag_mem]
      simp
    have hx : (fun x : G1 E n => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ *
        mapGL n (galAd σ) (x : GA E n))) = fun x => FE σ δ Φ (eE (x, 1)) := by
      funext x
      rw [h1, ext0, dite_eq_left (hm x)]
      rfl
    rw [hx]
    have hmeas : Measurable fun x : G1 E n => FE σ δ Φ (eE (x, 1)) := by
      simp only [h1]
      exact hΦ.comp measurable_subtype_coe
    have hinv : ∀ (t : Subgroup.centralizer {γ₁}) (g : G1 E n),
        FE σ δ Φ (eE (j t * g, 1)) = FE σ δ Φ (eE (g, 1)) := by
      intro t g
      have h2 := inv (eT (t, 1)) (g : GA E n)
      have h4 : ((mapGL n (adeleMap F E)).comp (TA γ).subtype) (eT (t, 1)) = (j t : GA E n) := by
        rw [MonoidHom.comp_apply, Subgroup.subtype_apply, heT, hjv]
        simp only [map_one, mul_one]
      rw [h4] at h2
      rw [h1, h1]
      simpa using h2
    have hq := hQ (GA E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) (normOneGL (K := E) (n := n)) isClosed_normOneGL
      μE j ν hPE _ hmeas hinv
    have hj' : (fun t : Subgroup.centralizer {γ₁} => (j t : GA E n)) =
        fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) := funext hjv
    rw [hj'] at hq
    exact hq
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductExtensionOfBaseRegroup
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Filter

namespace UpperTheory.ConvolutionTheory.T4.RPGroup

section
universe u
variable {W V : Type} {I : V → Type}

private theorem exists_fam (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    {X : W → Type u} (T : ∀ v (i : I v), X (ι v i)) :
    ∃ f : ∀ w, X w, ∀ v i, f (ι v i) = T v i := by
  have h : ∀ w, ∃ x : X w, ∀ v i (h : ι v i = w), h ▸ T v i = x := by
    intro w
    obtain ⟨v, i, rfl⟩ := hs w
    refine ⟨T v i, fun v' i' h => ?_⟩
    have hv : v' = v := by rw [← hb v' i', h, hb]
    subst hv
    have hi : i' = i := hinj v' h
    subst hi
    rfl
  choose f hf using h
  exact ⟨f, fun v i => (hf _ v i rfl).symm⟩

private theorem ev_up [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    {P : W → Prop} (h : ∀ᶠ w in cofinite, P w) : ∀ᶠ v in cofinite, ∀ i, P (ι v i) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image b).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  exact ⟨ι v i, hi, hb v i⟩

private theorem ev_down [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hs : ∀ w, ∃ v i, ι v i = w) {P : V → Prop} (h : ∀ᶠ v in cofinite, P v) :
    ∀ᶠ w in cofinite, P (b w) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.biUnion fun v _ => Set.finite_range (ι v)).subset fun w hw => ?_
  obtain ⟨v, i, rfl⟩ := hs w
  simp only [Set.mem_setOf_eq, hb] at hw
  exact Set.mem_biUnion hw ⟨i, rfl⟩

variable {G Gi : Type} {H : W → Type} {Gv : V → Type} [Group G] [Group Gi] [∀ w, Group (H w)]
  [∀ v, Group (Gv v)] [TopologicalSpace G] [TopologicalSpace Gi] [∀ w, TopologicalSpace (H w)]
  [∀ v, TopologicalSpace (Gv v)] [T2Space Gi] [∀ v, T2Space (Gv v)]

private theorem rp_group [∀ v, Finite (I v)] {q : G →* Gi} {p : ∀ w, G →* H w} {K : ∀ w, Subgroup (H w)}
    (hRP : RP q p K) (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    (e : ∀ v, Gv v ≃ₜ* ∀ i : I v, H (ι v i)) (p' : ∀ v, G →* Gv v) (K' : ∀ v, Subgroup (Gv v))
    (hp : ∀ v i g, e v (p' v g) i = p (ι v i) g)
    (hK : ∀ v x, x ∈ K' v ↔ ∀ i, e v x i ∈ K (ι v i)) : RP q p' K' := by
  have hcp : ∀ v, Continuous (p' v) := by
    intro v
    have h : ⇑(p' v) = fun g => (e v).symm (fun i => p (ι v i) g) := by
      funext g
      apply (e v).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact funext fun i => hp v i g
    rw [h]
    exact (e v).symm.continuous.comp (continuous_pi fun i => hRP.cp _)
  have hKset : ∀ v, (K' v : Set (Gv v)) = e v ⁻¹' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
    intro v
    ext x
    simp only [SetLike.mem_coe, hK, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine ⟨hRP.cq, hcp, fun v => ?_, fun v => ?_, fun g => ?_, fun S => ?_, fun g g' hq h => ?_,
    fun gi gv hgv => ?_, fun Ci C hCi hC hev => ?_⟩
  · rw [hKset]
    exact (isOpen_set_pi Set.finite_univ fun i _ => hRP.opn _).preimage (e v).continuous
  · have h : (K' v : Set (Gv v)) = (e v).symm '' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
      rw [hKset]
      ext x
      constructor
      · intro hx
        exact ⟨e v x, hx, (e v).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [Set.mem_preimage] using hy
    rw [h]
    exact (isCompact_univ_pi fun i => hRP.cpt _).image (e v).symm.continuous
  · refine (ev_up ι b hb (hRP.ae g)).mono fun v h => ?_
    rw [hK]
    intro i
    rw [hp]
    exact h i
  · have hfin : (⋃ v ∈ (S : Set V), Set.range (ι v)).Finite :=
      S.finite_toSet.biUnion fun v _ => Set.finite_range (ι v)
    have hmem : ∀ w, w ∈ hfin.toFinset ↔ b w ∈ S := by
      intro w
      rw [Set.Finite.mem_toFinset]
      constructor
      · intro h
        obtain ⟨v, hv, i, rfl⟩ := Set.mem_iUnion₂.1 h
        rw [hb]
        exact hv
      · intro h
        obtain ⟨v, i, rfl⟩ := hs w
        rw [hb] at h
        exact Set.mem_biUnion h ⟨i, rfl⟩
    have h : (US p' K' S : Set G) = US p K hfin.toFinset := by
      ext g
      simp only [SetLike.mem_coe, mem_US]
      constructor
      · intro h w hw
        obtain ⟨v, i, rfl⟩ := hs w
        have hv : v ∉ S := by
          rw [hmem, hb] at hw
          exact hw
        have := (hK v _).1 (h v hv) i
        rwa [hp] at this
      · intro h v hv
        rw [hK]
        intro i
        rw [hp]
        exact h _ (by rw [hmem, hb]; exact hv)
    rw [h]
    exact hRP.opnU _
  · refine hRP.ext g g' hq fun w => ?_
    obtain ⟨v, i, rfl⟩ := hs w
    rw [← hp, ← hp, h]
  · obtain ⟨gw, hgw⟩ := exists_fam ι b hb hinj hs (X := H) fun v i => e v (gv v) i
    have hae : ∀ᶠ w in cofinite, gw w ∈ K w := by
      refine (ev_down ι b hb hs hgv).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hgw]
      exact (hK v _).1 h i
    obtain ⟨g, hq, hpg⟩ := hRP.surj gi gw hae
    refine ⟨g, hq, fun v => (e v).injective (funext fun i => ?_)⟩
    rw [hp, hpg, hgw]
  · obtain ⟨D, hD⟩ := exists_fam ι b hb hinj hs (X := fun w => Set (H w))
      fun v i => (fun x => e v x i) '' C v
    have hDc : ∀ w, IsCompact (D w) := by
      intro w
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hD]
      exact (hC v).image ((continuous_apply i).comp (e v).continuous)
    have hDe : ∀ᶠ w in cofinite, D w ⊆ K w := by
      refine (ev_down ι b hb hs hev).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hD]
      rintro _ ⟨x, hx, rfl⟩
      exact (hK v x).1 (h hx) i
    have hA := hRP.prop Ci D hCi hDc hDe
    have hcl : IsClosed {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} := by
      have h : {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} = q ⁻¹' Ci ∩ ⋂ v, p' v ⁻¹' C v := by
        ext g
        simp
      rw [h]
      exact (hCi.isClosed.preimage hRP.cq).inter
        (isClosed_iInter fun v => (hC v).isClosed.preimage (hcp v))
    refine hA.of_isClosed_subset hcl ?_
    rintro g ⟨h1, h2⟩
    refine ⟨h1, fun w => ?_⟩
    obtain ⟨v, i, rfl⟩ := hs w
    rw [hD, ← hp]
    exact ⟨_, h2 v, rfl⟩

end

end UpperTheory.ConvolutionTheory.T4.RPGroup

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic in
theorem UpperTheory.restrictedProduct_extension_of_base_regroup :
    RPF → RPE := by
  intro hF F E _ _ _ _ _ n
  refine UpperTheory.ConvolutionTheory.T4.RPGroup.rp_group (I := fun v : Pl F => PlacesOver E v) (hF E n)
    (fun v i => i.1) (below F) (fun v i => (below_eq_iff i.1 v).2 i.2)
    (fun v => Subtype.val_injective)
    (fun w => ⟨below F w, ⟨w, (below_eq_iff w _).1 rfl⟩, rfl⟩)
    (fun v => glPiEquiv (Fin n) fun w : PlacesOver E v => w.1.adicCompletion E)
    (fun v => pE E n v) (fun v => KE E n v) ?_ ?_
  · intro v i g
    refine Units.ext ?_
    ext a b
    rfl
  · intro v x
    have h : ∀ w : PlacesOver E v,
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) x =
          glPiEquiv (Fin n) (fun w : PlacesOver E v => w.1.adicCompletion E) x w := by
      intro w
      refine Units.ext ?_
      ext a b
      rfl
    change (∀ w : PlacesOver E v, _ ∈ _) ↔ _
    exact forall_congr' fun w => by rw [h w]
end
