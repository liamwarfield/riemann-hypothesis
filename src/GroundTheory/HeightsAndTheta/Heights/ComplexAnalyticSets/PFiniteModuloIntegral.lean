module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

def germCompRingHom {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    Germ (𝓝 (L x)) ℂ →+* Germ (𝓝 x) ℂ where
  toFun s := s.compTendsto L (L.continuous.tendsto x)
  map_one' := rfl
  map_mul' s t := Germ.inductionOn₂ s t fun _ _ => rfl
  map_zero' := rfl
  map_add' s t := Germ.inductionOn₂ s t fun _ _ => rfl

def holGermsPullback {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    holGerms (L x) →+* holGerms x :=
  ((germCompRingHom x L).comp (holGerms (L x)).subtype).codRestrict (holGerms x) fun s => by
    obtain ⟨b, hb, hbs⟩ := s.2
    refine ⟨b ∘ L, hb.comp (L.analyticAt x), ?_⟩
    show _ = germCompRingHom x L s.1
    rw [← hbs]
    rfl

theorem FiniteModuloIntegral.proof : FiniteModuloIntegral.Statement := by
  classical
  intro σ τ _ _ x k f L hf hfin g hg
  obtain ⟨n, e, he, hrep⟩ := hfin
  set φ := holGermsPullback x L with hφdef
  set I : Ideal (holGerms x) :=
    Ideal.span (Set.range fun i => (⟨f i, f i, hf i, rfl⟩ : holGerms x)) with hIdef
  let _ : Algebra (holGerms (L x)) (holGerms x ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  have hsmul : ∀ (s : holGerms (L x)) (q : holGerms x),
      s • Ideal.Quotient.mk I q = Ideal.Quotient.mk I (φ s * q) := by
    intro s q
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp

  have hfg : Module.Finite (holGerms (L x)) (holGerms x ⧸ I) := by
    refine ⟨⟨Finset.univ.image fun m => Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩, ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨⟨_, u, hu, rfl⟩, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, h, hb, hh, hev⟩ := hrep u hu
    have hq : Ideal.Quotient.mk I ⟨u, u, hu, rfl⟩ = ∑ m, (⟨b m, b m, hb m, rfl⟩ : holGerms (L x)) •
        Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩ := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hsmul, ← map_sum]
      rw [Ideal.Quotient.eq]
      have hmem : ∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩ ∈ I :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      convert hmem using 1
      apply Subring.subtype_injective
      have e1 : (holGerms x).subtype ((⟨u, u, hu, rfl⟩ : holGerms x) -
          ∑ m, φ ⟨b m, b m, hb m, rfl⟩ * ⟨e m, e m, he m, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (u - ∑ m, (b m ∘ L) * e m) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, map_mul]
        rfl
      have e2 : (holGerms x).subtype (∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul]
        rfl
      rw [e1, e2]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev] with z hz
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Function.comp_apply]
      rw [hz]
      ring
    rw [hq]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have := Algebra.IsIntegral.of_finite (holGerms (L x)) (holGerms x ⧸ I)

  obtain ⟨p, hpm, hp⟩ :=
    Algebra.IsIntegral.isIntegral (R := holGerms (L x)) (Ideal.Quotient.mk I ⟨g, g, hg, rfl⟩)
  rw [RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem,
    hpm.as_sum] at hp
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  choose a ha hae using fun j : ℕ => (p.coeff j).2
  choose h hh hhe using fun i => (c i).2
  refine ⟨p.natDegree, fun j => a j, h, fun j => ha j, hh, ?_⟩
  have hcI : ∀ i, (holGerms x).subtype (c i) = Germ.coeRingHom (𝓝 x) (h i) := fun i => (hhe i).symm
  have hφI : ∀ j, (holGerms x).subtype (φ (p.coeff j)) = Germ.coeRingHom (𝓝 x) (a j ∘ L) := by
    intro j
    show germCompRingHom x L (p.coeff j).1 = _
    rw [← hae j]
    rfl
  have hgerm : Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) = Germ.coeRingHom (𝓝 x)
      (g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, (a j ∘ L) * g ^ j) := by
    have := congrArg (holGerms x).subtype hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, map_pow, hcI, hφI] at this ⊢
    exact this
  filter_upwards [Germ.coe_eq.1 hgerm] with z hz
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply] at hz
  rw [Fin.sum_univ_eq_sum_range (fun j => a j (L z) * g z ^ j), hz]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem IsolatedFibreNear.proof (hFin : CompactHolomorphicFibreFinite.Statement) :
    IsolatedFibreNear.Statement := by
  intro σ _ X w d A hX hiso
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have memX : ∀ z, z ∈ N → (∀ i, f i z = 0) → z ∈ X := fun z hz h0 => by
    have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hz, h0⟩
    exact this.1
  have zerosX : ∀ z, z ∈ X → z ∈ N → ∀ i, f i z = 0 := fun z hzX hzN => by
    have : z ∈ X ∩ N := ⟨hzX, hzN⟩
    rw [hXN] at this
    exact this.2
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall (x := w)).mem_iff.1 (inter_mem (hN.mem_nhds hwN) hW)
  have hBN : closedBall w r ⊆ N := fun z hz => (hrsub hz).1
  have hBW : closedBall w r ⊆ W := fun z hz => (hrsub hz).2

  set g : (σ → ℂ) → (Fin k → ℂ) := fun z i => f i z with hg
  have hgc : ContinuousOn g (closedBall w r) :=
    continuousOn_pi.2 fun i => ((hf i).continuousOn).mono hBN
  set K := sphere w r ∩ g ⁻¹' {0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_sphere w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed isClosed_sphere isClosed_singleton
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, ⟨hzs, hz0⟩, hzA⟩
    have hzB : z ∈ closedBall w r := sphere_subset_closedBall hzs
    have hz0' : ∀ i, f i z = 0 := fun i => congrFun hz0 i
    have hzw : z = w := hWiso z ⟨memX z (hBN hzB) hz0', hBW hzB⟩ hzA
    rw [mem_sphere, hzw, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.1 ((hKc.image A.continuous).isClosed.isOpen_compl) (A w) hAK
  refine ⟨ball w r ∩ A ⁻¹' ball (A w) ε, ?_, ?_⟩
  · exact inter_mem (ball_mem_nhds w hr) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
  rintro x ⟨hxX, hxB, hxD⟩

  set F := {z | z ∈ ball w r ∧ (∀ i, f i z = 0) ∧ A z = A x} with hF
  have hFeq : F = closedBall w r ∩ (fun z => (g z, A z)) ⁻¹' {(0, A x)} := by
    ext z
    simp only [hF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, hg, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hzb, h0, hzA⟩
      exact ⟨ball_subset_closedBall hzb, h0, hzA⟩
    · rintro ⟨hzb, h0, hzA⟩
      refine ⟨?_, h0, hzA⟩
      rcases (mem_closedBall.1 hzb).lt_or_eq with hlt | heq
      · exact mem_ball.2 hlt
      · exfalso
        have hzK : z ∈ K := ⟨mem_sphere.2 heq, by funext i; exact h0 i⟩
        apply hεsub (show A z ∈ ball (A w) ε by rw [funext hzA]; exact hxD)
        exact ⟨z, hzK, rfl⟩
  have hFc : IsCompact F := by
    rw [hFeq]
    refine (isCompact_closedBall w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.prodMk A.continuous.continuousOn).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U : Set (Fin n → ℂ) := L.symm ⁻¹' ball w r with hU
  set h : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hh
  set y : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) (A x) with hy
  have hUo : IsOpen U := isOpen_ball.preimage L.symm.continuous
  have hhd : DifferentiableOn ℂ h U := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hh, Fin.append_left]
      exact ((hf i).differentiableOn.mono (ball_subset_closedBall.trans hBN)).comp
        L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hh, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U ∧ h v = y} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU, hF, hh, hy]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨hv, fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, h0, hA⟩
      refine ⟨hv, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [h0 i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U ∧ h v = y} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U h y hUo hhd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  refine ⟨ball w r \ (F \ {x}), ?_, ?_⟩
  · exact (isOpen_ball.sdiff (hFfin.sdiff).isClosed).mem_nhds ⟨hxB, fun hx => hx.2 rfl⟩
  rintro x' ⟨hx'X, hx'B, hx'F⟩ hx'A
  by_contra hne
  exact hx'F ⟨⟨hx'B, zerosX x' hx'X (hBN (ball_subset_closedBall hx'B)), hx'A⟩, hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
