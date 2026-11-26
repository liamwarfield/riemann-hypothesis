module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicZeroSetDimH

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreSFlatAscent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem isWeaklyRegular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {rs : List R}
    (h : IsWeaklyRegular R rs) : IsWeaklyRegular S (rs.map e) :=
  (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => by simp [smul_eq_mul]))).mp h

theorem min_add_le_min_add_min {k a b : WithBot ℕ∞} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min k (a + b) ≤ min k a + min k b := by
  rcases le_total k a with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hk hb))
  rcases le_total k b with h' | h'
  · rw [min_eq_left h']
    exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hk ha))
  rw [min_eq_right h, min_eq_right h']
  exact min_le_right _ _

theorem SerreSFlatAscent.proof (hD : FlatDimFormula.Statement) (hR : FlatLocalRegularSequence.Statement) :
    SerreSFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hSA hfib P _
  set p : Ideal A := P.comap (algebraMap A B) with hp
  have : P.LiesOver p := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p P
  have hAp : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ hA
  have hBP : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hB

  have hJ : (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P)) (Ideal.map (algebraMap A B) p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotEquivOfEq hJ
  obtain ⟨rs, hrs, hrsreg, hrslen⟩ := hSA p
  obtain ⟨ts, hts, htsreg, htslen⟩ := hfib P
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.map (algebraMap B (Localization.AtPrime P))
    (Ideal.map (algebraMap A B) p)))
  have hg : ∀ t, Ideal.Quotient.mk _ (g t) = t := Function.surjInv_eq _
  set ys := ts.map g with hys
  have hysmap : ys.map (Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)))) = ts.map e.symm := by
    rw [hys, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    rw [Function.comp_apply]
    conv_rhs => rw [← hg t]
    simp [e]
  have hysmem : ∀ y ∈ ys, y ∈ maximalIdeal (Localization.AtPrime P) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    have := hts t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun hu => this (hg t ▸ hu.map _)
  have hreg := hR _ _ hAp hBP inferInstance inferInstance rs ys hrs hrsreg hysmem
    (hysmap ▸ isWeaklyRegular_map_ringEquiv e.symm htsreg)
  have hdim := hD _ _ hAp hBP inferInstance inferInstance
  rw [ringKrullDim_eq_of_ringEquiv e] at hdim
  refine ⟨rs.map (algebraMap _ _) ++ ys, ?_, hreg, ?_⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
      exact map_nonunit _ r (hrs r hr)
    · exact hysmem u hu
  · rw [hdim, List.length_append, List.length_map, hys, List.length_map, Nat.cast_add]
    refine (min_add_le_min_add_min (by simp) ringKrullDim_nonneg_of_nontrivial
      ringKrullDim_nonneg_of_nontrivial).trans ?_
    exact add_le_add hrslen htslen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationCotangentIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Matrix

theorem derivation_mem_of_mem_sq {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)
  · rw [map_add (f := _)]; exact P.add_mem ha hb

theorem mem_of_derivation_det_not_mem {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by
  set A : Matrix (Fin h) (Fin h) T := Matrix.of fun i j => D j (f i) with hA

  have hv : ∀ j, (b ᵥ* A) j ∈ P := by
    intro j
    have h1 := derivation_mem_of_mem_sq P (D j) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sum] at h1
    have h2 : (∑ i, b i * f i) * D j t ∈ P :=
      P.mul_mem_right _ (P.sum_mem fun i _ => P.mul_mem_left _ (hf i))
    have h3 : t * ∑ i, D j (b i * f i) ∈ P := by
      have := P.sub_mem h1 h2; simpa using this
    have h4 : ∑ i, D j (b i * f i) ∈ P :=
      ((Ideal.IsPrime.mem_or_mem inferInstance h3).resolve_left ht)
    have h5 : ∑ i, D j (b i * f i) - ∑ i, f i * D j (b i) = (b ᵥ* A) j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.of_apply, Derivation.leibniz, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← h5]
    exact P.sub_mem h4 (P.sum_mem fun i _ => P.mul_mem_right _ (hf i))

  have hw : (b ᵥ* A ᵥ* A.adjugate) i = A.det * b i := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Pi.smul_apply, smul_eq_mul]
  have hmem : (b ᵥ* A ᵥ* A.adjugate) i ∈ P := by
    simp only [Matrix.vecMul, dotProduct]
    exact P.sum_mem fun j _ => P.mul_mem_right _ (hv j)
  rw [hw] at hmem
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left hdet

theorem DerivationCotangentIndependent.proof : DerivationCotangentIndependent.Statement := by
  intro T _ P _ h D f hf hdet a hsum i

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl (Finset.univ : Finset (Fin h)) a
  choose b hb using fun k => hs k (Finset.mem_univ k)

  have hmax : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap T (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hsq : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) ∈ (P ^ 2).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_pow, ← hmax]
    have : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) =
        algebraMap T (Localization.AtPrime P) (s : T) * ∑ k, a k * algebraMap T (Localization.AtPrime P) (f k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Finset.mul_sum, hb, Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨⟨y, hy⟩, u⟩, hyu⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 hsq
  rw [← map_mul] at hyu
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 hyu
  have hbi : b i ∈ P := by
    refine mem_of_derivation_det_not_mem P D f hf hdet b ((c : T) * (u : T)) ?_ ?_ i
    · exact (P.primeCompl.mul_mem c.2 u.2 : _)
    · have : (c : T) * (u : T) * ∑ k, b k * f k = (c : T) * y := by rw [← hc]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hy

  have hsa : algebraMap T (Localization.AtPrime P) (s : T) * a i ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← Algebra.smul_def, ← hb i]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hbi
  have hs' : algebraMap T (Localization.AtPrime P) (s : T) ∉ maximalIdeal (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]; exact s.2
  exact ((maximalIdeal.isMaximal (Localization.AtPrime P)).isPrime.mem_or_mem hsa).resolve_left hs'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermProjectionImageNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

theorem le_of_isolated_fibres (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hy0)
  obtain ⟨y, hy⟩ := hfi e d (ball y0 ρ) φ hlt isOpen_ball ⟨y0, mem_ball_self hρ⟩
    (hφ.mono (ball_subset_closedBall.trans hρO))
  obtain ⟨p, hpK, hpacc⟩ := hy.exists_accPt_of_subset_isCompact (isCompact_closedBall y0 ρ)
    (fun t ht => ball_subset_closedBall ht.1)
  have hpO : p ∈ O := hρO hpK
  have hcl : p ∈ closure {t | t ∈ ball y0 ρ ∧ φ t = y} := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨q, hq, -⟩ := accPt_iff_nhds.1 hpacc U hU
    exact ⟨q, hq⟩
  have hφp : φ p = y := by
    have h1 := mem_closure_image ((hφ p hpO).differentiableAt (hO.mem_nhds hpO)).continuousAt hcl
    have h2 : φ '' {t | t ∈ ball y0 ρ ∧ φ t = y} ⊆ {y} := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    simpa using closure_mono h2 h1
  obtain ⟨W, hW, hWiso⟩ := hiso p hpO
  obtain ⟨q, ⟨hqW, hqB, hqy⟩, hqp⟩ := accPt_iff_nhds.1 hpacc W hW
  exact hqp (hWiso q hqW (hρO (ball_subset_closedBall hqB)) (hqy.trans hφp.symm))

theorem IrreducibleGermProjectionImageNear.proof (hdim : IrreducibleGermRegularDimGe.Statement)
    (hisoN : IsolatedFibreNear.Statement) (hreg : RegularLocusDense.Statement)
    (hopen : HolomorphicIsolatedFibreOpen.Statement) (hfi : HolomorphicFibreInfinite.Statement) :
    IrreducibleGermProjectionImageNear.Statement := by
  intro σ _ X w d A hX hirr hfin hnd
  obtain ⟨N1, hN1, hdimN⟩ := hdim σ X w d A hX hirr hfin hnd
  obtain ⟨N2, hN2, hisoX⟩ := hisoN σ X w d A hX hfin
  obtain ⟨N3, hN3o, hwN3, hdense⟩ := hreg σ X w hX
  refine ⟨interior (N1 ∩ N2) ∩ N3,
    inter_mem (interior_mem_nhds.2 (inter_mem hN1 hN2)) (hN3o.mem_nhds hwN3), ?_⟩
  have hBo : IsOpen (interior (N1 ∩ N2) ∩ N3) := isOpen_interior.inter hN3o
  rintro x ⟨hxX, hxB⟩ h hh hvan
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hvan
  set V1 := V ∩ (interior (N1 ∩ N2) ∩ N3) ∩ A ⁻¹' ball (A x) ε with hV1
  have hV1o : IsOpen V1 := (hVo.inter hBo).inter (isOpen_ball.preimage A.continuous)
  have hxV1 : x ∈ V1 := ⟨⟨hxV, hxB⟩, by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩
  have hcl := hdense V1 hV1o (fun z hz => hz.1.2.2) ⟨hxX, hxV1⟩
  obtain ⟨r, hr⟩ : (regLocus (X ∩ V1)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hcl
    exact hcl
  obtain ⟨hrX, e, A', O, V', g, hO, hV', hrV', hg, hA'g, hXV'⟩ := hr
  have hgX : ∀ t ∈ O, g t ∈ X ∩ V1 := fun t ht => by
    have : g t ∈ X ∩ V1 ∩ V' := hXV' ▸ mem_image_of_mem g ht
    exact this.1
  have hN12 : ∀ z ∈ V1, z ∈ N1 ∩ N2 := fun z hz => interior_subset hz.1.2.1
  have hchart : X ∩ (V1 ∩ V') = g '' O := by rw [← hXV']; exact (inter_assoc X V1 V').symm
  have hde : d ≤ e := hdimN r ⟨hrX.1, (hN12 r hrX.2).1⟩ e A' O (V1 ∩ V') g hO (hV1o.inter hV')
    ⟨hrX.2, hrV'⟩ hg hA'g hchart
  have hφ : DifferentiableOn ℂ (fun y => A (g y)) O :=
    A.differentiable.comp_differentiableOn hg.differentiableOn
  have hisoC : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → A (g v) = A (g t) → v = t := by
    intro t ht
    obtain ⟨W, hW, hiW⟩ := hisoX (g t) ⟨(hgX t ht).1, (hN12 _ (hgX t ht).2).2⟩
    refine ⟨g ⁻¹' W, (hg t ht).continuousAt.preimage_mem_nhds hW, fun v hvW hvO hv => ?_⟩
    have hgv := hiW (g v) ⟨(hgX v hvO).1, hvW⟩ hv
    rw [← hA'g v hvO, ← hA'g t ht, hgv]
  obtain ⟨y0, hy0O, hy0r⟩ : r ∈ g '' O := hXV' ▸ ⟨hrX, hrV'⟩
  have hed : e ≤ d := le_of_isolated_fibres hfi hO ⟨y0, hy0O⟩ hφ hisoC
  obtain rfl : e = d := le_antisymm hed hde
  have hop := hopen e O (fun y => A (g y)) y0 hO hy0O hφ (hisoC y0 hy0O) O (hO.mem_nhds hy0O)
  have hzero : ∀ y ∈ (fun y => A (g y)) '' O, h y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hV (hgX t ht).2.1.1 (hgX t ht).1
  have hAr : A (g y0) ∈ ball (A x) ε := (hgX y0 hy0O).2.2
  have hEq : EqOn h 0 (ball (A x) ε) :=
    hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hAr
      (Filter.mem_of_superset hop fun y hy => hzero y hy)
  filter_upwards [ball_mem_nhds (A x) hε] with y hy using hEq hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnbranchedFibreSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedFibreSections.proof : UnbranchedFibreSections.Statement := by
  intro σ _ X w B d A D δ N hP y₀ hy₀ hδ₀
  obtain ⟨_, _, hD, _, _, hprop, _, hδan, _, hcard, hchart, _⟩ := hP
  have hF0 : {x | x ∈ X ∩ B ∧ A x = y₀}.encard = N := hcard y₀ hy₀ hδ₀
  have hfin : {x | x ∈ X ∩ B ∧ A x = y₀}.Finite := Set.finite_of_encard_eq_coe hF0
  have ht : hfin.toFinset.card = N := by
    have h := hfin.encard_eq_coe_toFinset_card
    rw [hF0] at h
    exact_mod_cast h.symm
  let e : Fin N ≃ hfin.toFinset := (Finset.equivFinOfCardEq ht).symm
  have he : ∀ i, (e i : σ → ℂ) ∈ X ∩ B ∧ A (e i) = y₀ := fun i => hfin.mem_toFinset.mp (e i).2
  have hc : ∀ i : Fin N, ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ (e i : σ → ℂ) ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        X ∩ B ∩ V = g '' O := fun i => hchart _ (he i).1 (by rw [(he i).2]; exact hδ₀)
  choose O V g hO hV hxV hg hAg hXV using hc
  have hy₀O : ∀ i, y₀ ∈ O i := by
    intro i
    have hm : (e i : σ → ℂ) ∈ X ∩ B ∩ V i := ⟨(he i).1, hxV i⟩
    rw [hXV i] at hm
    obtain ⟨y', hy', hgy'⟩ := hm
    have h := hAg i y' hy'
    rw [hgy', (he i).2] at h
    rw [h]
    exact hy'
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp hD y₀ hy₀
  have hKD : Metric.closedBall y₀ (ρ / 2) ⊆ D :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρD
  set C := {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y₀ (ρ / 2)} with hCdef
  have hC : IsCompact C := hprop _ hKD (isCompact_closedBall _ _)
  have hC' : IsCompact (C \ ⋃ i, V i) := hC.diff (isOpen_iUnion hV)
  have hE : IsClosed (A '' (C \ ⋃ i, V i)) := (hC'.image A.continuous).isClosed
  have hy₀E : y₀ ∉ A '' (C \ ⋃ i, V i) := by
    rintro ⟨x, ⟨⟨hxXB, _⟩, hxV'⟩, hAx⟩
    have hxF : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hxXB, hAx⟩
    apply hxV'
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxF⟩, ?_⟩
    simpa using hxV (e.symm ⟨x, hxF⟩)
  have hnhds : Metric.ball y₀ (ρ / 2) ∩ (A '' (C \ ⋃ i, V i))ᶜ ∩ (⋂ i, O i) ∩ {y | δ y ≠ 0} ∈ 𝓝 y₀ := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Metric.ball_mem_nhds _ (by linarith)) (hE.isOpen_compl.mem_nhds hy₀E)) ?_) ?_
    · exact Filter.iInter_mem.mpr fun i => (hO i).mem_nhds (hy₀O i)
    · exact (hδan y₀ hy₀).continuousAt.eventually_ne hδ₀
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hrD : Metric.ball y₀ r ⊆ D := fun y hy =>
    hρD (Metric.ball_subset_ball (by linarith) (hrsub hy).1.1.1)
  refine ⟨r, g, hr, hrD, fun y hy => (hrsub hy).2,
    fun i y hy => hg i y (Set.mem_iInter.mp (hrsub hy).1.2 i), ?_⟩
  intro y hy
  obtain ⟨⟨⟨hyb, hyE⟩, hyO⟩, hyδ⟩ := hrsub hy
  have hyO' : ∀ i, y ∈ O i := Set.mem_iInter.mp hyO
  have hrange : {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y) := by
    ext x
    constructor
    · rintro ⟨hxXB, hAx⟩
      have hxC : x ∈ C := ⟨hxXB, by rw [hAx]; exact Metric.ball_subset_closedBall hyb⟩
      have hxU : x ∈ ⋃ i, V i := by
        by_contra hn
        exact hyE ⟨x, ⟨hxC, hn⟩, hAx⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hm : x ∈ X ∩ B ∩ V i := ⟨hxXB, hi⟩
      rw [hXV i] at hm
      obtain ⟨y', hy', rfl⟩ := hm
      have h := hAg i y' hy'
      rw [hAx] at h
      exact ⟨i, by rw [h]⟩
    · rintro ⟨i, rfl⟩
      have hm : g i y ∈ g i '' O i := ⟨y, hyO' i, rfl⟩
      rw [← hXV i] at hm
      exact ⟨hm.1, hAg i y (hyO' i)⟩
  refine ⟨?_, hrange⟩
  classical
  have hN : (Set.range (fun i => g i y)).encard = N := by
    rw [← hrange]
    exact hcard y (hrD hy) hyδ
  have himg : Set.range (fun i => g i y) = ↑(Finset.univ.image (fun i => g i y)) := by
    simp
  rw [himg, Set.encard_coe_eq_coe_finsetCard] at hN
  have hcardeq : (Finset.univ.image (fun i => g i y)).card = (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hN
  have hinj := Finset.card_image_iff.mp hcardeq
  intro i j hij
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ i)) (Finset.mem_coe.mpr (Finset.mem_univ j)) hij

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRueckertNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace RueckertNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz.exists_of_mem_holGermIdeal (k := k) (φ := φ) p hφ

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz.mem_holGermIdeal_of_eq (k := k) (p := p) (h := h) hp hh φ hφ

theorem proof (hNoeth : AnalyticGermsNoetherian.Statement) (hPrime : PrimeGermNullstellensatz.Statement) :
    RueckertNullstellensatz.Statement := by
  intro σ _ w k f g hf hg hvan
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  have : IsNoetherianRing (holGerms w) := hNoeth σ w

  have hrad : G ∈ (holGermIdeal w f).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hfP, hP⟩
    obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian P)
    choose p hp hps using fun j => (show ∃ q : (σ → ℂ) → ℂ, AnalyticAt ℂ q w ∧ (q : Germ (𝓝 w) ℂ) = s j from (s j).2)
    have hPeq : holGermIdeal w p = P := by
      rw [← hs, holGermIdeal]
      congr 1
      ext φ
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext (hj.trans (hps j)).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, (hps j).symm⟩
    have hfmem : ∀ i, (⟨(f i : Germ (𝓝 w) ℂ), f i, hf i, rfl⟩ : holGerms w) ∈ holGermIdeal w p := fun i =>
      hPeq ▸ hfP (Ideal.subset_span ⟨i, rfl⟩)
    choose c _ hc using fun i => exists_of_mem_holGermIdeal p (hfmem i)
    have hfev : ∀ᶠ z in 𝓝 w, ∀ i, f i z = ∑ j, c i j z * p j z :=
      eventually_all.2 fun i => Germ.coe_eq.1 (hc i)
    have hvanp : ∀ᶠ z in 𝓝 w, (∀ j, p j z = 0) → g z = 0 := by
      filter_upwards [hvan, hfev] with z hz hfz hpz
      exact hz fun i => by rw [hfz i]; simp [hpz]
    obtain ⟨h, hh, hgh⟩ := hPrime σ w r p g hp hg (hPeq ▸ hP) hvanp
    exact hPeq ▸ mem_holGermIdeal_of_eq hp hh G (Germ.coe_eq.2 hgh)

  obtain ⟨m, hm⟩ := hrad
  have hm' : G ^ (m + 1) ∈ holGermIdeal w f := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ G hm
  obtain ⟨h, hh, hgh⟩ := exists_of_mem_holGermIdeal f hm'
  refine ⟨m + 1, h, Nat.succ_pos m, hh, ?_⟩
  have hG : ((G ^ (m + 1) : holGerms w) : Germ (𝓝 w) ℂ) = ((g ^ (m + 1) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
    rw [Germ.coe_pow]
    rfl
  rw [hG] at hgh
  filter_upwards [Germ.coe_eq.1 hgh] with z hz
  simpa using hz

end RueckertNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscent
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscentLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

section FlatLocal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]

theorem isLocalRing_closedFibre :
    IsLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem ringKrullDim_eq_add_ringKrullDim_closedFibre [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have := isLocalRing_closedFibre (R := R) (S := S)
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]

theorem isRegularLocalRing_of_flat_of_closedFibre [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsRegularLocalRing R) (hF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by
  have : IsNoetherianRing R := by have := hR; infer_instance
  have := isLocalRing_closedFibre (R := R) (S := S)
  set J := (maximalIdeal R).map (algebraMap R S)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre (R := R), ← (isRegularLocalRing_iff R).mp hR,
    ← (isRegularLocalRing_iff (S ⧸ J)).mp hF]
  suffices h : (maximalIdeal S).spanFinrank ≤
      (maximalIdeal R).spanFinrank + (maximalIdeal (S ⧸ J)).spanFinrank by
    exact_mod_cast h
  have fgR := (maximalIdeal R).fg_of_isNoetherianRing
  have fgF := (maximalIdeal (S ⧸ J)).fg_of_isNoetherianRing
  set s := (maximalIdeal R).generators
  set t := (maximalIdeal (S ⧸ J)).generators
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let lift : S ⧸ J → S := Function.surjInv hsurj
  set t' := lift '' t
  have ht' : Ideal.Quotient.mk J '' t' = t := by
    rw [Set.image_image]
    simp [lift, Function.surjInv_eq hsurj]
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ hsurj
  have hcomap : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S :=
    maximalIdeal_comap _
  have heq : maximalIdeal S = Ideal.span (algebraMap R S '' s ∪ t') := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.map (Ideal.Quotient.mk J) (Ideal.span t') := by
        rw [Ideal.map_span, ht']
        change Ideal.Quotient.mk J x ∈ Submodule.span (S ⧸ J) t
        rw [Submodule.span_generators, ← Ideal.mem_comap, hcomap]
        exact hx
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker] at hx'
      rw [Ideal.span_union, sup_comm, ← Ideal.map_span]
      change x ∈ Submodule.span S t' ⊔ Ideal.map (algebraMap R S) (Submodule.span R s)
      rw [Submodule.span_generators]
      exact hx'
    · rw [Ideal.span_le, Set.union_subset_iff]
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        exact map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ (Submodule.FG.generators_mem _ hy))
      · rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, ← hcomap, Ideal.mem_comap, Function.surjInv_eq hsurj]
        exact Submodule.FG.generators_mem _ hy
  have fins := Submodule.FG.finite_generators fgR
  have fint := Submodule.FG.finite_generators fgF
  rw [heq, ← Submodule.FG.generators_ncard fgR, ← Submodule.FG.generators_ncard fgF]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite ((fins.image _).union (fint.image _))).trans ?_
  exact (Set.ncard_union_le _ _).trans (add_le_add (Set.ncard_image_le fins) (Set.ncard_image_le fint))

end FlatLocal

section Localized

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]

theorem map_maximalIdeal_localization_eq :
    letI := Localization.AtPrime.algebraOfLiesOver (P.under A) P
    (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P))
        (Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P)) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x

end Localized

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem SerreRFlatAscent.proof : SerreRFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hRA hfib P _ hdim
  have : IsNoetherianRing A := hA
  have : IsNoetherianRing B := hB
  have : Module.Flat A B := hflat
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have := isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)
  let e := Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A))
    (S := Localization.AtPrime P)
  have h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A)) :=
    ringKrullDim_nonneg_of_nontrivial
  have h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hsum] at hdim
  have hAk := (le_add_of_nonneg_right h0F).trans hdim
  have hFk := (le_add_of_nonneg_left h0A).trans hdim
  have hF : IsRegularLocalRing (primeFibreLocalRing A P) :=
    hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)
  exact isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTangentGraphLowerDensity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.inPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i))

def TangentGraphLowerDensity.outPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I} :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : {j : Fin n // j ∉ I} => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : {j : Fin n // j ∉ I} => innerSL ℂ (b j))

theorem TangentGraphLowerDensity.inPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by
  simp [TangentGraphLowerDensity.inPart]

theorem TangentGraphLowerDensity.outPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by
  simp [TangentGraphLowerDensity.outPart]

theorem TangentGraphLowerDensity.inPart_eq_toLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by
  refine PiLp.ext fun i => ?_
  simp [TangentGraphLowerDensity.inPart_apply, frameProj]

theorem TangentGraphLowerDensity.norm_sq_split {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by
  classical
  rw [← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply,
    OrthonormalBasis.repr_apply_apply]
  convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3
  congr 1; exact Subsingleton.elim _ _

theorem TangentGraphLowerDensity.proof : TangentGraphLowerDensity.Statement := by
  intro n d b I₀ S Ω V g w₀ hcard hΩ _hV hw₀ hg hproj hSV htan θ hθ
  classical
  set P := TangentGraphLowerDensity.inPart b I₀ with hPdef
  set Q := TangentGraphLowerDensity.outPart b I₀ with hQdef
  have hgd : DifferentiableAt ℂ g w₀ := hg.differentiableAt (hΩ.mem_nhds hw₀)

  have hQ0 : Q.comp (fderiv ℂ g w₀) = 0 := by
    refine ContinuousLinearMap.ext fun v => PiLp.ext fun j => ?_
    have h1 : HasFDerivAt (fun w => inner ℂ (b j) (g w))
        ((innerSL ℂ (b (j : Fin n))).comp (fderiv ℂ g w₀)) w₀ :=
      (innerSL ℂ (b (j : Fin n))).hasFDerivAt.comp w₀ hgd.hasFDerivAt
    have h2 := h1.fderiv
    rw [htan j j.2] at h2
    have h3 := congrArg (fun L => L v) h2
    simpa [hQdef, TangentGraphLowerDensity.outPart_apply] using h3.symm
  have hQd : HasFDerivAt (fun w => Q (g w)) (0 : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I₀}) w₀ := by
    have h := Q.hasFDerivAt.comp w₀ hgd.hasFDerivAt
    rw [hQ0] at h
    exact h

  obtain ⟨η, hη, hθη⟩ : ∃ η : ℝ, 0 < η ∧ θ * (1 + η) ^ (2 * d) < 1 := by
    have hc : Continuous fun η : ℝ => θ * (1 + η) ^ (2 * d) := by fun_prop
    have h0 : ∀ᶠ η in 𝓝 (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ.2)
    have h0' : ∀ᶠ η in 𝓝[>] (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 := nhdsWithin_le_nhds h0
    obtain ⟨η, h1, h2⟩ := (h0'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    exact ⟨η, h2, h1⟩
  have hlo := hasFDerivAt_iff_isLittleO.1 hQd
  have hev : ∀ᶠ w in 𝓝 w₀, ‖Q (g w) - Q (g w₀)‖ ≤ η * ‖w - w₀‖ ∧ w ∈ Ω := by
    refine ((hlo.def hη).mono fun w hw => ?_).and (hΩ.mem_nhds hw₀)
    simpa using hw
  obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨(1 + η) * δ, by positivity, fun ρ hρ => ?_⟩
  have h1η : 0 < 1 + η := by linarith
  set s := ρ / (1 + η) with hs
  have hs0 : 0 < s := div_pos hρ.1 h1η
  have hsδ : s < δ := by
    rw [hs, div_lt_iff₀ h1η]
    linarith [hρ.2]
  set x₀ : EuclideanSpace ℂ I₀ := WithLp.toLp 2 w₀ with hx₀
  have hPx : ∀ w ∈ Ω, P (g w) = WithLp.toLp 2 w := fun w hw => by
    rw [hPdef, TangentGraphLowerDensity.inPart_eq_toLp, hproj w hw]

  have hsub : Metric.ball x₀ s ⊆ P '' (S ∩ Metric.ball (g w₀) ρ) := by
    intro v hv
    have hv' : ‖v - x₀‖ < s := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have hww : ‖WithLp.ofLp v - w₀‖ ≤ ‖v - x₀‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simpa [hx₀] using PiLp.norm_apply_le (v - x₀) i
    have hwδ : dist (WithLp.ofLp v) w₀ < δ := by
      rw [dist_eq_norm]
      linarith
    obtain ⟨hQw, hwΩ⟩ := hδw hwδ
    refine ⟨g (WithLp.ofLp v), ⟨?_, ?_⟩, by rw [hPx _ hwΩ, WithLp.toLp_ofLp]⟩
    · have hm : g (WithLp.ofLp v) ∈ S ∩ V := hSV ▸ Set.mem_image_of_mem g hwΩ
      exact hm.1
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsplit := TangentGraphLowerDensity.norm_sq_split b I₀ (g (WithLp.ofLp v) - g w₀)
      have hPd : P (g (WithLp.ofLp v) - g w₀) = v - x₀ := by
        rw [map_sub, hPx _ hwΩ, hPx _ hw₀, WithLp.toLp_ofLp]
      have hQd' : Q (g (WithLp.ofLp v) - g w₀) = Q (g (WithLp.ofLp v)) - Q (g w₀) := map_sub _ _ _
      rw [← hPdef, ← hQdef, hPd, hQd'] at hsplit
      have hle : ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + ‖Q (g (WithLp.ofLp v)) - Q (g w₀)‖ := by
        nlinarith [norm_nonneg (g (WithLp.ofLp v) - g w₀), norm_nonneg (v - x₀),
          norm_nonneg (Q (g (WithLp.ofLp v)) - Q (g w₀))]
      calc ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + η * ‖v - x₀‖ := by nlinarith
        _ = (1 + η) * ‖v - x₀‖ := by ring
        _ < (1 + η) * s := by gcongr
        _ = ρ := by rw [hs]; field_simp

  have hd0 : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcardI : Fintype.card I₀ = d := by rw [Fintype.card_coe, hcard]
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFinOfCardEq hcardI)
  have hball : μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) =
      ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
    rw [← VarietyLelongMono.euclBall_measure d (L x₀) hs0, ← L.image_ball,
      L.isometry.hausdorffMeasure_image (Or.inl hd0)]
  have hLip : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    have h := TangentGraphLowerDensity.norm_sq_split b I₀ (x - y)
    rw [← hPdef, ← hQdef] at h
    nlinarith [norm_nonneg (P (x - y)), norm_nonneg (x - y), norm_nonneg (Q (x - y))]
  have hreal : θ * ρ ^ (2 * d) ≤ s ^ (2 * d) := by
    have hpos : 0 < (1 + η) ^ (2 * d) := by positivity
    have hρp : 0 ≤ ρ ^ (2 * d) := by have := hρ.1; positivity
    rw [hs, div_pow, le_div_iff₀ hpos]
    calc θ * ρ ^ (2 * d) * (1 + η) ^ (2 * d) = ρ ^ (2 * d) * (θ * (1 + η) ^ (2 * d)) := by ring
      _ ≤ ρ ^ (2 * d) * 1 := by gcongr
      _ = ρ ^ (2 * d) := mul_one _
  calc ENNReal.ofReal (θ * ρ ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1)
      ≤ ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
        gcongr
    _ = μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) := hball.symm
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (P '' (S ∩ Metric.ball (g w₀) ρ)) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ) := by
        have h := hLip.hausdorffMeasure_image_le hd0 (S ∩ Metric.ball (g w₀) ρ)
        simpa using h

end

end GroundTheory.Heights₂.Heights
end
