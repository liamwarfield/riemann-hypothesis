module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StarProjectionCommute
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CyclicScalar

theorem inner_map_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y

theorem map_inv_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have h : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

theorem orthogonal_stable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) (v : H) (hv : v ∈ Uᗮ) : σ g v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_inv_map σ g u, inner_map_map σ hσ]
  exact hv _ (hU _ _ hu)

theorem starProjection_commute {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) :
    U.starProjection * σ g = σ g * U.starProjection := by
  ext v
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : U.starProjection v ∈ U := Submodule.starProjection_apply_mem U v
  have h2 : v - U.starProjection v ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v) := by
    rw [← map_add (f := _)]; simp
  rw [h3, map_add (f := _), Submodule.starProjection_eq_self_iff.2 (hU g _ h1),
    (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]

theorem exists_isIrredSubrep : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W := by
  intro G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal
  haveI : CompleteSpace Q := hQ.completeSpace_coe

  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => σ g ξ)
  have hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
    intro g v hv
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact this hv
  have hW : IsSubrep σ S.topologicalClosure := isSubrep_topologicalClosure hSstable
  have horbit : ∀ g, σ g ξ ∈ S.topologicalClosure := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hξW : ξ ∈ S.topologicalClosure := by simpa using horbit 1

  have hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A := by
    intro A hA h
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA
    rintro _ ⟨g, rfl⟩
    exact h g

  have hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ) := by
    have hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous
    refine fun w hw => hmin _ hclosed (fun g => ?_) hw
    obtain ⟨c, hc⟩ := hscal g
    have e : σ g ξ = c • ξ + (σ g ξ - c • ξ) := by abel
    change Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)
    rw [e, map_add (f := _), (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul,
      Submodule.starProjection_eq_self_iff.2 hξQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)
  refine ⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩
  haveI : CompleteSpace U := hU.1.completeSpace_coe
  have hPc := starProjection_commute σ hσ U hU.2
  have hPQ : U.starProjection ξ ∈ Q := hcomm _ hPc ξ hξQ
  have hPU : U.starProjection ξ ∈ U := Submodule.starProjection_apply_mem U ξ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by
    have := hline _ (hUW hPU)
    rw [Submodule.starProjection_eq_self_iff.2 hPQ] at this
    exact Submodule.mem_span_singleton.1 this
  have hcc : c * c = c := by
    have h1 : U.starProjection (c • ξ) = c • ξ := by
      rw [hc]; exact Submodule.starProjection_eq_self_iff.2 hPU
    rw [map_smul, ← hc, smul_smul] at h1
    have h2 : (c * c - c) • ξ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc]; ring
    exact (mul_eq_zero.1 this).imp id sub_eq_zero.1
  rcases hc01 with rfl | rfl
  · left
    have hP0 : U.starProjection ξ = 0 := by rw [← hc, zero_smul]
    have hle : S.topologicalClosure ≤ Uᗮ := by
      refine hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_
      refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
      have := DFunLike.congr_fun (hPc g) ξ
      simpa [hP0] using this
    refine (Submodule.eq_bot_iff U).2 fun x hx => ?_
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)
  · right
    have hξU : ξ ∈ U := by
      rw [one_smul] at hc
      rw [hc]; exact hPU
    exact le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)

end GlobalTheory.CompanionTheory.CyclicScalar
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsMinimalOfOrthogonalBound
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.OrthoFamily

theorem exists_minimal_of_no_family_below
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Set (Submodule ℂ H))
    (hcl : ∀ S ∈ L, IsClosed (S : Set H))
    (hinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) (n : ℕ) :
    ∀ S ∈ L, S ≠ ⊥ →
      (∀ f : Fin n → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → (∀ i, f i ≤ S) →
        ¬ Pairwise fun i k => f i ⟂ f k) →
      ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact (hS (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)).elim
  | succ n ih =>
    intro S hSL hS0 hS
    by_cases hmin : ∀ T ∈ L, T ≤ S → T = ⊥ ∨ T = S
    · exact ⟨S, hSL, hS0, hmin⟩
    · push_neg at hmin
      obtain ⟨T, hTL, hTS, hT0, hTne⟩ := hmin
      refine ih T hTL hT0 ?_
      intro f hfL hf0 hfT hpw
      haveI : CompleteSpace T := (hcl T hTL).completeSpace_coe
      have hR0 : S ⊓ Tᗮ ≠ ⊥ := by
        intro h
        apply hTne
        have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTS
        rw [inf_comm, h, sup_bot_eq] at hsup
        exact hsup
      have ho : ∀ j, (S ⊓ Tᗮ) ⟂ f j := fun j => inf_le_right.trans (Submodule.orthogonal_le (hfT j))
      apply hS (Fin.cons (S ⊓ Tᗮ) f)
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hinf S hSL T hTL
        | succ j => rw [Fin.cons_succ]; exact hfL j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hR0
        | succ j => rw [Fin.cons_succ]; exact hf0 j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact inf_le_left
        | succ j => rw [Fin.cons_succ]; exact (hfT j).trans hTS
      · intro i k hik
        induction i using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact absurd rfl hik
          | succ j =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact ho j
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact (ho j).symm
          | succ j' =>
            rw [Fin.cons_succ, Fin.cons_succ]
            exact hpw (fun h => hik (congrArg Fin.succ h))

theorem exists_minimal_of_orthogonal_bound :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  intro H _ _ _ L m S₀ hcl hinf hS₀ hS₀0 hfam
  exact exists_minimal_of_no_family_below L hcl hinf (m + 1) S₀ hS₀ hS₀0
    (fun f hfL hf0 _ => hfam f hfL hf0)

end GlobalTheory.CompanionTheory.OrthoFamily
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SchurOnMinimalSubspace
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Factor

theorem schur_on_minimal_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ := by
  intro H _ _ _ N Q hstar hQc hQinv hmin A hcomm
  haveI : CompleteSpace Q := hQc.completeSpace_coe

  let σ : N → (Q →L[ℂ] Q) := fun T =>
    (T.1.comp Q.subtypeL).codRestrict Q (fun v => hQinv T.1 T.2 v v.2)
  have hσ : ∀ (T : N) (v : Q), ((σ T v : Q) : H) = T.1 v := fun _ _ => rfl

  have hperp : ∀ T ∈ N, ∀ w ∈ Qᗮ, T w ∈ Qᗮ := by
    intro T hT w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have h1 : ⟪u, T w⟫_ℂ = ⟪(star T) u, w⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hw _ (hQinv _ (hstar T hT) u hu)

  have hproj : ∀ T ∈ N, ∀ w : H, Q.starProjection (T w) = T (Q.starProjection w) := by
    intro T hT w
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact hQinv T hT _ (Submodule.starProjection_apply_mem Q w)
    · rw [← map_sub]
      exact hperp T hT _ (Submodule.sub_starProjection_mem_orthogonal w)
  let B : Q →L[ℂ] Q := (Q.orthogonalProjection).comp (A.comp Q.subtypeL)
  have hB : ∀ v : Q, ((B v : Q) : H) = Q.starProjection (A v) := fun _ => rfl
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur_of_adjoint_closed N Q σ
    (by
      intro g
      refine ⟨⟨star g.1, hstar g.1 g.2⟩, ?_⟩
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      change ⟪(star g.1) (x : H), (y : H)⟫_ℂ = ⟪(x : H), g.1 (y : H)⟫_ℂ
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left])
    (by
      intro S hS hSinv
      have hclosed : IsClosed ((S.map Q.subtype : Submodule ℂ H) : Set H) := by
        exact hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hS
      have hle : S.map Q.subtype ≤ Q := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hinv : ∀ T ∈ N, ∀ v ∈ S.map Q.subtype, T v ∈ S.map Q.subtype := by
        rintro T hT _ ⟨x, hx, rfl⟩
        exact ⟨σ ⟨T, hT⟩ x, hSinv ⟨T, hT⟩ x hx, rfl⟩
      rcases hmin _ hclosed hle hinv with h | h
      · left
        rw [eq_bot_iff]
        intro x hx
        have hx' : (x : H) ∈ S.map Q.subtype := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at hx'
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext hx')
      · right
        rw [eq_top_iff]
        intro x _
        have hx : (x : H) ∈ S.map Q.subtype := by
          rw [h]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy)
    B
    (by
      intro g
      ext v
      change Q.starProjection (A (g.1 v)) = g.1 (Q.starProjection (A v))
      have h := congrArg (fun X : H →L[ℂ] H => X (v : H)) (hcomm g.1 g.2)
      have h' : g.1 (A v) = A (g.1 v) := h
      rw [← h', hproj g.1 g.2])
  refine ⟨c, fun v hv => ?_⟩
  have h1 : Q.starProjection (A v) = c • v := by
    have := hB ⟨v, hv⟩
    rw [hc] at this
    simpa using this.symm
  rw [← h1]
  exact Submodule.sub_starProjection_mem_orthogonal _

end GlobalTheory.CompanionTheory.Factor
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BicommutantRestrictionPrime
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DirectFactor

theorem bicommutant_restriction_prime :
    ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0 := by
  intro G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy
  let W₀ : Submodule ℂ H := Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))
  have hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀ := fun g' h =>
    Submodule.subset_span ⟨(g', h), rfl⟩
  have hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀ := by
    intro g v hv
    obtain ⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k :=
      ⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩
    have hpg : π g = π (j (p g)) * π k := by
      have := congrArg π hg
      rwa [map_mul] at this
    have hKB : ∀ g', π k * π (j g') = π (j g') * π k := fun g' => by
      rw [← map_mul, ← map_mul, (hc g' k hk).eq]
    have hKy : π k * y = y * π k := hy (π k) hKB
    have a1 : ∀ v, π k (y v) = y (π k v) := fun v => DFunLike.congr_fun hKy v
    have a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v) := fun g' v =>
      DFunLike.congr_fun (hKB g') v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g', h⟩, rfl⟩ := hv
      have e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h)) := by
        rw [hpg, map_mul, map_mul]
        simp only [ContinuousLinearMap.mul_apply, a1, a2]
      simpa only [e] using hgen (p g * g') (π k h)
    | zero => simp
    | add u w _ _ hu hw => simpa only [map_add (f := _)] using W₀.add_mem hu hw
    | smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu
  have hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g', h⟩, rfl⟩
    exact DFunLike.congr_fun (hxy g') h
  rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop
  · exfalso
    apply hy0
    ext h
    have hm : y h ∈ W₀.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      simpa using hgen 1 h
    rw [hbot] at hm
    simpa using hm
  · ext h
    have hm : h ∈ W₀.topologicalClosure := by rw [htop]; trivial
    simpa using hker hm

end GlobalTheory.CompanionTheory.DirectFactor
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardPolynomialVanishesOnBicommutant
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Factor

open CompanionTheory.D.gk.admitted.FinOfPIAux

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_mem_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (C : Submodule ℂ (PiLp 2 (fun _ : ι => H))) (hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))))
    (hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S)
    (z : PiLp 2 (fun _ : ι => H)) (hz : z ∈ C) :
    diag T z ∈ C := by
  haveI : CompleteSpace C := hcl.completeSpace_coe
  have hPg := proj_comm (ι := ι) σ hσ C hC
  let Q : ι → ι → H →L[ℂ] H := fun k l =>
    (PiLp.proj 2 (fun _ : ι => H) k).comp (C.starProjection.comp (incl l))
  have hQ : ∀ k l, Q k l * T = T * Q k l := by
    intro k l
    apply hT
    intro g
    ext v
    simp only [Q, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    rw [← diag_incl, hPg, diag_apply]
  have hsum : ∀ w : PiLp 2 (fun _ : ι => H), ∀ k,
      (C.starProjection w).ofLp k = ∑ l, Q k l (w.ofLp l) := by
    intro w k
    conv_lhs => rw [← sum_incl w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Q, map_sum]
  have key : C.starProjection (diag T z) = diag T (C.starProjection z) := by
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, diag_apply, hsum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [diag_apply]
    exact congrArg (fun S : H →L[ℂ] H => S (z.ofLp l)) (hQ k l)
  have hz' : C.starProjection z = z := (Submodule.starProjection_eq_self_iff).2 hz
  rw [← hz', ← key]
  exact C.starProjection_apply_mem _

theorem sum_eq_zero_of_bicomm (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H)
    (hT : ∀ S : H →L[ℂ] H, (∀ g, S * σ g = σ g * S) → S * T = T * S) :
    ∑ k, L k (T (y k)) = 0 := by
  let y' : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 y
  let V : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    Submodule.span ℂ (Set.range fun g : G => diag (σ g) y')
  have hdiag_mul : ∀ a b : G, ∀ w : PiLp 2 (fun _ : ι => H),
      diag (σ a) (diag (σ b) w) = diag (σ (a * b)) w := by
    intro a b w
    ext k
    simp only [diag_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hCinv : ∀ g, ∀ z ∈ V.topologicalClosure, diag (σ g) z ∈ V.topologicalClosure := by
    intro g
    have hle : V ≤ V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show diag (σ g) (diag (σ b) y') ∈ V.topologicalClosure
      rw [hdiag_mul]
      exact V.le_topologicalClosure (Submodule.subset_span ⟨g * b, rfl⟩)
    have hcl' : IsClosed ((V.topologicalClosure.comap
        ((diag (σ g) : (PiLp 2 (fun _ : ι => H)) →L[ℂ] (PiLp 2 (fun _ : ι => H))) :
          (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] (PiLp 2 (fun _ : ι => H))) :
          Submodule ℂ (PiLp 2 (fun _ : ι => H))) : Set (PiLp 2 (fun _ : ι => H))) :=
      V.isClosed_topologicalClosure.preimage (diag (σ g)).continuous
    intro z hz
    exact Submodule.topologicalClosure_minimal V hle hcl' hz
  have hy' : y' ∈ V.topologicalClosure := by
    apply V.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    ext k
    simp [diag_apply]
  have hT' := diag_mem_of_bicomm σ hσ V.topologicalClosure V.isClosed_topologicalClosure
    hCinv T hT y' hy'
  let Λ : (PiLp 2 (fun _ : ι => H)) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ w : PiLp 2 (fun _ : ι => H), Λ w = ∑ k, L k (w.ofLp k) := by
    intro w
    simp [Λ]
  have hker : V.topologicalClosure ≤ LinearMap.ker (Λ : (PiLp 2 (fun _ : ι => H)) →ₗ[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply]
      simpa [y'] using h g
    · exact Λ.isClosed_ker
  have hfin := hker hT'
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΛ, diag_apply] at hfin
  simpa [y'] using hfin

end Diag

theorem standard_polynomial_vanishes_on_bicommutant (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (E : H →L[ℂ] H) (M : ℕ) (h : ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0)
    (a : Fin M → H →L[ℂ] H)
    (ha : ∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) :
    stdPoly E a = 0 := by
  classical
  have step : ∀ j : ℕ, ∀ g : Fin M → G,
      stdPoly E (fun i : Fin M => if (i : ℕ) < j then a i else σ (g i)) = 0 := by
    intro j
    induction j with
    | zero => intro g; simpa using h g
    | succ j ih =>
      intro g
      by_cases hj : j < M
      · let k : Fin M := ⟨j, hj⟩
        let b : Fin M → H →L[ℂ] H := fun i => if (i : ℕ) < j then a i else σ (g i)
        have hb : (fun i : Fin M => if (i : ℕ) < j + 1 then a i else σ (g i)) =
            Function.update b k (a k) := by
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            have hne : (i : ℕ) ≠ j := fun e => hik (Fin.ext e)
            by_cases hlt : (i : ℕ) < j
            · have h2 : (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
            · have h2 : ¬ (i : ℕ) < j + 1 := by omega
              simp [b, hlt, h2]
        obtain ⟨A, B, hAB⟩ := CompanionTheory.D.gk.admitted.FinOfPIAux.stdPoly_update E b k
        have hσk : ∀ x : G, stdPoly E (Function.update b k (σ x)) = 0 := by
          intro x
          have hx := ih (Function.update g k x)
          convert hx using 2
          funext i
          by_cases hik : i = k
          · subst hik
            simp [b, k]
          · rw [Function.update_of_ne hik]
            simp [b, Function.update_of_ne hik]
        rw [hb, hAB]
        ext v
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.zero_apply]
        refine sum_eq_zero_of_bicomm σ hσ A (fun π => B π v) ?_ (a k) (ha k)
        intro x
        have hv := congrArg (fun S : H →L[ℂ] H => S v) ((hAB (σ x)).symm.trans (hσk x))
        simpa [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply] using hv
      · have hiff : ∀ i : Fin M, ((i : ℕ) < j + 1 ↔ (i : ℕ) < j) := fun i => by
          have := i.isLt
          omega
        simpa [hiff] using ih g
  simpa using step M (fun _ => 1)

theorem stdPoly_bicomm : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0 := by
  intro G H _ _ _ _ σ hσ E m h a ha
  exact standard_polynomial_vanishes_on_bicommutant σ hσ E m h a ha

end GlobalTheory.CompanionTheory.Factor
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NoOrthogonalIdempotents
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

namespace GlobalTheory.CompanionTheory.PrimeRing.StdChain

variable {R : Type} [Ring R]

theorem word_left (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx : ∀ i < m, q i * x i = x i) (n k : ℕ) (hk : k + n = m) :
    q k * (word E ((List.range' k n).map x) * q m) = word E ((List.range' k n).map x) * q m := by
  cases n with
  | zero =>
    obtain rfl : k = m := by omega
    simp [hE k le_rfl, hid]
  | succ n =>
    have hkm : k < m := by omega
    have hEx : E * x k = x k := by
      rw [← hx k hkm, ← mul_assoc, hE k hkm.le]
    rw [List.range'_succ, List.map_cons, word_cons, hEx]
    simp only [← mul_assoc, hx k hkm]

theorem word_cases (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx1 : ∀ i < m, q i * x i = x i) (hx2 : ∀ i < m, x i * q (i + 1) = x i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (l : List ℕ) (hl : ∀ a ∈ l, a < m) :
    word E (l.map x) * q m = 0 ∨ ∃ k, k + l.length = m ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨m, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < m := hl a (by simp)
    have hEx : E * x a = x a := by
      rw [← hx1 a ha, ← mul_assoc, hE a ha.le]
    rw [List.map_cons, word_cons, hEx]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left
      rw [mul_assoc, h, mul_zero]
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        have hw := word_left E m q x hE hid hx1 l.length k hk
        rw [← h] at hw
        calc x a * word E (l.map x) * q m
            = x a * q (a + 1) * (q k * (word E (l.map x) * q m)) := by
              rw [hx2 a ha, hw, mul_assoc]
          _ = x a * (q (a + 1) * q k) * (word E (l.map x) * q m) := by
              simp only [mul_assoc]
          _ = 0 := by
              rw [horth (a + 1) (by omega) k (by omega) hak]
              simp

theorem exists_chain (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (hE : ∀ i ≤ m, E * q i = q i) (n k : ℕ) (hk : k + n = m) :
    ∃ (x : ℕ → R) (y : R), y ≠ 0 ∧ y ∈ A ∧ q k * y = y ∧
      (∀ i, k ≤ i → i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i) ∧
      word E ((List.range' k n).map x) * q m = y := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    exact ⟨0, q k, hne k le_rfl, hA k le_rfl, hid k le_rfl, fun i h1 h2 => absurd h2 (by omega),
      by simp [hE k le_rfl]⟩
  | succ n ih =>
    obtain ⟨x, y, hy0, hyA, hqy, hx, hw⟩ := ih (k + 1) (by omega)
    have hkm : k < m := by omega
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ S, q k * s * y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne k hkm.le (hprime _ (hA k hkm.le) y hyA hy0 hcon)
    have hqs : q k * s ∈ A := hmul _ (hA k hkm.le) _ (hS hs)
    have hxk : q k * s * q (k + 1) ∈ A := hmul _ hqs _ (hA (k + 1) hkm)
    refine ⟨Function.update x k (q k * s * q (k + 1)), q k * s * y, hsy, hmul _ hqs _ hyA, ?_, ?_, ?_⟩
    · simp only [← mul_assoc, hid k hkm.le]
    · intro i h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h3
      · rw [Function.update_self]
        refine ⟨hxk, ?_, ?_⟩
        · simp only [← mul_assoc, hid k hkm.le]
        · rw [mul_assoc _ (q (k + 1)), hid (k + 1) hkm]
      · rw [Function.update_of_ne (by omega)]
        exact hx i (by omega) h2
    · have hmap : (List.range' (k + 1) n).map (Function.update x k (q k * s * q (k + 1))) =
          (List.range' (k + 1) n).map x := by
        apply List.map_congr_left
        intro a ha
        have := List.mem_range'_1.mp ha
        rw [Function.update_of_ne (by omega)]
      have hEq : E * (q k * s * q (k + 1)) = q k * s * q (k + 1) := by
        simp only [← mul_assoc, hE k hkm.le]
      rw [List.range'_succ, List.map_cons, word_cons, hmap, Function.update_self, mul_assoc, hw, hEq,
        mul_assoc _ (q (k + 1)), hqy]

theorem no_chain_nat (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hstd : ∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (hE : ∀ i ≤ m, E * q i = q i) : False := by
  obtain ⟨x, y, hy0, -, -, hx, hw⟩ :=
    exists_chain A S E m q hmul hS hprime hA hne hid hE m 0 (by omega)
  have hx' : ∀ i, i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i :=
    fun i hi => hx i (Nat.zero_le _) hi
  have h0 := hstd (fun i => x i) (fun i => (hx' i i.2).1)
  have hm : ∀ π : Equiv.Perm (Fin m), (List.ofFn fun i => x (π i)) =
      (List.ofFn fun i => (π i : ℕ)).map x := by
    intro π
    rw [List.map_ofFn]
    rfl
  have key : stdPoly E (fun i : Fin m => x i) * q m = y := by
    rw [stdPoly, Finset.sum_mul, Finset.sum_eq_single 1]
    · rw [hm]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
      rw [CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val, hw]
    · intro π _ hπ
      rw [hm, mul_assoc]
      rcases word_cases E m q x hE (hid m le_rfl) (fun i hi => (hx' i hi).2.1)
        (fun i hi => (hx' i hi).2.2) horth (List.ofFn fun i => (π i : ℕ))
        (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
      · rw [h, mul_zero]
      · exfalso
        apply hπ
        rw [List.length_ofFn] at hk h
        obtain rfl : k = 0 := by omega
        rw [← CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val] at h
        ext i
        exact congrFun (List.ofFn_injective h) i
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, zero_mul] at key
  exact hy0 key.symm

theorem no_orthogonal_idempotents : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False := by
  intro R _ A S E m q hmul hS hprime hstd hA hne hid horth hE
  let qq : ℕ → R := fun i => if h : i < m + 1 then q ⟨i, h⟩ else 0
  have hqq : ∀ i (h : i ≤ m), qq i = q ⟨i, Nat.lt_succ_of_le h⟩ := fun i h =>
    dif_pos (Nat.lt_succ_of_le h)
  refine no_chain_nat A S E m qq hmul hS hprime hstd ?_ ?_ ?_ ?_ ?_
  · intro i h
    rw [hqq i h]
    exact hA _
  · intro i h
    rw [hqq i h]
    exact hne _
  · intro i h
    rw [hqq i h]
    exact hid _
  · intro i h k h' hik
    rw [hqq i h, hqq k h']
    exact horth _ _ fun e => hik (congrArg Fin.val e)
  · intro i h
    rw [hqq i h]
    exact hE _

end GlobalTheory.CompanionTheory.PrimeRing.StdChain
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement
noncomputable section

open CompanionTheory.D.gk.admitted (stdPoly)
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl

theorem proj_comm_of_star_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : Set (H →L[ℂ] H)} (hN : ∀ T ∈ N, star T ∈ N) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hS : ∀ T ∈ N, ∀ v ∈ S, T v ∈ S) (T : H →L[ℂ] H) (hT : T ∈ N) :
    T * S.starProjection = S.starProjection * T := by
  ext v
  have hperp : ∀ u, u ∈ Sᗮ → T u ∈ Sᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    have h1 : ⟪w, T u⟫_ℂ = ⟪star T w, u⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hu _ (hS _ (hN T hT) _ hw)
  show T (S.starProjection v) = S.starProjection (T v)
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (hS T hT _ (S.starProjection_apply_mem v))
  rw [← map_sub]
  exact hperp _ (S.sub_starProjection_mem_orthogonal v)

theorem stFactor_from (h1 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0) (h2 : ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0) (h3 : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False) (h4 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q) (h5 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ) (h6 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W) : StFactor := by
  intro G G₁ H _ _ _ _ _ π hπ hirr j p hpj hcomm E hE
  obtain ⟨hE0, hEE, hEadj, hEc, m, hm⟩ := hE
  set ρ : G₁ →* (H →L[ℂ] H) := π.comp j with hρdef
  have hρ : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hπ _ v
  let N : Set (H →L[ℂ] H) := {T | ∀ g, T * ρ g = ρ g * T}
  let A : Set (H →L[ℂ] H) := {T | ∀ n ∈ N, n * T = T * n}
  have hN : ∀ T ∈ N, star T ∈ N := by
    intro T hT g
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, CompanionTheory.D.gk.admitted.FinOfPIAux.star_eq ρ hρ, inv_inv] at h
    exact h.symm
  have hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb n hn
    rw [← mul_assoc, ha n hn, mul_assoc, hb n hn, mul_assoc]
  have hSA : Set.range ρ ⊆ A := by
    rintro _ ⟨g, rfl⟩ n hn
    exact hn g
  have hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ Set.range ρ, x * s * y = 0) → x = 0 := by
    intro x _ y hy hy0 h
    exact h2 G G₁ H π hirr j p hpj hcomm x y (fun T hT => hy T hT) hy0 (fun g => h _ ⟨g, rfl⟩)
  have hPI : ∀ a : Fin m → (H →L[ℂ] H), (∀ i, a i ∈ A) → stdPoly E a = 0 :=
    fun a ha => h1 G₁ H ρ hρ E m hm a fun i T hT => ha i T hT
  let R : Submodule ℂ H := LinearMap.range (E : H →ₗ[ℂ] H)
  have hRmem : ∀ v, v ∈ R ↔ E v = v := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      exact DFunLike.congr_fun hEE w
    · intro h
      exact ⟨v, h⟩
  have hRcl : IsClosed (R : Set H) := by
    have : (R : Set H) = {v | E v = v} := Set.ext hRmem
    rw [this]
    exact isClosed_eq E.continuous continuous_id
  let L : Set (Submodule ℂ H) :=
    {S | IsClosed (S : Set H) ∧ (∀ T ∈ N, ∀ v ∈ S, T v ∈ S) ∧ S ≤ R}
  have hRL : R ∈ L := by
    refine ⟨hRcl, fun T hT v hv => ?_, le_rfl⟩
    rw [hRmem] at hv ⊢
    have := DFunLike.congr_fun (hEc T hT) v
    simp only [mul_apply_eq_comp] at this
    rw [← this, hv]
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hE0
    ext v
    have : E v ∈ R := ⟨v, rfl⟩
    rw [h] at this
    simpa using this
  have hLinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L := by
    rintro S ⟨hS1, hS2, hS3⟩ U ⟨hU1, hU2, hU3⟩
    refine ⟨hS1.inter U.isClosed_orthogonal, fun T hT v hv => ⟨hS2 T hT v hv.1, ?_⟩, inf_le_left.trans hS3⟩
    have hv2 : v ∈ Uᗮ := hv.2
    show T v ∈ Uᗮ
    rw [Submodule.mem_orthogonal] at hv2 ⊢
    intro w hw
    have h1 : ⟪w, T v⟫_ℂ = ⟪star T w, v⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hv2 _ (hU2 _ (hN T hT) _ hw)
  have hbound : ∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) →
      ¬ Pairwise fun i k => f i ⟂ f k := by
    intro f hf hf0 hp
    have hc : ∀ i, CompleteSpace (f i) := fun i => (hf i).1.completeSpace_coe
    refine h3 (H →L[ℂ] H) A (Set.range ρ) E m (fun i => (f i).starProjection) hAmul hSA hprime hPI
      (fun i n hn => proj_comm_of_star_closed hN (f i) (hf i).2.1 n hn) (fun i h0 => hf0 i ?_) (fun i => ?_) (fun i k hik => ?_)
      (fun i => ?_)
    · rw [Submodule.eq_bot_iff]
      intro v hv
      have := Submodule.starProjection_eq_self_iff.mpr hv
      rw [← this, h0]
      rfl
    · ext v
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ v) |> fun h => h
    · ext v
      have hv : (f k).starProjection v ∈ (f i)ᗮ :=
        (hp hik).symm ((f k).starProjection_apply_mem v)
      exact Submodule.eq_starProjection_of_mem_orthogonal (zero_mem _) (by simpa using hv)
    · ext v
      exact (hRmem _).mp ((hf i).2.2 ((f i).starProjection_apply_mem v))
  obtain ⟨Q, hQL, hQ0, hQmin⟩ := h4 H L m R (fun S hS => hS.1) hLinf hRL hR0 hbound
  obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  refine h6 G₁ H ρ hρ Q ξ hQL.1 hξ hξ0 (fun T hT v hv => hQL.2.1 T hT v hv) (fun g => ?_)
  obtain ⟨c, hc⟩ := h5 H N Q hN hQL.1 hQL.2.1
    (fun U hU1 hU2 hU3 => hQmin U ⟨hU1, hU3, hU2.trans hQL.2.2⟩ hU2) (ρ g) (fun T hT => hT g)
  exact ⟨c, hc ξ hξ⟩

theorem stFactor : StFactor :=
  stFactor_from GlobalTheory.CompanionTheory.Factor.stdPoly_bicomm GlobalTheory.CompanionTheory.DirectFactor.bicommutant_restriction_prime GlobalTheory.CompanionTheory.PrimeRing.StdChain.no_orthogonal_idempotents GlobalTheory.CompanionTheory.OrthoFamily.exists_minimal_of_orthogonal_bound GlobalTheory.CompanionTheory.Factor.schur_on_minimal_subspace GlobalTheory.CompanionTheory.CyclicScalar.exists_isIrredSubrep

end GlobalTheory.CompanionTheory.RgFl

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FactorizationStatement : StFactor := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFactor | exact GlobalTheory.CompanionTheory.RgFl.stFactor | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFactor <;> assumption)
end
