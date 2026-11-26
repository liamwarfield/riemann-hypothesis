module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DExact

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdStep
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

private theorem contDiffOn_finsum_locally_finite_smul {V A I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A]
    [NormedSpace ℝ A] (Y : Set V) (φ : I → V → ℝ) (w : I → V → A)
    (hφ : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ i) Y)
    (hw : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w i) Y)
    (hfin : ∀ p ∈ Y, ∃ N ∈ nhds p, {i | ∃ x ∈ N, φ i x ≠ 0}.Finite) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ᶠ i, φ i p • w i p) Y := by
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨N, hN, hNf⟩ := hfin p hp
  obtain ⟨U, hUN, hUo, hpU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUo, hpU, ?_⟩
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ i ∈ hNf.toFinset, φ i p • w i p) (Y ∩ U) :=
    ContDiffOn.sum (fun i _ => ((hφ i).smul (hw i)).mono Set.inter_subset_left)
  refine hsum.congr ?_
  intro y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Set.Finite.coe_toFinset]
  refine ⟨y, hUN hy.2, ?_⟩
  intro h0
  apply hi
  simp [h0]

theorem UpperTheory.V.Cj.A.bwdStep :
    BwdStep := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q k u hu hhd hvan
  have hfinY : ∀ s, ∀ p ∈ G.Y, {i | φ i s p ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
    exact hf.subset (fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩)
  have hsupp : ∀ (c : I → ↥(G.Om q)) (s : S) (p : V), Function.HasFiniteSupport
      (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · refine (hfinY s p hp).subset ?_
      intro i hi h0
      apply hi
      simp [h0]
    · have hz : (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) = 0 := by
        funext i
        rw [((c i).2 s).2 p hp, smul_zero]
        rfl
      rw [hz]
      exact Set.finite_empty.subset (fun i hi => hi rfl)
  have hex : ∀ c : I → ↥(G.Om q), ∃ w : ↥(G.Om q), ∀ s p,
      (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p
        = ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p := by
    intro c
    refine ⟨⟨fun s p => ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, ?_⟩,
      fun s p => rfl⟩
    intro s
    refine ⟨contDiffOn_finsum_locally_finite_smul G.Y (fun i => φ i s)
      (fun i => ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)
      (fun i => hφ.smooth i s) (fun i => ((c i).2 s).1) (hφ.locFin s), ?_⟩
    intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [((c i).2 s).2 p hp, smul_zero]
  choose Sm hSm using hex
  refine ⟨fun x => Sm (fun i => u (i :: x)), ?_, ?_, ?_⟩
  · intro γ x hx
    have hσ : ∀ t, G.σ γ (G.σ γ⁻¹ t) = t := by
      intro t
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    have hρ : ∀ v, G.ρ γ (G.ρ γ⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    apply Subtype.ext
    funext s p
    show _ = G.tr q γ (((Sm fun i => u (i :: x)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [hSm, hSm, map_finsum (G.tr q γ) (hsupp _ _ _)]
    conv_lhs => rw [← finsum_comp_equiv (MulAction.toPerm γ : I ≃ I)]
    apply finsum_congr
    intro j
    simp only [MulAction.toPerm_apply]
    have h1 : u (γ • j :: List.map (fun x => γ • x) x) = G.act q γ (u (j :: x)) :=
      hu γ (j :: x) (by simp [hx])
    have h2 : φ (γ • j) s p = φ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
      rw [← hφ.equiv γ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p), hσ, hρ]
    rw [h1, map_smul, h2]
    rfl
  · intro x hx
    apply Subtype.ext
    funext s p
    let ev : ↥(G.Om q) →+ V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
      { toFun := fun w => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    change ev (hd (fun y => Sm fun i => u (i :: y)) x) = ev (u x)
    rw [← hdFacts.2.2.2.1 I _ _ ev (fun y => Sm fun i => u (i :: y)) x]
    have hinner : ∀ i, hd (fun y => ev (u (i :: y))) x = ev (u x) := by
      intro i
      have h2 := hdFacts.2.1 I _ u i x
      rw [hhd (i :: x) (by simp [hx]), eq_comm, sub_eq_zero] at h2
      calc hd (fun y => ev (u (i :: y))) x = ev (hd (fun y => u (i :: y)) x) :=
            hdFacts.2.2.2.1 I _ _ ev (fun y => u (i :: y)) x
        _ = ev (u x) := by rw [← h2]
    by_cases hp : p ∈ G.Y
    · have hrw : (fun y => ev (Sm fun i => u (i :: y)))
          = fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y)) := by
        funext y
        show ((Sm fun i => u (i :: y) : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = _
        rw [hSm]
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        show φ i s p ≠ 0
        intro h0
        apply hi
        simp [h0]
      rw [hrw]
      have hsplit : hd (fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y))) x
          = ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • hd (fun y => ev (u (i :: y))) x := by
        simp only [UpperTheory.V.Lit.Geo.hd, Finset.smul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_comm]
      rw [hsplit]
      simp only [hinner]
      rw [← Finset.sum_smul]
      have h1 : ∑ i ∈ (hfinY s p hp).toFinset, φ i s p = 1 := by
        rw [← hφ.sum_one s p hp]
        symm
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        exact hi
      rw [h1, one_smul]
    · have hz : ∀ w : ↥(G.Om q), ev w = 0 := fun w => (w.2 s).2 p hp
      simp only [hz]
      simp [UpperTheory.V.Lit.Geo.hd]
  · intro x hx s p hp hx'
    rw [hSm]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · have hall : ∀ i' ∈ i :: x, p ∈ C i' s := by
        intro i' hi'
        rcases List.mem_cons.mp hi' with h | h
        · rw [h]
          exact hC i s p hp h0
        · exact hx' i' h
      rw [hvan (i :: x) (by simp [hx]) s p hp hall, smul_zero]
end

open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem van_dOm {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (C : I → S → Set V) (F : S → Set V) (hC : ∀ i s, IsOpen (C i s))
    (hF : ∀ s, IsOpen (F s)) {q : ℕ} (k : ℕ) (b : List I → G.Om q) (hb : Van G C F k b) :
    Van G C F k (fun x => G.dOm q (b x)) := by
  intro x hx s p hp hxC
  beta_reduce
  by_cases hY : p ∈ G.Y
  · rw [G.dOm_apply (b x) s hY]
    have hW : IsOpen (F s ∩ ⋂ i ∈ {i | i ∈ x}, C i s) :=
      (hF s).inter ((List.finite_toSet x).isOpen_biInter (fun i _ => hC i s))
    have hev : ((b x : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hW.mem_nhds ⟨hp, Set.mem_iInter₂.mpr hxC⟩] with y hy
      exact hb x hx s y hy.1 (fun i hi => Set.mem_iInter₂.mp hy.2 i hi)
    rw [extDeriv, hev.fderiv_eq, fderiv_const_apply]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  · exact ((G.dOm q (b x)).2 s).2 p hY

theorem UpperTheory.V.Cj.A.zigBwd :
    ZigBwd := by
  intro Γ V S I _ _ _ _ _ d G hY hne φ hφ C F hC hF hφC n c hc hdc hvc q
  obtain ⟨-, -, -, hhom, -, -⟩ := hdFacts
  obtain ⟨hi1, -, hi3⟩ := inclFacts Γ V S d G hY hne
  induction q with
  | zero =>
    intro k hk
    obtain rfl : k = n := by omega
    refine ⟨fun x => G.incl (c x), fun x _ => rfl, fun γ x hx => ?_, fun x _ => hi3.apply_apply_eq_zero _,
      fun x hx => ?_, fun x hx s p _ hp => ?_⟩
    · beta_reduce
      rw [hc γ x hx, hi1]
    · refine (hhom I _ _ G.incl.toAddMonoidHom c x).trans ?_
      rw [hdc x hx, map_zero]
    · by_cases hpY : p ∈ G.Y
      · ext1 v
        rw [G.incl_apply _ _ hpY, hvc x hx s p hp]
        rfl
      · exact ((G.incl (c x)).2 s).2 p hpY
  | succ q ih =>
    intro k hk
    obtain ⟨u, hz, hu, hdu, hhu, hvu⟩ := ih (k + 1) (by omega)
    obtain ⟨b, hb, hhb, hvb⟩ := bwdStep Γ V S I d G φ hφ C F hφC q k u hu hhu hvu
    refine ⟨fun x => G.dOm q (b x), ⟨b, hb, fun _ _ => rfl, ?_⟩, fun γ x hx => ?_,
      fun x _ => (dExact Γ V S d G hY q).apply_apply_eq_zero _, fun x hx => ?_,
      van_dOm G C F hC.isOpen hF k b hvb⟩
    · exact (zigFormal Γ V S I d G).1 q (k + 1) u (hd b) c (fun x hx => (hhb x hx).symm) hz
    · beta_reduce
      rw [hb γ x hx, dEquiv]
    · refine (hhom I _ _ (G.dOm q).toAddMonoidHom b x).trans ?_
      rw [hhb x hx]
      exact hdu x hx
