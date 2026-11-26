module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenvectorEqZeroOfMemTwistedSpanChain
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAug
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAug
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem isEig_translate_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  intro G V _ _ _ _ _ π hπ J N₀ N₁ θ z hJ hN hsub hconj hdec u u' hu hu' hd
  have hmul : ∀ (a b : G) (v : V), π a (π b v) = π (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  have hw' : IsEig π N₀ (fun _ => 1) (π z u') := by
    intro y hy
    have h1 : z⁻¹ * y * z ∈ N₁ := (hconj _).2 (by
      have : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [this]; exact hy)
    have h2 := hu' _ h1
    have h3 : y * z = z * (z⁻¹ * y * z) := by group
    rw [hmul, h3, ← hmul, h2, map_smul]
  have hmap : ∀ x ∈ aug π N₁ (fun _ => 1), π z x ∈ aug π N₀ (fun _ => 1) := by
    intro x hx
    have : aug π N₁ (fun _ => 1) ≤ (aug π N₀ (fun _ => 1)).comap (π z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hh, w, rfl⟩
      refine Submodule.subset_span ⟨z * h * z⁻¹, (hconj h).1 hh, π z w, ?_⟩
      rw [map_sub, map_smul, hmul, hmul]
      congr 3
      group
    exact this hx
  have hww : π z u - π z u' ∈ aug π N₀ (fun _ => 1) := by
    rw [← map_sub]; exact hmap _ hd
  obtain ⟨R, hR1, hRJ, hS⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ J θ hJ (π z u)
  have hterm : ∀ j ∈ R, (θ j)⁻¹ • π j (π z u) - π z u ∈ aug π N₀ (fun _ => 1) := by
    intro j hj
    have hjJ := hRJ j hj
    obtain ⟨y, hy, h1, h2⟩ := hdec j hjJ
    have hne : θ j ≠ 0 := by
      intro h0
      have := hJ.val_mul j hjJ j⁻¹ (hJ.inv j hjJ)
      rw [mul_inv_cancel, hJ.val_one, h0, zero_mul] at this
      exact one_ne_zero this
    have h3 := hu _ h1
    have h4 : j * z = y * (z * (z⁻¹ * (y⁻¹ * j) * z)) := by group
    have h5 : π j (π z u) = θ j • π y (π z u) := by
      rw [hmul, h4, ← hmul, ← hmul, h3, h2, map_smul, map_smul]
    rw [h5, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact Submodule.subset_span ⟨y, hy, π z u, by rw [one_smul]⟩
  set S : V := ∑ j ∈ R, (θ j)⁻¹ • π j (π z u) with hSdef
  have hc : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, hR1⟩).ne'
  have hA : S - (R.card : ℂ) • π z u ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.sum_mem _ hterm
    rwa [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at this
  have hB : S - (R.card : ℂ) • π z u' ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.add_mem _ hA (Submodule.smul_mem _ (R.card : ℂ) hww)
    rwa [smul_sub, sub_add_sub_cancel] at this
  have hC : IsEig π N₀ (fun _ => 1) (S - (R.card : ℂ) • π z u') := by
    intro y hy
    rw [map_sub, map_smul, hS y (hsub y hy).1, (hsub y hy).2, hw' y hy]
    simp
  have h0 := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ N₀ _ hN).1 _ hB hC
  have hE : π z u' = (R.card : ℂ)⁻¹ • S := by
    rw [sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro j hj
  rw [hE, map_smul, hS j hj, smul_comm]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAugStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEig_apply_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  first | exact @GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | exact GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | (intros; apply GlobalTheory.PsType.isEig_translate_of_sub_mem_aug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwine
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwine
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem translate_mem_aug_of_not_intertwine {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (J : Set G) (θ : G → ℂ) (u : V) (hu : IsEig π J θ u) (y j : G) (hj : j ∈ J) (hc : y * j * y⁻¹ ∈ J)
    (hne : θ j ≠ θ (y * j * y⁻¹)) : π y u ∈ aug π J θ := by
  have h1 : π (y * j * y⁻¹) (π y u) = θ j • π y u := by
    have : π (y * j * y⁻¹) (π y u) = π y (π j u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [this, hu j hj, map_smul]
  have h2 : (θ j - θ (y * j * y⁻¹)) • π y u ∈ aug π J θ := by
    apply Submodule.subset_span
    exact ⟨_, hc, π y u, by rw [h1, sub_smul]⟩
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.mpr hne)).mp h2

theorem eig_eq_zero_of_mem_aug_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ →
    Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) →
    ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ hJ hN hy u hu he
  classical
  obtain ⟨R, h1, hR, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ N _ hN u hu
  simp only [inv_one, one_smul] at hs
  refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ J θ hJ).1 u ?_ he
  rw [← Finset.sum_filter_add_sum_filter_not R (fun y => y ∈ J ∧ θ y = 1)] at hs
  have hA : ∑ y ∈ R.filter (fun y => y ∈ J ∧ θ y = 1), π y u
      = ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) • u := by
    rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro y hy'
    obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hy'
    rw [he y a, b, one_smul]
  have hB : ∑ y ∈ R.filter (fun y => ¬ (y ∈ J ∧ θ y = 1)), π y u ∈ aug π J θ := by
    refine Submodule.sum_mem _ fun y hy' => ?_
    obtain ⟨a, b⟩ := Finset.mem_filter.mp hy'
    obtain ⟨j, hj, hc, hne⟩ := (hy y (hR y a)).resolve_left b
    exact translate_mem_aug_of_not_intertwine π J θ u he y j hj hc hne
  have hc : ((R.filter (fun y => y ∈ J ∧ θ y = 1)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, Finset.mem_filter.mpr ⟨h1, hJ.one, hJ.val_one⟩⟩
  rw [← Submodule.smul_mem_iff _ hc, ← hA, eq_neg_of_add_eq_zero_left hs]
  exact Submodule.neg_mem _ hB

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwineStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N : Set G) (θ : G → ℂ), Datum J θ → Datum N (fun _ => 1) → (∀ y ∈ N, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → ∀ u ∈ aug π N (fun _ => 1), IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenvectorEqZeroOfMemTwistedSpanChain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem map_mem_aug_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (A B : Set G) (z : G) (h : ∀ y ∈ B, z * y * z⁻¹ ∈ A) (u : V) (hu : u ∈ aug π B (fun _ => 1)) :
    π z u ∈ aug π A (fun _ => 1) := by
  have hle : aug π B (fun _ => 1) ≤ (aug π A (fun _ => 1)).comap (π z) := by
    unfold aug
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, w, rfl⟩
    refine Submodule.subset_span ⟨z * y * z⁻¹, h y hy, π z w, ?_⟩
    have e : π (z * y * z⁻¹) (π z w) = π z (π y w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [e, map_sub, map_smul]
  exact hle hu

theorem aug_mono_set {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    {A B : Set G} (θ : G → ℂ) (h : A ⊆ B) : aug π A θ ≤ aug π B θ := by
  unfold aug
  refine Submodule.span_mono ?_
  rintro x ⟨y, hy, w, rfl⟩
  exact ⟨y, h hy, w, rfl⟩

theorem eig_eq_zero_of_mem_aug_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ z hJ hN hmono h0 hconj h1 hz m
  induction m with
  | zero =>
    intro u hu heig
    refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 0) (fun _ => 1) (hN 0)).1 u hu ?_
    intro y hy
    rw [heig y (h0 y hy).1, (h0 y hy).2]
  | succ m ih =>
    intro u hu heig
    obtain ⟨u', hu'eig, hsub⟩ := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 1) (fun _ => 1) (hN 1)).2 u
    have hsub' : u - u' ∈ aug π (N (m + 1)) (fun _ => 1) :=
      aug_mono_set π _ (hmono (Nat.succ_le_succ (Nat.zero_le m))) hsub
    have hu' : u' ∈ aug π (N (m + 1)) (fun _ => 1) := by
      have := Submodule.sub_mem _ hu hsub'
      simpa using this
    have hzu : π z u' ∈ aug π (N m) (fun _ => 1) :=
      map_mem_aug_of_conj π (N m) (N (m + 1)) z (fun y hy => (hconj m y).1 hy) u' hu'
    have hzeig : IsEig π J θ (π z u') :=
      GlobalTheory.T.isEig_apply_of_sub_mem_aug G V π hπ J (N 0) (N 1) θ z hJ (hN 0) h0 (hconj 0) hz u u' heig hu'eig hsub
    have hz0 : π z u' = 0 := ih _ hzu hzeig
    have hu0 : u' = 0 := by
      have e : π z⁻¹ (π z u') = u' := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [← e, hz0, map_zero]
    rw [hu0, sub_zero] at hsub
    exact GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine G V π hπ J (N 1) θ hJ (hN 1) h1 u hsub heig

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenvectorEqZeroOfMemTwistedSpanChainStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  first | exact @GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | exact GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain | (intros; apply GlobalTheory.PsType.eig_eq_zero_of_mem_aug_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruence
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem corner_val_le_one {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) : valuation k (g.val i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hg
  exact (g.val i j).2

theorem corner_mem_KO {g : GL (Fin n) k} (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) :
    g ∈ KO k (Fin n) := by
  let N : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix N = g.val := rfl
  have hu : IsUnit N.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

end

theorem corner_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  intro k _ _ _ _ n ψ hord x hx a b hab hnt htr
  have hnt' := hnt
  unfold Triv at hnt'
  push_neg at hnt'
  obtain ⟨u, hu, hle, hne⟩ := hnt'
  have hx0 : x.val a b ≠ 0 := fun h0 => hnt (h0 ▸ triv_zero _)
  set s : k := ((u : k) - 1) / x.val a b with hs
  have hsx : s * x.val a b = (u : k) - 1 := div_mul_cancel₀ _ hx0
  have hs1 : valuation k s ≤ 1 := by
    rw [hs, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j) := fun i j => by
    rw [map_mul]
    exact mul_le_of_le_one_left' hs1
  let M : Matrix (Fin n) (Fin n) k := 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)
  have hdet : M.det = (u : k) := by
    simp only [M]
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]
    ring
  let j : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)
  have hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a) := rfl
  have hjK : j ∈ KO k (Fin n) := by
    refine corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)
    rw [hj, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.vecMulVec_apply, Pi.single_apply]
      split_ifs
      · exact (hsm _ _).trans (corner_val_le_one hx _ _)
      · simp
  refine ⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩
  · rw [hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      exact triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))
    · rw [zero_mul]; exact triv_zero _
  · intro h
    apply hne
    simp [h]
  · refine theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h, hsx]
    · simp
  · exact mul_mem (mul_mem hx hjK) (inv_mem hx)
  · have hxx : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
    congr 2
    · ext i
      simp [Matrix.mulVec_single, mul_comm]
    · ext l
      have := congrFun (congrFun hxx a) l
      rw [Matrix.mul_apply] at this
      rw [Matrix.vecMul, dotProduct]
      rw [Pi.single_apply, this, Matrix.one_apply]
      simp [eq_comm]

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruenceStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  first | exact @GlobalTheory.PsType.corner_rankOne | exact GlobalTheory.PsType.corner_rankOne | (intros; apply GlobalTheory.PsType.corner_rankOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutside
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem not_intertwine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  intro k _ _ _ _ n ψ hord y hy hny
  classical

  have hbad : ∃ a b : Fin n, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b) := by
    by_contra h
    push_neg at h
    exact hny ⟨hy, fun i j hij => h i j hij⟩
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∃ b, a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hS : S.Nonempty := by
    obtain ⟨a, b, hab, h⟩ := hbad
    exact ⟨a, by simp [S]; exact ⟨b, hab, h⟩⟩
  set a := S.min' hS with ha_def
  have haS : a ∈ S := S.min'_mem hS
  have hamin : ∀ i ∈ S, a ≤ i := fun i hi => S.min'_le i hi
  let T : Finset (Fin n) := Finset.univ.filter (fun b => a < b ∧ ¬ Triv (ψ a / ψ b) (y.val a b))
  have hT : T.Nonempty := by
    have := haS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by simp [T]; exact hb⟩
  set b := T.max' hT with hb_def
  have hbT : b ∈ T := T.max'_mem hT
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hbT
  obtain ⟨hab, hbad_ab⟩ := hbT
  have hbmax : ∀ j, b < j → Triv (ψ a / ψ j) (y.val a j) := by
    intro j hj
    by_contra hc
    have : j ∈ T := by simp [T]; exact ⟨lt_trans hab hj, hc⟩
    exact absurd (T.le_max' j this) (not_le.mpr hj)
  obtain ⟨j, hj, u, s, hu, hs, hsu, hne, hθj, hKO, hval⟩ :=
    GlobalTheory.T.exists_rankOne_corner_principalSeriesCongruence k n ψ hord y hy a b hab hbad_ab hbmax
  have hprops := GlobalTheory.PsType.triv_ev_props k
  refine ⟨j, hj, ⟨hKO, ?_⟩, ?_⟩
  · intro i i' hii'
    rw [hval]
    by_cases hi' : i' = a
    · subst hi'
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_same, mul_one,
        if_neg (ne_of_lt hii'), zero_add]

      have hiS : i ∉ S := fun h => absurd (hamin i h) (not_le.mpr hii')
      have hib : Triv (ψ i / ψ b) (y.val i b) := by
        by_contra hc
        exact hiS (by simp [S]; exact ⟨b, lt_trans hii' hab, hc⟩)
      have h2 : Triv (ψ i / ψ a) (y.val i b) := hord i i a b le_rfl hii'.le hab.le _ hib
      refine hprops.1 _ _ _ ?_ h2
      rw [map_mul]
      first
        | exact mul_le_of_le_one_left' hs
        | exact (mul_le_mul' hs le_rfl).trans_eq (one_mul _)
        | exact mul_le_of_le_one_left (zero_le _) hs
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hi', mul_zero,
        if_neg (ne_of_lt hii'), add_zero]
      exact hprops.2.2.1 _
  · have hθ : theta ψ (y * j * y⁻¹) = (ψ a u : ℂ) := by
      refine GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation k n ψ (y * j * y⁻¹) (fun i => s * y.val i b) (Pi.single a 1) a u hu hval ?_
      intro i
      by_cases hi : i = a
      · subst hi; simp [hsu]
      · simp [Pi.single_eq_of_ne hi, hi]
    rw [hθj, hθ]
    intro h
    exact hne (Units.ext h).symm

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutsideStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesType_not_intertwine_outside : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  first | exact @GlobalTheory.PsType.not_intertwine | exact GlobalTheory.PsType.not_intertwine | (intros; apply GlobalTheory.PsType.not_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadical
open Filter Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem strip_exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 →
    (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) →
    ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ r t ψ ϖ hψ _ hϖ _ y hy
  have hy' := (GlobalTheory.CuspEntries.mem_unipRad_two_stdSum rfl y).1 hy

  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  have hball : {z : k | valuation k z < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨1, one_ne_zero, fun _ hz => hz⟩
  have P := (triv_ev_props k)
  have hev : ∀ i j : Fin (r + t), ∀ᶠ m : ℕ in atTop,
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    intro i j
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [hij, and_self, if_true]
      have hsm : IsSmoothChar (ψ i / ψ j) := by
        have h1 := hψ i
        have h2 := hψ j
        unfold IsSmoothChar at *
        have : (ψ i).ker ⊓ (ψ j).ker ≤ (ψ i / ψ j).ker := by
          intro u hu
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hu
          rw [MonoidHom.mem_ker, MonoidHom.div_apply, hu.1, hu.2, div_one]
        exact Subgroup.isOpen_mono this (by rw [Subgroup.coe_inf]; exact h1.inter h2)
      have hopen := (P.2.2.2.2.2.1 _ hsm).1
      have hT : {z : k | Triv (ψ i / ψ j) z} ∈ 𝓝 (0 : k) := hopen.mem_nhds (P.2.2.1 _)
      have ht : Tendsto (fun m : ℕ => ϖ ^ m * y.val i j) atTop (𝓝 0) := by
        simpa using hpow.mul_const (y.val i j)
      filter_upwards [ht (inter_mem hball hT)] with m hm
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hij, if_false]
      exact Eventually.of_forall fun _ => hy' i j hij
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin (r + t),
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact hev i
  obtain ⟨m, hm⟩ := hall.exists
  exact ⟨m, hm⟩

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadicalStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_exhaust | exact GlobalTheory.PsType.strip_exhaust | (intros; apply GlobalTheory.PsType.strip_exhaust <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripProperties
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_int_det {I : Type} [Fintype I] [DecidableEq I] {g : GL I k}
    (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) : g ∈ KO k I := by
  classical
  let M : Matrix I I 𝒪[k] := fun i j => ⟨g.val i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  have hmap : M.map (algebraMap 𝒪[k] k) = g.val := by
    ext i j
    rfl
  have hdet : IsUnit M.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_of_one' ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hd]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨u, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hu]
  rfl

end GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem strip_off {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : y.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_neg h] at h0
  exact h0

theorem strip_on {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_pos h] at h0
  exact h0

theorem strip_lower {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : j < i) : y.val i j = 0 := by
  have hji : (j : ℕ) < (i : ℕ) := h
  rw [strip_off hy i j (fun hc => by omega), Matrix.one_apply_ne (ne_of_gt h)]

theorem strip_diag {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i : Fin n) : y.val i i = 1 := by
  rw [strip_off hy i i (fun hc => by omega), Matrix.one_apply_eq]

theorem strip_det {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m) :
    y.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => strip_lower hy i j h)]
  simp [strip_diag hy]

theorem strip_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ n ψ r ϖ hϖ hϖ1 hunif hcut
  have hent : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → ∀ i j : Fin n,
      ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → valuation k (y.val i j) ≤ 1 := by
    intro m y hy i j h
    rw [strip_off hy i j h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet1 : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → valuation k y.val.det = 1 := by
    intro m y hy
    rw [strip_det hy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    refine (show y ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (y.val i j) from ⟨?_, ?_⟩)
    · refine mem_KO_of_int_det (fun i j => ?_) (hdet1 0 y hy)
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).1
        rwa [pow_zero, one_mul] at h0
      · exact hent 0 y hy i j h
    · intro i j hij
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).2
        rwa [pow_zero, one_mul] at h0
      · rw [strip_off hy i j h, Matrix.one_apply_ne (ne_of_lt hij)]
        exact triv_zero _
  · intro m y hy
    rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ y (fun _ => 1) (fun _ => by simp) (fun i => by simp [strip_diag hy i])
      (Or.inr fun i j h => strip_lower hy i j h)]
    simp
  · intro y hy
    refine mem_KO_of_int_det (fun i j => ?_) (hdet1 1 y hy)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · obtain ⟨h1, h2⟩ := strip_on hy i j h
      rw [pow_one] at h1 h2
      have hlt : valuation k (ϖ * y.val i j) < 1 := by
        refine lt_of_le_of_ne h1 fun heq => hcut i j h.1 h.2 ?_
        exact triv_mono _ _ _ (le_of_eq (by rw [heq, map_one])) h2
      have hle := hunif _ hlt
      rw [map_mul] at hle
      have hpos : 0 < valuation k ϖ := zero_lt_iff.2 ((map_ne_zero _).2 hϖ)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    · exact hent 1 y hy i j h
  · intro z hz m y
    set d : Fin n → k := fun i : Fin n => if (i : ℕ) < r then ϖ else 1 with hd_def
    have hd : ∀ i, d i ≠ 0 := by
      intro i
      simp only [hd_def]
      split_ifs
      exacts [hϖ, one_ne_zero]
    have hzz : z.val * (z⁻¹).val = 1 := by simp
    have hzinv : (z⁻¹).val = Matrix.diagonal (fun i => (d i)⁻¹) := by
      calc (z⁻¹).val = (Matrix.diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by
            rw [hz, Matrix.diagonal_mul_diagonal]
            rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : k) from funext fun i => inv_mul_cancel₀ (hd i)]
            rw [Matrix.diagonal_one, one_mul]
        _ = Matrix.diagonal (fun i => (d i)⁻¹) := by rw [mul_assoc, hzz, mul_one]
    have hentry : ∀ i j : Fin n, (z * y * z⁻¹).val i j = d i * y.val i j * (d j)⁻¹ := by
      intro i j
      rw [Units.val_mul, Units.val_mul, hz, hzinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [strip, Set.mem_ofPred_eq, hentry]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos h, if_pos h]
      have hdi : d i = ϖ := by simp only [hd_def]; rw [if_pos h.1]
      have hdj : d j = 1 := by simp only [hd_def]; rw [if_neg (by omega)]
      rw [hdi, hdj, show ϖ ^ m * (ϖ * y.val i j * (1 : k)⁻¹) = ϖ ^ (m + 1) * y.val i j by ring]
    · rw [if_neg h, if_neg h]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_comm (d i), mul_inv_cancel_right₀ (hd i)]
      · rw [Matrix.one_apply_ne hij]
        simp [hd i, hd j]

end GlobalTheory.PsType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripPropertiesStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesUnipotentStrip_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_props | exact GlobalTheory.PsType.strip_props | (intros; apply GlobalTheory.PsType.strip_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotone
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotone
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.StripGrp

variable {k : Type} [Field k] [ValuativeRel k]

theorem triv_mono {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y :=
  fun u hu h1 => hx u hu (h1.trans h)

theorem triv_add {χ : kˣ →* ℂˣ} {x y : k} (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le h le_rfl)) hy
  · exact triv_mono ((Valuation.map_add _ _ _).trans (max_le le_rfl h)) hx

theorem triv_neg {χ : kˣ →* ℂˣ} {x : k} (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono (by rw [Valuation.map_neg]) hx

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ h1
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm (by simpa using h1) zero_le'
  have hu : u = 1 := Units.ext (sub_eq_zero.mp ((Valuation.zero_iff _).mp h0))
  simp [hu]

theorem le_inv_of_mul_le {a b : ValueGroupWithZero k} (ha : a ≠ 0) (h : a * b ≤ 1) : b ≤ a⁻¹ :=
  calc b = a⁻¹ * (a * b) := (inv_mul_cancel_left₀ ha b).symm
    _ ≤ a⁻¹ * 1 := by gcongr
    _ = a⁻¹ := mul_one _

variable {n : ℕ}

theorem ne_of_blk {r : ℕ} {i j : Fin n} (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) : i ≠ j := by
  rintro rfl; omega

theorem val_one_apply_le (i j : Fin n) : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mul_eq_zero_of_blk {r : ℕ} {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → A i j = 0)
    (hB : ∀ i j : Fin n, ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → B i j = 0) : A * B = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < r
  · rw [hA i l (fun h => absurd h.2 (not_le.mpr hl)), zero_mul]
  · rw [hB l j (fun h => hl h.1), mul_zero]

variable {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ}

theorem mem_strip {g : GL (Fin n) k} : g ∈ strip ψ r ϖ m ↔ ∀ i j : Fin n,
    if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := Iff.rfl

theorem sub_one_of_mem {g : GL (Fin n) k} (hg : g ∈ strip ψ r ϖ m) (i j : Fin n)
    (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : (g.val - 1) i j = 0 := by
  have := mem_strip.mp hg i j
  rw [if_neg h] at this
  simp [Matrix.sub_apply, this]

theorem one_mem : (1 : GL (Fin n) k) ∈ strip ψ r ϖ m := by
  intro i j
  split_ifs with h
  · simp only [Units.val_one, Matrix.one_apply_ne (ne_of_blk h), mul_zero, map_zero, zero_le',
      true_and]
    exact triv_zero _
  · rfl

theorem mul_mem {a b : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) (hb : b ∈ strip ψ r ϖ m) :
    a * b ∈ strip ψ r ϖ m := by
  have key : (a * b).val = 1 + (a.val - 1) + (b.val - 1) := by
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem hb)
    rw [Units.val_mul]
    calc a.val * b.val = (1 + (a.val - 1)) * (1 + (b.val - 1)) := by simp
      _ = 1 + (a.val - 1) + (b.val - 1) + (a.val - 1) * (b.val - 1) := by noncomm_ring
      _ = _ := by rw [h0, add_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  have hB := mem_strip.mp hb i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA hB
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.add_apply, Matrix.sub_apply, h1, sub_zero, zero_add]
    rw [mul_add]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le hA.1 hB.1), triv_add hA.2 hB.2⟩
  · rw [if_neg h] at hA hB
    simp only [Matrix.add_apply, Matrix.sub_apply, hA, hB, sub_self, add_zero]

theorem inv_mem {a : GL (Fin n) k} (ha : a ∈ strip ψ r ϖ m) : a⁻¹ ∈ strip ψ r ϖ m := by
  have key : (a⁻¹).val = 1 - (a.val - 1) := by
    apply Units.inv_eq_of_mul_eq_one_right
    have h0 := mul_eq_zero_of_blk (sub_one_of_mem ha) (sub_one_of_mem ha)
    calc a.val * (1 - (a.val - 1)) = 1 - (a.val - 1) * (a.val - 1) := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  intro i j
  have hA := mem_strip.mp ha i j
  rw [key]
  split_ifs with h
  · rw [if_pos h] at hA
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_blk h)
    simp only [Matrix.sub_apply, h1, sub_zero, zero_sub, mul_neg, Valuation.map_neg]
    exact ⟨hA.1, triv_neg hA.2⟩
  · rw [if_neg h] at hA
    simp only [Matrix.sub_apply, hA, sub_self, sub_zero]

theorem mono {m m' : ℕ} (hϖ : valuation k ϖ < 1) (hmm : m ≤ m') :
    strip ψ r ϖ m ⊆ strip ψ r ϖ m' := by
  intro g hg i j
  have hA := mem_strip.mp hg i j
  split_ifs with h
  · rw [if_pos h] at hA
    have hle : valuation k (ϖ ^ m' * g.val i j) ≤ valuation k (ϖ ^ m * g.val i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      gcongr ?_ * _
      exact pow_le_pow_right_of_le_one' hϖ.le hmm
    exact ⟨hle.trans hA.1, triv_mono hle hA.2⟩
  · rwa [if_neg h] at hA

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_triv (χ : kˣ →* ℂˣ) : IsClosed {x : k | Triv χ x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation k x ≠ 0 := fun h0 => hx (by
    have : x = 0 := (Valuation.zero_iff _).mp h0
    rw [this]; exact triv_zero χ)
  refine Filter.mem_of_superset ((valuation k).locally_const hx0) ?_
  intro y hy hT
  exact hx (triv_mono (le_of_eq hy.symm) hT)

theorem isClosed_strip : IsClosed (strip ψ r ϖ m) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hball : IsClosed {z : k | valuation k z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed
  have hS : IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ i j : Fin n,
      if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * A i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * A i j)
      else A i j = (1 : Matrix (Fin n) (Fin n) k) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) k => A i j :=
      (continuous_apply j).comp (continuous_apply i)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [if_pos h]
      exact (hball.inter (isClosed_triv _)).preimage (continuous_const.mul hc)
    · simp only [if_neg h]
      exact isClosed_eq hc continuous_const
  exact hS.preimage Units.continuous_val

theorem isCompact_strip (hϖ0 : ϖ ≠ 0) (hϖ : valuation k ϖ < 1) : IsCompact (strip ψ r ϖ m) := by
  set a := valuation k (ϖ ^ m) with ha_def
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hϖ0)
  have ha1 : a ≤ 1 := by rw [ha_def, map_pow]; exact pow_le_one' hϖ.le _
  have h1t : (1 : ValueGroupWithZero k) ≤ a⁻¹ := le_inv_of_mul_le ha0 (by rw [mul_one]; exact ha1)
  have hbd : ∀ g ∈ strip ψ r ϖ m, ∀ i j : Fin n, valuation k (g.val i j) ≤ a⁻¹ := by
    intro g hg i j
    have hA := mem_strip.mp hg i j
    split_ifs at hA with h
    · exact le_inv_of_mul_le ha0 (by rw [ha_def, ← map_mul]; exact hA.1)
    · rw [hA]; exact (val_one_apply_le i j).trans h1t
  refine (GlobalTheory.PairingOne.isCompact_bounded (m := Fin n) a⁻¹).of_isClosed_subset isClosed_strip ?_
  intro g hg
  exact ⟨hbd g hg, hbd g⁻¹ (inv_mem hg)⟩

theorem strip_datum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  intro k _ _ _ _ n ψ r ϖ _ hϖ0 hϖ _
  refine ⟨fun m => ⟨one_mem, fun a ha b hb => mul_mem ha hb, fun a ha => inv_mem ha,
    isCompact_strip hϖ0 hϖ, rfl, fun _ _ _ _ => (mul_one 1).symm,
    ⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩⟩, fun m m' hmm => mono hϖ hmm⟩

end GlobalTheory.StripGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotoneStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  first | exact @GlobalTheory.StripGrp.strip_datum_monotone | exact GlobalTheory.StripGrp.strip_datum_monotone | (intros; apply GlobalTheory.StripGrp.strip_datum_monotone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelMemTwistedSpanFiniteStage
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelMemTwistedSpanFiniteStage
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_one_mem_aug_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N →
    (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  intro G V _ _ _ π U N hN hU v hv
  have mono : ∀ {a b : ℕ}, a ≤ b → aug π (N a) (fun _ => 1) ≤ aug π (N b) (fun _ => 1) := by
    intro a b h
    refine Submodule.span_mono ?_
    rintro x ⟨g, hg, w, rfl⟩
    exact ⟨g, hN h hg, w, rfl⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, w, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hU n n.2
    exact ⟨m, Submodule.subset_span ⟨n, hm, w, by simp⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (mono (le_max_left _ _) ha) (mono (le_max_right _ _) hb)⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Submodule.smul_mem _ c ha⟩

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelMemTwistedSpanFiniteStageStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N → (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  first | exact @GlobalTheory.PsType.twKer_one_mem_aug_stage | exact GlobalTheory.PsType.twKer_one_mem_aug_stage | (intros; apply GlobalTheory.PsType.twKer_one_mem_aug_stage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesType
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem exists_uniformiser_max (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 ∧ ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx' : e (valuation k x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hx'
    exact WithZero.zero_ne_coe hx'
  · rw [← e.strictMono.lt_iff_lt, hx', map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro y hy
    rw [← e.strictMono.le_iff_le, hx']
    have hlt : e (valuation k y) < 1 := by rw [← map_one e]; exact e.strictMono hy
    rcases eq_or_ne (e (valuation k y)) 0 with h | h
    · rw [h]; exact zero_le'
    · rw [← WithZero.exp_log h] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]; omega

theorem eig_jacquet_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ r t ψ V _ _ π hπ hψ hord hcut v hv heig
  obtain ⟨ϖ, hϖ0, hϖ1, hϖmax⟩ := exists_uniformiser_max k
  let z : GL (Fin (r + t)) k := diagT k (Fin (r + t)) (fun i => if (i : ℕ) < r then Units.mk0 ϖ hϖ0 else 1)
  have hz : z.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then ϖ else 1) := by
    simp only [z]; rw [val_diagT]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨hD, -⟩ := GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum k (r + t) ψ hψ hord
  obtain ⟨hSD, hSmono⟩ := GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone k (r + t) ψ r ϖ hψ hϖ0 hϖ1 hϖmax
  obtain ⟨h0J, hθ1, h1KO, hconj⟩ := GlobalTheory.T.principalSeriesUnipotentStrip_properties k (r + t) ψ r ϖ hϖ0 hϖ1 hϖmax hcut
  obtain ⟨m, hm⟩ := GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage _ V π _ (strip ψ r ϖ) hSmono (GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical k r t ψ ϖ hψ hϖ0 hϖ1 hϖmax) v hv
  refine GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain (GL (Fin (r + t)) k) V π hπ (grp ψ) (strip ψ r ϖ) (theta ψ) z hD hSD hSmono
    (fun y hy => ⟨h0J y hy, hθ1 0 y hy⟩) (hconj z hz) ?_ ?_ m v hm heig
  · intro y hy
    by_cases hyJ : y ∈ grp ψ
    · exact Or.inl ⟨hyJ, hθ1 1 y hy⟩
    · exact Or.inr (GlobalTheory.T.principalSeriesType_not_intertwine_outside k (r + t) ψ hord y (h1KO y hy) hyJ)
  · intro j hj
    obtain ⟨y, hy, hblk⟩ := GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence k (r + t) ψ r ϖ hord hcut j hj
    have hyJ : y ∈ grp ψ := h0J y hy
    have hyinv : y⁻¹ ∈ grp ψ := hD.inv y hyJ
    have hg : y⁻¹ * j ∈ grp ψ := hD.mul _ hyinv _ hj
    obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_blockLower_mem_principalSeriesCongruence k (r + t) ψ r ϖ hϖ0 hϖ1 z hz (y⁻¹ * j) hg hblk
    refine ⟨y, hy, h1, ?_⟩
    rw [h2, GlobalTheory.T.principalSeriesTypeCharacter_mul k (r + t) ψ hord _ hyinv _ hj, hθ1 0 _ ((hSD 0).inv y hy), one_mul]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesTypeStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eig_jacquet_zero | exact GlobalTheory.PsType.eig_jacquet_zero | (intros; apply GlobalTheory.PsType.eig_jacquet_zero <;> assumption)
end
