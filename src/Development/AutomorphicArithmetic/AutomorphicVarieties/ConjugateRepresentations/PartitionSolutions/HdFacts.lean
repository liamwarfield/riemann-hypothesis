module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

private theorem hd_cons' {I M : Type} [AddCommGroup M] (c : List I → M) (i : I) (x : List I) :
    hd c (i :: x) = c x - hd (fun y => c (i :: y)) x := by
  unfold hd
  rw [List.length_cons, Finset.sum_range_succ', sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [pow_succ]

private theorem hd_sub' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I) :
    hd (fun y => c y - c' y) x = hd c x - hd c' x := by
  unfold hd
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _

private theorem hd_hd' {I M : Type} [AddCommGroup M] (x : List I) :
    ∀ c : List I → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons i x ih =>
    intro c
    rw [hd_cons']
    have h : (fun y => hd c (i :: y)) = fun y => c y - hd (fun z => c (i :: z)) y :=
      funext fun y => hd_cons' c i y
    rw [h, hd_sub', ih]
    simp

private theorem hd_map' {I J M : Type} [AddCommGroup M] (f : J → I) (c : List I → M) (x : List J) :
    hd (fun y => c (y.map f)) x = hd c (x.map f) := by
  unfold hd
  rw [List.length_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.eraseIdx_map]

private theorem hd_hom' {I M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (c : List I → M)
    (x : List I) : hd (fun y => f (c y)) x = f (hd c x) := by
  unfold hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_zsmul f _ _).symm

private theorem hd_congr' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I)
    (h : ∀ y : List I, y.length + 1 = x.length → (∀ i ∈ y, i ∈ x) → c y = c' y) : hd c x = hd c' x := by
  unfold hd
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < x.length := Finset.mem_range.1 hj
  rw [h (x.eraseIdx j) (by rw [List.length_eraseIdx_of_lt hj']; omega)
    (fun i hi => List.mem_of_mem_eraseIdx hi)]

theorem UpperTheory.V.Cj.A.hdFacts :
    HdFacts := by
  refine ⟨fun I M _ c x => hd_hd' x c, fun I M _ c i x => hd_cons' c i x,
    fun I J M _ f c x => hd_map' f c x, fun I M N _ _ f c x => hd_hom' f c x,
    fun I M _ c c' x h => hd_congr' c c' x h, ?_⟩
  intro Γ I M _ _ _ _ ρ k c hc γ x hx
  rw [← hd_map']
  refine Eq.trans (hd_congr' _ (fun y => (ρ γ).toAddMonoidHom (c y)) x fun y hy _ => ?_)
    (hd_hom' (ρ γ).toAddMonoidHom c x)
  exact hc γ y (by omega)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SandCpt
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Cj.A.sandCpt :
    SandCpt := by
  intro E _ _ a
  have hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) := by
    refine Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _
    change Continuous fun g : GL (Fin a) (Cinf E) =>
      (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))
    exact (Units.continuous_val.mul continuous_const).mul Units.continuous_val.star
  refine ⟨hcont, fun K hK hKc => ?_⟩
  obtain ⟨C, hC⟩ := boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)
  have hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C} := by
    have h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C) := isCompact_closedBall _ _
    have e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C} := by
      ext m; simp
    rw [e] at h
    exact h
  have hT := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  refine hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩
  · exact hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)
  · refine hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_
    have e : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e]
    exact Set.mem_insert _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartOp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartMem
open UpperTheory.V.Cj.A UpperTheory.V.Lit
open scoped ContDiff

theorem UpperTheory.V.Cj.A.partMem :
    PartMem := by
  intro Γ V S I _ _ _ _ d G φ hφ q c
  rw [Dr.Geo.mem_Om]
  intro s
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨N, hN, hfin⟩ := hφ.locFin s p hp
    have hsum : ContDiffAt ℝ ∞ (fun x => ∑ i ∈ hfin.toFinset, φ i s x • (c i).1 s x) p :=
      ContDiffAt.sum fun i _ =>
        ((hφ.smooth i s).contDiffAt (G.isOpen.mem_nhds hp)).smul (Dr.Geo.contDiffAt_Om (c i) s hp)
    refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hN] with x hx
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hx, fun h => hi ?_⟩
    simp only [h, zero_smul]
  · have h : ∀ i : I, φ i s p • (c i).1 s p = 0 := fun i => by
      rw [((c i).2 s).2 p hp, smul_zero]
    simp only [h, finsum_zero]
end

noncomputable section

open UpperTheory.V.Lit UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Cj.A

section

variable {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] {d : ℕ}
  {G : Dr.Geo Γ V S d} {φ : I → S → V → ℝ}

private theorem part_fin_φ (hφ : IsPart G φ) (s : S) {p : V} (hp : p ∈ G.Y) :
    (Function.support fun i : I => φ i s p).Finite := by
  obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
  exact hf.subset fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩

private theorem part_fin (hφ : IsPart G φ) {q : ℕ} (c : I → G.Om q) (s : S) (p : V) :
    (Function.support fun i : I => φ i s p • (c i).1 s p).Finite := by
  by_cases hp : p ∈ G.Y
  · refine (part_fin_φ hφ s hp).subset fun i hi h0 => hi ?_
    beta_reduce at h0 ⊢
    rw [h0, zero_smul]
  · refine Set.finite_empty.subset fun i hi => hi ?_
    beta_reduce
    rw [((c i).2 s).2 p hp, smul_zero]

private theorem part_shift (hφ : IsPart G φ) (γ : Γ) (i : I) (s : S) (p : V) :
    φ (γ • i) s p = φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
  have h := hφ.equiv γ⁻¹ (γ • i) s p
  rw [inv_smul_smul] at h
  exact h.symm

end

theorem partOp : PartOp := by
  intro Γ V S I _ _ _ _ d G φ hφ q
  refine ⟨{ toFun := fun c => ⟨_, partMem Γ V S I d G φ hφ q c⟩, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro c c'
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.add_apply, Submodule.coe_add, smul_add]
    exact finsum_add_distrib (part_fin hφ c s p) (part_fin hφ c' s p)
  · intro a c
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    rw [smul_finsum' a (part_fin hφ c s p)]
    exact finsum_congr fun i => smul_comm _ _ _
  · intro x
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    change ∑ᶠ i : I, φ i s p • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul' (part_fin_φ hφ s hp), hφ.sum_one s p hp, one_smul]
    · simp [(x.2 s).2 p hp]
  · intro γ c
    refine Subtype.ext (funext fun s => funext fun p => Eq.symm ?_)
    change G.tr q γ (∑ᶠ i : I, φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c i).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) =
      ∑ᶠ i : I, φ i s p • G.tr q γ ((c (γ⁻¹ • i)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (part_fin hφ c _ _)]
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm γ))
    refine finsum_congr fun i => ?_
    rw [MulAction.toPerm_apply, inv_smul_smul, part_shift hφ, map_smul]
  · intro c s p h
    change ∑ᶠ i : I, φ i s p • (c i).1 s p = 0
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · rw [h i h0, smul_zero]

end UpperTheory.V.Cj.A
end
end
