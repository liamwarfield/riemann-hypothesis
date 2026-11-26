module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledParts
open scoped ComplexConjugate

namespace GlobalTheory.ChainOnto

theorem exists_sum_pairwise_unrelated {A I : Type} [AddCommGroup A] [Module ℂ A]
    (pA : A → I → Prop) (RA : I → I → Prop) (hRA : Equivalence RA)
    (hmerge : ∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hsmul : ∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) (u : A)
    (hu : u ∈ Submodule.span ℂ {u | ∃ B, pA u B}) :
    ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i := by
  classical
  let Q : A → Prop := fun u => ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i
  have hQ0 : Q 0 := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  have hadd1 : ∀ u w B, Q u → pA w B → Q (u + w) := by
    rintro u w B ⟨s, v, hv, hp, rfl⟩ hw
    by_cases hex : ∃ i ∈ s, RA i B
    · obtain ⟨i, hi, hiB⟩ := hex
      by_cases hz : v i + w = 0
      · refine ⟨s.erase i, v, fun j hj => hv j (Finset.mem_of_mem_erase hj),
          fun j hj j' hj' => hp j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj'), ?_⟩
        rw [← Finset.add_sum_erase s v hi]
        calc v i + ∑ x ∈ s.erase i, v x + w = (v i + w) + ∑ x ∈ s.erase i, v x := by abel
          _ = _ := by rw [hz, zero_add]
      · refine ⟨s, Function.update v i (v i + w), ?_, hp, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have := hmerge (v j) w j B 1 (hv j hj) hw hiB (by simpa using hz)
            simpa using this
          · rw [Function.update_of_ne hji]; exact hv j hj
        · rw [← Finset.add_sum_erase s (Function.update v i (v i + w)) hi, ← Finset.add_sum_erase s v hi]
          simp only [Function.update_self]
          rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)]
          abel
    · push_neg at hex
      have hBs : B ∉ s := fun hB => hex B hB (hRA.refl B)
      refine ⟨insert B s, Function.update v B w, ?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with hj | hj
        · subst hj; simpa using hw
        · have hjB : j ≠ B := fun h => hBs (by rw [← h]; exact hj)
          rw [Function.update_of_ne hjB]; exact hv j hj
      · intro j hj j' hj' hne
        rw [Finset.mem_insert] at hj hj'
        rcases hj with hj | hj <;> rcases hj' with hj' | hj'
        · exact absurd (hj.trans hj'.symm) hne
        · subst hj; exact fun h => hex j' hj' (hRA.symm h)
        · subst hj'; exact hex j hj
        · exact hp j hj j' hj' hne
      · rw [Finset.sum_insert hBs, Function.update_self,
          Finset.sum_congr rfl (fun j hj => Function.update_of_ne (show j ≠ B from fun h => hBs (by rw [← h]; exact hj)) w v)]
        abel
  have haddS : ∀ (s' : Finset I) (v' : I → A) u, Q u → (∀ i ∈ s', pA (v' i) i) →
      Q (u + ∑ i ∈ s', v' i) := by
    intro s' v'
    induction s' using Finset.induction_on with
    | empty => intro u hu _; simpa using hu
    | insert a s ha ih =>
      intro u hu hv'
      rw [Finset.sum_insert ha, ← add_assoc]
      exact ih _ (hadd1 u (v' a) a hu (hv' a (Finset.mem_insert_self a s)))
        (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
  have hadd : ∀ u u', Q u → Q u' → Q (u + u') := by
    rintro u u' hu ⟨s', v', hv', -, rfl⟩
    exact haddS s' v' u hu hv'
  have hsm : ∀ (a : ℂ) u, Q u → Q (a • u) := by
    rintro a u ⟨s, v, hv, hp, rfl⟩
    by_cases ha : a = 0
    · subst ha; simpa using hQ0
    · exact ⟨s, fun i => a • v i, fun i hi => hsmul _ _ a (hv i hi) ha, hp, by rw [Finset.smul_sum]⟩
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B, hB⟩ := hx
    simpa using hadd1 0 x B hQ0 hB
  | zero => exact hQ0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsm a x hx

theorem exists_ne_zero_orth {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ipA x y = conj (ipA y x))
    (S : Submodule ℂ A) (hS : S ≠ ⊤) : ∃ u : A, u ≠ 0 ∧ ∀ s ∈ S, ipA s u = 0 := by
  classical
  let b := Module.finBasis ℂ S
  let f : A →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    { toFun := fun u i => ipA u (b i : A)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hlt : Module.finrank ℂ (Fin (Module.finrank ℂ S) → ℂ) < Module.finrank ℂ A := by
    rw [Module.finrank_fin_fun]
    exact Submodule.finrank_lt hS
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨u, hu0, fun s hs => ?_⟩
  have hzero : (ipA u).comp S.subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun (LinearMap.mem_ker.mp hu) i
    simpa [f] using this
  have : ipA u s = 0 := by
    have := LinearMap.congr_fun hzero ⟨s, hs⟩
    simpa using this
  rw [hsym, this, map_zero]

theorem surjective_of_adjoint_separates : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  intro A C I J _ _ _ _ _ ipA ip Θ pA pC RA RC T hsym _ hpos hRA hspan hmerge hsmul hRCA hli hex
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨u, hu0, horth⟩ := exists_ne_zero_orth ipA hsym _ hne
  have horth' : ∀ y, ipA (Θ y) u = 0 := fun y => horth _ (LinearMap.mem_range_self Θ y)
  obtain ⟨s, v, hv, hp, hus⟩ := exists_sum_pairwise_unrelated pA RA hRA hmerge hsmul u
    (by rw [hspan]; exact Submodule.mem_top)
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hu0 (by simpa using hus)
  have hx : ∀ i : s, ∃ x, (∀ y, ip y x = ipA (Θ y) (v i)) ∧ pC x (T i) :=
    fun i => hex _ _ (hv i i.2)
  choose x hx1 hx2 using hx
  have hlin := hli s x (fun i => T i) hx2
    (fun i i' hne hR => hp i i.2 i' i'.2 (fun h => hne (Subtype.ext h)) (hRCA _ _ hR))
  have hzy : ∀ y, ip y (∑ i, x i) = 0 := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.sum_coe_sort s v, ← hus, horth']
  have hz : ∑ i, x i = 0 := by
    by_contra h
    have := hpos _ h
    rw [hzy] at this
    simp at this
  obtain ⟨i, hi⟩ := hs
  have := Fintype.linearIndependent_iff.mp hlin (fun _ => 1) (by simpa using hz) ⟨i, hi⟩
  exact one_ne_zero this

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledPartsStatement
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  first | exact @GlobalTheory.ChainOnto.surjective_of_adjoint_separates | exact GlobalTheory.ChainOnto.surjective_of_adjoint_separates | (intros; apply GlobalTheory.ChainOnto.surjective_of_adjoint_separates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsolateAbstract
namespace GlobalTheory

theorem isolate_abstract : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  intro X _ Γ G V _ _ T W β a χ hΓG hT0 hTT hβ ha hχ hχc hsep J c hJ
  classical
  obtain ⟨A, hA⟩ : ∃ A : Submodule ℂ (V →ₗ[ℂ] V), A = Submodule.span ℂ (T '' (G : Set X)) := ⟨_, rfl⟩
  have hTA : ∀ y ∈ G, T y ∈ A := fun y hy => hA ▸ Submodule.subset_span ⟨y, hy, rfl⟩
  have hmulT : ∀ y ∈ G, ∀ g ∈ A, T y * g ∈ A := by
    intro y hy g hg
    rw [hA] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨z, hz, rfl⟩ := hg
      have e : T y * T z = β y z • T (y + z) := by ext v; simp [hTT]
      rw [e]; exact A.smul_mem _ (hTA _ (G.add_mem hy hz))
    | zero => simp
    | add f g _ _ hf hg => rw [mul_add]; exact A.add_mem hf hg
    | smul r f _ hf => rw [mul_smul_comm]; exact A.smul_mem r hf
  have hmul : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    rw [hA] at hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨y, hy, rfl⟩ := hf; exact hmulT y hy g hg
    | zero => simp
    | add f f' _ _ h h' => rw [add_mul]; exact A.add_mem h h'
    | smul r f _ h => rw [smul_mul_assoc]; exact A.smul_mem r h
  have hone : (1 : V →ₗ[ℂ] V) ∈ A := by
    have e : (1 : V →ₗ[ℂ] V) = T 0 := by ext v; simp [hT0]
    rw [e]; exact hTA 0 G.zero_mem
  have hκ : ∀ L ∈ A, ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ u, ∑ y ∈ κ.support, κ y • T y u = L u := by
    intro L hL
    rw [hA, Finsupp.mem_span_image_iff_linearCombination] at hL
    obtain ⟨l, hl, rfl⟩ := hL
    refine ⟨l, fun y hy => (Finsupp.mem_supported _ _).1 hl hy, fun u => ?_⟩
    simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  have hshift : ∀ x0 x, x - x0 ∈ Γ → ∀ v ∈ W, T x v = ((β x0 (x - x0))⁻¹ * a (x - x0)) • T x0 v := by
    intro x0 x h v hv
    have h1 := hTT x0 (x - x0) v
    have e : x0 + (x - x0) = x := by abel
    rw [(ha _ h).2 v hv, map_smul, e] at h1
    rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (hβ _ _), one_smul]
  have hcls : ∀ x0 (c : X → ℂ), ∀ v ∈ W, ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v
      = (∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0) • T x0 v := by
    intro x0 c v hv
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [mul_smul, ← hshift x0 x h v hv]
    · simp
  have hQ : ∀ γ ∈ Γ, ∀ k : ℂ, ∀ c : X → ℂ, ∀ v ∈ W,
      ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) (∑ x ∈ J, c x • T x v) = ∑ x ∈ J, (c x * (χ x γ - k)) • T x v := by
    intro γ hγ k c v hv
    have hb : ∀ x, T γ (T x v) = (χ x γ * a γ) • T x v := by
      intro x; rw [hχ γ hγ x v, (ha γ hγ).2 v hv, map_smul, smul_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sum, map_smul, hb,
      Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_smul, ← sub_smul]
    congr 1
    have := (ha γ hγ).1
    field_simp
  have hQA : ∀ γ ∈ Γ, ∀ k : ℂ, ((a γ)⁻¹ • T γ - k • (1 : V →ₗ[ℂ] V)) ∈ A := fun γ hγ k =>
    A.sub_mem (A.smul_mem _ (hTA γ (hΓG hγ))) (A.smul_mem _ hone)
  have hproj : ∀ x0 ∈ G, ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ)).card = n →
      ∃ L ∈ A, ∃ s : ℂ, s ≠ 0 ∧ ∀ v ∈ W,
        L (∑ x ∈ J, c x • T x v) = s • ∑ x ∈ J, (if x - x0 ∈ Γ then c x else 0) • T x v := by
    intro x0 hx0 n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x1 ∈ J, c x1 ≠ 0 ∧ x1 - x0 ∉ Γ
    · obtain ⟨x1, hx1J, hcx1, hx1⟩ := hS
      obtain ⟨γ, hγ, hne⟩ := hsep x1 (hJ x1 hx1J) x0 hx0 hx1
      obtain ⟨c', hc'⟩ : ∃ c' : X → ℂ, c' = fun x => c x * (χ x γ - χ x1 γ) := ⟨_, rfl⟩
      have hsub : J.filter (fun x => c' x ≠ 0 ∧ x - x0 ∉ Γ) ⊂ J.filter (fun x => c x ≠ 0 ∧ x - x0 ∉ Γ) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨x1, by simp [hx1J, hcx1, hx1], ?_⟩
          simp [hc']
        · intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, fun h => hx.2.1 (by simp [hc', h]), hx.2.2⟩
      obtain ⟨L', hL', s', hs', hL'eq⟩ := ih _ (hn ▸ Finset.card_lt_card hsub) c' rfl
      refine ⟨L' * ((a γ)⁻¹ • T γ - χ x1 γ • (1 : V →ₗ[ℂ] V)), hmul _ hL' _ (hQA γ hγ _),
        s' * (χ x0 γ - χ x1 γ), mul_ne_zero hs' (sub_ne_zero.2 (Ne.symm hne)), fun v hv => ?_⟩
      rw [Module.End.mul_apply, hQ γ hγ _ c v hv,
        show (∑ x ∈ J, (c x * (χ x γ - χ x1 γ)) • T x v) = ∑ x ∈ J, c' x • T x v by rw [hc'],
        hL'eq v hv, mul_smul]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · have hχx : χ x γ = χ x0 γ := by simpa using hχc x0 γ hγ (x - x0) h
        simp only [hc', smul_smul, hχx, mul_comm]
      · simp
    · push_neg at hS
      refine ⟨1, hone, 1, one_ne_zero, fun v hv => ?_⟩
      rw [Module.End.one_apply, one_smul]
      refine Finset.sum_congr rfl fun x hx => ?_
      split_ifs with h
      · rfl
      · by_cases hc : c x = 0
        · simp [hc]
        · exact absurd (hS x hx hc) h
  have main : ∀ n : ℕ, ∀ c : X → ℂ, (J.filter (fun x => c x ≠ 0)).card = n →
      (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ L ∈ A, ∀ v ∈ W, L (∑ x ∈ J, c x • T x v) = v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn
    by_cases hS : ∃ x0 ∈ J, c x0 ≠ 0
    · obtain ⟨x0, hx0J, hcx0⟩ := hS
      have hx0 := hJ x0 hx0J
      obtain ⟨d, hd⟩ : ∃ d : ℂ, d = ∑ x ∈ J, if x - x0 ∈ Γ then c x * ((β x0 (x - x0))⁻¹ * a (x - x0)) else 0 :=
        ⟨_, rfl⟩
      by_cases hd0 : d = 0
      · obtain ⟨c'', hc''⟩ : ∃ c'' : X → ℂ, c'' = fun x => if x - x0 ∈ Γ then 0 else c x := ⟨_, rfl⟩
        have hsub : J.filter (fun x => c'' x ≠ 0) ⊂ J.filter (fun x => c x ≠ 0) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨x0, by simp [hx0J, hcx0], ?_⟩
            simp [hc'']
          · intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, fun h => hx.2 ?_⟩
            simp [hc'', h]
        have heq : ∀ v ∈ W, ∑ x ∈ J, c x • T x v = ∑ x ∈ J, c'' x • T x v := by
          intro v hv
          have h1 := hcls x0 c v hv
          rw [← hd, hd0, zero_smul] at h1
          calc ∑ x ∈ J, c x • T x v
              = ∑ x ∈ J, ((if x - x0 ∈ Γ then c x else 0) • T x v + c'' x • T x v) :=
                Finset.sum_congr rfl fun x _ => by simp only [hc'']; split_ifs <;> simp
            _ = ∑ x ∈ J, c'' x • T x v := by rw [Finset.sum_add_distrib, h1, zero_add]
        rcases ih _ (hn ▸ Finset.card_lt_card hsub) c'' rfl with h | ⟨L, hL, hLeq⟩
        · exact Or.inl fun v hv => by rw [heq v hv]; exact h v hv
        · exact Or.inr ⟨L, hL, fun v hv => by rw [heq v hv]; exact hLeq v hv⟩
      · obtain ⟨L, hL, s, hs, hLeq⟩ := hproj x0 hx0 _ c rfl
        refine Or.inr ⟨(((s * d) * β (-x0) x0)⁻¹ • T (-x0)) * L,
          hmul _ (A.smul_mem _ (hTA _ (G.neg_mem hx0))) _ hL, fun v hv => ?_⟩
        rw [Module.End.mul_apply, LinearMap.smul_apply, hLeq v hv, hcls x0 c v hv, ← hd, map_smul, map_smul,
          hTT, neg_add_cancel, hT0, smul_smul, smul_smul, smul_smul]
        have hβ' := hβ (-x0) x0
        have e : ((s * d) * β (-x0) x0)⁻¹ * s * d * β (-x0) x0 = 1 := by
          field_simp
        rw [e, one_smul]
    · push_neg at hS
      exact Or.inl fun v _ => Finset.sum_eq_zero fun x hx => by simp [hS x hx]
  rcases main _ c rfl with h | ⟨L, hL, hLeq⟩
  · exact Or.inl h
  · obtain ⟨κ, hκG, hκeq⟩ := hκ L hL
    exact Or.inr ⟨κ, hκG, fun v hv => by rw [hκeq, hLeq v hv]⟩

end GlobalTheory
end
