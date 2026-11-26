module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Combine
noncomputable section

open GlobalTheory.Cong MvPolynomial

namespace UpperTheory.Gal.Gen

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

private theorem polyApprox_cut {η : J → k} {T : Set (J → k)} {Q : MvPolynomial J ℤ} (hQ : aeval η Q ≠ 0)
    (h : PolyApprox η T) : PolyApprox η {x | x ∈ T ∧ aeval x Q ≠ 0} := by
  classical
  intro ε hε
  have hq : 0 < ‖aeval η Q‖ := norm_pos_iff.2 hQ
  obtain ⟨s, c, hs, hc⟩ := h (ε * ‖aeval η Q‖) (mul_pos hε hq)
  refine ⟨s.filter (fun x => aeval x Q ≠ 0), fun x => c x * aeval x Q / aeval η Q, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact ⟨hs hx.1, hx.2⟩
  · intro P
    have e1 : ∑ x ∈ s.filter (fun x => aeval x Q ≠ 0), c x * aeval x Q / aeval η Q * aeval x P
        = (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [Finset.sum_filter_of_ne, Finset.sum_div]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_mul]
        ring
      · intro x _ hx hQx
        apply hx
        simp [hQx]
    rw [e1]
    have e2 : aeval η P - (∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q
        = (aeval η (P * Q) - ∑ x ∈ s, c x * aeval x (P * Q)) / aeval η Q := by
      rw [map_mul, sub_div, mul_div_assoc, div_self hQ, mul_one]
    rw [e2, norm_div, div_le_iff₀ hq]
    exact hc (P * Q)

private theorem polyApprox_trans {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hS : ∀ η ∈ S, PolyApprox η T) : PolyApprox θ T := by
  classical
  intro ε hε
  obtain ⟨s, c, hs, hc⟩ := h (ε / 2) (by positivity)
  have hM0 : 0 ≤ ∑ η ∈ s, ‖c η‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε2 : 0 < ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) := by positivity
  have hT : ∀ η ∈ S, ∃ (t : Finset (J → k)) (d : (J → k) → k), (↑t : Set (J → k)) ⊆ T ∧
      ∀ P : MvPolynomial J ℤ, ‖aeval η P - ∑ ζ ∈ t, d ζ * aeval ζ P‖
        ≤ ε / (2 * (∑ η ∈ s, ‖c η‖ + 1)) :=
    fun η hη => hS η hη _ hε2
  choose! t d ht hd using hT
  refine ⟨s.biUnion t, fun ζ => ∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0), ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hζ
    obtain ⟨η, hη, hζ⟩ := hζ
    exact ht η (hs hη) hζ
  · intro P
    have hsum : ∑ ζ ∈ s.biUnion t, (∑ η ∈ s, c η * (if ζ ∈ t η then d η ζ else 0)) * aeval ζ P
        = ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η hη => ?_
      rw [Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_biUnion_of_mem t hη)
      · intro ζ hζ
        rw [if_neg (Finset.mem_sdiff.1 hζ).2]
        ring
      · intro ζ hζ
        rw [if_pos hζ]
        ring
    rw [hsum]
    have split : aeval θ P - ∑ η ∈ s, c η * ∑ ζ ∈ t η, d η ζ * aeval ζ P
        = (aeval θ P - ∑ η ∈ s, c η * aeval η P)
          + ∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [split]
    calc _ ≤ ‖aeval θ P - ∑ η ∈ s, c η * aeval η P‖
          + ‖∑ η ∈ s, c η * (aeval η P - ∑ ζ ∈ t η, d η ζ * aeval ζ P)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ∑ η ∈ s, ‖c η‖ * (ε / (2 * (∑ η ∈ s, ‖c η‖ + 1))) := by
          gcongr
          · exact hc P
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun η hη => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hd η (hs hη) P) (norm_nonneg _)
      _ ≤ ε := by
          rw [← Finset.sum_mul]
          generalize ∑ η ∈ s, ‖c η‖ = M at hM0 ⊢
          have h1 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          have h2 : M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
            field_simp
          have h3 : ε / 2 * (M / (M + 1)) ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h1
          linarith

theorem combine_pf : Combine := by
  intro k _ _ J θ S T Q hθ h
  exact polyApprox_trans hθ fun η hη => polyApprox_cut (h η hη).1 (h η hη).2

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevFacts
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

open GlobalTheory.Cong.LevelExt in
theorem UpperTheory.Gal.Gen.levFacts_pf :
    UpperTheory.Gal.Gen.LevFacts := by
  intro E _ _ _ a w₀ hw K hK J hJo hJc
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let s : GL (Fin a) (w₀.adicCompletion E) → UA E a := fun h => ((e.symm h : locU a w₀) : UA E a)
  have hs_mem : ∀ h, s h ∈ locU a w₀ := fun h => (e.symm h).2
  have hs_loc : ∀ h, cLoc w₀ (s h) = h := fun h => by
    rw [← he]
    exact e.apply_symm_apply h
  have hs_cont : Continuous s := continuous_subtype_val.comp e.symm.continuous
  have hs_eq : ∀ x ∈ locU a w₀, s (cLoc w₀ x) = x := fun x hx => by
    have := e.symm_apply_apply ⟨x, hx⟩
    rw [he] at this
    exact congrArg Subtype.val this
  have hcont := GlobalTheory.BCT.GlobLev.continuous_cLoc (E := E) (n := a) w₀
  have hnap : ¬ Apart w₀ w₀ := not_apart_self w₀
  have hloc : ∀ k ∈ K, ∀ x, cLoc w₀ (k * x) = cLoc w₀ x := fun k hk x => by
    rw [map_mul, hK.one k hk w₀ hnap, one_mul]
  have hnorm : ∀ J' : Subgroup (GL (Fin a) (w₀.adicCompletion E)),
      K ≤ Subgroup.normalizer ((locU a w₀ ⊓ J'.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    intro J'
    have hKL : ∀ k ∈ K, ∀ l ∈ locU a w₀ ⊓ J'.comap (cLoc w₀), k * l * k⁻¹ ∈ locU a w₀ ⊓ J'.comap (cLoc w₀) := by
      rintro k hk l ⟨hl1, hl2⟩
      have hl1' := (mem_locU_iff l).1 hl1
      refine ⟨(mem_locU_iff _).2 ⟨mul_mem (mul_mem (hK.fin hk) hl1'.1) (inv_mem (hK.fin hk)), fun u hu => ?_⟩, ?_⟩
      · simp only [map_mul, map_inv, hl1'.2 u hu, mul_one, mul_inv_cancel]
      · show cLoc w₀ (k * l * k⁻¹) ∈ J'
        simp only [map_mul, map_inv, hK.one k hk w₀ hnap, one_mul, inv_one, mul_one]
        exact hl2
    exact fun k hk => Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hKL k hk l hl, fun hl => by
      have := hKL k⁻¹ (inv_mem hk) _ hl
      simpa [mul_assoc] using this⟩
  have hmem : ∀ (J' : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (c : UA E a),
      c ∈ lev K w₀ J' ↔ ∃ k ∈ K, ∃ x ∈ locU a w₀, cLoc w₀ x ∈ J' ∧ c = k * x := by
    intro J' c
    show c ∈ K ⊔ (locU a w₀ ⊓ J'.comap (cLoc w₀)) ↔ _
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J'), Set.mem_mul]
    constructor
    · rintro ⟨k, hk, x, hx, rfl⟩
      exact ⟨k, hk, x, hx.1, hx.2, rfl⟩
    · rintro ⟨k, hk, x, hx, hxJ, rfl⟩
      exact ⟨k, hk, x, ⟨hx, hxJ⟩, rfl⟩
  have hJmem : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J := by
    intro c hc
    obtain ⟨k, hk, x, -, hxJ, rfl⟩ := (hmem J c).1 hc
    rwa [hloc k hk]
  have hLc : IsCompact ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) := by
    have : ((locU a w₀ ⊓ J.comap (cLoc w₀) : Subgroup (UA E a)) : Set (UA E a)) = s '' (J : Set _) := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨cLoc w₀ x, hx2, hs_eq x hx1⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨hs_mem h, ?_⟩
        show cLoc w₀ (s h) ∈ J
        rw [hs_loc]
        exact hh
    rw [this]
    exact hJc.image hs_cont
  refine ⟨⟨sup_le hK.fin (fun x hx => ((mem_locU_iff x).1 (Subgroup.mem_inf.1 hx).1).1), ?_, ?_⟩, hmem J, hJmem,
    ?_, fun y => ⟨s y, hs_mem y, hs_loc y⟩, ?_⟩
  · show IsCompact ((K ⊔ (locU a w₀ ⊓ J.comap (cLoc w₀)) : Subgroup (UA E a)) : Set (UA E a))
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ (hnorm J)]
    exact hK.compact.mul hLc
  · obtain ⟨N₀, hN₀o, hN₀1, hN₀⟩ := hK.isOpen
    let k : UA E a → UA E a := fun x => x * (s (cLoc w₀ x))⁻¹
    have hkc : Continuous k := continuous_id.mul ((hs_cont.comp hcont).inv)
    have hs1 : s 1 = 1 := by
      have := hs_eq 1 (one_mem _)
      rwa [map_one] at this
    refine ⟨k ⁻¹' N₀ ∩ cLoc w₀ ⁻¹' (J : Set _), (hN₀o.preimage hkc).inter (hJo.preimage hcont), ⟨?_, ?_⟩, ?_⟩
    · show k 1 ∈ N₀
      have : k 1 = 1 := by simp [k, hs1]
      rw [this]
      exact hN₀1
    · show cLoc w₀ 1 ∈ J
      rw [map_one]
      exact J.one_mem
    · rintro x ⟨⟨hxN, hxJ⟩, hxf⟩
      have hkx : k x ∈ K := by
        refine hN₀ _ hxN ?_ ?_
        · exact mul_mem hxf (inv_mem ((mem_locU_iff _).1 (hs_mem _)).1)
        · exact one_of_cLoc hw _ (by simp only [k, map_mul, map_inv, hs_loc, mul_inv_cancel])
      refine (hmem J x).2 ⟨k x, hkx, s (cLoc w₀ x), hs_mem _, ?_, by simp [k]⟩
      rw [hs_loc]
      exact hxJ
  · intro c hc h1
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at h1
    have hx1 : x = 1 := by
      have h2 := hs_eq x hx
      have hs1 : s 1 = 1 := by
        have := hs_eq 1 (one_mem _)
        rwa [map_one] at this
      rw [h1, hs1] at h2
      exact h2.symm
    rw [hx1, mul_one]
    exact hk
  · intro J' c hc hcJ'
    obtain ⟨k, hk, x, hx, -, rfl⟩ := (hmem J c).1 hc
    rw [hloc k hk] at hcJ'
    exact (hmem J' _).2 ⟨k, hk, x, hx, hcJ', rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountCore
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem sq_sum_of_subsingleton {G : Type} (F : Finset G) (hF : ∀ g ∈ F, ∀ g' ∈ F, g = g') (t : G → ℂ) :
    ‖∑ g ∈ F, t g‖ ^ 2 = ∑ g ∈ F, ‖t g‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
  · simp
  · have e : F = {g} := Finset.eq_singleton_iff_unique_mem.2 ⟨hg, fun g' h' => hF _ h' _ hg⟩
    subst e
    simp

private theorem fibre_sum {G Y : Type} [Fintype Y] [DecidableEq Y] (S : Finset G) (π : G → Y)
    (hπ : ∀ g ∈ S, ∀ g' ∈ S, π g = π g' → g = g') (t : G → ℂ) :
    ∑ y, ‖∑ g ∈ S with π g = y, t g‖ ^ 2 = ∑ g ∈ S, ‖t g‖ ^ 2 := by
  refine Eq.trans ?_ (Finset.sum_fiberwise S π fun g => ‖t g‖ ^ 2)
  refine Finset.sum_congr rfl fun y _ => sq_sum_of_subsingleton _ (fun g hg g' hg' => ?_) t
  rw [Finset.mem_filter] at hg hg'
  exact hπ g hg.1 g' hg'.1 (hg.2.trans hg'.2.symm)

private noncomputable def mat {G X : Type} [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) : Matrix (X × Fin d) (X × Fin d) ℂ :=
  fun r s => ∑ g ∈ S with π r.1 g = s.1, t g * m r.1 g r.2 s.2

private theorem mat_mulVec {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (u : X × Fin d → ℂ) (y : X) (i : Fin d) :
    (mat S π t m).mulVec u (y, i) = ∑ g ∈ S, t g * ∑ j, m y g i j * u (π y g, j) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mat, Finset.sum_mul]
  refine Eq.trans ?_ (Finset.sum_fiberwise S (π y) _)
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.1 hg).2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

private theorem mat_hs {G X : Type} [Fintype X] [DecidableEq X] {d : ℕ} (S : Finset G) (π : X → G → X) (t : G → ℂ)
    (m : X → G → Fin d → Fin d → ℂ) (M₀ : ℝ) (hm : ∀ y g i j, ‖m y g i j‖ ≤ M₀)
    (hπ : ∀ y, ∀ g ∈ S, ∀ g' ∈ S, π y g = π y g' → g = g') :
    ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ((d : ℝ) ^ 2 * M₀ ^ 2) * Fintype.card X * ∑ g ∈ S, ‖t g‖ ^ 2 := by
  have hrow : ∀ r : X × Fin d, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) := by
    intro r
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hj : ∀ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 := by
      intro j
      have e := fibre_sum S (π r.1) (hπ r.1) (fun g => t g * m r.1 g r.2 j)
      calc ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 = ∑ g ∈ S, ‖t g * m r.1 g r.2 j‖ ^ 2 := e
        _ ≤ ∑ g ∈ S, M₀ ^ 2 * ‖t g‖ ^ 2 := Finset.sum_le_sum fun g _ => by
            rw [norm_mul, mul_pow, mul_comm]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm _ _ _ _) 2) (by positivity)
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc ∑ j : Fin d, ∑ y', ‖mat S π t m r (y', j)‖ ^ 2 ≤ ∑ j : Fin d, M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  calc ∑ r, ∑ s, ‖mat S π t m r s‖ ^ 2 ≤ ∑ r : X × Fin d, (d : ℝ) * (M₀ ^ 2 * ∑ g ∈ S, ‖t g‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = _ := by
      simp [Fintype.card_prod]
      ring

private theorem sep_eq {G : Type} [Group G] (R N C : Subgroup G) (hN : N.Normal) {z γ γ' x x' c c' : G}
    (hγ : γ ∈ R) (hγ' : γ' ∈ R) (hx : x ∈ N) (hx' : x' ∈ N) (hc : c ∈ C) (hc' : c' ∈ C) :
    ∃ Γ ∈ R, ∃ ξ ∈ N, ∃ k ∈ C, γ' * z * x' * c' = Γ * (γ * z * x * c) * ξ * k :=
  ⟨γ' * γ⁻¹, R.mul_mem hγ' (R.inv_mem hγ), c⁻¹ * (x⁻¹ * x') * c,
    hN.conj_mem' _ (N.mul_mem (N.inv_mem hx) hx') c, c⁻¹ * c', C.mul_mem (C.inv_mem hc) hc', by group⟩

private theorem form_val {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {W : Wt E a} {C : Subgroup (UA E a)}
    {f : algForms W} (hf : f ∈ fixedBy W C) {d : ℕ} (B : Module.Basis (Fin d) ℂ W.Sp) {γ q x c : UA E a}
    (hγ : γ ∈ ratU E a) (hx : x ∈ infU E a) (hc : c ∈ C) (v : W.Sp) :
    f.1 v (γ * q * x * c) = ∑ j, B.repr (W.rep ⟨x, hx⟩ v) j * f.1 (B j) q := by
  have h1 : f.1 v (γ * q * x * c) = f.1 (W.rep ⟨x, hx⟩ v) q := by
    rw [mem_fixedBy.1 hf c hc v, mul_assoc γ q x, (f.2.1 v).left γ hγ, f.2.2 ⟨x, hx⟩ v]
    rfl
  refine h1.trans ?_
  have h2 := congrFun (congrArg f.1 (B.sum_repr (W.rep ⟨x, hx⟩ v))) q
  refine h2.symm.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.countCore_pf :
    UpperTheory.Gal.Gen.HS → UpperTheory.Gal.Gen.WBound → UpperTheory.Gal.Gen.CountCore := by
  classical
  intro hHS hWB E _ _ _ a W
  let d := Module.finrank ℂ W.Sp
  let B : Module.Basis (Fin d) ℂ W.Sp := Module.finBasis ℂ W.Sp
  obtain ⟨M₀, hM₀⟩ := hWB E a W d B
  refine ⟨(d : ℝ) ^ 2 * M₀ ^ 2, by positivity, ?_⟩
  intro C X _ p hcov h hsep V hVC hV
  choose γ hγ π ξ hξ c hc hdec using fun (y : X) (g : UA E a) => hcov (p y * g)
  let η : X → UA E a → infU E a := fun y g => ⟨ξ y g, hξ y g⟩
  let m : X → UA E a → Fin d → Fin d → ℂ := fun y g i j => B.repr (W.rep (η y g) (B i)) j
  let ev : V →ₗ[ℂ] (X × Fin d → ℂ) :=
    { toFun := fun f q => f.1.1 (B q.2) (p q.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf0
    have hz : ∀ j y, f.1.1 (B j) (p y) = 0 := fun j y => congrFun hf0 (y, j)
    refine Subtype.ext (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
    obtain ⟨γ₀, hγ₀, y, x, hx, c₀, hc₀, rfl⟩ := hcov g
    rw [form_val (hVC f.2) B hγ₀ hx hc₀ v]
    exact Finset.sum_eq_zero fun j _ => by rw [hz, mul_zero]
  have hfix : ∀ f : V, (mat h.support π h m).mulVec (ev f) = ev f := by
    intro f
    funext ⟨y, i⟩
    rw [mat_mulVec]
    have hop := congrFun (hV f.1 f.2 (B i)) (p y)
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul] at hop
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hop
    rw [hdec y g, form_val (hVC f.2) B (hγ y g) (hξ y g) (hc y g) (B i)]
    rfl
  have hπ : ∀ y, ∀ g ∈ h.support, ∀ g' ∈ h.support, π y g = π y g' → g = g' := by
    intro y g hg g' hg' e
    obtain ⟨Γ, hΓ, ξ', hξ', k, hk, e'⟩ := sep_eq (ratU E a) (infU E a) C inferInstance (z := p (π y g))
      (hγ y g) (hγ y g') (hξ y g) (hξ y g') (hc y g) (hc y g')
    refine hsep y g hg g' hg' Γ hΓ ξ' hξ' k hk ?_
    have e1 := hdec y g'
    rw [← e] at e1
    rw [e1, e', ← hdec y g]
  have hfd : FiniteDimensional ℂ V := FiniteDimensional.of_injective ev hinj
  refine ⟨hfd, ?_⟩
  have h1 := hHS (X × Fin d) (mat h.support π h m) (LinearMap.range ev) (by rintro _ ⟨f, rfl⟩; exact hfix f)
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  exact h1.trans (mat_hs h.support π h m M₀ (fun y g i j => hM₀ (η y g) i j) hπ)
end
