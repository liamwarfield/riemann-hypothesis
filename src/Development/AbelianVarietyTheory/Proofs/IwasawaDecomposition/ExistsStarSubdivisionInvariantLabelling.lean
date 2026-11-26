module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarLabEvalZOfEqOne
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

variable {O : Type} [CommRing O]

def IsCentreRay (w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ β : LinearMap.BilinForm ℤ X, w.evalZ β = 1 ∧ ∀ a b, t * B a b = β a b

theorem isCentreRay_comp (w : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] {r : X →ₗ[O] X₁}
    (hr : Function.Surjective r) (B : X₁ → X₁ → ℝ) :
    IsCentreRay w X (fun a b => B (r a) (r b)) ↔ IsCentreRay w X₁ B := by
  constructor
  · rintro ⟨t, ht, β, hw, hβ⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hs' : ∀ x, r (s x) = x := fun x => LinearMap.congr_fun hs x
    refine ⟨t, ht, pull s β, ?_, fun x y => ?_⟩
    · have e : pull r (pull s β) = β := LinearMap.ext₂ fun a b => by
        have h1 := hβ (s (r a)) (s (r b))
        have h2 := hβ a b
        simp only [hs'] at h1
        simp only [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [← evalZ_pull w hr, e, hw]
    · have := hβ (s x) (s y)
      simp only [hs'] at this
      simpa only [pull_apply] using this
  · rintro ⟨t, ht, β, hw, hβ⟩
    exact ⟨t, ht, pull r β, by rw [evalZ_pull w hr, hw], fun a b => by simp only [pull_apply, hβ]⟩


open Classical in
def starLab (lab w : InvFun O) : InvFun O where
  toFun n B := if IsCentreRay w (Fin n → O) B then -1 else Real.exp (lab.toFun n B) - 1
  inv n m r hr B := by
    simp only [isCentreRay_comp w hr B, lab.inv n m r hr B]
  zero B := by
    have : ¬ IsCentreRay w (Fin 0 → O) B := by
      rintro ⟨t, -, β, hw, -⟩
      rw [InvFun.evalZ, w.eval_of_subsingleton] at hw
      norm_num at hw
    rw [if_neg this, lab.zero, Real.exp_zero, sub_self]


open Classical in
theorem starLab_eval (lab w : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (B : X → X → ℝ) :
    (starLab lab w).eval X B = if IsCentreRay w X B then -1 else Real.exp (lab.eval X B) - 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(starLab lab w).eval_eq hr, lab.eval_eq hr]
  simp only [starLab, isCentreRay_comp w hr B]

variable {X : Type} [AddCommGroup X]


open Classical in
theorem starLab_evalZ_of_eq_one (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : w.evalZ β = 1) : (starLab lab w).evalZ β = -1 := by
  rw [InvFun.evalZ, starLab_eval, if_pos ⟨1, one_pos, β, h, fun a b => one_mul _⟩]

theorem starLab_evalZ_of_not (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : ¬ IsCentreRay w X (fun a b => (β a b : ℝ))) :
    (starLab lab w).evalZ β = Real.exp (lab.evalZ β) - 1 := by
  rw [InvFun.evalZ, starLab_eval, if_neg h]; rfl

theorem isCentreRay_smul_iff (w : InvFun O) [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) :
    IsCentreRay w X (fun a b => ((((k : ℤ) • β) a b : ℤ) : ℝ)) ↔ IsCentreRay w X (fun a b => (β a b : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t * k, mul_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; ring
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t / k, div_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; field_simp

theorem starLab_evalZ_smul (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) {k : ℕ} (hk : 0 < k) (hlab : lab.evalZ ((k : ℤ) • β) = lab.evalZ β) :
    (starLab lab w).evalZ ((k : ℤ) • β) = (starLab lab w).evalZ β := by
  unfold InvFun.evalZ at hlab ⊢
  rw [starLab_eval, starLab_eval, hlab]
  by_cases hc : IsCentreRay w X (fun a b => (β a b : ℝ))
  · rw [if_pos ((isCentreRay_smul_iff w β hk).2 hc), if_pos hc]
  · rw [if_neg (mt (isCentreRay_smul_iff w β hk).1 hc), if_neg hc]

theorem exists_of_isCentreRay {bar : O → O} (w : InvFun O) [Module O X] [Module.Finite O X]
    {β : LinearMap.BilinForm ℤ X} (hb : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y)
    (h : IsCentreRay w X (fun a b => (β a b : ℝ))) :
    ∃ t : ℝ, 0 < t ∧ ∃ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X ∧ (∀ y, 0 ≤ β' y y) ∧ w.evalZ β' = 1 ∧
      toReal β' = t • toReal β := by
  obtain ⟨t, ht, β', hw, h⟩ := h
  simp only at h
  refine ⟨t, ht, β', ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, hw, LinearMap.ext₂ fun a b => ?_⟩
  · have : (β' y z : ℝ) = β' z y := by rw [← h, ← h, hb.1 y z]
    exact_mod_cast this
  · have : (β' (a • y) z : ℝ) = β' y (bar a • z) := by rw [← h, ← h, hb.2 a y z]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β' y y := by rw [← h]; exact mul_nonneg ht.le (by exact_mod_cast hp y)
    exact_mod_cast this
  · simp [← h]

theorem InRCone.of_toReal_eq_smul {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β β' : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) {t : ℝ} (ht : 0 ≤ t) (e : toReal β' = t • toReal β) : InRCone γ β' := by
  obtain ⟨c, hc, e'⟩ := hβ
  refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
  rw [e, e', Finset.smul_sum]
  simp only [smul_smul]

theorem exists_isFaceCut {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hh : ∀ j, 0 ≤ h (γ j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut γ s h := by
  classical
  let e := Fintype.equivFin {j : Fin m // h (γ j) = 0}
  refine ⟨_, e.symm.toEmbedding.trans (Function.Embedding.subtype _), hh, fun j => ⟨fun hj => ⟨e ⟨j, hj⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at h1
  have hz : ∀ i, c i * (h (γ i) : ℝ) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hc i) (by exact_mod_cast hf.1 i))).1 h1.symm i
      (Finset.mem_univ _)
  have hc0 : ∀ i, i ∉ Set.range s → c i = 0 := fun i hi => by
    have hpos : (h (γ i) : ℝ) ≠ 0 := by exact_mod_cast fun h' => hi ((hf.2 i).1 h')
    exact (mul_eq_zero.1 (hz i)).resolve_right hpos
  refine ⟨fun j => c (s j), fun j => hc _, ?_⟩
  rw [e]
  have hm := Finset.sum_map Finset.univ s (fun i => c i • toReal (γ i))
  rw [← hm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hc0 i (fun ⟨j, hj⟩ => hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)), zero_smul]

theorem IsFaceCut.apply_eq_zero {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone (fun j => γ (s j)) β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  simp only [(hf.2 _).2 ⟨_, rfl⟩, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
  exact_mod_cast h1

theorem inRCone_of_sub {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' → Fin m)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone (fun j => γ (s j)) β) : InRCone γ β :=
  inRCone_trans (fun j => inRCone_self γ (s j)) hβ

theorem isTwInv_starLab {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {lab w : InvFun (𝓞 E)}
    (hl : IsTwInv H lab) (hw : IsTwInv H w) : IsTwInv H (starLab lab w) := by
  intro σ hσ n B
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  have he : ∀ a, e a = fun i => σ (a i) := fun a => rfl
  have hwt : ∀ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E),
      w.evalZ (β.compl₁₂ e.toLinearMap e.toLinearMap) = w.evalZ β := fun β => by
    simp only [InvFun.evalZ, InvFun.eval_pi, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
    exact hw σ hσ n (fun a b => (β a b : ℝ))
  have key : IsCentreRay w (Fin n → 𝓞 E) (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ↔
      IsCentreRay w (Fin n → 𝓞 E) B := by
    constructor
    · rintro ⟨t, ht, β, h1, h2⟩
      refine ⟨t, ht, β.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, ?_, fun a b => ?_⟩
      · rw [← hwt, ← h1]
        congr 1
        ext a b
        simp
      · have := h2 (e.symm a) (e.symm b)
        simp only [← he, LinearEquiv.apply_symm_apply] at this
        simpa using this
    · rintro ⟨t, ht, β, h1, h2⟩
      exact ⟨t, ht, β.compl₁₂ e.toLinearMap e.toLinearMap, by rw [hwt, h1], fun a b => by
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he, h2]⟩
  have hlab := hl σ hσ n B
  simp only [starLab]
  by_cases hc : IsCentreRay w (Fin n → 𝓞 E) B
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (mt key.1 hc), if_neg hc, hlab]

end GlobalTheory.PolFan.StarLab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabelling
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

theorem exists_isTwInv_simpLab_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  intro E _ _ _ H q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwInv_starLab H hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell H.bar φ (fun j => δ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell H.bar φ (fun j => γ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · refine LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => ?_
      have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
      have h2 := congrArg g hz
      rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.PolFan.StarLab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabellingStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_labelling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  first | exact @GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | exact GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | (intros; apply GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star <;> assumption)
end
