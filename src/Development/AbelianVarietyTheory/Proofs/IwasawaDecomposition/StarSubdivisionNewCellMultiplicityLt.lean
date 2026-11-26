module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem linearIndependent_cons_of_coord_ne_zero :
    ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  intro O _ bar X _ _ m p δ β c j e hδ hβ hcj hj
  rw [Fintype.linearIndependent_iff] at hδ ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg

  have hgB : g 0 • (β : LinearMap.BilinForm ℤ X) + ∑ k, g k.succ • (δ (e k) : LinearMap.BilinForm ℤ X) = 0 := by
    have := congrArg Subtype.val hg
    simpa [Submodule.coe_sum] using this

  let s : Fin m → ℝ := fun i => ∑ k, if e k = i then (g k.succ : ℝ) else 0
  let r : Fin m → ℝ := fun i => (g 0 : ℝ) * c i + s i
  have hind : ∀ (d : Fin 0 → ℤ) (a : Fin m → ℤ),
      ∑ i, a i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → a = 0 := by
    intro d a h
    have h' : ∑ i, a i • δ i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using h
    funext i
    exact hδ a h' i
  have hrel : ∑ i, r i • toReal (δ i : LinearMap.BilinForm ℤ X) =
      ∑ k : Fin 0, (0 : Fin 0 → ℝ) k • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    apply LinearMap.ext₂
    intro x y
    have h1 := LinearMap.congr_fun₂ hβ x y
    have h2 := LinearMap.congr_fun₂ hgB x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, LinearMap.add_apply, smul_eq_mul,
      LinearMap.zero_apply] at h1 h2
    have h2' : (g 0 : ℝ) * (((β : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) + ∑ k, (g k.succ : ℝ) * (((δ (e k) : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
      exact_mod_cast h2
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, Finset.univ_eq_empty,
      Finset.sum_empty, LinearMap.zero_apply]
    rw [← h2', h1]
    simp only [r, s, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_assoc]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hr : r = 0 := eq_zero_of_toReal_rel hind hrel
  have hsj : s j = 0 := Finset.sum_eq_zero fun k _ => by
    rw [if_neg]
    intro h
    exact hj ⟨k, h⟩
  have hg0 : g 0 = 0 := by
    have := congrFun hr j
    simp only [r, hsj, add_zero, Pi.zero_apply] at this
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hcj
  intro i
  refine Fin.cases hg0 (fun k => ?_) i
  have := congrFun hr (e k)
  have hs : s (e k) = (g k.succ : ℝ) := by
    simp only [s]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      rw [if_neg]
      exact fun h => hk' (e.injective h)
    · simp
  simp only [r, hs, hg0, Int.cast_zero, zero_mul, zero_add, Pi.zero_apply] at this
  exact_mod_cast this

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentConsBalancedFormOfCoordNeZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  first | exact @GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero | exact GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero | (intros; apply GlobalTheory.PolFan.linearIndependent_cons_of_coord_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem inRCone_of_apply_eq_zero {X : Type} [AddCommGroup X] {m p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X) (hnn : ∀ i, 0 ≤ h (δ i))
    (hz : ∀ i, h (δ i) = 0 → i ∈ Set.range e) (hβ : InRCone δ β) (hβ0 : h β = 0) :
    InRCone (fun k => δ (e k)) β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have happ := apply_eq_of_toReal_eq hsum h
  rw [hβ0, Int.cast_zero] at happ
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)), c i * (h (δ i) : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hnn i)).1 happ.symm
  have hvan : ∀ i, i ∉ Set.range e → c i = 0 := by
    intro i hi
    rcases mul_eq_zero.1 (hterm i (Finset.mem_univ i)) with h1 | h1
    · exact h1
    · exact absurd (hz i (by exact_mod_cast h1)) hi
  refine ⟨fun k => c (e k), fun k => hc (e k), ?_⟩
  rw [hsum, ← Finset.sum_map Finset.univ e (fun i => c i • toReal (δ i))]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have : i ∉ Set.range e := by
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_map_of_mem e (Finset.mem_univ k))
  rw [hvan i this, zero_smul]

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero : ∀ {X : Type} [AddCommGroup X] {m p : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X), (∀ i, 0 ≤ h (δ i)) → (∀ i, h (δ i) = 0 → i ∈ Set.range e) →
    InRCone δ β → h β = 0 → InRCone (fun k => δ (e k)) β := by
  first | exact @GlobalTheory.PolFan.inRCone_of_apply_eq_zero | exact GlobalTheory.PolFan.inRCone_of_apply_eq_zero | (intros; apply GlobalTheory.PolFan.inRCone_of_apply_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan
namespace ConsMult

variable {M : Type} [AddCommGroup M]

def sat (P : Submodule ℤ M) : Submodule ℤ M := (Submodule.torsion ℤ (M ⧸ P)).comap P.mkQ

theorem mem_sat {P : Submodule ℤ M} {x : M} : x ∈ sat P ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ P := by
  simp only [sat, Submodule.mem_comap, Submodule.mkQ_apply, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨n, hn⟩, h⟩
    refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
    rw [Submonoid.smul_def] at h
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact h
  · rintro ⟨n, hn, h⟩
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    rw [Submonoid.smul_def]
    show n • Submodule.Quotient.mk x = (0 : M ⧸ P)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact h

theorem le_sat (P : Submodule ℤ M) : P ≤ sat P := fun x hx => mem_sat.2 ⟨1, one_ne_zero, by simpa using hx⟩

theorem sat_eq {E P : Submodule ℤ M} (hEP : E ≤ P) (hP : P ≤ sat E) : sat P = sat E := by
  ext x
  rw [mem_sat, mem_sat]
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨k, hk, h'⟩ := mem_sat.1 (hP h)
    exact ⟨k * n, mul_ne_zero hk hn, by rw [mul_smul]; exact h'⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, hEP h⟩

theorem card_torsion_eq_relIndex (P : Submodule ℤ M) :
    Nat.card (Submodule.torsion ℤ (M ⧸ P)) = P.toAddSubgroup.relIndex (sat P).toAddSubgroup := by
  let f : (sat P).toAddSubgroup →+ Submodule.torsion ℤ (M ⧸ P) :=
    { toFun := fun x => ⟨P.mkQ x.1, x.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : f.ker = P.toAddSubgroup.addSubgroupOf (sat P).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    change (⟨P.mkQ x.1, x.2⟩ : Submodule.torsion ℤ (M ⧸ P)) = 0 ↔ x.1 ∈ P
    rw [← Subtype.coe_inj]
    exact Submodule.Quotient.mk_eq_zero P
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm

theorem relIndex_cons_smul {p : ℕ} (v : M) (w : Fin p → M) (n : ℤ)
    (hli : LinearIndependent ℤ (Fin.cons v w : Fin (p + 1) → M)) :
    (Submodule.span ℤ (Set.range (Fin.cons (n • v) w : Fin (p + 1) → M))).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M))).toAddSubgroup = n.natAbs := by
  set u : Fin (p + 1) → M := Fin.cons v w with hu
  set K := Submodule.span ℤ (Set.range u)
  set K' := Submodule.span ℤ (Set.range (Fin.cons (n • v) w : Fin (p + 1) → M))
  let b := Module.Basis.span hli
  have hb : ∀ i, (b i : M) = u i := fun i => by simp [b, Module.Basis.span_apply]
  let f : K →ₗ[ℤ] ℤ := b.coord 0
  have hf0 : f (b 0) = 1 := by simp [f]
  have hfs : ∀ i : Fin p, f (b i.succ) = 0 := fun i => by
    simp [f, Finsupp.single_apply, Fin.succ_ne_zero]
  have hmem : ∀ x : K, (x : M) ∈ K' ↔ n ∣ f x := by
    intro x
    constructor
    · intro hx
      let S' : Submodule ℤ K := Submodule.comap f (Ideal.span ({n} : Set ℤ))
      have hle : K' ≤ S'.map K.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun i => ?_) i
        · refine ⟨n • b 0, ?_, ?_⟩
          · simp [S', Ideal.mem_span_singleton, hf0]
          · simp [hb, u]
        · refine ⟨b i.succ, ?_, ?_⟩
          · simp [S', hfs]
          · simp [hb, u]
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = x := Subtype.ext hyx
      subst this
      simpa [S', Ideal.mem_span_singleton] using hy
    · rintro ⟨q, hq⟩
      have hx : (x : M) = ∑ i, b.repr x i • u i := by
        have e0 := congrArg Subtype.val (b.sum_repr x)
        rw [← e0, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, hb]
      rw [hx, Fin.sum_univ_succ]
      refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
      · have h0 : b.repr x 0 = f x := rfl
        rw [h0, hq, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp [u]⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, by simp [u]⟩)
  have hsurj : Function.Surjective f.toAddMonoidHom := fun t => ⟨t • b 0, by simp [hf0]⟩
  have heq : K'.toAddSubgroup.addSubgroupOf K.toAddSubgroup =
      (AddSubgroup.zmultiples n).comap f.toAddMonoidHom := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, Int.mem_zmultiples_iff]
    exact hmem x
  rw [AddSubgroup.relIndex, heq, AddSubgroup.index_comap_of_surjective _ hsurj, Int.index_zmultiples]

theorem card_torsion_cons_mul {p : ℕ} (v β : M) (w : Fin p → M) (k a : ℤ) (b : Fin p → ℤ) (hk : k ≠ 0) (ha : a ≠ 0)
    (hli : LinearIndependent ℤ (Fin.cons v w : Fin (p + 1) → M)) (hrel : k • β = a • v + ∑ i, b i • w i) :
    k.natAbs * Nat.card (Submodule.torsion ℤ (M ⧸ Submodule.span ℤ (Set.range (Fin.cons β w : Fin (p + 1) → M)))) =
      a.natAbs * Nat.card (Submodule.torsion ℤ (M ⧸ Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M)))) := by
  have hli' : LinearIndependent ℤ (Fin.cons β w : Fin (p + 1) → M) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have h2 : (g 0 * a) • v + ∑ i, (g 0 * b i + k * g i.succ) • w i = 0 := by
      have e1 := congrArg (k • ·) hg
      simp only [smul_add, smul_zero, Finset.smul_sum, smul_smul] at e1
      rw [mul_comm k (g 0), mul_smul, hrel] at e1
      rw [← e1]
      simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      abel
    have h3 := hli (Fin.cons (g 0 * a) fun i => g 0 * b i + k * g i.succ) (by
      rw [Fin.sum_univ_succ]; simpa using h2)
    have hg0 : g 0 = 0 := by
      have := h3 0
      simp only [Fin.cons_zero, mul_eq_zero] at this
      tauto
    intro i
    refine Fin.cases hg0 (fun i => ?_) i
    have := h3 i.succ
    simp only [Fin.cons_succ, hg0, zero_mul, zero_add, mul_eq_zero] at this
    tauto
  set D := Submodule.span ℤ (Set.range (Fin.cons v w : Fin (p + 1) → M)) with hD
  set N := Submodule.span ℤ (Set.range (Fin.cons β w : Fin (p + 1) → M)) with hN
  set E := Submodule.span ℤ (Set.range (Fin.cons (k • β) w : Fin (p + 1) → M)) with hE
  have hw : ∀ P : Submodule ℤ M, (∀ i, w i ∈ P) → ∑ i, b i • w i ∈ P := fun P h =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)
  have hwE : ∀ i, w i ∈ E := fun i => Submodule.subset_span ⟨i.succ, by simp⟩
  have hkE : k • β ∈ E := Submodule.subset_span ⟨0, by simp⟩
  have haE : a • v ∈ E := by
    have : a • v = k • β - ∑ i, b i • w i := by rw [hrel]; abel
    rw [this]; exact sub_mem hkE (hw _ hwE)
  have hE' : E = Submodule.span ℤ (Set.range (Fin.cons (a • v) w : Fin (p + 1) → M)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero, SetLike.mem_coe]
        rw [hrel]
        exact add_mem (Submodule.subset_span ⟨0, by simp⟩) (hw _ fun i => Submodule.subset_span ⟨i.succ, by simp⟩)
      · exact Submodule.subset_span ⟨i.succ, by simp⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using haE
      · simpa using hwE i
  have hED : E ≤ D := by
    rw [hE', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using Submodule.smul_mem D a (Submodule.subset_span ⟨0, by simp⟩)
    · exact Submodule.subset_span ⟨i.succ, by simp⟩
  have hEN : E ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using Submodule.smul_mem N k (Submodule.subset_span ⟨0, by simp⟩)
    · exact Submodule.subset_span ⟨i.succ, by simp⟩
  have hDs : D ≤ sat E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact mem_sat.2 ⟨a, ha, by simpa using haE⟩
    · exact le_sat E (by simpa using hwE i)
  have hNs : N ≤ sat E := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact mem_sat.2 ⟨k, hk, by simpa using hkE⟩
    · exact le_sat E (by simpa using hwE i)
  have h1 := card_torsion_eq_relIndex D
  rw [sat_eq hED hDs] at h1
  have h2 := card_torsion_eq_relIndex N
  rw [sat_eq hEN hNs] at h2
  rw [h1, h2, ← relIndex_cons_smul β w k hli', ← relIndex_cons_smul v w a hli, ← hE']
  change E.toAddSubgroup.relIndex N.toAddSubgroup * _ = E.toAddSubgroup.relIndex D.toAddSubgroup * _
  rw [AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hEN) ((Submodule.toAddSubgroup_le _ _).2 hNs),
    AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hED) ((Submodule.toAddSubgroup_le _ _).2 hDs)]

theorem exists_int_rel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (hli : LinearIndependent ℤ δ)
    (hc : toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X)) :
    ∃ (k : ℤ) (a : Fin m → ℤ), k ≠ 0 ∧ k • β = ∑ i, a i • δ i ∧ ∀ i, (k : ℝ) * c i = a i := by
  have hind : ∀ (d : Fin 0 → ℤ) (g : Fin m → ℤ),
      ∑ i, g i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → g = 0 :=
    fun d g hg => by
      refine funext (Fintype.linearIndependent_iff.1 hli g (Subtype.ext ?_))
      simpa using hg
  have hdep : ¬ LinearIndependent ℤ (Fin.cons β δ : Fin (m + 1) → balForms bar X) := by
    intro h
    have hind' : ∀ (d : Fin 0 → ℤ) (g : Fin (m + 1) → ℤ),
        ∑ i, g i • (((Fin.cons β δ : Fin (m + 1) → balForms bar X) i : balForms bar X) : LinearMap.BilinForm ℤ X) =
          ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → g = 0 :=
      fun d g hg => by
        refine funext (Fintype.linearIndependent_iff.1 h g (Subtype.ext ?_))
        simpa using hg
    have := eq_zero_of_toReal_rel hind' (r := Fin.cons 1 (-c)) (s := 0) (by
      rw [Fin.sum_univ_succ]
      simp [hc])
    simpa using congrFun this 0
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have hg0 : g 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg
    have := Fintype.linearIndependent_iff.1 hli _ hg
    exact hi0 (Fin.cases h0 (fun i => this i) i0)
  have hb : g 0 • β = -∑ i, g i.succ • δ i := eq_neg_of_add_eq_zero_left hg
  refine ⟨g 0 * g 0, fun i => -(g 0 * g i.succ), mul_ne_zero hg0 hg0, ?_, ?_⟩
  · rw [mul_smul, hb, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, neg_smul]
  · have hr := eq_zero_of_toReal_rel hind (r := fun i => (g 0 : ℝ) * c i + g i.succ) (s := 0) (by
      ext x y
      have h1 := LinearMap.congr_fun₂ hc x y
      have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val hg) x y
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
        Submodule.coe_sum, LinearMap.add_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h1 h2 ⊢
      simp only [Fin.sum_univ_zero]
      have h3 : ((g 0 * (β : LinearMap.BilinForm ℤ X) x y + ∑ i, g i.succ * (δ i : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
        exact_mod_cast h2
      push_cast at h3
      rw [h1] at h3
      rw [Finset.mul_sum, ← Finset.sum_add_distrib] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    intro i
    have := congrFun hr i
    simp only [Pi.zero_apply] at this
    push_cast
    linear_combination (g 0 : ℝ) * this

theorem cellMult_cons_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    0 < c j → (∀ i, i ∈ Set.range e ↔ i ≠ j) → 0 < cellMult bar δ →
    (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) = c j * cellMult bar δ := by
  intro O _ bar X _ _ m p δ β c j e hli hc hcj he _
  obtain ⟨k, a, hk, hrel, hca⟩ := exists_int_rel δ β c hli hc

  have hinj : Function.Injective (Fin.cons j e : Fin (p + 1) → Fin m) := by
    rw [Fin.cons_injective_iff]
    exact ⟨fun h => (he j).1 h rfl, e.injective⟩
  have hsurj : Function.Surjective (Fin.cons j e : Fin (p + 1) → Fin m) := by
    intro i
    by_cases hij : i = j
    · exact ⟨0, by simp [hij]⟩
    · obtain ⟨l, hl⟩ := (he i).2 hij
      exact ⟨l.succ, by simp [hl]⟩
  let σ : Fin (p + 1) ≃ Fin m := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  have hσ0 : σ 0 = j := by
    show (Fin.cons j e : Fin (p + 1) → Fin m) 0 = j
    exact Fin.cons_zero _ _
  have hσs : ∀ l, σ l.succ = e l := fun l => by
    show (Fin.cons j e : Fin (p + 1) → Fin m) l.succ = e l
    exact Fin.cons_succ _ _ _
  have hσ : (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) = δ ∘ σ := by
    funext r
    refine Fin.cases ?_ (fun l => ?_) r
    · simp [hσ0]
    · simp [hσs]
  have hli' : LinearIndependent ℤ (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
    rw [hσ]; exact hli.comp σ σ.injective
  have hrange : Set.range (Fin.cons (δ j) (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) = Set.range δ := by
    rw [hσ]; exact EquivLike.range_comp δ σ
  have hsum : ∀ f : Fin m → balForms bar X, ∑ i, f i = f j + ∑ l, f (e l) := fun f => by
    rw [← σ.sum_comp, Fin.sum_univ_succ, hσ0]
    simp only [hσs]
  have hrel' : k • β = a j • δ j + ∑ l, a (e l) • δ (e l) := by rw [hrel, hsum (fun i => a i • δ i)]
  have haj : (a j : ℝ) = k * c j := (hca j).symm
  have haj0 : a j ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at haj
    exact (mul_ne_zero (by exact_mod_cast hk) hcj.ne') haj.symm
  have key := card_torsion_cons_mul (δ j) β (fun l => δ (e l)) k (a j) (fun l => a (e l)) hk haj0 hli' hrel'
  rw [hrange] at key
  have key' : (k.natAbs : ℝ) * (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) =
      ((a j).natAbs : ℝ) * (cellMult bar δ : ℝ) := by
    unfold cellMult; exact_mod_cast key
  have hkabs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have haabs : (((a j).natAbs : ℕ) : ℝ) = |(k : ℝ)| * c j := by
    rw [Nat.cast_natAbs, Int.cast_abs, haj, abs_mul, abs_of_pos hcj]
  rw [hkabs, haabs, mul_assoc] at key'
  exact mul_left_cancel₀ (abs_ne_zero.2 (by exact_mod_cast hk)) key'

end ConsMult
end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_multiplicity_positive_cone : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    0 < c j → (∀ i, i ∈ Set.range e ↔ i ≠ j) → 0 < cellMult bar δ →
    (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) = c j * cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | exact GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | (intros; apply GlobalTheory.PolFan.ConsMult.cellMult_cons_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.StarNewCell

variable {X : Type} [AddCommGroup X]

theorem inRCone_trans {m n : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (hγ : ∀ k, InRCone δ (γ k)) (hβ : InRCone γ β) : InRCone δ β := by
  obtain ⟨c, hc, hβ⟩ := hβ
  choose a ha hγ using hγ
  refine ⟨fun i => ∑ k, c k * a k i, fun i => Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (ha k i), ?_⟩
  rw [hβ]
  simp only [hγ, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem val_eq (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (e : toReal β = ∑ i, c i • toReal (γ i)) :
    (h β : ℝ) = ∑ i, c i * (h (γ i) : ℝ) := by
  have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id h (u := fun _ : Fin 1 => β) (w := γ)
    (a := fun _ => 1) (b := c) (by simpa using e)
  simpa using this

theorem val_nonneg (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, 0 ≤ h (γ i)) (hβ : InRCone γ β) : 0 ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (0 : ℝ) ≤ h β := by
    rw [val_eq h e]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast h0 i)
  exact_mod_cast this

theorem val_zero (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h0 : ∀ i, h (γ i) = 0) (hβ : InRCone γ β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have : (h β : ℝ) = 0 := by
    rw [val_eq h e]; exact Finset.sum_eq_zero fun i _ => by rw [h0 i]; simp
  exact_mod_cast this

theorem inRCone_cons_succ {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) (k : Fin n) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) (p k) := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) k.succ

theorem inRCone_cons_zero {n : ℕ} (x : LinearMap.BilinForm ℤ X) (p : Fin n → LinearMap.BilinForm ℤ X) :
    InRCone (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) x := by
  simpa using inRCone_self (Fin.cons x p : Fin (n + 1) → LinearMap.BilinForm ℤ X) 0

end GlobalTheory.PolFan.StarNewCell


open GlobalTheory.PolFan.StarNewCell in
theorem GlobalTheory.PolFan.cellMult_lt_of_star_new : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  intro E _ _ _ H q φ lab w ψ' hSL hCS hcoord M hM X _ _ _ _ hX n γ' hγ' hliγ' hprimγ' m γ β₀ m' s h hγ hβ₀ hβ₀p hw
    hβ₀γ hcut hpos hτ hγ'τ
  classical

  obtain ⟨m₀, δ, hδ, hliδ, -, hγδ⟩ := hSL.2 X hX m γ hγ
  obtain ⟨δt, hδt, hliδt, hprimδt, hδδt⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell H.bar φ δ hδ hliδ
  have hγδt : ∀ k, InRCone δt (γ k) := fun k => hδδt _ (hγδ k)

  obtain ⟨h₂, h₂0, h₂γ, h₂cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar φ δt γ hδt hγ hγδt
  have hcutγ : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 →
      InRCone (fun k => γ (s k)) β :=
    fun β _ _ hβ hβ0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero γ h s β hcut.1 (fun i hi => (hcut.2 i).1 hi) hβ hβ0
  have hhs : ∀ k, h (γ (s k)) = 0 := fun k => (hcut.2 (s k)).2 ⟨k, rfl⟩
  obtain ⟨h₃, h₃0, h₃γs, h₃cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone H.bar δt γ (fun k => γ (s k)) h₂ h hδt.mem hδt.nonneg
    (fun k => inRCone_self γ (s k)) h₂0 h₂γ h₂cut hcut.1 hhs hcutγ

  set I : Finset (Fin m₀) := Finset.univ.filter (fun i => h₃ (δt i) = 0) with hI
  set eI : Fin I.card ↪ Fin m₀ := (I.orderEmbOfFin rfl).toEmbedding with heIdef
  have heI : ∀ i, i ∈ Set.range eI ↔ h₃ (δt i) = 0 := by
    intro i
    show i ∈ Set.range (I.orderEmbOfFin rfl) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [I]
  have hsupp : ∀ β, InRCone δt β → h₃ β = 0 → InRCone (fun k => δt (eI k)) β :=
    fun β hβ h0 => GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero δt h₃ eI β h₃0 (fun i hi => (heI i).2 hi) hβ h0

  obtain ⟨c, hc0, hcβ⟩ : InRCone δt β₀ := inRCone_trans hγδt hβ₀γ
  have hclt : ∀ i, c i < 1 := hcoord X hX m₀ δt hδt hliδt hprimδt β₀ hβ₀ hβ₀p hw c hc0 hcβ
  obtain ⟨j, hcj, hjI⟩ : ∃ j, 0 < c j ∧ h₃ (δt j) ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h30 : h₃ β₀ = 0 := by
      have : (h₃ β₀ : ℝ) = 0 := by
        rw [val_eq h₃ hcβ]
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases (hc0 i).eq_or_lt with hi | hi
        · rw [← hi, zero_mul]
        · rw [hno i hi]; simp
      exact_mod_cast this
    have := val_zero h hhs (h₃cut β₀ hβ₀ hβ₀p ⟨c, hc0, hcβ⟩ h30)
    omega

  have hprimβ₀ : ∀ hx : β₀ ∈ balForms H.bar X, IsPrim H.bar (⟨β₀, hx⟩ : balForms H.bar X) := by
    intro hx k β' hk
    refine (hCS X hX).2.1 β₀ hβ₀ hβ₀p hw k β' ?_
    have h' : β₀ = ((k • β' : balForms H.bar X) : LinearMap.BilinForm ℤ X) := congrArg Subtype.val hk
    rw [h', Submodule.coe_smul_of_tower, natCast_zsmul]

  set δs : Fin m₀ → balForms H.bar X := fun i => ⟨δt i, hδt.mem i⟩ with hδs
  set βs : balForms H.bar X := ⟨β₀, hβ₀⟩ with hβs
  have hliδs : LinearIndependent ℤ δs := LinearIndependent.of_comp (balForms H.bar X).subtype hliδt

  set ρs : Fin (I.card + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eI k)) with hρsdef
  obtain ⟨ρ, hρ0, hρs, hρv⟩ : ∃ ρ : Fin (I.card + 1) → LinearMap.BilinForm ℤ X, ρ 0 = β₀ ∧
      (∀ k, ρ k.succ = δt (eI k)) ∧ ∀ i, ρ i = (ρs i : LinearMap.BilinForm ℤ X) :=
    ⟨fun i => (ρs i : LinearMap.BilinForm ℤ X), by simp [ρs, βs], fun k => by simp [ρs, δs], fun i => rfl⟩
  have hjeI : j ∉ Set.range eI := fun hh => hjI ((heI j).1 hh)
  have hliρ : LinearIndependent ℤ ρ := by
    have h1 := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eI hliδs hcβ hcj.ne' hjeI
    have h2 := h1.map' (balForms H.bar X).subtype (Submodule.ker_subtype _)
    have : ρ = (balForms H.bar X).subtype ∘ ρs := funext hρv
    rw [this]; exact h2
  have hρmem : ∀ i, ρ i ∈ balForms H.bar X := fun i => by rw [hρv]; exact (ρs i).2
  have hρnn : ∀ i y, 0 ≤ ρ i y y := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact hβ₀p
    · rw [hρs]; exact hδt.nonneg _
  have hρprim : ∀ i, IsPrim H.bar (⟨ρ i, hρmem i⟩ : balForms H.bar X) := by
    have key : ∀ (x y : LinearMap.BilinForm ℤ X) (hx : x ∈ balForms H.bar X) (hy : y ∈ balForms H.bar X), x = y →
        IsPrim H.bar (⟨y, hy⟩ : balForms H.bar X) → IsPrim H.bar (⟨x, hx⟩ : balForms H.bar X) := by
      rintro x y hx hy rfl hp; exact hp
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · exact key _ _ _ hβ₀ hρ0 (hprimβ₀ hβ₀)
    · exact key _ _ _ (hδt.mem _) (hρs k) (hprimδt _)

  have hτρ : ∀ i, InRCone ρ ((Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.cons_zero, ← hρ0]; exact inRCone_self ρ 0
    · rw [Fin.cons_succ]
      exact inRCone_trans (fun l => hρs l ▸ inRCone_self ρ l.succ) (hsupp _ (hγδt (s k)) (h₃γs k))
  have hρτ : ∀ i, InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) (ρ i) := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · rw [hρ0]; exact inRCone_cons_zero _ _
    · rw [hρs]
      exact inRCone_trans (fun l => inRCone_cons_succ β₀ (fun j => γ (s j)) l)
        (h₃cut _ (hδt.mem _) (hδt.nonneg _) (inRCone_self δt _) ((heI _).1 ⟨k, rfl⟩))

  obtain ⟨h₁, h₁0, h₁γ', h₁cut⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar ψ' _ γ' hτ hγ' hγ'τ
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive H.bar ρ γ' hρmem hγ'.mem h₁ hliρ hliγ' hρprim hprimγ'
    (fun k => inRCone_trans hτρ (hγ'τ k)) (fun i => val_nonneg h₁ h₁0 (hρτ i)) h₁γ'
    (fun i hi => h₁cut (ρ i) (hρmem i) (hρnn i) (hρτ i) hi)

  set J : Finset (Fin m₀) := Finset.univ.erase j with hJ
  have hJc : J.card = m₀ - 1 := by simp [J]
  set eJ : Fin (m₀ - 1) ↪ Fin m₀ := (J.orderEmbOfFin hJc).toEmbedding with heJdef
  have heJ : ∀ i, i ∈ Set.range eJ ↔ i ≠ j := by
    intro i
    show i ∈ Set.range (J.orderEmbOfFin hJc) ↔ _
    rw [Finset.range_orderEmbOfFin]
    simp [J]
  set ρ's : Fin (m₀ - 1 + 1) → balForms H.bar X := Fin.cons βs (fun k => δs (eJ k)) with hρ'sdef
  have hliρ' : LinearIndependent ℤ ρ's := GlobalTheory.T.linearIndependent_cons_balancedForm_of_coord_ne_zero H.bar δs βs c j eJ hliδs hcβ hcj.ne' (fun hh => (heJ j).1 hh rfl)
  have hmultρ' : (cellMult H.bar ρ's : ℝ) = c j * cellMult H.bar δs :=
    GlobalTheory.T.cell_multiplicity_positive_cone H.bar δs βs c j eJ hliδs hcβ hcj heJ (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs)
  have hrange : Set.range (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ⊆ Set.range ρ's := by
    rintro _ ⟨k, rfl⟩
    have e := hs' k
    rcases Fin.eq_zero_or_eq_succ (s' k) with h0 | ⟨l, hl⟩
    · refine ⟨0, Subtype.ext ?_⟩
      simp [ρ's, βs]
      rw [e, h0, hρ0]
    · have hne : eI l ≠ j := fun hh => hjI (hh ▸ (heI (eI l)).1 ⟨l, rfl⟩)
      obtain ⟨r, hr⟩ := (heJ (eI l)).2 hne
      refine ⟨r.succ, Subtype.ext ?_⟩
      simp [ρ's, δs]
      rw [e, hl, hρs, hr]
  have hdvd : cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) ∣ cellMult H.bar ρ's :=
    GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms H.bar X) ρ's _ hliρ' hrange
  have hle := Nat.le_of_dvd (GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar ρ's) hdvd
  have hδpos := GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar δs
  have hlt : (cellMult H.bar ρ's : ℝ) < cellMult H.bar δs := by
    rw [hmultρ']; exact mul_lt_of_lt_one_left (by exact_mod_cast hδpos) (hclt j)
  have hlt' : cellMult H.bar ρ's < cellMult H.bar δs := by exact_mod_cast hlt
  have hδsM : cellMult H.bar δs ≤ M := by
    have := (SmoothEnd.cellMult_le_maxMult hX hδt hliδt hprimδt).trans hM
    exact_mod_cast this
  omega
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLtStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_newCell_multiplicity_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  first | exact @GlobalTheory.PolFan.cellMult_lt_of_star_new | exact GlobalTheory.PolFan.cellMult_lt_of_star_new | (intros; apply GlobalTheory.PolFan.cellMult_lt_of_star_new <;> assumption)
end
