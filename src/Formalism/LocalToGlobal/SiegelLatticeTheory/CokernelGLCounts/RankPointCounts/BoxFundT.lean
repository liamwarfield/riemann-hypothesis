module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFund
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Tri

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

def mlaw (x y : ∀ q, α q) : ∀ p, α p := fun p => x p + y p + B p x y

end Tri

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section TriT

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

include hBd hτ hFd in

include hBd hτ hFd in
theorem box_fundT (g : ∀ q, α q) :
    ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ ∀ p, mlaw B γ g p ∈ F p := by
  let c : (∀ q, α q) → ∀ p, A p := fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose
  have hc : ∀ x p, ((c x p : A p) : α p) + (τ p x + g p + B p x g) ∈ F p :=
    fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose_spec
  let Φ : (∀ q, α q) → ∀ q, α q := fun x p => τ p x + (c x p : α p)
  have hΦ : ∀ (k : ℕ) (x x' : ∀ q, α q), (∀ q, h q < k → x q = x' q) →
      ∀ p, h p < k + 1 → Φ x p = Φ x' p := by
    intro k x x' hxx p hp
    have e1 : ∀ q, h q < h p → x q = x' q := fun q hq => hxx q (by omega)
    have h1 : τ p x = τ p x' := hτ p x x' e1
    have h2 : B p x g = B p x' g := hBd p x x' g g fun q hq => ⟨e1 q hq, rfl⟩
    show τ p x + ((hFd p (τ p x + g p + B p x g)).exists.choose : α p) =
      τ p x' + ((hFd p (τ p x' + g p + B p x' g)).exists.choose : α p)
    rw [h1, h2]
  have hit : ∀ (n : ℕ) p, h p < n → Φ (Φ^[n] 0) p = (Φ^[n] 0) p := by
    intro n
    induction n with
    | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply']
      exact hΦ k _ _ ih p hp
  have uniq : ∀ x y : ∀ q, α q, ((∀ p, x p - τ p x ∈ A p) ∧ ∀ p, mlaw B x g p ∈ F p) →
      ((∀ p, y p - τ p y ∈ A p) ∧ ∀ p, mlaw B y g p ∈ F p) → x = y := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have step : ∀ (n : ℕ) p, h p < n → x p = y p := by
      intro n
      induction n with
      | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
      | succ k ih =>
        intro p hp
        have e1 : ∀ q, h q < h p → x q = y q := fun q hq => ih q (by omega)
        have ht : τ p x = τ p y := hτ p x y e1
        have hb : B p x g = B p y g := hBd p x y g g fun q hq => ⟨e1 q hq, rfl⟩
        have hx2' : ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : x p + g p + B p x g ∈ F p := hx2 p
          rw [show ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) = x p - τ p x from rfl,
            show x p - τ p x + (τ p x + g p + B p x g) = x p + g p + B p x g by abel]
          exact hm
        have hy2' : ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : y p + g p + B p y g ∈ F p := hy2 p
          rw [ht, hb, show ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) = y p - τ p y from rfl,
            show y p - τ p y + (τ p y + g p + B p y g) = y p + g p + B p y g by abel]
          exact hm
        have h3 : x p - τ p x = y p - τ p y :=
          congrArg Subtype.val ((hFd p _).unique hx2' hy2')
        rw [ht] at h3
        exact sub_left_injective h3
    funext p
    exact step _ p (Nat.lt_succ_self _)
  have hfix : ∀ p, τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) =
      (Φ^[Finset.univ.sup h + 1] 0) p :=
    fun p => hit _ p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))
  have hsol : (∀ p, (Φ^[Finset.univ.sup h + 1] 0) p - τ p (Φ^[Finset.univ.sup h + 1] 0) ∈ A p) ∧
      ∀ p, mlaw B (Φ^[Finset.univ.sup h + 1] 0) g p ∈ F p := by
    constructor
    · intro p
      rw [← hfix p, add_sub_cancel_left]
      exact (c _ p).2
    · intro p
      show (Φ^[Finset.univ.sup h + 1] 0) p + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g ∈ F p
      rw [← hfix p]
      rw [show τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) + g p +
          B p (Φ^[Finset.univ.sup h + 1] 0) g = (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) +
          (τ p (Φ^[Finset.univ.sup h + 1] 0) + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g) by abel]
      exact hc _ p
  exact ⟨_, hsol, fun y hy => uniq y _ hy hsol⟩

end TriT

theorem triFundT (P : Type) [Fintype P] [DecidableEq P] (α : P → Type) [∀ p, AddCommGroup (α p)]
    [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
    (hBm : ∀ p, Measurable (fun z : (∀ q, α q) × (∀ q, α q) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : ∀ q, α q), B p x 0 = 0)
    (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (A : ∀ p, AddSubgroup (α p)) [∀ p, Countable (A p)]
    (hinv : ∀ γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) → ∃ γ' : ∀ q, α q, (∀ p, γ' p - τ p γ' ∈ A p) ∧
      ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (F : ∀ p, Set (α p)) (hF : ∀ p, MeasurableSet (F p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
    (K : Set (∀ p, α p)) (hK : MeasurableSet K)
    (hKd : ∀ g, ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ mlaw B γ g ∈ K) :
    Measure.pi μ K = ∏ p, μ p (F p) := by
  classical
  set T : (∀ q, α q) → (∀ q, α q) → (∀ q, α q) := fun γ g => mlaw B γ g with hTdef
  have hT : ∀ γ, MeasurePreserving (T γ) (Measure.pi μ) (Measure.pi μ) := by
    intro γ
    have := shear_mp (Fintype.card P) P rfl α μ h (fun p g => γ p + B p γ g)
      (fun p => measurable_const.add ((hBm p).comp (measurable_const.prodMk measurable_id)))
      (fun p x x' hxx => by rw [hBd p γ γ x x' fun q hq => ⟨rfl, hxx q hq⟩])
    convert this using 1
    funext g p
    simp only [hTdef, mlaw]
    abel
  have hTm : ∀ γ, Measurable (T γ) := fun γ => (hT γ).measurable
  have hT0 : ∀ γ, T γ 0 = γ := by
    intro γ; funext p; simp [hTdef, mlaw, hB0]
  let Γs := {x : ∀ q, α q // ∀ p, x p - τ p x ∈ A p}
  have hcount : Countable Γs := by
    have hinj : Function.Injective (fun x : Γs => fun p => (⟨x.1 p - τ p x.1, x.2 p⟩ : A p)) := by
      intro x y hxy
      apply Subtype.ext
      funext p
      suffices H : ∀ n, ∀ p, h p < n → x.1 p = y.1 p from H (h p + 1) p (by omega)
      intro n
      induction n with
      | zero => intro p hp; omega
      | succ k ih =>
        intro p hp
        have hl : ∀ q, h q < h p → x.1 q = y.1 q := fun q hq => ih q (by omega)
        have e := congrArg Subtype.val (congrFun hxy p)
        simp only at e
        rw [hτ p x.1 y.1 hl] at e
        simpa using e
    exact hinj.countable
  choose inv hinvA hinvT using hinv
  let iv : Γs → Γs := fun γ => ⟨inv γ.1 γ.2, hinvA γ.1 γ.2⟩
  have hiv1 : ∀ (γ : Γs) g, T (iv γ).1 (T γ.1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).1
  have hiv2 : ∀ (γ : Γs) g, T γ.1 (T (iv γ).1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).2
  have hivv : ∀ γ : Γs, iv (iv γ) = γ := by
    intro γ
    apply Subtype.ext
    have e : ∀ g, T (iv (iv γ)).1 g = T γ.1 g := by
      intro g
      calc T (iv (iv γ)).1 g = T (iv (iv γ)).1 (T (iv γ).1 (T γ.1 g)) := by rw [hiv1 γ g]
        _ = T γ.1 g := hiv1 (iv γ) (T γ.1 g)
    rw [← hT0 (iv (iv γ)).1, ← hT0 γ.1, e]
  let ivE : Γs ≃ Γs := ⟨iv, iv, hivv, hivv⟩
  let R : Set (∀ p, α p) := Set.pi Set.univ F
  have hR : MeasurableSet R := MeasurableSet.univ_pi hF
  have hRd := box_fundT h B hBd τ hτ A F hFd
  have hK1 : Measure.pi μ K = ∑' γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) := by
    have hU : K = ⋃ γ : Γs, K ∩ T γ.1 ⁻¹' R := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγF⟩, -⟩ := hRd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, fun p _ => hγF p⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hK.inter (hTm γ.1 hR)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hRd g).unique ⟨γ.2, fun p => hg1 p (Set.mem_univ p)⟩ ⟨δ.2, fun p => hg2 p (Set.mem_univ p)⟩
  have hR1 : Measure.pi μ R = ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) := by
    have hU : R = ⋃ γ : Γs, R ∩ T γ.1 ⁻¹' K := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγK⟩, -⟩ := hKd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, hγK⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hR.inter (hTm γ.1 hK)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hKd g).unique ⟨γ.2, hg1⟩ ⟨δ.2, hg2⟩
  have hterm : ∀ γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) = Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K) := by
    intro γ
    have e : K ∩ T γ.1 ⁻¹' R = T γ.1 ⁻¹' (R ∩ T (iv γ).1 ⁻¹' K) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [hiv1 γ g]
      tauto
    rw [e]
    exact (hT γ.1).measure_preimage (hR.inter (hTm _ hK)).nullMeasurableSet
  rw [hK1, tsum_congr hterm, show (∑' γ : Γs, Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K)) =
      ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) from ivE.tsum_eq (fun γ => Measure.pi μ (R ∩ T γ.1 ⁻¹' K)),
    ← hR1]
  exact Measure.pi_pi μ F

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapConjOfBounded
noncomputable section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.CovariantRepresentation

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem map_conj_of_mem (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by
  have hinv : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hr : ν.map (fun x => x * n) = ν := by
    have e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹)) := by
      funext x; simp [mul_inv_rev]
    rw [e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi,
      hl _ (R.inv_mem hn), hi]
  have e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]

theorem map_conj_of_bounded (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (h0 : ν ≠ 0)
    (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (k : G) (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R)
    (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) : ν.map (fun x => k⁻¹ * x * k) = ν := by
  obtain ⟨C, hCc, hCm⟩ := hC
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  set μ : Measure R := ν.comap Subtype.val with hμ
  have hν : μ.map Subtype.val = ν := by
    rw [hemb.map_comap, Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    exact hc
  have hcm : ∀ μ' : Measure R, (μ'.map Subtype.val).comap Subtype.val = μ' := fun μ' => hemb.comap_map μ'
  haveI : μ.IsMulLeftInvariant := ⟨fun r => by
    have h1 : (μ.map (r * ·)).map Subtype.val = μ.map Subtype.val := by
      rw [map_map hemb.measurable (measurable_const_mul r)]
      have e : (Subtype.val ∘ (r * ·) : R → G) = (fun x : G => (r : G) * x) ∘ Subtype.val := rfl
      rw [e, ← map_map (measurable_const_mul (r : G)) hemb.measurable, hν, hl _ r.2]
    rw [← hcm (μ.map (r * ·)), h1, hcm]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by
    rw [hμ, hemb.comap_apply]
    exact hK _ (hKc.image continuous_subtype_val)⟩
  haveI : NeZero μ := ⟨fun h => h0 (by rw [← hν, h, Measure.map_zero])⟩
  haveI : IsOpenPosMeasure μ := by
    obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering R n) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply NeZero.ne μ
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
      exact measure_iUnion_null hall
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering R n) hn
  haveI : IsHaarMeasure μ :=
    { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
      toIsOpenPosMeasure := inferInstance }
  let α : R ≃ₜ* R :=
    { toFun := fun r => ⟨k⁻¹ * r * k, (hk r).1 r.2⟩
      invFun := fun r => ⟨k * r * k⁻¹, (hk _).2 (by simpa [mul_assoc] using r.2)⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hit : ∀ (n : ℕ) (x : R), (((⇑α)^[n] x : R) : G) = k ^ (-(n : ℤ)) * x * k ^ (n : ℤ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k⁻¹ * (((⇑α)^[n] x : R) : G) * k = _
      rw [ih]
      push_cast
      group
  have hit' : ∀ (n : ℕ) (x : R), (((⇑α.symm)^[n] x : R) : G) = k ^ (n : ℤ) * x * k ^ (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k * (((⇑α.symm)^[n] x : R) : G) * k⁻¹ = _
      rw [ih]
      push_cast
      group
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : R)
  have hL : IsCompact (Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) : Set R) :=
    hce.isCompact_preimage ((hCc.mul (hV.image continuous_subtype_val)).mul hCc)
  have hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) ∧
      (⇑α.symm)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) := by
    intro n
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α.symm)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit' n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
  have hμα : μ.map α = μ := haar_map_equiv_of_bounded μ α hV hV1 hL hb
  have hmc : Measurable (fun x : G => k⁻¹ * x * k) := (measurable_const_mul _).mul_const _
  have hma : Measurable (⇑α) := α.continuous.measurable
  calc ν.map (fun x => k⁻¹ * x * k) = (μ.map Subtype.val).map (fun x => k⁻¹ * x * k) := by rw [hν]
    _ = (μ.map α).map Subtype.val := by
        rw [map_map hmc hemb.measurable, map_map hemb.measurable hma]
        rfl
    _ = ν := by rw [hμα, hν]

theorem conj_of_decomp (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (_hs : SigmaFinite ν)
    (h0 : ν ≠ 0) (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (hi : ν.map (fun x => x⁻¹) = ν) (k n : G)
    (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R) (hn : n ∈ R) (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) :
    ν.map (fun x => (k * n)⁻¹ * x * (k * n)) = ν := by
  have e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k) := by
    funext x
    simp only [Function.comp]
    group
  rw [e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _),
    map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]

end Conj

end Formalism.L2.SG.CovariantRepresentation
end
end
