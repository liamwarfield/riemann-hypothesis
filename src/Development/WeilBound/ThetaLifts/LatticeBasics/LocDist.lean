module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistA
open MeasureTheory Filter Topology GlobalTheory.WeilM

namespace GlobalTheory.ThK.Dbl.LD

theorem sb_chart {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {U : Set X} {T : Set Y} (hU : IsOpen U)
    {e : X → Y} {r : Y → X} (ce : ContinuousOn e U) (cr : ContinuousOn r T) (hre : ∀ x ∈ U, r (e x) = x)
    (hr : ∀ y ∈ T, r y ∈ U) {F : Y → ℂ} (hF : F ∈ SB Y) (hT : ∀ y ∉ T, F y = 0) {G : X → ℂ}
    (h1 : ∀ x ∈ U, G x = F (e x)) (h0 : ∀ x ∉ U, G x = 0) : G ∈ SB X := by
  have hcl : IsClosed (Function.support F) := (hF.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support F) := hF.2.of_isClosed_subset hcl subset_closure
  have hsub : Function.support F ⊆ T := fun y hy => by_contra fun h => hy (hT y h)
  have hC : IsCompact (r '' Function.support F) := hc.image_of_continuousOn (cr.mono hsub)
  have hz : ∀ x ∉ r '' Function.support F, G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [h1 x hxU]; exact by_contra fun h => hx ⟨e x, h, hre x hxU⟩
    · exact h0 x hxU
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro hC hz⟩
  by_cases hxU : x ∈ U
  · filter_upwards [(ce.continuousAt (hU.mem_nhds hxU)).eventually (hF.1.eventually_eq (e x)), hU.mem_nhds hxU] with y a b
    rw [h1 y b, h1 x hxU, a]
  · have : x ∉ r '' Function.support F := by rintro ⟨y, hy, rfl⟩; exact hxU (hr y (hsub hy))
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds this] with y hy
    rw [hz y hy, h0 x hxU]

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (e : X → Y) (r : Y → X)
    (ce : Continuous e) (cr : Continuous r) (hre : ∀ x, r (e x) = x) {F : Y → ℂ} (hF : F ∈ SB Y) :
    (fun x => F (e x)) ∈ SB X :=
  sb_chart (U := Set.univ) (T := Set.univ) isOpen_univ ce.continuousOn cr.continuousOn (fun x _ => hre x)
    (fun _ _ => trivial) hF (fun _ h => absurd trivial h) (fun _ _ => rfl) (fun _ h => absurd trivial h)

theorem sb_tens {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : (fun z : X × Y => f z.1 * g z.2) ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (IsCompact.prod hf.2 hg.2) fun z hz => ?_⟩
  rcases not_and_or.1 hz with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem sb_cut {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClopen A) {f : X → ℂ} (hf : f ∈ SB X) :
    A.indicator f ∈ SB X := by
  have : A.indicator f = fun x => A.indicator (fun _ => (1 : ℂ)) x * f x := by
    ext x; by_cases h : x ∈ A <;> simp [h]
  rw [this]
  exact ⟨(LocallyConstant.charFn ℂ hA).isLocallyConstant.mul hf.1, HasCompactSupport.mul_left hf.2⟩

theorem sb_unif {X P : Type} [TopologicalSpace X] [TopologicalSpace P] {φ : X → ℂ} (hφ : φ ∈ SB X) (a : P → X → X) (p : P)
    (ha : Continuous fun z : P × X => a z.1 z.2) (h0 : ∀ x, a p x = x) :
    ∀ᶠ k in 𝓝 p, ∀ x ∈ tsupport φ, φ (a k x) = φ x := by
  apply IsCompact.eventually_forall_of_forall_eventually hφ.2
  intro y _
  have e := hφ.1.eventually_eq y
  have t1 : Tendsto (fun z : P × X => a z.1 z.2) (𝓝 (p, y)) (𝓝 y) := by simpa [h0] using ha.tendsto (p, y)
  filter_upwards [t1.eventually e, (continuous_snd.tendsto (p, y)).eventually e] with z h1 h2
  rw [h1, h2]

theorem kill_tens {X V : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup V] [TopologicalSpace V]
    [NonarchimedeanAddGroup V] [LocallyCompactSpace V] [T2Space V] (S : Set X) (l : (X × V → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ f ∈ SB X, (∀ x ∉ S, f x = 0) → ∀ g ∈ SB V, l (fun z => f z.1 * g z.2) = 0)
    {F : X × V → ℂ} (hF : F ∈ SB (X × V)) (hS : ∀ z : X × V, z.1 ∉ S → F z = 0) : l F = 0 := by
  classical
  obtain ⟨K₁, hK₁⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (sb_unif hF (fun (k : V) z => (z.1, z.2 + k)) 0 (by fun_prop) (by simp))
  obtain ⟨K₀, hK₀⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  set K := K₀ ⊓ K₁
  have hK : IsCompact (K : Set V) := hK₀.of_isClosed_subset K.isClosed (fun x hx => hx.1)
  have hinv : ∀ k ∈ K, ∀ x v, F (x, v + k) = F (x, v) := fun k hk x v => by
    by_cases hx : (x, v) ∈ tsupport F
    · exact hK₁ hk.2 _ hx
    · by_cases hx' : (x, v + k) ∈ tsupport F
      · simpa using (hK₁ (neg_mem hk.2 : -k ∈ K₁) _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  haveI : DiscreteTopology (V ⧸ K.toAddSubgroup) := QuotientAddGroup.discreteTopology K.isOpen
  have hfin : ((fun z : X × V => (z.2 : V ⧸ K.toAddSubgroup)) '' tsupport F).Finite :=
    (IsCompact.image hF.2 (QuotientAddGroup.continuous_mk.comp continuous_snd)).finite_of_discrete
  have hmem : ∀ (x : V) (q : V ⧸ K.toAddSubgroup), x + -q.out ∈ (K : Set V) ↔ q = (x : V ⧸ K.toAddSubgroup) := by
    intro x q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq]
    rw [add_comm]; rfl
  have : F = ∑ q ∈ hfin.toFinset, fun z : X × V =>
      F (z.1, q.out) * Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (z.2 + -q.out) := by
    ext ⟨x, v⟩
    have hx : F (x, (v : V ⧸ K.toAddSubgroup).out) = F (x, v) := by
      rw [← hinv _ ((hmem v _).2 rfl) x]; congr 2; abel
    rw [Finset.sum_apply, Finset.sum_eq_single (v : V ⧸ K.toAddSubgroup)]
    · rw [Set.indicator_of_mem ((hmem v _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [Set.indicator_of_notMem (fun h => hq ((hmem v q).1 h)), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := F) (x := (x, v)), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  exact h (fun x => F (x, q.out)) (sb_comp (fun x => (x, q.out)) Prod.fst (by fun_prop) (by fun_prop) (fun _ => rfl) hF)
    (fun x hx => hS _ hx) (fun v => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (v + -q.out))
    (sb_comp (fun v => v + -q.out) (fun v => v + q.out) (by fun_prop) (by fun_prop) (by simp) (HaarUniq.indicator_mem K hK))

theorem kill_loc {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [T2Space V]
    (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ} (hφ : φ ∈ SB V)
    (h : ∀ x, φ x ≠ 0 → ∃ U ∈ 𝓝 x, ∀ ψ ∈ SB V, (∀ y ∉ U, ψ y = 0) → l ψ = 0) : l φ = 0 := by
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support φ) := hφ.2.of_isClosed_subset hcl subset_closure
  have : ∃ A, IsClopen A ∧ Function.support φ ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0 := by
    refine hc.induction_on (p := fun s => ∃ A, IsClopen A ∧ s ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0)
      ⟨∅, isClopen_empty, subset_rfl, fun ψ _ h => ?_⟩ ?_ ?_ ?_
    · rw [show ψ = 0 from funext fun y => h y (by simp), map_zero]
    · rintro s t hst ⟨A, h1, h2, h3⟩; exact ⟨A, h1, hst.trans h2, h3⟩
    · rintro s t ⟨A, h1, h2, h3⟩ ⟨B, k1, k2, k3⟩
      refine ⟨A ∪ B, h1.union k1, Set.union_subset_union h2 k2, fun ψ hψ h => ?_⟩
      rw [← Set.indicator_self_add_compl A ψ, map_add (f := _), h3 _ (sb_cut h1 hψ) (fun y hy => Set.indicator_of_notMem hy _),
        k3 _ (sb_cut h1.compl hψ), add_zero]
      intro y hy
      by_cases hA : y ∈ A
      · exact Set.indicator_of_notMem (not_not.2 hA) _
      · rw [Set.indicator_of_mem hA]; exact h y (not_or.2 ⟨hA, hy⟩)
    · intro x hx
      obtain ⟨U, hU, hl⟩ := h x hx
      have : (fun k => k + x) ⁻¹' U ∈ 𝓝 (0 : V) := (continuous_add_const x).continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
      have hA : IsClopen ((fun y => y - x) ⁻¹' (K : Set V)) := K.isClopen.preimage (by fun_prop)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hA.isOpen.mem_nhds (by simp)), _, hA, subset_rfl,
        fun ψ hψ h0 => hl ψ hψ fun y hy => h0 y fun hy' => hy ?_⟩
      simpa using hK hy'
  obtain ⟨A, -, h2, h3⟩ := this
  exact h3 φ hφ fun y hy => by_contra fun h => hy (h2 h)

def Bump {V : Type} [Zero V] [TopologicalSpace V] (g : V → ℂ) : Prop := g ∈ SB V ∧ (∀ x, g x = 0 ∨ g x = 1) ∧ g 0 = 1

theorem exists_bump (V : Type) [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] : ∃ g : V → ℂ, Bump g := by
  obtain ⟨K, hK⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  refine ⟨_, HaarUniq.indicator_mem K hK, fun x => ?_, Set.indicator_of_mem K.zero_mem _⟩
  by_cases h : x ∈ (K : Set V) <;> simp [h]

theorem bump_ratio {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [LocallyCompactSpace V]
    [T2Space V] {g₀ g₁ : V → ℂ} (h₀ : Bump g₀) (h₁ : Bump g₁) : ∃ s : ℝ, 0 < s ∧ ∀ m : (V → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ ∈ SB V, ∀ a : V, m (fun x => φ (x + a)) = m φ) → m g₀ = s * m g₁ ∧ (m g₀ = 0 → ∀ g ∈ SB V, m g = 0) := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have pos : ∀ g : V → ℂ, Bump g → ∃ s : ℝ, 0 < s ∧ ∫ x, g x ∂μ = s := fun g hg => by
    refine ⟨∫ x, (g x).re ∂μ, ?_, ?_⟩
    · refine (Complex.continuous_re.comp hg.1.1.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hg.1.2.comp_left (g := Complex.re) rfl) (fun x => ?_) (x := 0) (by simp [hg.2.2])
      rcases hg.2.1 x with h | h <;> simp [h]
    · rw [← integral_complex_ofReal]
      congr 1; ext x; rcases hg.2.1 x with h | h <;> simp [h]
  obtain ⟨a, ha, ea⟩ := pos _ h₀
  obtain ⟨b, hb, eb⟩ := pos _ h₁
  refine ⟨a / b, div_pos ha hb, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := HaarUniq.exists_eq_mul_integral V μ m hm
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [hc _ h₀.1, hc _ h₁.1, ea, eb]
  refine ⟨by push_cast; field_simp, fun h g hg => ?_⟩
  rw [hc g hg, (mul_eq_zero.1 h).resolve_right ha', zero_mul]

theorem nonarch_pi (ι V : Type) [Finite ι] [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] :
    NonarchimedeanAddGroup (ι → V) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hU⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i).toAddSubgroup, isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩,
      fun x hx => hU fun i _ => hK i (hx i trivial)⟩

end GlobalTheory.ThK.Dbl.LD
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistE
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistD
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistC
open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] {n d : ℕ}

def blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : Matrix (Fin (d + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons a b) fun i => Fin.cons 0 (h i))

theorem det_blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : (blk a b h).det = a * h.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have : (blk a b h).submatrix Fin.succ Fin.succ = h := by ext i j; simp [blk]
  simp [blk] at this ⊢
  simp [this]

theorem mul_blk_zero {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m) :
    (X * blk a b h) i 0 = X i 0 * a := by simp [Matrix.mul_apply, Fin.sum_univ_succ, blk]

theorem mul_blk_succ {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m)
    (j : Fin d) : (X * blk a b h) i j.succ = X i 0 * b j + ∑ s, X i s.succ * h s j := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, blk]

theorem blk_comm (a : k) (b b' : Fin d → k) (hb : b = (a - 1) • b') :
    blk a 0 1 * blk 1 b' 1 = blk 1 b 1 * (blk 1 b' 1 * blk a 0 1) := by
  subst hb
  have hsum (f : Fin d → k) (j : Fin d) : ∑ x, f x * (1 : Matrix (Fin d) (Fin d) k) x j = f j := by
    simpa [Matrix.vecMul, dotProduct] using congrFun (Matrix.vecMul_one f) j
  ext i j
  rw [← Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j <;> simp only [mul_blk_zero, mul_blk_succ] <;>
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [blk, hsum, one_apply]
  ring

def chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k :=
  ((fun i => X i 0, fun j => X 0 j.succ / X 0 0), Matrix.of fun i j => X i.succ j.succ - X i.succ 0 * (X 0 j.succ / X 0 0))

def chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) : Matrix (Fin (n + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons (y.1.1 0) fun j => y.1.1 0 * y.1.2 j)
    fun i => Fin.cons (y.1.1 i.succ) fun j => y.1.1 i.succ * y.1.2 j + y.2 i j)

theorem chR_chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) : chR (chE X) = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR, chE]
  field_simp

theorem chE_chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) (hy : y.1.1 0 ≠ 0) : chE (chR y) = y := by
  obtain ⟨⟨x, u⟩, W⟩ := y
  simp only at hy
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [chR, chE]
  · ext j; simp [chR, chE, hy]
  · ext i j; simp [chR, chE, hy]

theorem chE_unip (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) (b : Fin d → k) :
    chE (X * blk 1 b 1) = (((chE X).1.1, (chE X).1.2 + b), (chE X).2) := by
  have hsum (f : Fin d → k) (j : Fin d) : ∑ x, f x * (1 : Matrix (Fin d) (Fin d) k) x j = f j := by
    simpa [Matrix.vecMul, dotProduct] using congrFun (Matrix.vecMul_one f) j
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j; simp [chE, mul_blk_zero, mul_blk_succ, hsum, one_apply]; field_simp; ring
  · ext i j; simp [chE, mul_blk_zero, mul_blk_succ, hsum, one_apply]; field_simp; ring

theorem chE_levi (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (h : Matrix (Fin d) (Fin d) k) :
    chE (X * blk 1 0 h) = (((chE X).1.1, (chE X).1.2 ᵥ* h), (chE X).2 * h) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j
    simp only [chE, mul_blk_zero, mul_blk_succ, vecMul, dotProduct, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  · ext i j
    simp only [chE, mul_blk_zero, mul_blk_succ, of_apply, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [of_apply]; ring

def Deg {m : Type} (X : Matrix m (Fin d) k) : Prop := ∃ v ≠ 0, X *ᵥ v = 0

theorem Deg.chE {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k} (h : Deg X) (hX : X 0 0 ≠ 0) : Deg (chE X).2 := by
  obtain ⟨v, hv, h⟩ := h
  have hi : ∀ i, X i 0 * v 0 + ∑ j : Fin d, X i j.succ * v j.succ = 0 := fun i => by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h i
  refine ⟨fun j => v j.succ, fun h0 => hv ?_, ?_⟩
  · have h1 : ∀ j : Fin d, v j.succ = 0 := congrFun h0
    ext j
    refine Fin.cases ?_ h1 j
    simpa [h1, hX] using hi 0
  · ext i
    have : ∑ j : Fin d, X i.succ 0 * (X 0 j.succ / X 0 0) * v j.succ = X i.succ 0 / X 0 0 * ∑ j : Fin d, X 0 j.succ * v j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    simp only [LD.chE, mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib, this, Pi.zero_apply,
      eq_neg_of_add_eq_zero_right (hi 0), eq_neg_of_add_eq_zero_right (hi i.succ)]
    field_simp; ring

variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]

theorem sb_right {m : Type} {φ : Matrix m (Fin d) k → ℂ} (hφ : φ ∈ SB _) {h : Matrix (Fin d) (Fin d) k} (hh : h.det ≠ 0) :
    (fun y => φ (y * h)) ∈ SB (Matrix m (Fin d) k) :=
  sb_comp (· * h) (· * h⁻¹) (by fun_prop) (by fun_prop) (fun x => mul_nonsing_inv_cancel_right h x hh.isUnit) hφ

theorem cont_chE : ContinuousOn (chE (k := k) (n := n) (d := d)) {X | X 0 0 ≠ 0} := by
  have h : ∀ j : Fin d, ContinuousOn (fun X : Matrix (Fin (n + 1)) (Fin (d + 1)) k => X 0 j.succ / X 0 0) {X | X 0 0 ≠ 0} :=
    fun j => ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun _ h => h
  refine ContinuousOn.prodMk (ContinuousOn.prodMk (by fun_prop) (continuousOn_pi.2 h))
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_)
  exact ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) (h j))

theorem cont_chR : Continuous (chR (k := k) (n := n) (d := d)) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR] <;> fun_prop

theorem sb_chE {F : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k → ℂ} (hF : F ∈ SB _)
    (h0 : ∀ y, y.1.1 0 = 0 → F y = 0) : (fun X => F (chE X)) ∈ SB (Matrix (Fin (n + 1)) (Fin (d + 1)) k) :=
  sb_chart (U := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (T := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const) cont_chE
    cont_chR.continuousOn chR_chE (fun y hy => by simpa [chR] using hy) hF (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun X hX => h0 _ (not_not.1 hX)

theorem sb_chR {φ : Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X 0 0 = 0 → φ X = 0) :
    (fun y => φ (chR y)) ∈ SB (((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) :=
  sb_chart (T := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (U := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const)
    cont_chR.continuousOn cont_chE chE_chR (fun _ hy => hy) hφ (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun y hy => h0 _ (by simpa [chR] using hy)

def Eqv (c : k → ℂ) {m : Type} (l : (Matrix m (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ h : Matrix (Fin d) (Fin d) k, h.det ≠ 0 → ∃ t : ℝ, 0 < t ∧ ∀ φ ∈ SB _, l (fun y => φ (y * h)) = c h.det * t * l φ

theorem Eqv.unip {c : k → ℂ} (hc : ∀ a ≠ 0, c a ≠ 0) {ϖ : k} (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {m : Type}
    {l : (Matrix m (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} [Fintype m] (hl : Eqv c l) (b : Fin d → k) :
    ∀ φ ∈ SB _, l (fun y => φ (y * blk 1 b 1)) = l φ := by
  have hu : ∀ b : Fin d → k, (blk 1 b 1).det ≠ 0 := fun b => by simp [det_blk]
  have hD : (blk ϖ (0 : Fin d → k) 1).det ≠ 0 := by simp [det_blk, h0]
  obtain ⟨t₁, -, e₁⟩ := hl _ (hu b)
  obtain ⟨t₂, p₂, e₂⟩ := hl _ (hu ((ϖ - 1)⁻¹ • b))
  obtain ⟨t₃, p₃, e₃⟩ := hl _ hD
  intro φ hφ
  have a := e₃ _ (sb_right hφ (hu ((ϖ - 1)⁻¹ • b)))
  have a' := e₁ _ (sb_right (sb_right hφ hD) (hu ((ϖ - 1)⁻¹ • b)))
  simp only [Matrix.mul_assoc] at a a'
  rw [blk_comm ϖ b _ (by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 h1), one_smul]), a', e₂ _ hφ] at a
  have a2 := e₂ _ (sb_right hφ hD)
  simp only [Matrix.mul_assoc] at a2
  rw [a2, e₃ _ hφ] at a
  rw [e₁ _ hφ]
  have n2 : c (blk 1 ((ϖ - 1)⁻¹ • b) 1).det * t₂ ≠ 0 := mul_ne_zero (hc _ (hu _)) (by exact_mod_cast p₂.ne')
  have n3 : c (blk ϖ (0 : Fin d → k) 1).det * t₃ ≠ 0 := mul_ne_zero (hc _ hD) (by exact_mod_cast p₃.ne')
  apply mul_left_cancel₀ (mul_ne_zero n2 n3)
  linear_combination a

end GlobalTheory.ThK.Dbl.LD
end

open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}

theorem nonarch_mat (n d : ℕ) : NonarchimedeanAddGroup (Matrix (Fin n) (Fin d) k) :=
  haveI := nonarch_pi (Fin d) k
  nonarch_pi (Fin n) (Fin d → k)

theorem lc_mat (n d : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))

def Claim (c : k → ℂ) (n d : ℕ) : Prop :=
  ∀ l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, Eqv c l → (∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) → ∀ φ ∈ SB _, l φ = 0

theorem step_chart (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {n d : ℕ} (ih : Claim c n d)
    {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_pi (Fin d) k
  have := nonarch_mat (k := k) n d
  have := lc_mat (k := k) n d
  intro φ hφ hz
  let L := l ∘ₗ LinearMap.funLeft ℂ ℂ (chE (k := k) (n := n) (d := d))
  have hL : ∀ F, L F = l fun X => F (chE X) := fun _ => rfl
  have e : φ = fun X => φ (chR (chE X)) := by
    ext X
    by_cases hX : X 0 0 = 0
    · rw [hz X hX, hz _ (by simpa [chR, chE] using hX)]
    · rw [chR_chE X hX]
  rw [e, ← hL fun y => φ (chR y)]
  refine kill_tens {z | z.1 0 ≠ 0} L (fun F hF hF0 ψ hψ => ?_) (sb_chR hφ hz)
    fun z h => hz _ (by simpa [chR] using h)
  let T : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin (n + 1) → k) × (Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun F => L fun z => F z.1 * ψ z.2
      map_add' := fun F F' => by rw [← map_add (f := _)]; congr 1; ext z; simp [add_mul]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_assoc] }
  refine kill_tens {x : Fin (n + 1) → k | x 0 ≠ 0} (T ψ) (fun f hf hf0 => ?_) hF fun z h => hF0 z h
  replace hf0 : ∀ x, x 0 = 0 → f x = 0 := fun x hx => hf0 x (not_not.2 hx)
  let m : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun g => T ψ fun z => f z.1 * g z.2
      map_add' := fun F F' => by rw [← map_add (f := _)]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have hm : ∀ ψ g, m ψ g = l fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2 := fun _ _ => rfl
  have sb : ∀ ψ ∈ SB _, ∀ g ∈ SB (Fin d → k), (fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2) ∈ SB _ := fun ψ hψ g hg =>
    sb_chE (sb_tens (sb_tens hf hg) hψ) fun y hy => by simp [hf0 _ hy]
  have inv : ∀ ψ ∈ SB _, ∀ g ∈ SB _, ∀ a, m ψ (fun x => g (x + a)) = m ψ g := fun ψ hψ g hg a => by
    rw [hm, hm, ← hl.unip hc h0 h1 a _ (sb ψ hψ g hg)]
    congr 1; ext X
    by_cases hX : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX), hf0 _ (by simpa [chE, mul_blk_zero] using hX)]; simp
    · rw [chE_unip X hX]
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  obtain ⟨_, -, hs⟩ := bump_ratio hg₀ hg₀
  refine (hs _ (inv ψ hψ)).2 ?_
  let l₁ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => f (chE X).1.1 * g₀ (chE X).1.2 * ψ (chE X).2
      map_add' := fun F F' => by rw [← map_add (f := _)]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  refine ih l₁ (fun h hh => ?_) (fun ψ hψ hψ0 => hd _ (sb ψ hψ _ hg₀.1) fun X hX => ?_) ψ hψ
  · have hg₁ : Bump fun u => g₀ (u ᵥ* h) :=
      ⟨sb_comp (· ᵥ* h) (· ᵥ* h⁻¹) (by fun_prop) (by fun_prop)
        (fun x => by simp [mul_nonsing_inv h hh.isUnit]) hg₀.1, fun _ => hg₀.2.1 _, by simpa using hg₀.2.2⟩
    obtain ⟨s, ps, hs⟩ := bump_ratio hg₀ hg₁
    obtain ⟨t, pt, ht⟩ := hl (blk 1 0 h) (by simpa [det_blk] using hh)
    refine ⟨t * s, mul_pos pt ps, fun ψ hψ => ?_⟩
    have a := ht _ (sb ψ hψ _ hg₀.1)
    simp only [chE_levi, det_blk, one_mul] at a
    have b := (hs _ (inv _ (sb_right hψ hh))).1
    refine b.trans ((congrArg ((s : ℂ) * ·) a).trans ?_)
    show _ * (_ * l₁ ψ) = _
    push_cast; ring
  · by_cases hX0 : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX0)]; simp
    · rw [hψ0 _ (hX.chE hX0), mul_zero]

theorem step_row (hc : ∀ a ≠ 0, c a ≠ 0) {n d : ℕ} {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hz : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_mat (k := k) (n + 1) (d + 1)
  intro φ hφ h0
  refine kill_loc l hφ fun x hx => ?_
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (fun h => hx (h0 x h) : x 0 ≠ 0)
  refine ⟨{X | X 0 j ≠ 0}, (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hj, fun ψ hψ hψ0 => ?_⟩
  have hh : (swap k 0 j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self 0 j)).ne_zero
  obtain ⟨t, pt, ht⟩ := hl _ hh
  have a := ht ψ hψ
  rw [hz _ (sb_right hψ hh) fun X hX => hψ0 _ (by simpa [mul_swap_apply_right] using hX)] at a
  exact (mul_eq_zero.1 a.symm).resolve_left (mul_ne_zero (hc _ hh) (by exact_mod_cast pt.ne'))

theorem step_closed {n d : ℕ} (ih : Claim c n d) {l : (Matrix (Fin (n + 1)) (Fin d) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) (hz : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0) :
    ∀ φ ∈ SB _, l φ = 0 := by
  have := nonarch_pi (Fin d) k
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  let cn : (Fin d → k) → Matrix (Fin n) (Fin d) k → Matrix (Fin (n + 1)) (Fin d) k := fun y Y => Matrix.of (Fin.cons y Y)
  let tl : Matrix (Fin (n + 1)) (Fin d) k → Matrix (Fin n) (Fin d) k := fun X => X.submatrix Fin.succ id
  have ccn : Continuous fun z : (Fin d → k) × Matrix (Fin n) (Fin d) k => cn z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [cn] <;> fun_prop
  have ctl : Continuous tl := by fun_prop
  have hcn : ∀ X, cn (X 0) (tl X) = X := fun X => by
    ext i j; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have sb : ∀ ψ ∈ SB _, (fun X => g₀ (X 0) * ψ (tl X)) ∈ SB (Matrix (Fin (n + 1)) (Fin d) k) := fun ψ hψ =>
    sb_comp (fun X => (X 0, tl X)) (fun z => cn z.1 z.2) (by fun_prop) ccn hcn (sb_tens hg₀.1 hψ)
  let l₂ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => g₀ (X 0) * ψ (tl X)
      map_add' := fun F F' => by rw [← map_add (f := _)]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have eq : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, (∀ X, X 0 = 0 → φ X = φ' X) → l φ = l φ' := fun φ hφ φ' hφ' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hz _ (sub_mem hφ hφ') fun X hX => sub_eq_zero.2 (h X hX)
  have z := ih l₂ (fun h hh => ?_) fun ψ hψ hψ0 => hd _ (sb ψ hψ) fun X hX => ?_
  · intro φ hφ
    have hr : (fun Y => φ (cn 0 Y)) ∈ SB _ :=
      sb_comp (cn 0) tl (ccn.comp (Continuous.prodMk_right 0)) ctl (fun Y => rfl) hφ
    refine (eq φ hφ _ (sb _ hr) fun X hX => ?_).trans (z _ hr)
    have := hcn X
    rw [hX] at this
    rw [this, hX, hg₀.2.2, one_mul]
  · obtain ⟨t, pt, ht⟩ := hl h hh
    refine ⟨t, pt, fun ψ hψ => (eq _ (sb _ (sb_right hψ hh)) _ (sb_right (sb ψ hψ) hh) fun X hX => ?_).trans (ht _ (sb ψ hψ))⟩
    have : (X * h) 0 = 0 := by ext j; simp [Matrix.mul_apply, hX]
    rw [hX, this]; rfl
  · obtain ⟨v, hv, h⟩ := hX
    rw [hψ0 (tl X) ⟨v, hv, funext fun i => congrFun h i.succ⟩, mul_zero]

theorem claim (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) (hϖ : ∀ t : ℝ, 0 < t → c ϖ * t ≠ 1) (n : ℕ) :
    ∀ d, Claim c n d := by
  have zero : ∀ n, Claim c n 0 := fun n l _ h φ hφ => h φ hφ fun X ⟨v, hv, _⟩ => absurd (Subsingleton.elim _ _) hv
  induction n with
  | zero =>
    rintro (_ | d)
    · exact zero _
    intro l hl _ φ hφ
    obtain ⟨t, pt, ht⟩ := hl (blk ϖ 0 1) (by simp [det_blk, h0])
    have a := ht φ hφ
    have e : ∀ y : Matrix (Fin 0) (Fin (d + 1)) k, y * blk ϖ (0 : Fin d → k) 1 = y := fun y => by ext i; exact i.elim0
    simp only [e, det_blk, det_one, mul_one] at a
    by_contra h
    exact hϖ t pt (mul_right_cancel₀ h (by rw [← a, one_mul]))
  | succ n ih =>
    rintro (_ | d)
    · exact zero _
    exact fun l hl hd => step_closed (ih _) hl hd (step_row hc hl (step_chart hc h0 h1 (ih d) hl hd))

end GlobalTheory.ThK.Dbl.LD
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocDistB
open Filter Topology GlobalTheory.WeilM

namespace GlobalTheory.ThK.Dbl.LD

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

noncomputable def ind (K : Subgroup G) : G → ℂ := Set.indicator (K : Set G) fun _ => 1

theorem ind_mem {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : ind K ∈ SB G :=
  ⟨(LocallyConstant.charFn ℂ ⟨K.isClosed_of_isOpen ho, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun _ hx => Set.indicator_of_notMem hx _⟩

theorem ind_index (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {H K : Subgroup G} (hHK : H ≤ K) (ho : IsOpen (H : Set G)) (hc : IsCompact (K : Set G)) (hχ : ∀ k ∈ K, χ k = 1) :
    l (ind K) = H.relIndex K * l (ind H) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : DiscreteTopology (K ⧸ H.subgroupOf K) := QuotientGroup.discreteTopology (ho.preimage continuous_subtype_val)
  haveI : Fintype (K ⧸ H.subgroupOf K) := @Fintype.ofFinite _ finite_of_compact_of_discrete
  have hH := ind_mem ho (hc.of_isClosed_subset (H.isClosed_of_isOpen ho) hHK)
  have : ind K = ∑ q : K ⧸ H.subgroupOf K, fun x => ind H (x * q.out.1) := by
    ext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ K
    · have hmem : ∀ q : K ⧸ H.subgroupOf K, x * q.out.1 ∈ (H : Set G) ↔ ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K) = q := by
        intro q
        conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
        rfl
      rw [Finset.sum_eq_single ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K)]
      · rw [ind, ind, Set.indicator_of_mem ((hmem _).2 rfl), Set.indicator_of_mem (by exact hx)]
      · intro q _ hq; exact Set.indicator_of_notMem (fun h => hq ((hmem q).1 h).symm) _
      · simp
    · rw [ind, Set.indicator_of_notMem (by exact hx)]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem
        (fun h => hx ((mul_mem_cancel_right q.out.2).1 (hHK h))) _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum, Finset.sum_congr rfl fun q _ => by rw [hl _ hH, hχ _ q.out.2, one_mul]]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem ind_zero (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (hχ : χ k ≠ 1) :
    l (ind K) = 0 := by
  have h := hl _ (ind_mem ho hc) k
  have : (fun x => ind K (x * k)) = ind K := by
    classical
    ext x; exact if_congr (K.mul_mem_cancel_right hk) rfl rfl
  rw [this] at h
  by_contra h0
  exact hχ (mul_right_cancel₀ h0 (by rw [← h, one_mul]))

theorem left_of_right (χ : G →* ℂ) (θ : G →* G) (cθ : Continuous θ) (iθ : ∀ x, θ (θ x) = x) {g : G} (hg : θ g = g⁻¹)
    (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ) {φ : G → ℂ} (hφ : φ ∈ SB G) :
    l (fun x => φ (g * x)) = χ g * l φ := by
  classical
  by_cases h0 : φ = 0
  · subst h0; exact (map_zero l).trans (by rw [map_zero, mul_zero])
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 h0
  let K₀ : Subgroup G :=
    { carrier := {k | ∀ x, φ (k * x) = φ x}
      one_mem' := fun x => by rw [one_mul]
      mul_mem' := fun {a b} ha hb x => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha x => by rw [← ha, mul_inv_cancel_left] }
  have o₀ : IsOpen (K₀ : Set G) := by
    refine K₀.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [sb_unif hφ (fun k x => k * x) (1 : G) (by fun_prop) one_mul,
      sb_unif hφ (fun k x => k⁻¹ * x) (1 : G) (by fun_prop) (by simp)] with k h1 h2 x
    by_cases hx : x ∈ tsupport φ
    · exact h1 x hx
    · by_cases hx' : k * x ∈ tsupport φ
      · simpa using (h2 _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  have c₀ : IsCompact (K₀ : Set G) :=
    (IsCompact.image hφ.2 (continuous_mul_const x₀⁻¹)).of_isClosed_subset (K₀.isClosed_of_isOpen o₀) fun k hk =>
      ⟨k * x₀, subset_tsupport _ (by rw [Function.mem_support, hk x₀]; exact hx₀), by simp⟩
  let K := K₀ ⊓ K₀.comap θ
  have o : IsOpen (K : Set G) := o₀.inter (o₀.preimage cθ)
  have c : IsCompact (K : Set G) := c₀.of_isClosed_subset (K.isClosed_of_isOpen o) fun k hk => hk.1
  have hθ : ∀ x, θ x ∈ K ↔ x ∈ K := fun x => by
    show θ x ∈ K₀ ∧ θ (θ x) ∈ K₀ ↔ x ∈ K₀ ∧ θ x ∈ K₀
    rw [iθ]; exact and_comm
  let K' := K.comap (MulAut.conj g).toMonoidHom
  have hK' : ∀ x, x ∈ K' ↔ g * x * g⁻¹ ∈ K := fun x => Iff.rfl
  have hs : ind K' = fun x => ind K (g * x * g⁻¹) := rfl
  have o' : IsOpen (K' : Set G) := o.preimage (f := fun x => g * x * g⁻¹) (by fun_prop)
  have c' : IsCompact (K' : Set G) := (c.image (f := fun x => g⁻¹ * x * g) (by fun_prop)).of_isClosed_subset
    (K'.isClosed_of_isOpen o') fun x hx => ⟨_, (hK' x).1 hx, by group⟩
  have hconj : ∀ x, χ (g * x * g⁻¹) = χ x := fun x => by
    rw [map_mul, map_mul, mul_comm (χ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have key : l (ind K') = l (ind K) := by
    by_cases hχ : ∀ k ∈ K, χ k = 1
    · have hχ' : ∀ k ∈ K', χ k = 1 := fun k hk => by rw [← hconj, hχ _ ((hK' k).1 hk)]
      rw [ind_index χ l hl (inf_le_left : K ⊓ K' ≤ K) (o.inter o') c hχ,
        ind_index χ l hl (inf_le_right : K ⊓ K' ≤ K') (o.inter o') c' hχ', Subgroup.inf_relIndex_left,
        Subgroup.inf_relIndex_right]
      let α := θ.comp (MulAut.conj g).toMonoidHom
      have hα : ∀ x, α x = θ (g * x * g⁻¹) := fun _ => rfl
      have e1 : K.comap α = K' := by ext x; rw [Subgroup.mem_comap, hα, hθ, hK']
      have e2 : K.map α = K' := by
        ext x
        rw [Subgroup.mem_map, hK']
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hα, map_mul, map_mul, map_inv, hg]; simpa [mul_assoc] using (hθ y).2 hy
        · intro hx
          refine ⟨_, (hθ _).2 hx, ?_⟩
          rw [hα, map_mul, map_mul, map_inv, hg, iθ]; group
      conv_rhs => rw [← e1, Subgroup.relIndex_comap, e2, e1]
    · push Not at hχ
      obtain ⟨k, hk, hχ⟩ := hχ
      rw [ind_zero χ l hl o c hk hχ, ind_zero χ l hl o' c' (k := g⁻¹ * k * g) ((hK' _).2 (by simpa [mul_assoc] using hk))]
      rw [← hconj]; simpa [mul_assoc] using hχ
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology o
  have hfin : ((fun x : G => ((x⁻¹ : G) : G ⧸ K)) '' tsupport φ).Finite :=
    (IsCompact.image hφ.2 (QuotientGroup.continuous_mk.comp continuous_inv)).finite_of_discrete
  have hmem : ∀ (x : G) (q : G ⧸ K), x * q.out ∈ (K : Set G) ↔ ((x⁻¹ : G) : G ⧸ K) = q := by
    intro x q
    conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
    rfl
  have dec : ∀ x, φ x = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ * ind K (x * q.out) := fun x => by
    have hx : φ ((x⁻¹ : G) : G ⧸ K).out⁻¹ = φ x := by
      rw [← ((hmem x _).2 rfl).1, mul_inv_cancel_right]
    rw [Finset.sum_eq_single ((x⁻¹ : G) : G ⧸ K)]
    · rw [ind, Set.indicator_of_mem ((hmem x _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [ind, Set.indicator_of_notMem (fun h => hq ((hmem x q).1 h).symm), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := φ) (x := x), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  have d1 : φ = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K (x * q.out) := by
    ext x; rw [dec x]; simp
  have d2 : (fun x => φ (g * x)) = ∑ q ∈ hfin.toFinset, φ q.out⁻¹ • fun x => ind K' (x * (q.out * g)) := by
    ext x; rw [dec, hs]; simp [mul_assoc]
  rw [d2]
  conv_rhs => rw [d1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, map_smul, hl _ (ind_mem o' c'), hl _ (ind_mem o c), key, map_mul, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.ThK.Dbl.LD
end

open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}

def invT : GL (Fin d) k →* GL (Fin d) k where
  toFun x := ⟨x.invᵀ, x.valᵀ, by rw [← transpose_mul, x.val_inv, transpose_one], by rw [← transpose_mul, x.inv_val, transpose_one]⟩
  map_one' := Units.ext transpose_one
  map_mul' x y := Units.ext (transpose_mul _ _)

theorem cont_invT : Continuous (invT (k := k) (d := d)) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩


open Classical in
noncomputable def toGL (X : Matrix (Fin d) (Fin d) k) : GL (Fin d) k := if h : IsUnit X then h.unit else 1

theorem toGL_val {X : Matrix (Fin d) (Fin d) k} (h : X.det ≠ 0) : (toGL X).1 = X := by
  rw [toGL, dite_eq_left ((isUnit_iff_isUnit_det X).2 h.isUnit)]; rfl

theorem toGL_coe (x : GL (Fin d) k) : toGL x.1 = x := Units.ext (toGL_val x.det_ne_zero)

theorem cont_toGL : ContinuousOn (toGL (k := k) (d := d)) {X | X.det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨continuous_subtype_val.congr fun X => (toGL_val X.2).symm, ?_⟩
  have : ContinuousOn (fun X : Matrix (Fin d) (Fin d) k => X⁻¹) {X | X.det ≠ 0} := fun X hX =>
    (continuousAt_matrix_inv X (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hX)).continuousWithinAt
  refine this.restrict.congr fun X => ?_
  rw [coe_units_inv]
  exact congrArg _ (toGL_val X.2).symm

theorem top_cell (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    {g : GL (Fin d) k} (hg : g.1ᵀ = g.1) {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X.det = 0 → φ X = 0) :
    l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  classical
  have hU : IsOpen {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  let m : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => if X.det ≠ 0 then ψ (toGL X) else 0
      map_add' := fun F F' => by rw [← map_add (f := _)]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h] }
  have hm : ∀ ψ, m ψ = l fun X => if X.det ≠ 0 then ψ (toGL X) else 0 := fun _ => rfl
  have a := left_of_right ((Units.coeHom ℂ).comp (ξ.comp GeneralLinearGroup.det)) invT cont_invT
    (fun x => Units.ext (transpose_transpose _)) (g := g)
    (inv_injective (Units.ext hg)) m (fun ψ hψ h => ?_) (φ := fun x => φ x.1)
    (sb_chart (U := Set.univ) (T := {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0}) isOpen_univ Units.continuous_val.continuousOn cont_toGL
      (fun x _ => toGL_coe x) (fun _ _ => trivial) hφ (fun X hX => h0 X (not_not.1 hX)) (fun _ _ => rfl)
      fun _ h => absurd trivial h)
  · rw [hm, hm] at a
    convert a using 3 with X
    · split_ifs with h
      · rw [Units.val_mul, toGL_val h]
      · exact h0 _ (by rw [det_mul, not_not.1 h, mul_zero])
    · rfl
    · ext X
      split_ifs with h
      · rw [toGL_val h]
      · exact h0 _ (not_not.1 h)
  · rw [hm, hm]
    refine Eq.trans ?_ (hl (fun X => if X.det ≠ 0 then ψ (toGL X) else 0) (sb_chart (T := Set.univ) hU cont_toGL Units.continuous_val.continuousOn (fun X hX => toGL_val hX)
      (fun x _ => x.det_ne_zero) hψ (fun _ h => absurd trivial h) (fun X hX => if_pos hX) fun X hX => if_neg hX) h)
    congr 1; ext X
    by_cases hX : X.det = 0
    · simp [hX]
    · have : (X * h.1).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hX h.det_ne_zero
      rw [if_pos hX, if_pos this]
      congr 1; apply Units.ext
      rw [Units.val_mul, toGL_val hX, toGL_val this]

variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]

theorem vanish (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ}
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, l φ = 0 := by
  classical
  let c : k → ℂ := fun a => if h : a = 0 then 0 else ξ (Units.mk0 a h)
  have hc : ∀ a : kˣ, c a = ξ a := fun a => by simp [c]
  refine claim (c := c) (ϖ := ϖ) (fun a ha => ?_) ϖ.ne_zero (fun h => hξ 1 one_pos ?_) (fun t ht h => hξ t⁻¹ (inv_pos.2 ht) ?_)
    n d l (fun h hh => ⟨1, one_pos, fun φ hφ => ?_⟩) hd
  · simp [c, ha]
  · rw [Units.val_eq_one.1 h]; simp
  · rw [← hc, Complex.ofReal_inv]; exact eq_inv_of_mul_eq_one_left h
  · have := hl φ hφ (toGL h)
    rw [← hc, GeneralLinearGroup.val_det_apply, toGL_val hh] at this
    simpa using this

theorem lt_case (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ} (hn : n < d)
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) :
    ∀ φ ∈ SB _, l φ = 0 := by
  refine vanish ξ ϖ hξ l hl fun φ _ h => ?_
  rw [show φ = 0 from funext fun X => h X ?_, map_zero]
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := X.mulVecLin) (by simpa using hn))
  exact ⟨v, h0, hv⟩

theorem sb_left {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin d) k) :
    (fun y => φ (g.1 * y)) ∈ SB (Matrix (Fin d) (Fin d) k) :=
  sb_comp (g.1 * ·) ((g⁻¹).1 * ·) (by fun_prop) (by fun_prop) (fun x => g.inv_mul_cancel_left x) hφ

theorem eq_case (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t)
    (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) (g : GL (Fin d) k) :
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  let P : Matrix (Fin d) (Fin d) k → Prop := fun M => ∀ g : GL (Fin d) k, g.1 = M →
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ
  have sym : ∀ M, Mᵀ = M → P M := by
    rintro _ hg g rfl φ hφ
    refine sub_eq_zero.1 (vanish ξ ϖ hξ (l ∘ₗ LinearMap.funLeft ℂ ℂ (g.1 * ·) - (ξ (GeneralLinearGroup.det g) : ℂ) • l)
      (fun ψ hψ h => ?_) (fun ψ hψ h0 => sub_eq_zero.2 (top_cell ξ l hl hg hψ fun X hX => h0 X ?_)) φ hφ)
    · have a := hl _ (sb_left hψ g) h
      simp only [← Matrix.mul_assoc] at a
      show (l fun y => ψ (g.1 * y * h.1)) - _ * (l fun y => ψ (y * h.1)) = _ * ((l fun y => ψ (g.1 * y)) - _ * l ψ)
      rw [a, hl ψ hψ h]; ring
    · exact exists_mulVec_eq_zero_iff.2 hX
  have mul : ∀ A B : Matrix (Fin d) (Fin d) k, A.det ≠ 0 → B.det ≠ 0 → P A → P B → P (A * B) := by
    intro A B hA hB pA pB g hg φ hφ
    have e : g = toGL A * toGL B := Units.ext (by rw [hg, Units.val_mul, toGL_val hA, toGL_val hB])
    have a := pB _ (toGL_val hB) _ (sb_left hφ (toGL A))
    rw [pA _ (toGL_val hA) _ hφ] at a
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [a]; ring
  refine diagonal_transvection_induction_of_det_ne_zero P g.1 g.det_ne_zero (fun D _ => sym _ (diagonal_transpose D))
    (fun t => ?_) mul g rfl
  have hs : (swap k t.i t.j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self _ _)).ne_zero
  have := mul _ (swap k t.i t.j * t.toMatrix) hs (by rw [det_mul, t.det, mul_one]; exact hs) (sym _ (transpose_swap _ _))
    (sym _ ?_)
  · rwa [← Matrix.mul_assoc, swap_mul_self, Matrix.one_mul] at this
  have e : swap k t.i t.j * single t.i t.j t.c = single t.j t.j t.c := by
    ext a b
    by_cases h1 : a = t.i
    · rw [h1, swap_mul_apply_left]; simp [single_apply, t.hij, t.hij.symm]
    by_cases h2 : a = t.j
    · rw [h2, swap_mul_apply_right]; simp [single_apply]
    · rw [swap_mul_of_ne h1 h2]; simp [single_apply, Ne.symm h1, Ne.symm h2]
  rw [TransvectionStruct.toMatrix, transvection, Matrix.mul_add, Matrix.mul_one, e, transpose_add, transpose_swap,
    transpose_single]

end GlobalTheory.ThK.Dbl.LD
end

namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel

theorem locDist : LocDist := by
  intro F _ _ v n d ξ hξ l hl
  have : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
  have : LocallyCompactSpace (Fv F v) := inferInstance
  have : NonarchimedeanAddGroup (Fv F v) := by
    refine ⟨fun U hU => ?_⟩
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    exact ⟨⟨(Valued.v.restrict.ltAddSubgroup γ), Valued.isOpen_ball _ _⟩, hγ⟩
  refine ⟨fun h => LD.lt_case ξ _ hξ h l hl, ?_⟩
  rintro rfl φ hφ g
  exact LD.eq_case ξ _ hξ l hl g φ hφ

end GlobalTheory.ThK.Dbl
