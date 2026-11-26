module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSign
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComboNotMemSpan
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI

theorem combo_notMem_span {V : Type} [AddCommGroup V] [Module ℚ V] {s : Set V} {p q : V} {a b : ℚ}
    (ha : a ≠ 0) (hp : p ∉ Submodule.span ℚ s) (hq : q ∈ Submodule.span ℚ s) :
    a • p + b • q ∉ Submodule.span ℚ s := by
  intro h
  apply hp
  have h1 : a • p ∈ Submodule.span ℚ s := by
    have := Submodule.sub_mem _ h (Submodule.smul_mem _ b hq)
    simpa using this
  have h2 := Submodule.smul_mem _ a⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2

theorem main : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq V] (p q : V) (r : Finset V) (a b : ℚ), 0 < a → 0 < b → p ≠ q → p ∉ r → q ∉ r →
  LinearIndepOn ℚ id ((insert p (insert q r) : Finset V) : Set V) →
  (a • p + b • q) ∉ r ∧ (a • p + b • q) ≠ p ∧ (a • p + b • q) ≠ q ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) (insert q r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert p (insert (a • p + b • q) r) : Finset V) : Set V) ∧
  LinearIndepOn ℚ id ((insert (a • p + b • q) r : Finset V) : Set V) := by
  intro V _ _ _ p q r a b ha hb hpq hpr hqr hli
  simp only [Finset.coe_insert] at hli ⊢
  have hp' : p ∉ insert q (r : Set V) := by simp [hpq, hpr]
  have hq' : q ∉ (r : Set V) := by simpa using hqr
  have hq'' : q ∉ insert p (r : Set V) := by simp [hpq.symm, hqr]
  obtain ⟨hli1, hpn⟩ := (linearIndepOn_id_insert hp').mp hli
  obtain ⟨hliR, -⟩ := (linearIndepOn_id_insert hq').mp hli1
  have hli' : LinearIndepOn ℚ id (insert q (insert p (r : Set V))) := by rwa [Set.insert_comm]
  obtain ⟨hli2, hqn2⟩ := (linearIndepOn_id_insert hq'').mp hli'
  have hw1 : a • p + b • q ∉ Submodule.span ℚ (insert q (r : Set V)) :=
    combo_notMem_span ha.ne' hpn (Submodule.subset_span (Set.mem_insert q _))
  have hw2 : a • p + b • q ∉ Submodule.span ℚ (insert p (r : Set V)) := by
    rw [add_comm]
    exact combo_notMem_span hb.ne' hqn2 (Submodule.subset_span (Set.mem_insert p _))
  have hw3 : a • p + b • q ∉ Submodule.span ℚ (r : Set V) := fun h =>
    hw1 (Submodule.span_mono (Set.subset_insert q _) h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hw3 (Submodule.subset_span (Finset.mem_coe.mpr h))
  · intro h
    exact hw2 (by rw [h]; exact Submodule.subset_span (Set.mem_insert p _))
  · intro h
    exact hw1 (by rw [h]; exact Submodule.subset_span (Set.mem_insert q _))
  · exact (linearIndepOn_id_insert fun h => hw1 (Submodule.subset_span h)).mpr ⟨hli1, hw1⟩
  · rw [Set.insert_comm]
    exact (linearIndepOn_id_insert fun h => hw2 (Submodule.subset_span h)).mpr ⟨hli2, hw2⟩
  · exact (linearIndepOn_id_insert fun h => hw3 (Submodule.subset_span h)).mpr ⟨hliR, hw3⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.StellarLI
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSign
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem signConst_of_nonneg (l : V →ₗ[ℚ] ℚ) (s : Finset V) (h : ∀ v ∈ s, 0 ≤ l v) : SignConst l (coneOn s) := by
  unfold SignConst
  by_cases hz : ∀ v ∈ s, l v = 0
  · refine Or.inl ?_
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, -, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => by rw [map_smul, hz i hi, smul_zero])
  · refine Or.inr (Or.inl ?_)
    push_neg at hz
    obtain ⟨w, hw, hlw⟩ := hz
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hnn : ∀ i ∈ s, 0 ≤ l (t i • i) := fun i hi => by
      rw [map_smul, smul_eq_mul]; exact mul_nonneg (ht i hi).le (h i hi)
    have hpos : 0 < l (t w • w) := by
      rw [map_smul, smul_eq_mul]; exact mul_pos (ht w hw) (lt_of_le_of_ne (h w hw) (Ne.symm hlw))
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnn hw)

theorem signConst_of_nonpos (l : V →ₗ[ℚ] ℚ) (s : Finset V) (h : ∀ v ∈ s, l v ≤ 0) : SignConst l (coneOn s) := by
  unfold SignConst
  by_cases hz : ∀ v ∈ s, l v = 0
  · refine Or.inl ?_
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, -, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => by rw [map_smul, hz i hi, smul_zero])
  · refine Or.inr (Or.inr ?_)
    push_neg at hz
    obtain ⟨w, hw, hlw⟩ := hz
    intro x hx
    simp only [coneOn, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hnp : ∀ i ∈ s, 0 ≤ -l (t i • i) := fun i hi => by
      rw [map_smul, smul_eq_mul]; nlinarith [(ht i hi).le, h i hi]
    have hneg : l (t w • w) < 0 := by
      have hlt : l w < 0 := lt_of_le_of_ne (h w hw) hlw
      rw [map_smul, smul_eq_mul]; nlinarith [ht w hw]
    have key := Finset.single_le_sum hnp hw
    simp only [Finset.sum_neg_distrib] at key
    linarith

private theorem sum_insert_insert_ite_ite_smul [DecidableEq V] {p q : V} {X : Finset V} (hp : p ∉ insert q X) (hq : q ∉ X)
    (α β : ℚ) (t : V → ℚ) :
    ∑ i ∈ insert p (insert q X), (if i = p then α else if i = q then β else t i) • i
      = α • p + (β • q + ∑ i ∈ X, t i • i) := by
  have hqp : q ≠ p := fun e => hp (by rw [← e]; exact Finset.mem_insert_self q X)
  have hpX : p ∉ X := fun e => hp (Finset.mem_insert_of_mem e)
  have hX : ∑ i ∈ X, (if i = p then α else if i = q then β else t i) • i = ∑ i ∈ X, t i • i :=
    Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (fun e => hpX (by rw [← e]; exact hj)), if_neg (fun e => hq (by rw [← e]; exact hj))])
  rw [Finset.sum_insert hp, Finset.sum_insert hq, if_pos rfl, if_neg hqp, if_pos rfl, hX]

private theorem sum_insert_ite_smul [DecidableEq V] {p : V} {X : Finset V} (hp : p ∉ X) (α : ℚ) (t : V → ℚ) :
    ∑ i ∈ insert p X, (if i = p then α else t i) • i = α • p + ∑ i ∈ X, t i • i := by
  have hX : ∑ i ∈ X, (if i = p then α else t i) • i = ∑ i ∈ X, t i • i :=
    Finset.sum_congr rfl (fun j hj => by rw [if_neg (fun e => hp (by rw [← e]; exact hj))])
  rw [Finset.sum_insert hp, if_pos rfl, hX]

private theorem pos_ite_ite_of_pos_insert_insert [DecidableEq V] {p q : V} {X : Finset V} {α β : ℚ} {t : V → ℚ}
    (hα : 0 < α) (hβ : 0 < β) (ht : ∀ j ∈ X, 0 < t j) :
    ∀ i ∈ insert p (insert q X), 0 < (if i = p then α else if i = q then β else t i) := by
  intro i hi
  split_ifs with h1 h2
  · exact hα
  · exact hβ
  · exact ht i ((Finset.mem_insert.mp ((Finset.mem_insert.mp hi).resolve_left h1)).resolve_left h2)

private theorem pos_ite_of_pos_insert [DecidableEq V] {p : V} {X : Finset V} {α : ℚ} {t : V → ℚ}
    (hα : 0 < α) (ht : ∀ j ∈ X, 0 < t j) :
    ∀ i ∈ insert p X, 0 < (if i = p then α else t i) := by
  intro i hi
  split_ifs with h1
  · exact hα
  · exact ht i ((Finset.mem_insert.mp hi).resolve_left h1)

private theorem eq_of_sum_smul_eq_of_linearIndepOn {s : Finset V} (hs : LinearIndepOn ℚ id (s : Set V)) (T T' : V → ℚ)
    (h : ∑ i ∈ s, T i • i = ∑ i ∈ s, T' i • i) : ∀ i ∈ s, T i = T' i := by
  have h0 : ∑ i ∈ s, (T i - T' i) • id i = 0 := by
    simp only [id, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  intro i hi
  exact sub_eq_zero.mp (linearIndepOn_finset_iff.mp hs (fun i => T i - T' i) h0 i hi)

private theorem coeff_eq_of_linearIndepOn_insert_insert [DecidableEq V] {p q : V} {X : Finset V} (hp : p ∉ insert q X) (hq : q ∉ X)
    (hli : LinearIndepOn ℚ id ((insert p (insert q X) : Finset V) : Set V)) {α β α' β' : ℚ} {t t' : V → ℚ}
    (h : α • p + (β • q + ∑ i ∈ X, t i • i) = α' • p + (β' • q + ∑ i ∈ X, t' i • i)) :
    α = α' ∧ β = β' := by
  have hqp : q ≠ p := fun e => hp (by rw [← e]; exact Finset.mem_insert_self q X)
  rw [← sum_insert_insert_ite_ite_smul hp hq α β t, ← sum_insert_insert_ite_ite_smul hp hq α' β' t'] at h
  have hc := eq_of_sum_smul_eq_of_linearIndepOn hli _ _ h
  have h1 := hc p (Finset.mem_insert_self _ _)
  have h2 := hc q (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  exact ⟨by simpa using h1, by simpa [hqp] using h2⟩

private theorem exists_coords_lt_of_mem_coneOn_insert_u_c [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hu : u ∉ insert c r) (hcr : c ∉ r) {x : V}
    (hx : x ∈ coneOn (insert u (insert c r))) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ β * a < α * b := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htu : 0 < t u := ht u (Finset.mem_insert_self _ _)
  have htc : 0 < t c := ht c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨t u + t c * a, t c * b, t, add_pos htu (mul_pos htc ha), mul_pos htc hb,
    fun j hj => ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)), ?_,
    by nlinarith [mul_pos htu hb]⟩
  rw [Finset.sum_insert hu, Finset.sum_insert hcr, hc]
  module

private theorem exists_coords_lt_swap_of_mem_coneOn_c_w [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hcw : c ∉ insert w r) (hwr : w ∉ r) {x : V}
    (hx : x ∈ coneOn (insert c (insert w r))) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ α * b < β * a := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htc : 0 < t c := ht c (Finset.mem_insert_self _ _)
  have htw : 0 < t w := ht w (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  refine ⟨t c * a, t c * b + t w, t, mul_pos htc ha, add_pos (mul_pos htc hb) htw,
    fun j hj => ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)), ?_,
    by nlinarith [mul_pos htw ha]⟩
  rw [Finset.sum_insert hcw, Finset.sum_insert hwr, hc]
  module

private theorem exists_coords_eq_of_mem_coneOn_insert_c [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (hcr : c ∉ r) {x : V} (hx : x ∈ coneOn (insert c r)) :
    ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
      x = α • u + (β • w + ∑ j ∈ r, t j • j) ∧ α * b = β * a := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htc : 0 < t c := ht c (Finset.mem_insert_self _ _)
  refine ⟨t c * a, t c * b, t, mul_pos htc ha, mul_pos htc hb,
    fun j hj => ht j (Finset.mem_insert_of_mem hj), ?_, by ring⟩
  rw [Finset.sum_insert hcr, hc]
  module

private theorem coneOn_u_w_subset_union [DecidableEq V] {u w c : V} {r : Finset V} {a b : ℚ} (hc : c = a • u + b • w)
    (ha : 0 < a) (hb : 0 < b) (huw : u ∉ insert w r) (hwr : w ∉ r) (huc : u ∉ insert c r)
    (hcr : c ∉ r) (hcw : c ∉ insert w r) {x : V} (hx : x ∈ coneOn (insert u (insert w r))) :
    x ∈ coneOn (insert u (insert c r)) ∪ coneOn (insert c (insert w r)) ∪ coneOn (insert c r) := by
  simp only [coneOn, Set.mem_setOf_eq] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have htu : 0 < t u := ht u (Finset.mem_insert_self _ _)
  have htw : 0 < t w := ht w (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have htr : ∀ j ∈ r, 0 < t j := fun j hj =>
    ht j (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj))
  rw [Finset.sum_insert huw, Finset.sum_insert hwr]
  rcases lt_trichotomy (t w * a) (t u * b) with h | h | h
  · refine Or.inl (Or.inl ?_)
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * b = t w := ⟨t w / b, div_mul_cancel₀ _ hb.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have e : (t u - k * a) * b = t u * b - t w * a := by rw [← hk]; ring
    have hm : 0 < (t u - k * a) * b := by rw [e]; linarith
    have hku : 0 < t u - k * a := by nlinarith
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = u then t u - k * a else if i = c then k else t i,
      pos_ite_ite_of_pos_insert_insert hku hk0 htr, ?_⟩
    beta_reduce
    rw [sum_insert_insert_ite_ite_smul huc hcr, hc, ← hk]
    module
  · refine Or.inr ?_
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * a = t u := ⟨t u / a, div_mul_cancel₀ _ ha.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have hkb : k * b = t w := mul_right_cancel₀ ha.ne' (by rw [h, ← hk]; ring)
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = c then k else t i, pos_ite_of_pos_insert hk0 htr, ?_⟩
    beta_reduce
    rw [sum_insert_ite_smul hcr, hc, ← hk, ← hkb]
    module
  · refine Or.inl (Or.inr ?_)
    obtain ⟨k, hk⟩ : ∃ k : ℚ, k * a = t u := ⟨t u / a, div_mul_cancel₀ _ ha.ne'⟩
    have hk0 : 0 < k := by nlinarith
    have e : (t w - k * b) * a = t w * a - t u * b := by rw [← hk]; ring
    have hm : 0 < (t w - k * b) * a := by rw [e]; linarith
    have hkw : 0 < t w - k * b := by nlinarith
    simp only [coneOn, Set.mem_setOf_eq]
    refine ⟨fun i => if i = c then k else if i = w then t w - k * b else t i,
      pos_ite_ite_of_pos_insert_insert hk0 hkw htr, ?_⟩
    beta_reduce
    rw [sum_insert_insert_ite_ite_smul hcw hwr, hc, ← hk]
    module

theorem tile_of_card_lt [DecidableEq V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (n : ℕ) :
    ∀ s : Finset V, (s.filter (fun v => l v ≠ 0)).card < n → LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
      Tile (P : Set V) (SignConst l) (coneOn s) := by
  have hfr : ∀ (x : V) (X : Finset V), l x = 0 →
      ((insert x X).filter (fun v => l v ≠ 0)).card = (X.filter (fun v => l v ≠ 0)).card := by
    intro x X hx
    rw [Finset.filter_insert, if_neg (not_not.mpr hx)]
  have hfi : ∀ (x : V) (X : Finset V), l x ≠ 0 → x ∉ X →
      ((insert x X).filter (fun v => l v ≠ 0)).card = (X.filter (fun v => l v ≠ 0)).card + 1 := by
    intro x X hx hxX
    rw [Finset.filter_insert, if_pos hx, Finset.card_insert_eq_ite,
      if_neg (fun h => hxX (Finset.mem_filter.mp h).1)]
  induction n with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
  | succ n ih =>
    intro s hs hli hP
    by_cases hnn : ∀ v ∈ s, 0 ≤ l v
    · exact Tile.cone s hli hP (signConst_of_nonneg l s hnn)
    by_cases hnp : ∀ v ∈ s, l v ≤ 0
    · exact Tile.cone s hli hP (signConst_of_nonpos l s hnp)
    push_neg at hnn hnp
    obtain ⟨w, hws, hlw⟩ := hnn
    obtain ⟨u, hus, hlu⟩ := hnp
    have huw : u ≠ w := by rintro rfl; linarith
    obtain ⟨r, hur, hwr, rfl⟩ : ∃ r : Finset V, u ∉ r ∧ w ∉ r ∧ s = insert u (insert w r) :=
      ⟨(s.erase u).erase w, by simp, by simp,
        by rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨huw.symm, hws⟩), Finset.insert_erase hus]⟩
    have huwr : u ∉ insert w r := by simp [huw, hur]
    have hlw0 : l w ≠ 0 := hlw.ne
    have hlu0 : l u ≠ 0 := hlu.ne'
    have ha : (0 : ℚ) < -l w := by linarith
    have hb : (0 : ℚ) < l u := hlu
    have hPu : u ∈ P := hP (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
    have hPw : w ∈ P := hP (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    have hPr : ∀ x ∈ r, x ∈ P := fun x hx =>
      hP (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
    have hcP : (-l w) • u + (l u) • w ∈ P := P.add_mem (P.smul_mem ha hPu) (P.smul_mem hb hPw)
    have hlc : l ((-l w) • u + (l u) • w) = 0 := by
      simp only [map_add (f := _), map_smul, smul_eq_mul]; ring
    obtain ⟨hcr, hcu, hcw, hli1, hli2, hli3⟩ := StellarLI.main u w r (-l w) (l u) ha hb huw hur hwr hli
    generalize hcdef : (-l w) • u + (l u) • w = c at hcP hlc hcr hcu hcw hli1 hli2 hli3
    have hc' : c = (-l w) • u + (l u) • w := hcdef.symm
    have huc : u ∉ insert c r := by simp [Ne.symm hcu, hur]
    have hcwr : c ∉ insert w r := by simp [hcw, hcr]
    have hs' := hs
    rw [hfi u _ hlu0 huwr, hfi w r hlw0 hwr] at hs'
    have hcA : ((insert u (insert c r)).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfi u _ hlu0 huc, hfr c r hlc]; omega
    have hcB : ((insert c (insert w r)).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfr c _ hlc, hfi w r hlw0 hwr]; omega
    have hcC : ((insert c r).filter (fun v => l v ≠ 0)).card < n := by
      rw [hfr c r hlc]; omega
    have hsubA : ((insert u (insert c r) : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h | h
      · rw [h]; exact hPu
      · rw [h]; exact hcP
      · exact hPr x h
    have hsubB : ((insert c (insert w r) : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h | h
      · rw [h]; exact hcP
      · rw [h]; exact hPw
      · exact hPr x h
    have hsubC : ((insert c r : Finset V) : Set V) ⊆ P := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with h | h
      · rw [h]; exact hcP
      · exact hPr x h
    have hA := ih _ hcA hli2 hsubA
    have hB := ih _ hcB hli1 hsubB
    have hC := ih _ hcC hli3 hsubC
    have dAB : Disjoint (coneOn (insert u (insert c r))) (coneOn (insert c (insert w r))) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dAC : Disjoint (coneOn (insert u (insert c r))) (coneOn (insert c r)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dBC : Disjoint (coneOn (insert c (insert w r))) (coneOn (insert c r)) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      obtain ⟨α, β, t, -, -, -, e1, r1⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr h1
      obtain ⟨α', β', t', -, -, -, e2, r2⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr h2
      obtain ⟨rfl, rfl⟩ := coeff_eq_of_linearIndepOn_insert_insert huwr hwr hli (e1.symm.trans e2)
      linarith
    have dABC : Disjoint (coneOn (insert u (insert c r)) ∪ coneOn (insert c (insert w r)))
        (coneOn (insert c r)) := Set.disjoint_union_left.mpr ⟨dAC, dBC⟩
    have heq : coneOn (insert u (insert w r)) = (coneOn (insert u (insert c r)) ∪
        coneOn (insert c (insert w r))) ∪ coneOn (insert c r) := by
      ext x
      constructor
      · exact fun hx => coneOn_u_w_subset_union hc' ha hb huwr hwr huc hcr hcwr hx
      · intro hx
        have key : ∃ α β : ℚ, ∃ t : V → ℚ, 0 < α ∧ 0 < β ∧ (∀ j ∈ r, 0 < t j) ∧
            x = α • u + (β • w + ∑ j ∈ r, t j • j) := by
          rcases hx with (hx | hx) | hx
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_lt_of_mem_coneOn_insert_u_c hc' ha hb huc hcr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_lt_swap_of_mem_coneOn_c_w hc' ha hb hcwr hwr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
          · obtain ⟨α, β, t, h1, h2, h3, h4, -⟩ := exists_coords_eq_of_mem_coneOn_insert_c hc' ha hb hcr hx
            exact ⟨α, β, t, h1, h2, h3, h4⟩
        obtain ⟨α, β, t, h1, h2, h3, h4⟩ := key
        simp only [coneOn, Set.mem_setOf_eq]
        refine ⟨fun i => if i = u then α else if i = w then β else t i, pos_ite_ite_of_pos_insert_insert h1 h2 h3, ?_⟩
        beta_reduce
        rw [sum_insert_insert_ite_ite_smul huwr hwr]
        exact h4
    rw [heq]
    exact Tile.union (Tile.union hA hB dAB) hC dABC

theorem main : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (s : Finset V), LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
    Tile (P : Set V) (SignConst l) (coneOn s) := by
  intro V _ _ P l s hli hP
  classical
  exact tile_of_card_lt P l _ s (Nat.lt_succ_self _) hli hP

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSignStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicial_cone_tiles_sign : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (s : Finset V), LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
    Tile (P : Set V) (SignConst l) (coneOn s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTiling
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem tile_mono {P : Set V} {Q Q' : Set V → Prop} (hQ : ∀ A, Q A → Q' A) {C : Set V} (h : Tile P Q C) :
    Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP (hQ _ hQs)
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_refine {P : Set V} {Q Q' : Set V → Prop}
    (hc : ∀ s : Finset V, LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P → Q (coneOn s) → Tile P Q' (coneOn s))
    {C : Set V} (h : Tile P Q C) : Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact hc s hli hP hQs
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_inside {P : Set V} {Q : Set V → Prop} {C : Set V} (h : Tile P Q C) :
    Tile P (fun A => Q A ∧ A ⊆ C) C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP ⟨hQs, subset_rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    exact .union (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_left⟩) ihA)
      (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_right⟩) ihB) hAB

theorem signConst_mono {l : V →ₗ[ℚ] ℚ} {A C : Set V} (h : SignConst l C) (hAC : A ⊆ C) : SignConst l A := by
  rcases h with h | h | h
  · exact Or.inl fun x hx => h x (hAC hx)
  · exact Or.inr (Or.inl fun x hx => h x (hAC hx))
  · exact Or.inr (Or.inr fun x hx => h x (hAC hx))

theorem sign_eq_of_signConst {l : V →ₗ[ℚ] ℚ} {A : Set V} (h : SignConst l A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    SignType.sign (l x) = SignType.sign (l y) := by
  rcases h with h | h | h
  · rw [h x hx, h y hy]
  · rw [sign_pos (h x hx), sign_pos (h y hy)]
  · rw [sign_neg (h x hx), sign_neg (h y hy)]

theorem tile_signs (P : ConvexCone ℚ V) (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V))
    (hP : (s : Set V) ⊆ (P : Set V)) (Λ : Set (V →ₗ[ℚ] ℚ)) (hΛ : Λ.Finite) :
    Tile (P : Set V) (fun A => A ⊆ coneOn s ∧ ∀ l ∈ Λ, SignConst l A) (coneOn s) := by
  classical
  obtain ⟨t, rfl⟩ := hΛ.exists_finset_coe
  refine Finset.induction_on t ?_ ?_
  · exact .cone s hli hP ⟨subset_rfl, fun l hl => by simp at hl⟩
  · intro l t _ ih
    refine tile_refine (fun u hu huP hQu => ?_) ih
    refine tile_mono (fun A hA => ⟨hA.2.trans hQu.1, fun l' hl' => ?_⟩)
      (tile_inside (GlobalTheory.T.simplicial_cone_tiles_sign P l u hu huP))
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hl') with rfl | h'
    · exact hA.1
    · exact signConst_mono (hQu.2 l' (Finset.mem_coe.2 h')) hA.2

theorem tile_inter {P E C : Set V} (h : Tile P (fun A => A ⊆ E ∨ Disjoint A E) C) :
    Tile P (fun _ => True) (C ∩ E) := by
  induction h with
  | empty =>
    rw [Set.empty_inter]
    exact .empty
  | cone s hli hP hQs =>
    rcases hQs with hs | hs
    · rw [Set.inter_eq_left.2 hs]
      exact .cone s hli hP trivial
    · rw [Set.disjoint_iff_inter_eq_empty.1 hs]
      exact .empty
  | union _ _ hAB ihA ihB =>
    rw [Set.union_inter_distrib_right]
    exact .union ihA ihB (hAB.mono Set.inter_subset_left Set.inter_subset_left)

theorem mem_coneOn_basis [DecidableEq V] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ V) (x : V) :
    x ∈ coneOn (Finset.univ.image b) ↔ ∀ i, 0 < b.repr x i := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
    have hrep : b.repr (∑ j, t (b j) • b j) i = t (b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hrep]
    exact ht _ (Finset.mem_image_of_mem b (Finset.mem_univ i))
  · intro hx
    have key : ∀ i, ∑ j, b.repr (b i) j * b.repr x j = b.repr x i := by
      intro i
      rw [Module.Basis.repr_self, Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl, one_mul]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg (Ne.symm hji), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    refine ⟨fun v => ∑ j, b.repr v j * b.repr x j, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      show 0 < ∑ j, b.repr (b i) j * b.repr x j
      rw [key]
      exact hx i
    · rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      show b.repr x i • b i = (∑ j, b.repr (b i) j * b.repr x j) • b i
      rw [key]

theorem tile_of_signs : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  classical
  intro V _ _ κ _ P b hb Λ hΛ E hE hdec
  have hcoe : ((Finset.univ.image b : Finset V) : Set V) = Set.range b := by
    simp [Set.image_univ]
  have hli : LinearIndepOn ℚ id ((Finset.univ.image b : Finset V) : Set V) := by
    rw [hcoe]
    exact (linearIndepOn_id_range_iff b.injective).2 b.linearIndependent
  have hP' : ((Finset.univ.image b : Finset V) : Set V) ⊆ (P : Set V) := by
    rw [hcoe]
    rintro v ⟨i, rfl⟩
    exact hb i
  have hT := tile_inter (tile_mono (Q' := fun A => A ⊆ E ∨ Disjoint A E) (fun A hA => ?_)
    (tile_signs P _ hli hP' Λ hΛ))
  · have hEs : coneOn (Finset.univ.image b) ∩ E = E :=
      Set.inter_eq_right.2 fun x hx => (mem_coneOn_basis b x).2 (hE x hx)
    rw [hEs] at hT
    exact hT
  · obtain ⟨hAs, hAl⟩ := hA
    by_cases hex : ∃ x ∈ A, x ∈ E
    · left
      obtain ⟨x, hxA, hxE⟩ := hex
      intro y hyA
      exact hdec x y ((mem_coneOn_basis b x).1 (hAs hxA)) ((mem_coneOn_basis b y).1 (hAs hyA))
        (fun l hl => sign_eq_of_signConst (hAl l hl) hxA hyA) hxE
    · right
      exact Set.disjoint_left.2 fun x hxA hxE => hex ⟨x, hxA, hxE⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilingStatement
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_tiling_by_sign_regions : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs <;> assumption)
end
