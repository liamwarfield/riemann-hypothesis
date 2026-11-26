module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PhiPerm
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PhiPerm

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem mem_ncV_iff_apply {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem phi_apply_eq (k : ℕ) (F : Big n k M) : phi E k F = ∑ κ, word E κ (F κ) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

theorem listProd_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    (l : List (Fin n × Fin n)) {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) :
    (l.map fun p => E p.1 p.2).prod v ∈ layer ε E V (j + l.length) := by
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact apply_mem_layer_succ hE hV p.1 p.2 ih

theorem listProd_perm_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) (hnc : ∀ p ∈ l₁, ε p.1 ≠ ε p.2)
    {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) (m : ℕ) (hm : l₁.length ≤ m + 1) :
    (l₁.map fun p => E p.1 p.2).prod v - (l₂.map fun p => E p.1 p.2).prod v ∈
      layer ε E V (j + m) := by
  induction hp generalizing m with
  | nil => simp
  | @cons x l₁ l₂ h ih =>
    rcases m with _ | m
    · have hl1 : l₁ = [] := by simpa using hm
      subst hl1
      have hl2 := List.Perm.nil_eq h
      subst hl2
      simp
    · have hD := ih (fun p hp' => hnc p (List.mem_cons_of_mem _ hp')) m (by simpa using hm)
      have := apply_mem_layer_succ hE hV x.1 x.2 hD
      rw [map_sub] at this
      simpa [List.map_cons, List.prod_cons, Module.End.mul_apply, add_assoc] using this
  | swap x y l =>
    have hw := listProd_mem_layer hE hV l hv
    have hlen : j + l.length + 1 ≤ j + m := by simp at hm; omega
    have h1 : ∀ a b, (E a b) ((l.map fun p => E p.1 p.2).prod v) ∈ layer ε E V (j + m) :=
      fun a b => layer_mono hlen (apply_mem_layer_succ hE hV a b hw)
    have key : ((y :: x :: l).map fun p => E p.1 p.2).prod v - ((x :: y :: l).map fun p => E p.1 p.2).prod v =
        (E y.1 y.2 * E x.1 x.2 - E x.1 x.2 * E y.1 y.2) ((l.map fun p => E p.1 p.2).prod v) := by
      simp only [List.map_cons, List.prod_cons, LinearMap.sub_apply, Module.End.mul_apply]
    rw [key, hE, LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact h1 _ _
      · simp
    · split_ifs
      · exact h1 _ _
      · simp
  | trans h₁ h₂ ih₁ ih₂ =>
    have hA := ih₁ hnc m hm
    have hB := ih₂ (fun p hp' => hnc p (h₁.symm.subset hp')) m (by rw [← h₁.length_eq]; exact hm)
    have := Submodule.add_mem _ hA hB
    rwa [sub_add_sub_cancel] at this

theorem word_eq_listProd {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    word E κ = ((List.ofFn κ).map fun p => E p.1 p.2).prod := by
  rw [word, List.map_ofFn]
  rfl

theorem phi_permute_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V) {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) {F : Big n (k + 1) M} (hF : F ∈ ncV ε V (k + 1)) :
    phi E (k + 1) F - phi E (k + 1) (permute σ F) ∈ layer ε E V k := by
  rw [phi_apply_eq, phi_apply_eq]
  have hre : ∑ κ, word E κ ((permute σ F) κ) = ∑ κ, word E (κ ∘ σ.symm) (F κ) := by
    let e : (Fin (k + 1) → Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
      ⟨fun κ => κ ∘ σ, fun κ => κ ∘ σ.symm, fun κ => by funext i; simp, fun κ => by funext i; simp⟩
    refine Fintype.sum_equiv e _ _ (fun κ => ?_)
    show word E κ (permute σ F κ) = word E ((κ ∘ σ) ∘ σ.symm) (F (κ ∘ σ))
    have hκ : (κ ∘ σ) ∘ σ.symm = κ := by funext i; simp
    rw [hκ, permute_apply]
  rw [hre, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun κ _ => ?_)
  have hFκ := (mem_ncV_iff_apply.1 hF) κ
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · rw [if_pos hc] at hFκ
    rw [word_eq_listProd, word_eq_listProd]
    have hp : (List.ofFn κ).Perm (List.ofFn (κ ∘ σ.symm)) := (Equiv.Perm.ofFn_comp_perm σ.symm κ).symm
    have hnc : ∀ p ∈ List.ofFn κ, ε p.1 ≠ ε p.2 := fun p hp' => by
      rw [List.mem_ofFn] at hp'
      obtain ⟨i, rfl⟩ := hp'
      exact hc i
    have := listProd_perm_sub_mem hE hV hp hnc (show F κ ∈ layer ε E V 0 from hFκ) k (by simp)
    rw [zero_add] at this
    exact this
  · rw [if_neg hc] at hFκ
    rw [(Submodule.mem_bot ℂ).1 hFκ]
    simp

end PhiPerm

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Sch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem phi_one_Wm (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hlay : phi E 1 x₀ ∈ layer ε E V 1 := phi_mem_layer (Wm_le_ncV hx₀)
  have hcas : casimir E (phi E 1 x₀) = (casVal lam : ℂ) • phi E 1 x₀ :=
    casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 hlay)
  rw [hμ] at hyμ
  exact hy0 (khw_lowK_sub_root_eq_zero ε hE hU lam hab hε
    (sch_gap ⟨hmono, h, hh, hbig⟩ hab hε) hyμ hcas)

theorem sch_coord_apply {k : ℕ} (κ : Fin k → Fin n × Fin n) (F : Big n k M) : coord k κ F = F κ := rfl

theorem sch_slice_apply {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M)
    (ι : Fin 1 → Fin n × Fin n) : slice i κ F ι = F (Function.update κ i (ι 0)) := rfl

theorem sch_permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem sch_word_snoc {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) = word E init * E p.1 p.2 := by
  simp only [word, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem sch_word_one (ι : Fin 1 → Fin n × Fin n) : word E ι = E (ι 0).1 (ι 0).2 := by
  simp only [word, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

theorem sch_phi_one_apply (G : Big n 1 M) :
    phi E 1 G = ∑ p : Fin n × Fin n, E p.1 p.2 (G (fun _ => p)) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun κ => ?_)
  rw [Equiv.funUnique_apply, sch_word_one, sch_coord_apply]
  obtain ⟨p, rfl⟩ : ∃ p, κ = fun _ => p := ⟨κ 0, funext fun j => by rw [Fin.fin_one_eq_zero j]⟩
  rfl

theorem phi_Wm_last (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by

  let e : (Fin k → Fin n × Fin n) × (Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
    { toFun := fun q => Fin.snoc q.1 q.2
      invFun := fun κ => (Fin.init κ, κ (Fin.last k))
      left_inv := fun q => by simp
      right_inv := fun κ => Fin.snoc_init_self κ }
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply, sch_coord_apply]
  rw [Fintype.sum_equiv e.symm _
    (fun q => word E (Fin.snoc q.1 q.2 : Fin (k + 1) → Fin n × Fin n) (F (Fin.snoc q.1 q.2)))
    (fun κ => by simp only [e, Equiv.coe_fn_symm_mk, Fin.snoc_init_self])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun init _ => ?_
  simp only [sch_word_snoc, Module.End.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hX | ⟨⟨p0⟩⟩
  · simp
  · have h := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
    rw [sch_phi_one_apply] at h
    simp only [sch_slice_apply, Fin.update_snoc_last] at h
    rw [h, map_zero]

theorem phi_Wm_position (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by

  have hperm : ∀ κ, slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) ∈ Wm ε E V := by
    intro κ
    have heq : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      refine PiLp.ext fun ι => ?_
      rw [sch_slice_apply, sch_permute_apply, sch_slice_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [heq]
    exact hF _
  have h0 := phi_Wm_last hE hU hV hc hmono hh hbig hperm
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  rw [h0, sub_zero] at hsub
  exact hsub

end Sch

end ReciprocityTheory.ChartRestriction.DS
