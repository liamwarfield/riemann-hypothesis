module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PmInduction
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ExistsNearSmooth

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
set_option autoImplicit false

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lt (ε : Fin n → Bool) (p : Fin n × Fin n) (b : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if b then S7.cpart2 ε (Matrix.single p.1 p.2 1) else S7.cpart1 ε (Matrix.single p.1 p.2 1)

theorem lt_inG (ε : Fin n → Bool) (p : Fin n × Fin n) (b : Bool) : inG ε (lt ε p b) := by
  unfold lt
  split
  · exact SmDerA.inG_cpart2 ε _
  · exact SmDerA.inG_cpart1 ε _

def wordOf (ε : Fin n → Bool) (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : List (Matrix (Fin n) (Fin n) ℂ) :=
  List.ofFn fun i => lt ε (w.get i) (s i)

def coefOf (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : ℂ :=
  ∏ i, if s i then Complex.I else 1

theorem dS_fsum {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSmoothVecU ε σ (v i)) : dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := dS_smul_vec (σ := σ) (0 : ℂ) X (0 : H)
    simpa using this
  | @insert i s hi ih =>
    have h1 : IsSmoothVecU ε σ (c i • v i) := IsSmoothVecU.smul (c i) (hv i)
    have h2 : IsSmoothVecU ε σ (∑ j ∈ s, c j • v j) :=
      (SmDerA.smSub ε σ).sum_mem fun j _ => (SmDerA.smSub ε σ).smul_mem (c j) (hv j)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dS_add_vec hσ hX h1 h2, dS_smul_vec, ih]

theorem coef_cons (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (b : Bool) (s : Fin w.length → Bool) :
    coefOf (p :: w) (Fin.cons b s : Fin (w.length + 1) → Bool) = (if b then Complex.I else 1) * coefOf w s := by
  unfold coefOf
  exact Fin.prod_univ_succ _

theorem word_cons (ε : Fin n → Bool) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (b : Bool)
    (s : Fin w.length → Bool) :
    wordOf ε (p :: w) (Fin.cons b s : Fin (w.length + 1) → Bool) = lt ε p b :: wordOf ε w s := by
  unfold wordOf
  exact List.ofFn_succ

theorem wAct_expand {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (x : smD ε σ) : ∀ w : List (Fin n × Fin n),
      ((wAct (smE ε σ) w x : smD ε σ) : H) = ∑ s : Fin w.length → Bool, coefOf w s • dSW σ (wordOf ε w s) x
  | [] => by simp [wAct, wordOf, coefOf, dSW]
  | p :: w => by
    have hx : IsSmoothVecU ε σ (x : H) := (mem_smD_iff ε σ _).mp x.2
    have ih := wAct_expand hσ x w
    have hsm : ∀ s : Fin w.length → Bool, IsSmoothVecU ε σ (dSW σ (wordOf ε w s) x) := fun s =>
      dSW_smooth hσ (fun X hX => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hX
        exact lt_inG ε _ _) hx
    show ((smE ε σ p.1 p.2 (wAct (smE ε σ) w x) : smD ε σ) : H) = _
    rw [smE_apply hσ, ih, dS_fsum hσ (SmDerA.inG_cpart1 ε _) _ _ _ hsm,
      dS_fsum hσ (SmDerA.inG_cpart2 ε _) _ _ _ hsm, Finset.smul_sum]
    show _ = ∑ s : Fin (w.length + 1) → Bool, coefOf (p :: w) s • dSW σ (wordOf ε (p :: w) s) (x : H)
    rw [← (Fin.consEquiv fun _ : Fin (w.length + 1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      show _ = coefOf (p :: w) (Fin.cons true s : Fin (w.length + 1) → Bool) •
        dSW σ (wordOf ε (p :: w) (Fin.cons true s : Fin (w.length + 1) → Bool)) (x : H)
      rw [coef_cons, word_cons]
      simp [lt, dSW, smul_smul]
    · refine Finset.sum_congr rfl fun s _ => ?_
      show _ = coefOf (p :: w) (Fin.cons false s : Fin (w.length + 1) → Bool) •
        dSW σ (wordOf ε (p :: w) (Fin.cons false s : Fin (w.length + 1) → Bool)) (x : H)
      rw [coef_cons, word_cons]
      simp [lt, dSW]

theorem coefOf_norm (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : ‖coefOf w s‖ = 1 := by
  unfold coefOf
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split <;> simp

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (f : β → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

private lemma toList_map_sum_eq_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ) : (s.toList.map f).sum = ∑ a ∈ s, f a := by
  rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList s, Multiset.map_coe, Multiset.sum_coe]

theorem NE_le_nuJ {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (j : ℕ) :
    ∃ (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ),
      (∀ w ∈ Ws, w.length ≤ j ∧ ∀ X ∈ w, inG ε X) ∧
      ∀ x : smD ε σ, NE (smE ε σ) j x ≤ C * nuJ σ Ws (x : H) := by
  classical
  refine ⟨(Finset.range (j + 1)).toList.flatMap fun l =>
      (Finset.univ : Finset (Fin l → Fin n × Fin n)).toList.flatMap fun w =>
        (Finset.univ : Finset (Fin (List.ofFn w).length → Bool)).toList.map fun s => wordOf ε (List.ofFn w) s,
    1, ?_, ?_⟩
  · intro W hW
    simp only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
      Finset.mem_range] at hW
    obtain ⟨l, hl, w, s, rfl⟩ := hW
    refine ⟨?_, ?_⟩
    · simp only [wordOf, List.length_ofFn]
      omega
    · intro X hX
      simp only [wordOf, List.mem_ofFn] at hX
      obtain ⟨i, rfl⟩ := hX
      exact lt_inG _ _ _
  · intro x
    rw [one_mul]
    simp only [nuJ, sum_flatMap_map, List.map_map, Function.comp_def, toList_map_sum_eq_finset_sum]
    unfold NE
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro w _
    rw [wAct_expand hσ x]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro s _
    rw [norm_smul, coefOf_norm, one_mul]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJOfSigLam
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Equiv

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem dSW_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ x : H₁, dSW σ₂ w (U x) = U (dSW σ₁ w x)
  | [], _, _ => rfl
  | X :: w, hw, x => by
    simp only [dSW]
    rw [dSW_map_isometry U hU w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) x,
      dS_map_isometry U hU (hw X List.mem_cons_self)]

theorem nuJ_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (x : H₁) :
    nuJ σ₂ Ws (U x) = nuJ σ₁ Ws x := by
  delta nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [dSW_map_isometry U hU w (hWs w hw) x, U.norm_map]

end Equiv

theorem decBoundJ_of_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) (m N : ℕ) (hL : DecBoundJ ε (sigLam ε Ψ v₀) m N) :
    DecBoundJ ε σ m N := by
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hstd hP hv₀
  obtain ⟨C, Ws, hWs, hB⟩ := hL
  have hWs' : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  refine ⟨C, Ws, hWs, fun u v hu hv g hg => ?_⟩
  obtain ⟨x, rfl⟩ := U.surjective u
  obtain ⟨y, rfl⟩ := U.surjective v
  have hx := smooth_symm_of_isometry U hU hu
  have hy := smooth_symm_of_isometry U hU hv
  rw [U.symm_apply_apply] at hx hy
  have hb := hB x y hx hy g hg
  rw [← hU g hg x, U.inner_map_map, nuJ_map_isometry U hU hWs' x, nuJ_map_isometry U hU hWs' y]
  exact hb

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJSigLam
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DSWSigLamCoe
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nuJ_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : 0 ≤ nuJ σ Ws v := by
  unfold nuJ
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

theorem nuJ_cons_nil (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : nuJ σ ([] :: Ws) v = ‖v‖ + nuJ σ Ws v := by
  simp [nuJ, dSW]

theorem nuJ_le_add_of (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a b c : H) :
    ∀ Ws : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ w ∈ Ws, ‖dSW σ w a‖ ≤ ‖dSW σ w b‖ + ‖dSW σ w c‖) → nuJ σ Ws a ≤ nuJ σ Ws b + nuJ σ Ws c
  | [], _ => by simp [nuJ]
  | w :: Ws, h => by
    have h1 := h w List.mem_cons_self
    have h2 := nuJ_le_add_of σ a b c Ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [nuJ, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

theorem NE_nonneg' {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

end Gen

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem dS_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : Hlam ε Ψ v₀) :
    ((dS (sigLam ε Ψ v₀) X y : Hlam ε Ψ v₀) : L2 ε) = dS (rreg ε) X (y : L2 ε) := by
  unfold dS
  set f : ℝ → Hlam ε Ψ v₀ := fun t => sigLam ε Ψ v₀ (NormedSpace.exp ((t : ℂ) • X)) y with hfdef
  have hf : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (y : L2 ε)) = fun t => ((f t : Hlam ε Ψ v₀) : L2 ε) := by
    funext t
    rw [hfdef, sigLam_coe hgap hP hv₀ (exp_smul_mem_UJset hX t)]
  rw [hf]
  let Ir : Hlam ε Ψ v₀ →L[ℝ] L2 ε := ((Hlam ε Ψ v₀).subtypeL).restrictScalars ℝ
  let Pr : L2 ε →L[ℝ] Hlam ε Ψ v₀ := ((Hlam ε Ψ v₀).orthogonalProjectionOnto).restrictScalars ℝ
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((Ir.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd.hasDerivAt).deriv).symm
  · have hd' : ¬ DifferentiableAt ℝ (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 := by
      intro h
      apply hd
      have h2 := Pr.differentiableAt.comp (0 : ℝ) h
      have e : (Pr ∘ fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) = f := by
        funext t
        exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f t)
      rw [e] at h2
      exact h2
    have h0 : deriv f 0 = 0 := deriv_zero_of_not_differentiableAt hd
    have h1 : deriv (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 = 0 := deriv_zero_of_not_differentiableAt hd'
    exact (congrArg Subtype.val h0).trans h1.symm

theorem dSW_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ y : Hlam ε Ψ v₀,
      ((dSW (sigLam ε Ψ v₀) w y : Hlam ε Ψ v₀) : L2 ε) = dSW (rreg ε) w (y : L2 ε)
  | [], _, _ => rfl
  | X :: w, hw, y => by
    simp only [dSW]
    rw [dS_sigLam_coe hgap hP hv₀ (hw X List.mem_cons_self),
      dSW_sigLam_coe hgap hP hv₀ w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) y]

theorem nuJ_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (y : Hlam ε Ψ v₀) :
    nuJ (rreg ε) Ws (y : L2 ε) = nuJ (sigLam ε Ψ v₀) Ws y := by
  unfold nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [← dSW_sigLam_coe hgap hP hv₀ w (hWs w hw) y, Submodule.coe_norm]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem decBoundJ_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (m N : ℕ)
    (hM : ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m * ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ ≤
          C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y) :
    DecBoundJ ε (sigLam ε Ψ v₀) m N := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨Ws, C', hWs, hNE⟩ := NE_le_nuJ (rreg_isURepOn ε) N
  have hU : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWsG : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  have hVs : ∀ w ∈ ([] :: Ws), w.length ≤ N ∧ ∀ X ∈ w, inG ε X := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · exact hWs w hw
  have hVsG : ∀ w ∈ ([] :: Ws), ∀ X ∈ w, inG ε X := fun w hw => (hVs w hw).2
  have hnn : ∀ z : Hlam ε Ψ v₀, 0 ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := fun z =>
    nuJ_nonneg _ _ _
  have hnorm : ∀ z : Hlam ε Ψ v₀, ‖z‖ ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := by
    intro z
    rw [nuJ_cons_nil]
    linarith [nuJ_nonneg (sigLam ε Ψ v₀) Ws z]
  have hC₁ : 0 ≤ max C' 0 := le_max_right _ _
  have hK : 0 ≤ max C 0 * max C' 0 * max C' 0 :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hC₁) hC₁
  have hNE' : ∀ (x : smD ε (rreg ε)) (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      NE (smE ε (rreg ε)) N x ≤
        max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) := by
    intro x hx
    have h1 := hNE x
    have h2 : nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) =
        nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_sigLam_coe hgap hP hv₀ hWsG (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)
    have h3 := nuJ_nonneg (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)
    have h4 : nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) =
        ‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
          nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_cons_nil _ _ _
    rw [h4, ← h2]
    calc NE (smE ε (rreg ε)) N x ≤ C' * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) := h1
      _ ≤ max C' 0 * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C' 0 * (‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
            nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hC₁
  have hfin : ∀ (x : smD ε (rreg ε)), x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      ∀ (y : smD ε (rreg ε)), y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hy : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀), ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m *
            ‖inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
              (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩)‖ ≤
          max C 0 * max C' 0 * max C' 0 *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ := by
    intro x hxg hx y hyg hy g hg
    have he : inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) =
        inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)) := by
      rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hg]
    rw [he]
    have hb := hC x hxg y hyg g hg
    have hx0 := NE_nonneg' (smE ε (rreg ε)) N x
    have hy0 := NE_nonneg' (smE ε (rreg ε)) N y
    have hxb := hNE' x hx
    have hyb := hNE' y hy
    calc _ ≤ C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y := hb
      _ ≤ max C 0 * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) hy0
      _ ≤ max C 0 * (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) *
            (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩) := by
          have hm := le_max_right C 0
          exact mul_le_mul (mul_le_mul_of_nonneg_left hxb hm) hyb hy0
            (mul_nonneg hm (mul_nonneg hC₁ (hnn _)))
      _ = _ := by ring
  refine ⟨max C 0 * max C' 0 * max C' 0, [] :: Ws, hVs, ?_⟩
  intro u v hu hv g hg
  have hA : 0 ≤ Real.sqrt (S7.hs g) ^ m := pow_nonneg (Real.sqrt_nonneg _) _
  have hiso : ∀ z : Hlam ε Ψ v₀, ‖sigLam ε Ψ v₀ g z‖ = ‖z‖ := fun z => hU.2.1 g hg z
  have hnear : ∀ (w : Hlam ε Ψ v₀), IsSmoothVecU ε (sigLam ε Ψ v₀) w → ∀ (e : ℝ), 0 < e →
      ∃ (x : smD ε (rreg ε)) (_ : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
        ‖w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩‖ ≤ e ∧
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ ≤
          nuJ (sigLam ε Ψ v₀) ([] :: Ws) w + e := by
    intro w hw e he
    obtain ⟨x, hxg, hx, hlt⟩ := exists_near_smooth hlam hgap hP hv₀ ([] :: Ws) hVsG w hw he
    refine ⟨x, hxg, hx, (hnorm _).trans hlt.le, ?_⟩
    have hxs := sigLam_smooth_of_genSub (ε := ε) (Ψ := Ψ) (v₀ := v₀) hx
    have htri := nuJ_le_add_of (sigLam ε Ψ v₀) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ w
      (w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) ([] :: Ws) (by
        intro W hW
        rw [dSW_sub hU (hVsG W hW) hw hxs]
        set a := dSW (sigLam ε Ψ v₀) W w
        set b := dSW (sigLam ε Ψ v₀) W ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩
        calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _)
    linarith
  have hbound : ∀ e : ℝ, 0 < e →
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (sigLam ε Ψ v₀ g u)‖ ≤
        Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
          max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
            (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
    intro e he
    obtain ⟨x, hxg, hx, hux, hnx⟩ := hnear u hu e he
    obtain ⟨y, hyg, hy, hvy, hny⟩ := hnear v hv e he
    set x' : Hlam ε Ψ v₀ := ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ with hx'
    set y' : Hlam ε Ψ v₀ := ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ with hy'
    have hsplit : inner ℂ v (sigLam ε Ψ v₀ g u) =
        inner ℂ (v - y') (sigLam ε Ψ v₀ g u) +
          (inner ℂ y' (sigLam ε Ψ v₀ g (u - x')) + inner ℂ y' (sigLam ε Ψ v₀ g x')) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : ‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ ≤ e * ‖u‖ := by
      calc _ ≤ ‖v - y'‖ * ‖sigLam ε Ψ v₀ g u‖ := norm_inner_le_norm _ _
        _ = ‖v - y'‖ * ‖u‖ := by rw [hiso]
        _ ≤ e * ‖u‖ := mul_le_mul_of_nonneg_right hvy (norm_nonneg _)
    have hy'n : ‖y'‖ ≤ ‖v‖ + e := by
      calc ‖y'‖ = ‖v - (v - y')‖ := by rw [sub_sub_cancel]
        _ ≤ ‖v‖ + ‖v - y'‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + e := by linarith
    have h2 : ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ ≤ (‖v‖ + e) * e := by
      calc _ ≤ ‖y'‖ * ‖sigLam ε Ψ v₀ g (u - x')‖ := norm_inner_le_norm _ _
        _ = ‖y'‖ * ‖u - x'‖ := by rw [hiso]
        _ ≤ (‖v‖ + e) * e := mul_le_mul hy'n hux (norm_nonneg _) (by linarith [norm_nonneg v])
    have h3 := hfin x hxg hx y hyg hy g hg
    have h3' : Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ ≤
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
      refine h3.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnx hK) hny (hnn _)
        (mul_nonneg hK (by linarith [hnn u]))
    rw [hsplit]
    calc _ ≤ Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            (‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ + ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) hA
      _ = Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖) +
            Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA) h3'
  have hlim : Filter.Tendsto (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (max C 0 * max C' 0 * max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) u *
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) v)) := by
    have hc : Continuous (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun e he => hbound e he)

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecSmOfDecBoundJ
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.Bridge
set_option autoImplicit false

noncomputable section

open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem br_facts {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    P⁻¹ = Pᴴ ∧ P * Pᴴ = 1 ∧ Pᴴ * P = 1 ∧ Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
  obtain ⟨⟨_, hJ⟩, hU⟩ := hP
  have h1 : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hU
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.inv_eq_left_inv h2, h1, h2, ?_⟩
  have hJe : Jm ε = Formalism.REAL.Jm ε := rfl
  rw [hJe, ← hJ]
  calc Formalism.REAL.Jm ε = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by simp only [Matrix.mul_assoc]

theorem bridge_group {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ↔ P * g * P⁻¹ ∈ UJset ε := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hJ' : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = P * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * Pᴴ := by
    rw [hinv, ← hJ']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  show gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r ↔ inUJ ε (P * g * P⁻¹)
  unfold inUJ
  rw [e, hJ]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key] at this
    exact this

theorem bridge_lie {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.S.InLieHpk k r X ↔ inG ε (P * X * P⁻¹) := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have h2' : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have key : ∀ Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * Y * Pᴴ) * P = Y := fun Y => by
    calc Pᴴ * (P * Y * Pᴴ) * P = (Pᴴ * P) * Y * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  have e : (P * X * P⁻¹)ᴴ * Jm ε + Jm ε * (P * X * P⁻¹) =
      P * (Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X) * Pᴴ := by
    rw [hinv, hJ]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, h2']
  show Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0 ↔ inG ε (P * X * P⁻¹)
  unfold inG
  rw [e]
  constructor
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    have := congrArg (fun M => Pᴴ * M * P) h
    simp only [key, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this

theorem bridge_gN {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g = Real.sqrt (S7.hs (P * g * P⁻¹)) := by
  obtain ⟨hi, h2, h1, -⟩ := br_facts hP
  have key : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Matrix.trace (Mᴴ * M)).re := by
    intro M
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  have e1 : ∑ i, ∑ j, Complex.normSq (g i j) = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
    simp [Complex.normSq_eq_norm_sq]
  have e2 : (P * g * Pᴴ)ᴴ * (P * g * Pᴴ) = P * ((gᴴ * g) * Pᴴ) := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul]
  have L : ∑ i, ∑ j, ‖g i j‖ ^ 2 = (gᴴ * g).trace.re := key g
  have R : ∑ i, ∑ j, ‖(P * g * Pᴴ) i j‖ ^ 2 = ((P * g * Pᴴ)ᴴ * (P * g * Pᴴ)).trace.re := key _
  rw [e1, hi, L, R, e2, Matrix.trace_mul_comm P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bridge_smooth {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ ↔ IsSmoothVecU ε (fun g => σ (P⁻¹ * g * P)) v := by
  obtain ⟨hinv, h1, h2, hJ⟩ := br_facts hP
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  let cA : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P⁻¹).comp (LinearMap.mulRight ℝ P))
  let cB : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ P).comp (LinearMap.mulRight ℝ P⁻¹))
  have hcA : ∀ g, cA g = P⁻¹ * g * P := fun g => by simp [cA, Matrix.mul_assoc]
  have hcB : ∀ g, cB g = P * g * P⁻¹ := fun g => by simp [cB, Matrix.mul_assoc]
  have hAB : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hBA : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hPd, Matrix.mul_one]
  have hmem : ∀ g, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) g ↔ inUJ ε (P * g * P⁻¹) := fun g => bridge_group hP g
  simp only [Formalism.MainNotions.S.smoothVecs, Set.mem_setOf_eq, Formalism.MainNotions.S.IsSmoothVec, IsSmoothVecU]
  constructor
  · intro hv g₀ hg₀
    have hg₁ : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g₀ * P) := (hmem _).2 (by rw [hBA]; exact hg₀)
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cA ⁻¹' U, F ∘ cA, hU.preimage cA.continuous, by simp [hcA, hxU],
      hF.comp cA.contDiff.contDiffOn (fun x hx => hx), fun g hg hgJ => ?_⟩
    have hgH : Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) (P⁻¹ * g * P) := (hmem _).2 (by rw [hBA]; exact hgJ)
    have h3 := hfF _ (by simpa [hcA] using hg) hgH
    simp only at h3
    simp only [Function.comp_apply, hcA]
    exact h3
  · intro hv g₀ hg₀
    have hg₁ : inUJ ε (P * g₀ * P⁻¹) := (hmem g₀).1 hg₀
    obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hv _ hg₁
    refine ⟨cB ⁻¹' U, F ∘ cB, hU.preimage cB.continuous, by simp [hcB, hxU],
      hF.comp cB.contDiff.contDiffOn (fun x hx => hx), fun g hg hgH => ?_⟩
    have h3 := hfF _ (by simpa [hcB] using hg) ((hmem g).1 hgH)
    simp only at h3
    simp only [Function.comp_apply, hcB]
    rw [← h3, hAB]

theorem bridge_dsigW {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v =
      dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v := by
  have hPu : IsUnit P := hP.1.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hE : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (t : ℝ),
      P⁻¹ * NormedSpace.exp ((t : ℂ) • (P * X * P⁻¹)) * P = NormedSpace.exp ((t : ℂ) • X) := by
    intro X t
    have e1 : ((t : ℂ) • (P * X * P⁻¹)) = P * ((t : ℂ) • X) * P⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.exp_conj P ((t : ℂ) • X) hPu]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
  have hconj : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (u : H),
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X u = dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) u := by
    intro X u
    unfold Formalism.MainNotions.S.dsig dS
    simp only [hE]
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) =
      dS (fun g => σ (P⁻¹ * g * P)) (P * X * P⁻¹) (dSW (fun g => σ (P⁻¹ * g * P)) (w.map fun X => P * X * P⁻¹) v)
    rw [ih, hconj]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decSm_of_decBoundJ {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (m N : ℕ)
    (hJ : DecBoundJ ε (fun g => σ (P⁻¹ * g * P)) m N) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨hinv, -, -, -⟩ := br_facts hP
  have hPPi : P * P⁻¹ = 1 := by
    rw [hinv]; exact (br_facts hP).2.1
  have hPiP : P⁻¹ * P = 1 := by
    rw [hinv]; exact (br_facts hP).2.2.1
  have hconj : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P * (P⁻¹ * X * P) * P⁻¹ = X := by
    intro X
    calc P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  have hconj' : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  have hmapid : ∀ w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      ((w.map fun X => P⁻¹ * X * P).map fun X => P * X * P⁻¹) = w := by
    intro w
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left (fun X _ => hconj X)
  obtain ⟨C, Ws, hWs, hb⟩ := hJ
  refine ⟨C, Ws.map fun w => w.map fun X => P⁻¹ * X * P, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    refine ⟨by rw [List.length_map]; exact (hWs w hw).1, ?_⟩
    intro X' hX'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hX'
    rw [bridge_lie hP, hconj]
    exact (hWs w hw).2 X hX
  · intro u hu v hv g hg
    have hsum : ∀ x : H,
        ((Ws.map fun w => w.map fun X => P⁻¹ * X * P).map
            fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w x‖).sum = nuJ (fun g => σ (P⁻¹ * g * P)) Ws x := by
      intro x
      unfold nuJ
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun w _ => ?_)
      simp only [Function.comp_apply]
      rw [bridge_dsigW hP, hmapid]
    have key := hb u v ((bridge_smooth hP σ u).1 hu) ((bridge_smooth hP σ v).1 hv)
      (P * g * P⁻¹) ((bridge_group hP g).1 hg)
    simp only [] at key
    rw [hconj'] at key
    rw [hsum, hsum, bridge_gN hP]
    exact key

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.HsPowMulLe
set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem hs_pow_mul_le (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) {c A : ℝ} (hc : 0 ≤ c)
    (h : ∀ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ ≤ A) :
    Real.sqrt (S7.hs g) ^ m * c ≤ (n : ℝ) ^ (2 * m) * A := by
  have hsq : Real.sqrt (S7.hs g) ≤ ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ := by
    have h1 : S7.hs g = ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 := by
      rw [S7.hs, ← Finset.univ_product_univ, Finset.sum_product]
    have h2 : ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ 2 := by
      rw [sq (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖), Finset.sum_mul]
      refine Finset.sum_le_sum fun ab _ => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun ab : Fin n × Fin n => ‖g ab.1 ab.2‖)
        (fun (i : Fin n × Fin n) _ => norm_nonneg (g i.1 i.2)) (Finset.mem_univ ab)) (norm_nonneg (g ab.1 ab.2))
    rw [h1, Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact h2
  have hpow : (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m =
      ∑ idx : Fin m → Fin n × Fin n, ∏ t, ‖g (idx t).1 (idx t).2‖ := by
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    rfl
  calc Real.sqrt (S7.hs g) ^ m * c ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq m) hc
    _ = ∑ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ := by
        rw [hpow, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∑ _idx : Fin m → Fin n × Fin n, A := Finset.sum_le_sum fun idx _ => h idx
    _ = (n : ℝ) ^ (2 * m) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [Fintype.card_fin]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem hs_eq_of_compact {n : ℕ} {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : S7.hs g = n := by
  have h2 : inUJ ε g := hg
  delta inUJ Jm at h2
  delta pOf qOf at hpq
  have hU : g.conjTranspose * g = 1 := by
    rcases hpq with hp | hq
    · have hall : ∀ a, ε a = false := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = -1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
    · have hall : ∀ a, ε a = true := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hq) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
  delta S7.hs
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, ‖g i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have hjj := congrFun (congrFun hU j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
    have hc : ∀ i, g.conjTranspose j i * g i j = ((‖g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [hc] at hjj
    exact_mod_cast hjj
  simp [key]

theorem decBound_of_compact {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0) (m N : ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m N := by
  obtain ⟨_, _, hU, _⟩ := hσ
  refine ⟨Real.sqrt (n : ℝ) ^ m, [[]], ?_, ?_⟩
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp
  · intro u v _ _ g hg
    have hn : S7.hs g = n := hs_eq_of_compact hpq hg
    have hnorm : ‖σ g u‖ = ‖u‖ := hU.2.1 g hg u
    simp only [nuJ, dSW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hn, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
    calc ‖inner ℂ v (σ g u)‖ ≤ ‖v‖ * ‖σ g u‖ := norm_inner_le_norm v (σ g u)
      _ = ‖u‖ * ‖v‖ := by rw [hnorm, mul_comm]

theorem decSmJ {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (m : ℕ) (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m (m * (n - 1)) := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · exact decBound_of_compact hpq m _ hσ
  have hp : 1 ≤ pOf ε := by omega
  have hq : 1 ≤ qOf ε := by omega
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have hth : thrStar ε < h := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε := le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hlam hgap hq0 h8
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨C, hC⟩ := pm_induction hp hq m hlam hgap hm hP hv₀
  refine decBoundJ_of_sigLam hlam hgap hth hP hv₀ hσ m _ ?_
  refine decBoundJ_sigLam hlam hstd hP hv₀ m _ ⟨(n : ℝ) ^ (2 * m) * C, fun x hx y hy g hg => ?_⟩
  have := hs_pow_mul_le m g (norm_nonneg _) fun idx => hC x hx y hy g hg idx
  calc _ ≤ _ := this
    _ = _ := by ring

theorem decSm {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m : ℕ)
    (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ m * (2 * r + k) ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hJ := decSmJ ((mir_isHCParam_iff lam).1 hlam) ((mir_gapAtLeast_iff ε lam h).1 hgap) m hm hDS
  have hN : m * (2 * r + k + 1 - 1) = m * (2 * r + k) := by rw [Nat.add_sub_cancel]
  rw [hN] at hJ
  exact decSm_of_decBoundJ hP m _ hJ

end ReciprocityTheory.ChartRestriction.DS.DecInf
