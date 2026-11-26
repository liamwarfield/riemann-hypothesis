module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FormCc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PsiForPosGelfand

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SquareIntegrableGeneratedVectors
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ProjectionSquareIntegrable
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FormBSelfLe
set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

theorem wAct_append {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    ∀ (w : List (Fin n × Fin n)) (p : Fin n × Fin n), wAct E (w ++ [p]) = wAct E w * E p.1 p.2
  | [], p => by
    change E p.1 p.2 * 1 = 1 * E p.1 p.2
    rw [mul_one, one_mul]
  | q :: w, p => by
    show E q.1 q.2 * wAct E (w ++ [p]) = E q.1 q.2 * wAct E w * E p.1 p.2
    rw [wAct_append E w p, mul_assoc]

theorem NE_nonneg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem NE_add (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x y : D) :
    NE E j (x + y) ≤ NE E j x + NE E j y := by
  delta NE
  simp only [← sum_add_distrib]
  refine sum_le_sum fun l _ => sum_le_sum fun w _ => ?_
  rw [map_add (f := _), Submodule.coe_add]
  exact norm_add_le _ _

theorem NE_smul (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (c : ℂ) (x : D) :
    NE E j (c • x) = ‖c‖ * NE E j x := by
  delta NE
  simp only [mul_sum, map_smul, Submodule.coe_smul, norm_smul]

theorem NE_zero (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) : NE E j 0 = 0 := by
  simpa using NE_smul E j 0 0

theorem NE_neg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : NE E j (-x) = NE E j x := by
  rw [← neg_one_smul ℂ x, NE_smul]; simp

theorem NE_sum (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) {ι : Type*} (s : Finset ι) (x : ι → D) :
    NE E j (∑ i ∈ s, x i) ≤ ∑ i ∈ s, NE E j (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NE_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (NE_add E j _ _).trans (add_le_add le_rfl ih)

theorem NE_mono (E : Fin n → Fin n → Module.End ℂ D) {j j' : ℕ} (h : j ≤ j') (x : D) :
    NE E j x ≤ NE E j' x :=
  sum_le_sum_of_subset_of_nonneg (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun _ _ _ =>
    sum_nonneg fun _ _ => norm_nonneg _

theorem NE_zero_eq (E : Fin n → Fin n → Module.End ℂ D) (x : D) : NE E 0 x = ‖((x : D) : H)‖ := by
  delta NE
  have hw : wAct E [] = 1 := rfl
  simp [hw]

theorem NT_nonneg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) : 0 ≤ NT E j f :=
  sum_nonneg fun _ _ => NE_nonneg E j _

theorem NT_smul (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (c : ℂ) (f : Fin n → D) :
    NT E j (c • f) = ‖c‖ * NT E j f := by
  delta NT
  simp only [mul_sum, Pi.smul_apply, NE_smul]

theorem NT_mono (E : Fin n → Fin n → Module.End ℂ D) {j j' : ℕ} (h : j ≤ j') (f : Fin n → D) :
    NT E j f ≤ NT E j' f :=
  sum_le_sum fun _ _ => NE_mono E h _

theorem NE_apply_le (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (a b : Fin n) (x : D) :
    NE E j (E a b x) ≤ NE E (j + 1) x := by
  unfold NE
  have key : ∀ l, ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖ ≤
      ∑ w : Fin (l + 1) → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖ := by
    intro l
    have e0 : ∀ w : Fin l → Fin n × Fin n,
        wAct E (List.ofFn (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) = wAct E (List.ofFn w) * E a b := by
      intro w
      rw [List.ofFn_succ', List.concat_eq_append, wAct_append]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    have e : ∀ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖ =
        ‖((wAct E (List.ofFn (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) x : D) : H)‖ := by
      intro w
      rw [e0, mul_apply_eq_comp]
    simp_rw [e]
    have hinj : Function.Injective (fun w : Fin l → Fin n × Fin n => (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) :=
      fun w w' h => funext fun i => by simpa using congrFun h i.castSucc
    rw [← sum_image (f := fun w : Fin (l + 1) → Fin n × Fin n => ‖((wAct E (List.ofFn w) x : D) : H)‖)
      (fun w _ w' _ h => hinj h)]
    exact sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _
  calc ∑ l ∈ range (j + 1), ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖
      ≤ ∑ l ∈ range (j + 1), ∑ w : Fin (l + 1) → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖ :=
        sum_le_sum fun l _ => key l
    _ ≤ _ := by
        rw [sum_range_succ' (fun l => ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖) (j + 1)]
        exact le_add_of_nonneg_right (sum_nonneg fun _ _ => norm_nonneg _)

theorem NT_tensV_le (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (a b : Fin n) (f : Fin n → D) :
    NT E j (tensV E a b f) ≤ NT E (j + 1) f + NT E j f := by
  unfold NT
  have e : ∀ c, tensV E a b f c = E a b (f c) + if c = a then f b else 0 := fun c => tensV_coord E a b f c
  calc ∑ c, NE E j (tensV E a b f c) ≤ ∑ c, (NE E (j + 1) (f c) + if c = a then NE E j (f b) else 0) := by
        refine sum_le_sum fun c _ => ?_
        rw [e]
        refine (NE_add E j _ _).trans (add_le_add (NE_apply_le E j a b _) ?_)
        split_ifs <;> simp [NE_zero]
    _ = ∑ c, NE E (j + 1) (f c) + NE E j (f b) := by rw [sum_add_distrib]; simp
    _ ≤ _ := add_le_add le_rfl (single_le_sum (f := fun c => NE E j (f c)) (fun _ _ => NE_nonneg E j _)
        (mem_univ b))

theorem NT_eeF_le (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) :
    NT E j (eeF dual E f) ≤ (n : ℝ) ^ 2 * NT E (j + 1) f := by
  unfold NT
  have e1 : ∀ d, NE E j (eeF dual E f d) ≤ NT E (j + 1) f := fun d => by
    cases dual
    · show NE E j (eeV E f d) ≤ _
      rw [eeV_coord]
      exact (NE_sum E j _ _).trans (sum_le_sum fun c _ => NE_apply_le E j _ _ _)
    · show NE E j (eeVd E f d) ≤ _
      rw [eeVd_coord, NE_neg]
      exact (NE_sum E j _ _).trans (sum_le_sum fun c _ => NE_apply_le E j _ _ _)
  calc ∑ d, NE E j (eeF dual E f d) ≤ ∑ _d : Fin n, NT E (j + 1) f := sum_le_sum fun d _ => e1 d
    _ = (n : ℝ) * NT E (j + 1) f := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (NT_nonneg E _ f)
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · exact_mod_cast Nat.le_self_pow two_ne_zero n

theorem NT_poly_le (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (p : Polynomial ℂ) (j : ℕ) :
    ∃ C : ℝ, ∀ f : Fin n → D, NT E j (Polynomial.aeval (eeF dual E) p f) ≤ C * NT E (j + p.natDegree) f := by
  have hpow : ∀ i j, ∀ f : Fin n → D, NT E j (((eeF dual E) ^ i) f) ≤ ((n : ℝ) ^ 2) ^ i * NT E (j + i) f := by
    intro i
    induction i with
    | zero => intro j f; simp
    | succ i ih =>
      intro j f
      rw [pow_succ', mul_apply_eq_comp]
      refine (NT_eeF_le dual E j _).trans ?_
      calc (n : ℝ) ^ 2 * NT E (j + 1) (((eeF dual E) ^ i) f) ≤ (n : ℝ) ^ 2 * (((n : ℝ) ^ 2) ^ i * NT E (j + 1 + i) f) :=
            mul_le_mul_of_nonneg_left (ih _ f) (by positivity)
        _ = _ := by rw [show j + 1 + i = j + (i + 1) by omega]; ring
  refine ⟨∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ 2) ^ i, fun f => ?_⟩
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, sum_mul]
  delta NT
  calc ∑ c, NE E j ((∑ i ∈ range (p.natDegree + 1), (p.coeff i • (eeF dual E) ^ i) f) c)
      ≤ ∑ c, ∑ i ∈ range (p.natDegree + 1), NE E j (((p.coeff i • (eeF dual E) ^ i) f) c) :=
        sum_le_sum fun c _ => by rw [Finset.sum_apply]; exact NE_sum E j _ _
    _ = ∑ i ∈ range (p.natDegree + 1), NT E j ((p.coeff i • (eeF dual E) ^ i) f) := by
        rw [sum_comm]; rfl
    _ ≤ ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ 2) ^ i * NT E (j + p.natDegree) f := by
        refine sum_le_sum fun i hi => ?_
        rw [LinearMap.smul_apply, NT_smul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ((hpow i j f).trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (NT_mono E (by have := mem_range.mp hi; omega) f) (by positivity)

theorem NT_single (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (b : Fin n) (x : D) :
    NT E j (Pi.single b x) = NE E j x := by
  unfold NT
  rw [sum_eq_single b (fun c _ hc => by rw [Pi.single_eq_of_ne hc, NE_zero]) (by simp)]
  simp

theorem formB_self_le (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    ‖formB ε f f‖ ≤ NT E 0 f ^ 2 := by
  unfold formB NT
  calc ‖∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f c : D) : H) ((f c : D) : H)‖
      ≤ ∑ c, ‖((f c : D) : H)‖ ^ 2 := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        rw [norm_mul, inner_self_eq_norm_sq_to_K]
        split_ifs <;> simp
    _ ≤ (∑ c, ‖((f c : D) : H)‖) ^ 2 := by
        rw [sq, sum_mul]
        refine sum_le_sum fun c _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (single_le_sum (f := fun c => ‖((f c : D) : H)‖) (fun _ _ => norm_nonneg _)
          (mem_univ c)) (norm_nonneg _)
    _ = _ := by simp [NE_zero_eq]

theorem NE_q_le {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {D' : Submodule ℂ H'}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (E' : Fin n → Fin n → Module.End ℂ D')
    (S : Submodule ℂ (Fin n → D)) (hS : ∀ a b, ∀ f ∈ S, tensV E a b f ∈ S)
    (q : (Fin n → D) → D') (P : Module.End ℂ (Fin n → D)) (d : ℕ)
    (hP : ∀ j, ∃ C : ℝ, ∀ f ∈ S, NT E j (P f) ≤ C * NT E (j + d) f)
    (ka : ℝ) (hka : ka ≠ 0)
    (hT2 : ∀ a b, ∀ f ∈ S, q (tensV E a b f) = E' a b (q f))
    (hT3 : ∀ f ∈ S, ((ka * ‖((q f : D') : H')‖ ^ 2 : ℝ) : ℂ) = formB ε (P f) (P f)) (j : ℕ) :
    ∃ C : ℝ, ∀ f ∈ S, NE E' j (q f) ≤ C * NT E (j + d) f := by
  obtain ⟨C0, hC0⟩ := hP 0
  set C1 := max C0 0 with hC1
  have hk : 0 < |ka| := abs_pos.mpr hka
  set C' := C1 / Real.sqrt |ka| with hC'
  have hC'0 : 0 ≤ C' := div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hq0 : ∀ g ∈ S, ‖((q g : D') : H')‖ ≤ C' * NT E d g := by
    intro g hg
    have h1 := congrArg norm (hT3 g hg)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖((q g : D') : H')‖)] at h1
    have h2 : |ka| * ‖((q g : D') : H')‖ ^ 2 ≤ (C1 * NT E d g) ^ 2 := by
      rw [h1]
      refine (formB_self_le ε E _).trans (pow_le_pow_left₀ (NT_nonneg E 0 _) ?_ 2)
      have h4 : C0 * NT E (0 + d) g ≤ C1 * NT E d g := by
        rw [zero_add]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NT_nonneg E d g)
      exact (hC0 g hg).trans h4
    have hx : ‖((q g : D') : H')‖ ^ 2 ≤ (C1 * NT E d g) ^ 2 / |ka| := by
      rw [le_div_iff₀ hk, mul_comm]; exact h2
    have hy : 0 ≤ C1 * NT E d g := mul_nonneg (le_max_right _ _) (NT_nonneg E d g)
    calc ‖((q g : D') : H')‖ = Real.sqrt (‖((q g : D') : H')‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((C1 * NT E d g) ^ 2 / |ka|) := Real.sqrt_le_sqrt hx
      _ = C' * NT E d g := by
          rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hy, hC']; ring
  let T : List (Fin n × Fin n) → Module.End ℂ (Fin n → D) := fun w => (w.map fun p => tensV E p.1 p.2).prod
  have hTS : ∀ w f, f ∈ S → T w f ∈ S := by
    intro w
    induction w with
    | nil => intro f hf; exact hf
    | cons p w ih => intro f hf; exact hS _ _ _ (ih f hf)
  have hTq : ∀ w f, f ∈ S → wAct E' w (q f) = q (T w f) := by
    intro w
    induction w with
    | nil => intro f hf; rfl
    | cons p w ih =>
      intro f hf
      show E' p.1 p.2 (wAct E' w (q f)) = q (tensV E p.1 p.2 (T w f))
      rw [ih f hf, hT2 _ _ _ (hTS w f hf)]
  have hTN : ∀ w j f, NT E j (T w f) ≤ 2 ^ w.length * NT E (j + w.length) f := by
    intro w
    induction w with
    | nil => intro j f; simp [T]
    | cons p w ih =>
      intro j f
      show NT E j (tensV E p.1 p.2 (T w f)) ≤ _
      refine (NT_tensV_le E j _ _ _).trans ?_
      have e1 := ih (j + 1) f
      have e2 := ih j f
      have e3 : NT E (j + w.length) f ≤ NT E (j + 1 + w.length) f := NT_mono E (by omega) f
      rw [List.length_cons, pow_succ, show j + (w.length + 1) = j + 1 + w.length by omega]
      nlinarith [NT_nonneg E (j + 1 + w.length) f, pow_pos (two_pos (α := ℝ)) w.length]
  refine ⟨∑ l ∈ range (j + 1), ((n : ℝ) ^ 2) ^ l * (C' * 2 ^ l), fun f hf => ?_⟩
  unfold NE
  rw [sum_mul]
  refine sum_le_sum fun l hl => ?_
  have hl' : l ≤ j := by have := mem_range.mp hl; omega
  calc ∑ w : Fin l → Fin n × Fin n, ‖((wAct E' (List.ofFn w) (q f) : D') : H')‖
      ≤ ∑ _w : Fin l → Fin n × Fin n, C' * (2 ^ l * NT E (d + j) f) := by
        refine sum_le_sum fun w _ => ?_
        rw [hTq _ f hf]
        refine (hq0 _ (hTS _ f hf)).trans (mul_le_mul_of_nonneg_left ?_ hC'0)
        refine (hTN _ d f).trans ?_
        rw [List.length_ofFn]
        exact mul_le_mul_of_nonneg_left (NT_mono E (by omega) f) (by positivity)
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        simp only [Fintype.card_fin]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem poles_injective {lam : Fin n → ℝ} (hlam : StrictAnti lam) : Function.Injective (poleF false lam) := by
  simpa only [poleF, Bool.cond_false] using poleV_injective hlam.injective

theorem projection_square_integrable {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)),
      (∀ s, IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (P s)) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) (P s f) = poleF false lam s • P s f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P s f = f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
        eeF false (smE ε (rreg ε)) f = z' • f → P s f = 0) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), f = ∑ s, P s f) ∧
      ∀ s (j : ℕ), ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        NT (smE ε (rreg ε)) j (P s f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f := by
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  have hc := datumV_casimir hP v₀
  have hVK := datumV_kStable hP v₀
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε) := fun v =>
    (mem_smD_iff ε (rreg ε) (v : L2 ε)).1 v.2
  obtain ⟨B, hdec, -⟩ := ee_decomp false hσ hD hgap hV hc hVK hW
  obtain ⟨hpole, -⟩ := pole_match false hσ hD hsm hgap hV hc hVK hW hG
  have hinj : Set.InjOn (poleF false lam) (Finset.univ : Finset (Fin n)) :=
    (poles_injective hlam.1).injOn
  set a := poleF false lam with ha
  set EE := eeF false (smE ε (rreg ε)) with hEE
  set S := tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) with hS
  let P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)) := fun s =>
    Polynomial.aeval EE (Lagrange.basis Finset.univ a s)
  have hPe : ∀ s (e : Fin n → smD ε (rreg ε)) (z : ℂ), EE e = z • e →
      P s e = (Lagrange.basis Finset.univ a s).eval z • e := fun s e z he => dc_aeval_eigen he _
  have hLval : ∀ s t, (Lagrange.basis Finset.univ a s).eval (a t) = if s = t then 1 else 0 := by
    intro s t
    split_ifs with hst
    · subst hst; exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne hst (Finset.mem_univ _)

  have hterm : ∀ s, ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → EE (P s e) = a s • P s e := by
    intro s e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    rw [hPe s e _ hz, hLval s t]
    split_ifs with hst
    · subst hst; rw [one_smul, hz]
    · simp
  have hsum1 : ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → ∑ s, P s e = e := by
    intro e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨t, Finset.mem_univ _⟩
    have h1 : ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) = 1 := by
      rw [← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj hne, Polynomial.eval_one]
    calc ∑ s, P s e = ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) • e :=
          Finset.sum_congr rfl fun s _ => hPe s e _ hz
      _ = e := by rw [← Finset.sum_smul, h1, one_smul]
  refine ⟨P, fun s => dc_isGKEndo_aeval (isGKEndo_eeF hσ hD _ false) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    rw [hfe, map_sum (P s), map_sum EE, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => hterm s _ (hfb b).1 _ (hfb b).2
  · intro s f _ hf
    rw [hPe s f _ hf, Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul]
  · intro s f hf z' hz' hfz
    by_cases h0 : f = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z' f hf h0 hfz
    have hts : s ≠ t := fun h => hz' (by rw [h])
    rw [hPe s f _ hfz, hLval s t, ite_eq_right hts, zero_smul]
  · intro f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    calc
      f = ∑ b ∈ B, fb b := hfe
      _ = ∑ b ∈ B, ∑ s, P s (fb b) :=
        Finset.sum_congr rfl fun b _ => (hsum1 _ (hfb b).1 _ (hfb b).2).symm
      _ = ∑ s, P s f := by
        rw [Finset.sum_comm, hfe]
        exact Finset.sum_congr rfl fun s _ => (map_sum (P s) fb B).symm
  · intro s j
    obtain ⟨C, hC⟩ := NT_poly_le false (smE ε (rreg ε)) (Lagrange.basis Finset.univ a s) j
    have hdeg : (Lagrange.basis Finset.univ a s).natDegree = n - 1 := by
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    refine ⟨C, fun f _ => ?_⟩
    have := hC f
    rw [hdeg] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

def PmProp (ε : Fin n → Bool) (m : ℕ) {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : Prop :=
  ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y

theorem one_le_q_zero {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  exact le_min hp hq

theorem square_integrable_generated_vectors {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
        (Formalism.REAL.muG ε) := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, -, -⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  obtain ⟨hgap_std, hgap_weighted⟩ := swA_thr hth
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, hgap_std⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' hv₀
  refine weighted_datum hstd hP hv₀ (fun μ hμ => ?_)
  refine ((h6 μ hμ).2.2 2 (by norm_num) hw2).congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [heq _ g.2]

theorem standard_gap_data {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    StdGap ε lam ∧ (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, (swA_thr hth).1⟩
  obtain ⟨hpos, hGel⟩ := psiFor_pos_gelfand hlam hgap hth hq hP
  exact ⟨hstd, hpos, square_integrable_generated_vectors hlam hgap hth hq hP hv₀, hasGelfandChar_sigLam hstd hP hv₀ hGel⟩

theorem tensor_inner_single_coef {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (a b : Fin n) (x y : D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((((Pi.single a y : Fin n → D) c) : D) : H)
        (tensGrp false σ g (fun d => ((((Pi.single b x : Fin n → D) d) : D) : H)) c) =
      (if ε a then (1 : ℂ) else -1) * (g a b * inner ℂ (y : H) (σ g (x : H))) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Pi.single_eq_of_ne hc]) (by simp)]
  congr 1
  delta tensGrp
  simp only [Pi.single_eq_same, Bool.cond_false, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single b (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
  simp

theorem tensor_inner_sum_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (η : Fin n → H) {β : Type*} (B : Finset β) (F : β → Fin n → D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => (((∑ b ∈ B, F b) d : D) : H)) c) =
      ∑ b ∈ B, ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => ((F b d : D) : H)) c) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  delta tensGrp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum, inner_sum]
  rw [Finset.sum_comm]

theorem pmProp_zero {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : PmProp ε 0 T Ψ v₀ := by
  refine ⟨1, fun x _ y _ g hg idx => ?_⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one, zero_mul, NE_zero_eq, NE_zero_eq, one_mul]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖
      ≤ ‖((y : smD ε (rreg ε)) : L2 ε)‖ * ‖rreg ε g ((x : smD ε (rreg ε)) : L2 ε)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [(rreg_isURepOn ε).2.1 g hg, mul_comm]

theorem regular_term_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (hstd : StdGap ε lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hth : thrStar ε < h) (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (s : Fin n) {P : Module.End ℂ (Fin n → smD ε (rreg ε))}
    (hPG : IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) P)
    (hPz : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) (P f) = poleF false lam s • P f)
    (hP1 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
      eeF false (smE ε (rreg ε)) f = z' • f → P f = 0)
    (hPN : ∀ j : ℕ, ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      NT (smE ε (rreg ε)) j (P f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f)
    {T' : S7.KType ε (lowK ε (shiftF false lam s))}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok : ReciprocityTheory.ChartRestriction.DS.cns_Ok ε (shiftF false lam s) T' Ψ') (m : ℕ) (IH : PmProp ε m T' Ψ' T'.w) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ a b : Fin n, ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok
  have := Hlam_nontrivial hstd hP hv₀
  have := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ v₀)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, hιe, hιs⟩, -⟩ := cc_gk false hstd hP hv₀ hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s rfl hw hw'
  obtain ⟨ka, q, hka, -, hqm, hT2, hT3, hT1⟩ :=
    form_cc false hstd hP hv₀ hgap' hP' hv' hW s hι hιe hιs hPG hPz hP1 hP0
  obtain ⟨K, hK⟩ := NE_q_le ε (smE ε (rreg ε)) (smE ε (rreg ε)) (tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (fun a b f hf => tensSub_stable false a b f hf) q P (n - 1) hPN ka hka (fun a b f hf => hT2 a b f hf) hT3
    (m * (n - 1))
  obtain ⟨C', hC'⟩ := IH
  refine ⟨|ka| * max C' 0 * max K 0 * max K 0, fun x hx y hy g hg a b idx => ?_⟩
  have hfx : (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = b
    · subst hc; simpa using hx
    · simp [Pi.single_eq_of_ne hc]
  have hfy : (Pi.single a y : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = a
    · subst hc; simpa using hy
    · simp [Pi.single_eq_of_ne hc]
  rw [hT1 _ hfx _ hfy g hg]
  have hidx : m * (n - 1) + (n - 1) = (m + 1) * (n - 1) := by ring
  have hX := (hqm _ hfx).1
  have hY := (hqm _ hfy).1
  have h1 := hC' _ hX _ hY g hg idx
  have h2 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x := by
    refine (hK _ hfx).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have h3 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    refine (hK _ hfy).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have hA := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x))
  have hB := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y))
  have hC0 : (0 : ℝ) ≤ max C' 0 := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ max K 0 := le_max_right _ _
  have h4 : C' * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
      NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y) := by
    calc _ ≤ max C' 0 * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
          NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA) hB
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h3 hB (mul_nonneg hC0 (mul_nonneg hK0 (NE_nonneg _ _ _)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  calc |ka| * (‖inner ℂ ((q (Pi.single a y) : smD ε (rreg ε)) : L2 ε)
          (rreg ε g ((q (Pi.single b x) : smD ε (rreg ε)) : L2 ε))‖ * ∏ t, ‖g (idx t).1 (idx t).2‖)
      ≤ |ka| * (max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y)) :=
        mul_le_mul_of_nonneg_left (h1.trans h4) (abs_nonneg _)
    _ = _ := by ring

theorem single_mem_tensSub {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (b : Fin n) {x : smD ε (rreg ε)}
    (hx : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  rw [tset_mem]; intro c; by_cases hc : c = b
  · subst hc; simpa using hx
  · simp [Pi.single_eq_of_ne hc]

theorem pmProp_succ_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ)
    (IH : ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀)
    {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hm : thrStar ε + ((m + 1 : ℕ) : ℝ) < h) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    PmProp ε (m + 1) T Ψ v₀ := by
  have hq0 := one_le_q_zero hp hq
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast at hm
  have hth : thrStar ε < h := by linarith
  obtain ⟨hstd, hpos, hW, hG⟩ := standard_gap_data hlam hgap hth hq0 hP hv₀
  obtain ⟨P, hPG, hPz, hP1, hP0, hsum, hPN⟩ := projection_square_integrable hlam hstd hP hv₀ hW hG
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  have hterm : ∀ s, ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ g ∈ UJset ε, ∀ a b : Fin n,
      ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P s (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF false lam s)
    · have hg' := ReciprocityTheory.ChartRestriction.DS.cns_shift_gap false hgap s
      obtain ⟨T', Ψ', hok⟩ := ReciprocityTheory.ChartRestriction.DS.cns_data' hq0 hs hg' (by linarith)
      exact regular_term_bound hP hv₀ hstd hgap hth hpos hW hG s (hPG s) (hPz s) (hP1 s) (hP0 s) (hPN s) hok m
        (IH hs hg' (by linarith) T' Ψ' T'.w hok.2.2.1 hok.2.2.2.1)
    · refine ⟨0, fun x hx y hy g hg a b idx => ?_⟩
      have hfx := single_mem_tensSub b hx
      have h0 : P s (Pi.single b x) = 0 :=
        cc_gk_singular false hσ hD hsm hstd (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
          (datumV_kStable hP v₀) hW hG s (ReciprocityTheory.ChartRestriction.DS.cns_sing false hlam hs) _ ((hPG s).1 _ hfx)
          (hPz s _ hfx)
      rw [h0]
      delta tensGrp
      simp
  choose Cs hCs using hterm
  refine ⟨∑ s, Cs s, fun x hx y hy g hg idx => ?_⟩
  have hfx := single_mem_tensSub (idx 0).2 hx
  have key := tensor_inner_single_coef (ε := ε) (rreg ε) g (idx 0).1 (idx 0).2 x y
  rw [hsum _ hfx, tensor_inner_sum_eq] at key
  have hsgn : ‖(if ε (idx 0).1 then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [Fin.prod_univ_succ]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
        (‖g (idx 0).1 (idx 0).2‖ * ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖)
      = ‖(if ε (idx 0).1 then (1 : ℂ) else -1) * (g (idx 0).1 (idx 0).2 *
          inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)))‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [norm_mul, norm_mul, hsgn]; ring
    _ ≤ (∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖) *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (prod_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := Finset.sum_mul _ _ _
    _ ≤ ∑ s, Cs s * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y :=
        Finset.sum_le_sum fun s _ => hCs s x hx y hy g hg (idx 0).1 (idx 0).2 (fun t => idx t.succ)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

theorem pmProp_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) :
    ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀ := by
  induction m with
  | zero => intro lam _ h _ _ T Ψ v₀ _ _; exact pmProp_zero T Ψ v₀
  | succ m ih => intro lam hlam h hgap hm T Ψ v₀ hP hv₀; exact pmProp_succ_of_gap hp hq m ih hlam hgap hm hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem pm_induction {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) {lam : Fin n → ℝ}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hm : thrStar ε + m < h)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y :=
  pmProp_of_gap hp hq m hlam hgap hm T Ψ v₀ hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
