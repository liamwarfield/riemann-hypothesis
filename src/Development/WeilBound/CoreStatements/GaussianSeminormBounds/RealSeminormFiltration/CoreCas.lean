module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasB
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]

def wordX (X : I → Module.End ℂ M) (l : List I) : Module.End ℂ M := (l.map X).prod

def filtX (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List I) (v : V), l.length ≤ n ∧ y = wordX X l (ι v)}

theorem wordX_cons (X : I → Module.End ℂ M) (a : I) (l : List I) (y : M) :
    wordX X (a :: l) y = X a (wordX X l y) := by
  simp [wordX]

theorem filtX_zero (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by
  apply le_antisymm
  · rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact ⟨v, by simp [wordX]⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩

theorem filtX_mono (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨l, v, hl, rfl⟩
  exact ⟨l, v, hl.trans h, rfl⟩

theorem filtX_X (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) (i : I) :
    ∀ x ∈ filtX X ι n, X i x ∈ filtX X ι (n + 1) := by
  have : filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i) := by
    rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩
  exact fun x hx => this hx

theorem filtX_fd [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by
  induction n with
  | zero => rw [filtX_zero]; infer_instance
  | succ n ih =>
    classical
    have hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i) := by
      rw [filtX, Submodule.span_le]
      rintro _ ⟨l, v, hl, rfl⟩
      cases l with
      | nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)
      | cons a l =>
        refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)
        exact ⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩
    exact Submodule.finiteDimensional_of_le hle

theorem filtX_succ_le (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by
  conv_lhs => rw [filtX]
  rw [Submodule.span_le]
  rintro _ ⟨l, v, hl, rfl⟩
  by_cases h : l.length ≤ n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)
  · have h' : l.length = n + 1 := by omega
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)
    congr 2
    apply List.ext_getElem
    · simp [h']
    · intro m h1 h2
      rw [List.getElem_ofFn]
      simp

theorem filtX_e [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) (n : ℕ) (k : K) :
    ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := by
  have key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length := by
    intro l v
    induction l with
    | nil =>
      have : e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v)) := by simp [wordX, hι]
      rw [this]
      exact Submodule.subset_span ⟨[], _, le_rfl, rfl⟩
    | cons a l ih =>
      have h := LinearMap.congr_fun (h1 k a) (wordX X l (ι v))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
        (filtX_X X ι _ a _ ih)
      exact filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)
  have : filtX X ι n ≤ (filtX X ι n).comap (e k) := by
    conv_lhs => rw [filtX]
    rw [Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact filtX_mono X ι hl (key l v)
  exact fun x hx => this hx

theorem filtX_perm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e)) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) {l l' : List I} (h : l.Perm l') (n : ℕ)
    (hn : l.length ≤ n + 1) (v : V) : wordX X l (ι v) - wordX X l' (ι v) ∈ filtX X ι n := by
  induction h generalizing n with
  | nil => simp
  | @cons a l l' hp ih =>
    rw [wordX_cons, wordX_cons, ← map_sub]
    cases n with
    | zero =>
      have h0 : l = [] := List.length_eq_zero_iff.1 (by simpa using hn)
      subst h0
      have h0' : l' = [] := hp.nil_eq.symm
      subst h0'
      simp
    | succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))
  | swap a b l =>
    have hl : l.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hm : wordX X l (ι v) ∈ filtX X ι n := Submodule.subset_span ⟨l, v, hl, rfl⟩
    have hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨k, rfl⟩ := hE
        exact filtX_e e X c h1 ρ ι hι n k _ hm
      | zero => simp
      | add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul a E _ h1 => exact Submodule.smul_mem _ a h1
    simp only [wordX_cons]
    exact hall _ (h2 b a)
  | trans p1 p2 ih1 ih2 =>
    have := Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))
    rwa [sub_add_sub_cancel] at this

theorem wordX_comm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (k : K) (n : ℕ) (w : Fin n → I) :
    e k * wordX X (List.ofFn w) = wordX X (List.ofFn w) * e k +
      ∑ i, ∑ j, c k j (w i) • wordX X (List.ofFn (Function.update w i j)) := by
  induction n with
  | zero => simp [wordX]
  | succ n ih =>
    have hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l := fun a l => by simp [wordX]
    have u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ) := by
      intro j
      rw [List.ofFn_succ]
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    have us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) =
        w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j) := by
      intro i j
      rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · rw [Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]
    rw [Fin.sum_univ_succ]
    simp only [u0, us, hc]
    rw [List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc,
      ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

end PositivityTheory.KReal

end
end

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasC
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

section SlopeTestRemainingChoices

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem updInv (s : J) : Function.Involutive
    (fun x : (J → I) × I => (Function.update x.1 s x.2, x.1 s)) := by
  rintro ⟨w, i⟩
  simp [Function.update_idem, Function.update_self, Function.update_eq_self]

theorem sum_upd {β : Type} [AddCommMonoid β] (s : J) (g : (J → I) → I → β) :
    ∑ w, ∑ j, g w j = ∑ w, ∑ j, g (Function.update w s j) (w s) := by
  calc ∑ w, ∑ j, g w j = ∑ x : (J → I) × I, g x.1 x.2 := (Fintype.sum_prod_type' g).symm
    _ = ∑ x : (J → I) × I, g (Function.update x.1 s x.2) (x.1 s) :=
        (Equiv.sum_comp (Function.Involutive.toPerm _ (PositivityTheory.KReal.updInv s))
          (fun x => g x.1 x.2)).symm
    _ = ∑ w, ∑ j, g (Function.update w s j) (w s) :=
        Fintype.sum_prod_type' (fun w j => g (Function.update w s j) (w s))

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def positionA (m : Matrix I I ℂ) (Θ : (J → I) → V) : (J → I) → V :=
  fun w => ∑ s, ∑ j, m (w s) j • Θ (Function.update w s j)

def formT (Θ Θ' : (J → I) → V) : ℂ := ∑ w, ⟪Θ w, Θ' w⟫_ℂ

theorem formT_positionA (m : Matrix I I ℂ) (Θ Θ' : (J → I) → V) :
    formT (positionA mᴴ Θ) Θ' = formT Θ (positionA m Θ') := by
  unfold PositivityTheory.KReal.formT PositivityTheory.KReal.positionA
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_rhs => rw [PositivityTheory.KReal.sum_upd s]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

theorem formT_self_nonneg (a : (J → I) → V) : 0 ≤ (formT a a).re := by
  unfold PositivityTheory.KReal.formT
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun w _ => by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := a w)
    rwa [RCLike.re_to_complex] at h

end SlopeTestRemainingChoices

theorem cas_tensor {K I J : Type} [Fintype K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J]
    (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (c0 : ℝ) (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (W : (J → I) → Module.End ℂ M)
    (hW : ∀ k w, e k * W w = W w * e k + ∑ i, ∑ j, c k j (w i) • W (Function.update w i j))
    (φ : M →ₗ[ℂ] ℂ) (Ψ : (J → I) → V) (hΨ : ∀ w v, ⟪Ψ w, v⟫_ℂ = φ (W w (ι v)))
    (hφ : ∀ w v, φ ((∑ k, e k * e (σ k)) (W w (ι v)) - (c0 : ℂ) • W w (ι v)) = 0)
    (hpos : ∀ (s : J) (w : J → I),
      0 ≤ (∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re = 0 →
        (fun i => Ψ (Function.update w s i)) = 0)) : Ψ = 0 := by
  have hc : ∀ k u x, e k (W u x) = W u (e k x) + ∑ i, ∑ j, c k j (u i) • W (Function.update u i j) x := by
    intro k u x
    have h := LinearMap.congr_fun (hW k u) x
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have hk : ∀ k u x, e k (e (σ k) (W u x)) = W u (e k (e (σ k) x)) +
      (∑ i, ∑ j, c k j (u i) • W (Function.update u i j) (e (σ k) x) +
        ∑ i, ∑ j, c (σ k) j (u i) • (W (Function.update u i j) (e k x) +
          ∑ i', ∑ j', c k j' (Function.update u i j i') •
            W (Function.update (Function.update u i j) i' j') x)) := by
    intro k u x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_add (f := _), map_sum, map_smul, add_assoc]
  have hΨ' : ∀ u v, φ (W u (ι v)) = ⟪Ψ u, v⟫_ℂ := fun u v => (hΨ u v).symm
  have hΨe : ∀ k u v, φ (W u (e k (ι v))) = ⟪Ψ u, ρ k v⟫_ℂ := by
    intro k u v
    rw [← hι, hΨ]
  have hcas : ∀ v, ∑ k, e k (e (σ k) (ι v)) = (c0 : ℂ) • ι v := by
    intro v
    have h := congrArg ι (LinearMap.congr_fun hc0 v)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, hι, LinearMap.smul_apply,
      Module.End.one_apply, map_smul] using h
  have hA : ∀ u v, ∑ k, φ (W u (e k (e (σ k) (ι v)))) = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by
    intro u v
    calc ∑ k, φ (W u (e k (e (σ k) (ι v)))) = φ (W u (∑ k, e k (e (σ k) (ι v)))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum]
      _ = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by rw [hcas, map_smul, map_smul, hΨ', smul_eq_mul]
  have hF : ∀ w, ∑ k, (⟪PositivityTheory.KReal.positionA (c (σ k)) Ψ w, ρ (σ k) (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) Ψ w, ρ k (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ) w, Ψ w⟫_ℂ) = 0 := by
    intro w
    have h := hφ w (Ψ w)
    have h' := hA w (Ψ w)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hk, map_add (f := _), map_smul,
      smul_eq_mul, hΨ', hΨe, h3, Matrix.conjTranspose_apply, starRingEnd_apply, star_star,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h
    simp only [PositivityTheory.KReal.positionA, sum_inner, inner_smul_left, h3, Matrix.conjTranspose_apply,
      starRingEnd_apply, star_star, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    linear_combination h - h'
  have hsum : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun w _ => hF w)
    rw [Finset.sum_comm] at h
    simpa only [PositivityTheory.KReal.formT, Finset.sum_add_distrib] using h
  have hT1 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) =
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) :=
    Fintype.sum_equiv (Function.Involutive.toPerm σ hσ) _ _ (fun _ => rfl)
  have hck : ∀ k, c k = (c (σ k))ᴴ := fun k => by rw [← h3 (σ k), hσ k]
  have hT3 : 0 ≤ (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k)
      (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [hck k, PositivityTheory.KReal.formT_positionA]
    exact PositivityTheory.KReal.formT_self_nonneg _
  have hre2 : (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re ≤ 0 := by
    have h := congrArg Complex.re hsum
    rw [hT1, Complex.add_re, Complex.add_re, Complex.zero_re] at h
    linarith
  obtain ⟨q, hq⟩ : ∃ q : J → (J → I) → ℂ, ∀ s w, q s w = ∑ k, ∑ i, ∑ j,
      ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : J → (J → I) → ℂ, ∀ s w, H s w = ∑ k, ∑ j,
      ⟪Ψ w, c k (w s) j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  have hpos' : ∀ s w, 0 ≤ (q s w).re ∧ ((q s w).re = 0 → (fun i => Ψ (Function.update w s i)) = 0) := by
    intro s w
    rw [hq]
    exact hpos s w
  have hqH : ∀ s w, q s w = ∑ i, H s (Function.update w s i) := by
    intro s w
    simp only [hq, hH, Function.update_self, Function.update_idem]
    exact Finset.sum_comm
  have hsumH : ∀ s, ∑ w, q s w = (Fintype.card I : ℂ) * ∑ w, H s w := by
    intro s
    have h := PositivityTheory.KReal.sum_upd s (fun w i => H s (Function.update w s i))
    simp only [Function.update_idem, Function.update_eq_self] at h
    simp only [hqH, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hHc : ∀ s w, H s w = starRingEnd ℂ (∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
      ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
    intro s w
    rw [hH]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj, inner_conj_symm, inner_smul_right, ← hadj]
  have hT2 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) =
      ∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) * ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ := by
    simp only [PositivityTheory.KReal.formT, PositivityTheory.KReal.positionA, sum_inner, inner_smul_left]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have hHT : (∑ s, ∑ w, H s w).re =
      (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re := by
    rw [hT2, Finset.sum_comm]
    have e1 : ∑ w, ∑ s, H s w = starRingEnd ℂ (∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
        ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hHc, map_sum]
    rw [e1, Complex.conj_re]
  have hQle : ∑ s, ∑ w, (q s w).re ≤ 0 := by
    have e2 : ∑ s, ∑ w, (q s w).re = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
      calc ∑ s, ∑ w, (q s w).re = ∑ s, ((Fintype.card I : ℂ) * ∑ w, H s w).re := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Complex.re_sum, hsumH]
        _ = ((Fintype.card I : ℂ) * ∑ s, ∑ w, H s w).re := by
            rw [Finset.mul_sum, Complex.re_sum]
        _ = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
            rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e2, hHT]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hre2
  have hQ0 : ∀ s w, (q s w).re = 0 := by
    intro s w
    have h1 : (q s w).re ≤ ∑ w', (q s w').re :=
      Finset.single_le_sum (f := fun w' => (q s w').re) (fun w' _ => (hpos' s w').1) (Finset.mem_univ w)
    have h2 : ∑ w', (q s w').re ≤ ∑ s', ∑ w', (q s' w').re :=
      Finset.single_le_sum (f := fun s' => ∑ w', (q s' w').re)
        (fun s' _ => Finset.sum_nonneg fun w' _ => (hpos' s' w').1) (Finset.mem_univ s)
    linarith [(hpos' s w).1]
  funext w
  have h := congrFun ((hpos' (Classical.arbitrary J) w).2 (hQ0 _ w)) (w (Classical.arbitrary J))
  simpa using h

end PositivityTheory.KReal

end
end

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasA
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem pos_of_eig {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (h : ∀ t : ℝ, t ≤ 0 → ∀ x, S x = (t : ℂ) • x → x = 0) (x : E) :
    0 ≤ (⟪x, S x⟫_ℂ).re ∧ ((⟪x, S x⟫_ℂ).re = 0 → x = 0) := by
  let b := hS.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let ev := hS.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (ev i : ℂ) • b i := fun i => hS.apply_eigenvectorBasis rfl i
  have hev : ∀ i, 0 < ev i := by
    intro i
    by_contra hc
    exact b.orthonormal.ne_zero i (h _ (not_lt.1 hc) _ (hb i))
  have key : (⟪x, S x⟫_ℂ).re = ∑ i, ev i * Complex.normSq ⟪b i, x⟫_ℂ := by
    rw [← b.sum_inner_mul_inner x (S x), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS (b i) x, hb, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b i), mul_left_comm,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ev i * Complex.normSq ⟪b i, x⟫_ℂ :=
    fun i _ => mul_nonneg (hev i).le (Complex.normSq_nonneg _)
  rw [key]
  refine ⟨Finset.sum_nonneg hnn, fun h0 => ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  have hz : ∀ i, ⟪b i, x⟫_ℂ = 0 := fun i =>
    Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hev i).ne')
  rw [← b.sum_repr' x]
  simp [hz]

section Ops

variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def matOp (m : Matrix I I ℂ) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => ∑ j, m i j • Θ j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [Finset.smul_sum, smul_comm a]

def valOp (A : Module.End ℂ V) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => A (Θ i))
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

theorem matOp_apply (m : Matrix I I ℂ) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    matOp m Θ i = ∑ j, m i j • Θ j := rfl

theorem valOp_apply (A : Module.End ℂ V) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    valOp A Θ i = A (Θ i) := rfl

theorem matOp_adj (m : Matrix I I ℂ) (x y : PiLp 2 (fun _ : I => V)) :
    ⟪matOp m x, y⟫_ℂ = ⟪x, matOp mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, matOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

end Ops

theorem cas_one {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (Φ : I → V) (hΦ : ∀ Θ : I → V, ∑ i, X i (ι (Θ i)) = 0 → ∑ i, ⟪Φ i, Θ i⟫_ℂ = 0) :
    0 ≤ (∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re = 0 → Φ = 0) := by
  let R : K → Module.End ℂ (PiLp 2 (fun _ : I => V)) := fun k => matOp (c k) + valOp (ρ k)
  have hRa : ∀ k Θ i, R k Θ i = ∑ j, c k i j • Θ j + ρ k (Θ i) := fun k Θ i => rfl
  have hRadj : ∀ k x y, ⟪R k x, y⟫_ℂ = ⟪x, R (σ k) y⟫_ℂ := by
    intro k x y
    simp only [R, LinearMap.add_apply, inner_add_left, inner_add_right]
    rw [matOp_adj, h3]
    congr 1
    simp only [PiLp.inner_apply, valOp_apply, hadj]
  let m1 : PiLp 2 (fun _ : I => V) →ₗ[ℂ] M :=
    { toFun := fun Θ => ∑ i, X i (ι (Θ i))
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.smul_sum] }
  have hm1 : ∀ Θ, m1 Θ = ∑ i, X i (ι (Θ i)) := fun _ => rfl
  have hem : ∀ k Θ, e k (m1 Θ) = m1 (R k Θ) := by
    intro k Θ
    have h1' : ∀ i y, e k (X i y) = ∑ j, c k j i • X j y + X i (e k y) := by
      intro i y
      have := LinearMap.congr_fun (h1 k i) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at this
      rw [← this]; abel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hm1, hRa, map_sum, map_add (f := _), map_smul, h1', hι, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  let N := (LinearMap.ker m1)ᗮ
  have hRN : ∀ k, ∀ x ∈ N, R k x ∈ N := by
    intro k x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hRadj]
    apply hx
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← hem, hu, map_zero]
  let S : Module.End ℂ (PiLp 2 (fun _ : I => V)) := ∑ k, R k * R (σ k) - ((c0 + d : ℝ) : ℂ) • 1
  have hSa : ∀ x, S x = ∑ k, R k (R (σ k) x) - ((c0 + d : ℝ) : ℂ) • x := by
    intro x
    simp only [S, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  have hS : LinearMap.IsSymmetric S := by
    intro x y
    rw [hSa, hSa, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hRadj, hRadj, hσ]
  have hSN : ∀ x ∈ N, S x ∈ N := by
    intro x hx
    rw [hSa]
    exact N.sub_mem (N.sum_mem fun k _ => hRN _ _ (hRN _ _ hx)) (N.smul_mem _ hx)
  have hΦN : WithLp.toLp 2 Φ ∈ N := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [PiLp.inner_apply]
    exact hΦ (fun i => u i) hu
  have hpos := pos_of_eig (S.restrict hSN) (hS.restrict_invariant hSN) (by
    intro t ht x hx
    have hx' : S x.1 = (t : ℂ) • x.1 := congrArg Subtype.val hx
    have h0 : m1 x.1 = 0 := by
      refine h5 (t + (c0 + d)) (by linarith) _ ?_ ?_
      · rw [hm1]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, _, rfl⟩
      · rw [hSa, sub_eq_iff_eq_add, ← add_smul] at hx'
        rw [LinearMap.sum_apply]
        simp only [Module.End.mul_apply, hem]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hx', map_smul]
        push_cast
        rfl
    have h2 : ⟪x.1, x.1⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 x.2 _ h0
    exact Subtype.ext (inner_self_eq_zero.1 h2)) ⟨_, hΦN⟩
  have hval : ∀ i, S (WithLp.toLp 2 Φ) i = (2 : ℂ) • ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
    intro i
    have e1 : ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l = (d : ℂ) • Φ i := by
      have : ∀ l, ∑ k, ∑ j, c k i j * c (σ k) j l = (d : ℂ) * (if i = l then 1 else 0) := by
        intro l
        have := congrFun (congrFun h4 i) l
        simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
      calc ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l
          = ∑ k, ∑ l, ∑ j, (c k i j * c (σ k) j l) • Φ l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum, smul_smul]
        _ = ∑ l, (∑ k, ∑ j, c k i j * c (σ k) j l) • Φ l := by
            rw [Finset.sum_comm]
            simp only [Finset.sum_smul]
        _ = (d : ℂ) • Φ i := by simp [this]
    have e2 : ∑ k, ρ k (ρ (σ k) (Φ i)) = (c0 : ℂ) • Φ i := by
      have := LinearMap.congr_fun hc0 (Φ i)
      simpa [LinearMap.sum_apply] using this
    have e3 : ∑ k, ρ k (∑ l, c (σ k) i l • Φ l) = ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
      rw [← Equiv.sum_comp hσ.toPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Function.Involutive.coe_toPerm, hσ k, map_sum, map_smul]
    have e4 : S (WithLp.toLp 2 Φ) i = ∑ k, R k (R (σ k) (WithLp.toLp 2 Φ)) i - ((c0 + d : ℝ) : ℂ) • Φ i := by
      rw [hSa]
      simp
    rw [e4]
    simp only [hRa, smul_add, map_add (f := _), Finset.sum_add_distrib]
    rw [e1, e2, e3, two_smul]
    push_cast
    rw [add_smul]
    abel
  have hin : (⟪(⟨_, hΦN⟩ : N), S.restrict hSN ⟨_, hΦN⟩⟫_ℂ) =
      2 * ∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ := by
    change ⟪WithLp.toLp 2 Φ, S (WithLp.toLp 2 Φ)⟫_ℂ = _
    rw [PiLp.inner_apply, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval, inner_smul_right]
    simp only [inner_sum]
  rw [hin] at hpos
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [h2re] at hpos
  refine ⟨by linarith [hpos.1], fun h0 => ?_⟩
  have := congrArg Subtype.val (hpos.2 (by rw [h0, mul_zero]))
  funext i
  exact congrArg (fun z : PiLp 2 (fun _ : I => V) => z i) this

end PositivityTheory.KReal

end
end

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem cas_bound {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e))
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (G : Submodule ℂ M)
    (hG : G = sInf {N | LinearMap.range ι ≤ N ∧ (∀ k, ∀ x ∈ N, e k x ∈ N) ∧ ∀ i, ∀ x ∈ N, X i x ∈ N}) :
    (∀ x ∈ G, (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ G, ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ ∀ k, ∀ y ∈ F, e k y ∈ F := by
  classical
  have hFe : ∀ n k, ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := fun n k => filtX_e e X c h1 ρ ι hι n k
  have hGF : ∀ x ∈ G, ∃ n, x ∈ filtX X ι n := by
    intro x hx
    have hdir : Directed (· ≤ ·) (filtX X ι) := (Monotone.directed_le fun _ _ h => filtX_mono X ι h)
    have hle : G ≤ ⨆ n, filtX X ι n := by
      rw [hG]
      refine sInf_le ⟨?_, ?_, ?_⟩
      · rw [← filtX_zero X ι]; exact le_iSup (filtX X ι) 0
      · intro k y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem n (hFe n k y hn)
      · intro i y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem (n + 1) (filtX_X X ι n i y hn)
    exact (Submodule.mem_iSup_of_directed _ hdir).1 (hle hx)
  refine ⟨?_, fun x hx => ?_⟩
  swap
  · obtain ⟨n, hn⟩ := hGF x hx
    exact ⟨filtX X ι n, filtX_fd X ι n, hn, hFe n⟩
  set C : Module.End ℂ M := (∑ k, e k * e (σ k)) - (c0 : ℂ) • (1 : Module.End ℂ M) with hC
  have hCa : ∀ x, C x = (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x := fun x => by simp [hC]
  have hCF : ∀ n, ∀ x ∈ filtX X ι n, C x ∈ filtX X ι n := by
    intro n x hx
    rw [hCa, LinearMap.sum_apply]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => hFe n k _ (hFe n _ x hx)) (Submodule.smul_mem _ _ hx)

  have hsurj : ∀ n, filtX X ι (n + 1) ≤ filtX X ι n ⊔ (filtX X ι (n + 1)).map C := by
    intro n
    by_contra hcon
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.1 hcon
    obtain ⟨φ, hφx, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxn inferInstance
    have hφz : ∀ y ∈ filtX X ι n ⊔ (filtX X ι (n + 1)).map C, φ y = 0 := by
      intro y hy
      have : φ y ∈ (filtX X ι n ⊔ (filtX X ι (n + 1)).map C).map φ := Submodule.mem_map_of_mem hy
      rw [hφ0] at this
      exact (Submodule.mem_bot ℂ).1 this
    let W : (Fin (n + 1) → I) → Module.End ℂ M := fun w => wordX X (List.ofFn w)
    have hex : ∀ w : Fin (n + 1) → I, ∃ u : V, ∀ v, ⟪u, v⟫_ℂ = φ (W w (ι v)) := by
      intro w
      haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
      refine ⟨(InnerProductSpace.toDual ℂ V).symm
        (LinearMap.toContinuousLinearMap (φ ∘ₗ (W w) ∘ₗ ι)), fun v => ?_⟩
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    choose Ψ hΨ using hex
    have hWm : ∀ w v, W w (ι v) ∈ filtX X ι (n + 1) := fun w v =>
      Submodule.subset_span ⟨List.ofFn w, v, by simp, rfl⟩
    have hΨ0 : Ψ = 0 := by
      refine cas_tensor σ hσ e c c0 h3 ρ hadj hc0 ι hι W (fun k w => wordX_comm e X c h1 k (n + 1) w) φ Ψ hΨ
        (fun w v => ?_) (fun s w => ?_)
      · rw [← hCa]
        exact hφz _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hWm w v)))
      · refine cas_one σ hσ e X c d c0 h1 h3 h4 ρ hadj hc0 ι hι h5 (fun i => Ψ (Function.update w s i))
          (fun Θ hΘ => ?_)
        have key : ∀ i, ⟪Ψ (Function.update w s i), Θ i⟫_ℂ =
            φ (wordX X ((List.ofFn w).eraseIdx s) (X i (ι (Θ i)))) := by
          intro i
          rw [hΨ]
          have hp : (List.ofFn (Function.update w s i)).Perm ((List.ofFn w).eraseIdx s ++ [i]) := by
            have e1 : List.ofFn (Function.update w s i) = (List.ofFn w).set s i := by
              apply List.ext_getElem
              · simp
              · intro m h1 h2
                rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
                by_cases hm : (s : ℕ) = m
                · subst hm; simp
                · rw [if_neg hm, Function.update_of_ne]
                  intro h; exact hm (by rw [← h])
            rw [e1]
            exact (List.set_perm_cons_eraseIdx (by simpa using s.2) i).trans
              (List.perm_append_singleton _ _).symm
          have hm := filtX_perm e X c h1 h2 ρ ι hι hp n (by simp) (Θ i)
          have h0 := hφz _ (Submodule.mem_sup_left hm)
          rw [map_sub, sub_eq_zero] at h0
          refine h0.trans ?_
          simp [wordX]
        simp only [key]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, ← map_sum, hΘ, map_zero, map_zero]
    apply hφx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (filtX_succ_le X ι n hx)
    rw [map_add (f := _), hφz y (Submodule.mem_sup_left hy), zero_add]
    have : Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} ≤
        LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, v, rfl⟩
      have := hΨ w v
      rw [hΨ0] at this
      rw [Pi.zero_apply, inner_zero_left] at this
      exact this.symm
    exact this hz
  have hstep : ∀ n, ∀ x ∈ filtX X ι (n + 1), C x ∈ filtX X ι n → x ∈ filtX X ι n := by
    intro n x hx hCx
    haveI := filtX_fd X ι (n + 1)
    let P : Submodule ℂ (filtX X ι (n + 1)) := (filtX X ι n).comap (filtX X ι (n + 1)).subtype
    let C1 : Module.End ℂ (filtX X ι (n + 1)) := C.restrict (hCF (n + 1))
    have hP : P ≤ P.comap C1 := fun y hy => hCF n y hy
    have hs : Function.Surjective (P.mapQ P C1 hP) := by
      intro z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective z
      obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, hab⟩ := Submodule.mem_sup.1 (hsurj n y.2)
      refine ⟨P.mkQ ⟨b, hb⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
      show C b - (y : M) ∈ filtX X ι n
      rw [← hab]
      simpa using ha
    have hi : Function.Injective (P.mapQ P C1 hP) := LinearMap.injective_iff_surjective.2 hs
    have : P.mkQ ⟨x, hx⟩ = 0 := by
      apply hi
      rw [map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hCx
    exact (Submodule.Quotient.mk_eq_zero P).1 this
  intro x hx hCx
  rw [← hCa, ← filtX_zero X ι] at hCx
  rw [← filtX_zero X ι]
  obtain ⟨n, hn⟩ := hGF x hx
  induction n with
  | zero => exact hn
  | succ n ih => exact ih (hstep n x hn (filtX_mono X ι (Nat.zero_le n) hCx))

end PositivityTheory.KReal

end
