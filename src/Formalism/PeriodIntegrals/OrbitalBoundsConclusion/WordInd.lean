module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.WordInductionOfPartsHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.BasePointSmoothAndMem
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.DzFamilySmooth
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.WordActionLetterSiteApply
open scoped ContDiff ComplexConjugate

set_option linter.unusedSimpArgs false

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def row (κ : ℂ) (pl : Bool) (Y : ℂ) (A B : ℂ → E) (s : Fin 2) : ℂ → E := fun τ =>
  if s = 0 then
    (if pl then (Y + κ) • A τ + τ • PBP.dz A τ - τ • B τ
     else (conj Y - κ) • A τ - conj τ • PBP.dzb A τ - conj τ • B τ)
  else (if pl then τ⁻¹ • A τ else (conj τ)⁻¹ • A τ)

section slots

variable {S : Type} [Fintype S] [DecidableEq S]

def rawA (κ : ℂ) (l : Wd.Letter ℂ S) (x : Wd.Ix S → ℂ → E) : Wd.Ix S → ℂ → E := fun e =>
  row κ l.plus l.pt (x (Function.update e l.intersection_update_fsHerm_neg_one 0)) (x (Function.update e l.intersection_update_fsHerm_neg_one 1)) (e l.intersection_update_fsHerm_neg_one)

def rawBT (κ : ℂ) : List (Wd.Letter ℂ S) → (Wd.Ix S → ℂ → E) → Wd.Ix S → ℂ → E
  | [], x => x
  | l :: w, x => rawA κ l (rawBT κ w x)

end slots

theorem dz_congr {f g : ℂ → E} {U : Set ℂ} (hU : IsOpen U) (h : ∀ τ ∈ U, f τ = g τ) {τ : ℂ} (hτ : τ ∈ U) :
    PBP.dz f τ = PBP.dz g τ := by
  have e : f =ᶠ[nhds τ] g := Filter.eventually_of_mem (hU.mem_nhds hτ) h
  unfold PBP.dz
  rw [e.fderiv_eq]

theorem dzb_congr {f g : ℂ → E} {U : Set ℂ} (hU : IsOpen U) (h : ∀ τ ∈ U, f τ = g τ) {τ : ℂ} (hτ : τ ∈ U) :
    PBP.dzb f τ = PBP.dzb g τ := by
  have e : f =ᶠ[nhds τ] g := Filter.eventually_of_mem (hU.mem_nhds hτ) h
  unfold PBP.dzb
  rw [e.fderiv_eq]

theorem row_congr (κ : ℂ) (pl : Bool) (Y : ℂ) {A B A' B' : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hA : ∀ τ ∈ U, A τ = A' τ) (hB : ∀ τ ∈ U, B τ = B' τ) (s : Fin 2) {τ : ℂ} (hτ : τ ∈ U) :
    row κ pl Y A B s τ = row κ pl Y A' B' s τ := by
  have h1 := dz_congr hU hA hτ
  have h2 := dzb_congr hU hA hτ
  simp only [row, hA τ hτ, hB τ hτ, h1, h2]

section positions2

variable {S : Type} [Fintype S] [DecidableEq S]

theorem rawBT_congr (κ : ℂ) (w : List (Wd.Letter ℂ S)) {x y : Wd.Ix S → ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (h : ∀ b, ∀ τ ∈ U, x b τ = y b τ) : ∀ e, ∀ τ ∈ U, rawBT κ w x e τ = rawBT κ w y e τ := by
  induction w with
  | nil => exact h
  | cons l w ih =>
    intro e τ hτ
    simp only [rawBT, rawA]
    exact row_congr κ l.plus l.pt hU (fun t ht => ih _ t ht) (fun t ht => ih _ t ht) (e l.intersection_update_fsHerm_neg_one) hτ

theorem word_action_mul (M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) :
    act1 (M * N) x = act1 M (act1 N x) := by
  funext a
  have hs : ∀ (s : Finset (Wd.Ix S)) (f : Wd.Ix S → Q.Pr (V1 E)), (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := by
    intro s f
    refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty]; rfl) (fun j t hj ih => ?_)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl
  have hm : ∀ p q : Q.Pr (V1 E), (p * q).1 = p.1 * q.1 := fun p q => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [act1, Matrix.mul_apply, hs, hm, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  rw [Finset.sum_comm]

section pr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_add (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl
theorem pr_fst_neg (x : Q.Pr V) : (-x).1 = -x.1 := rfl
theorem pr_fst_zero : (0 : Q.Pr V).1 = 0 := rfl
theorem pr_fst_alg (Y : ℂ) : (algebraMap ℂ (Q.Pr V) Y).1 = algebraMap ℂ (Module.End ℂ V) Y := rfl
theorem pr_fst_star (x : Q.Pr V) : (star x).1 = x.2.unop := rfl
theorem pr_snd_add (x y : Q.Pr V) : (x + y).2.unop = x.2.unop + y.2.unop := rfl
theorem pr_snd_neg (x : Q.Pr V) : (-x).2.unop = -x.2.unop := rfl
theorem pr_snd_alg (Y : ℂ) : (algebraMap ℂ (Q.Pr V) Y).2.unop = algebraMap ℂ (Module.End ℂ V) (conj Y) := rfl
theorem mkPair_fst (X Xs : Module.End ℂ V) : (Q.mkP X Xs).1 = X := rfl
theorem snd_eq_of_mkPair_eq (X Xs : Module.End ℂ V) : (Q.mkP X Xs).2.unop = Xs := rfl

end pr

theorem pathSpace_add_apply (f g : V1 E) (τ : ℂ) : (f + g).1 τ = f.1 τ + g.1 τ := rfl
theorem pathSpace_neg_apply (f : V1 E) (τ : ℂ) : (-f).1 τ = -f.1 τ := rfl
theorem pathSpace_smul_apply (c : ℂ) (f : V1 E) (τ : ℂ) : (c • f).1 τ = c • f.1 τ := rfl
theorem pathSpace_zero_apply (τ : ℂ) : (0 : V1 E).1 τ = 0 := rfl
theorem opP_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    (opP κ f).1 τ = τ • PBP.dz f.1 τ + κ • f.1 τ := by
  simp [opP, off0, hτ]
theorem opPb_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    (opPb κ f).1 τ = conj τ • PBP.dzb f.1 τ + κ • f.1 τ := by
  simp [opPb, off0, hτ]
theorem opM_apply (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) (f : V1 E) (τ : ℂ) :
    (opM m hm f).1 τ = m τ • f.1 τ := rfl

theorem vlet_apply {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (σ : Wd.Site A) (l : Wd.Letter ℂ S)
    (e b : Wd.Ix S) :
    Wd.vlet σ l e b = if (∀ c, c ≠ l.intersection_update_fsHerm_neg_one → e c = b c) then
      (if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) (b l.intersection_update_fsHerm_neg_one) else 0 := by
  simp only [Wd.vlet, Wd.ins, Wd.lift0, Wd.io, Wd.eU, Matrix.sum_apply, Matrix.map_apply,
    Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  by_cases h : ∀ c, c ≠ l.intersection_update_fsHerm_neg_one → e c = b c
  · simp [h, ite_and]
  · simp [h]

private theorem sum_ite_eq_sum_update {R : Type} [Fintype R] [DecidableEq R] {β : Type} [AddCommMonoid β]
    (e : Wd.Ix R) (a : R) (g : Fin 2 → Wd.Ix R → β) :
    ∑ b : Wd.Ix R, (if (∀ c, c ≠ a → e c = b c) then g (b a) b else 0) =
      ∑ s : Fin 2, g s (Function.update e a s) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun s => Function.update e a s) (fun b => b a) ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro c hc
    rw [Function.update_of_ne hc]
  · intro b _
    exact Finset.mem_univ _
  · intro s _
    simp
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    funext c
    by_cases hc : c = a
    · subst hc
      simp
    · rw [Function.update_of_ne hc, hb c hc]
  · intro s _
    simp

theorem word_action_letter_apply (σ : Wd.Site (Q.Pr (V1 E))) (l : Wd.Letter ℂ S) (y : Wd.Ix S → V1 E) (e : Wd.Ix S) :
    act1 (Wd.vlet σ l) y e = ∑ s : Fin 2,
      ((if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) s).1
        (y (Function.update e l.intersection_update_fsHerm_neg_one s)) := by
  unfold act1
  refine (Finset.sum_congr rfl (fun b _ => ?_)).trans
    (sum_ite_eq_sum_update e l.intersection_update_fsHerm_neg_one (fun s b => ((if l.plus then Wd.Ts σ l.pt else (Wd.Ts σ l.pt).map star) (e l.intersection_update_fsHerm_neg_one) s).1 (y b)))
  rw [vlet_apply]
  split_ifs <;> rfl

theorem word_action_letter_site_apply (κ : ℂ) (l : Wd.Letter ℂ S) (y : Wd.Ix S → V1 E) (e : Wd.Ix S) {τ : ℂ} (hτ : τ ≠ 0) :
    (act1 (Wd.vlet (site1 κ) l) y e).1 τ = rawA κ l (fun b => (y b).1) e τ := by
  rw [word_action_letter_apply]
  obtain ⟨pl, a, Y⟩ := l
  simp only [rawA, row]
  generalize e a = s
  fin_cases s <;> cases pl <;>
    simp [Fin.sum_univ_two, pathSpace_add_apply, pathSpace_neg_apply, pathSpace_smul_apply, pathSpace_zero_apply, Wd.Ts, YangianSpanCharacter.T.Tm, site1,
      pr_fst_add, pr_fst_neg, pr_fst_zero, pr_fst_alg, pr_fst_star, pr_snd_add, pr_snd_neg,
      pr_snd_alg, mkPair_fst, snd_eq_of_mkPair_eq, opP_apply _ _ hτ, opPb_apply _ _ hτ, opM_apply] <;>
    first
    | rfl
    | (simp only [add_smul, sub_smul]; abel)

theorem oneBT_eq_raw (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    ∀ e, ∀ τ, τ ≠ 0 → (act1 (Wd.bT (site1 κ) w) x e).1 τ = rawBT κ w (fun b => (x b).1) e τ := by
  induction w with
  | nil =>
    intro e τ _
    have hx : act1 (Wd.bT (site1 κ) ([] : List (Wd.Letter ℂ S))) x e = x e := by
      rw [Wd.bT.eq_1]
      unfold act1
      rw [Finset.sum_eq_single e]
      · rw [Matrix.one_apply_eq]
        rfl
      · intro b _ hb
        rw [Matrix.one_apply_ne (Ne.symm hb)]
        rfl
      · intro h
        exact absurd (Finset.mem_univ e) h
    rw [hx]
    rfl
  | cons l w ih =>
    intro e τ hτ
    rw [Wd.bT.eq_2, word_action_mul, word_action_letter_site_apply κ l _ e hτ]
    simp only [rawBT, rawA]
    exact row_congr κ l.plus l.pt (U := {(0 : ℂ)}ᶜ) isOpen_compl_singleton
      (fun t ht => ih _ t ht) (fun t ht => ih _ t ht) (e l.intersection_update_fsHerm_neg_one) hτ

end positions2

section succ

theorem upd_succ_zero {n : ℕ} (e : Wd.Ix (Fin (n + 1))) (a : Fin n) (s : Fin 2) :
    Function.update e a.succ s 0 = e 0 :=
  Function.update_of_ne (Fin.succ_ne_zero a).symm _ _

theorem rawBT_map_succ (κ : ℂ) {n : ℕ} (L : List (Wd.Letter ℂ (Fin n))) (x : Wd.Ix (Fin (n + 1)) → ℂ → E) :
    rawBT κ (L.map fun m => (⟨m.plus, m.intersection_update_fsHerm_neg_one.succ, m.pt⟩ : Wd.Letter ℂ (Fin (n + 1)))) x =
      fun e => rawBT κ L (fun b => x (Fin.cons (e 0) b : Wd.Ix (Fin (n + 1)))) (Fin.tail e) := by
  induction L with
  | nil =>
    funext e
    simp only [List.map_nil, rawBT, Fin.cons_self_tail]
  | cons m L ih =>
    simp only [List.map_cons, rawBT]
    rw [ih]
    funext e
    simp only [rawA, upd_succ_zero, Fin.tail_update_succ]
    rfl

theorem positioned_cons (l : C.Letter) (w : List C.Letter) :
    D.positionted (l :: w) = (⟨l.1, 0, (l.2 : ℂ)⟩ : Wd.Letter ℂ (Fin (w.length + 1))) ::
      (D.positionted w).map fun m => (⟨m.plus, m.intersection_update_fsHerm_neg_one.succ, m.pt⟩ : Wd.Letter ℂ (Fin (w.length + 1))) := by
  unfold D.positionted
  rw [List.ofFn_succ, List.map_ofFn]
  rfl

theorem rawBT_indexed_cons (κ : ℂ) (l : C.Letter) (w : List C.Letter) (x : Wd.Ix (Fin (w.length + 1)) → ℂ → E)
    (e : Wd.Ix (Fin (w.length + 1))) :
    rawBT κ (D.positionted (l :: w)) x e =
      row κ l.1 (l.2 : ℂ) (rawBT κ (D.positionted w) (fun b => x (Fin.cons 0 b : Wd.Ix (Fin (w.length + 1)))) (Fin.tail e))
        (rawBT κ (D.positionted w) (fun b => x (Fin.cons 1 b : Wd.Ix (Fin (w.length + 1)))) (Fin.tail e)) (e 0) := by
  rw [positioned_cons]
  simp only [rawBT, rawA, rawBT_map_succ, Function.update_self, Fin.tail_update_zero]

end succ

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
end
end

open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem paramComm_local {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A) {W : Set (Fin j → Fin j → ℂ)} (hW : IsOpen W)
    (hWd : W ⊆ {Z | (Matrix.of Z).det ≠ 0}) {f g : Matrix (Fin j) (Fin j) ℂ → E} (hfg : ∀ Z ∈ W, f (Matrix.of Z) = g (Matrix.of Z)) :
    ∀ Z ∈ W, A f (Matrix.of Z) = A g (Matrix.of Z) := by
  intro Z hZ
  set h : Matrix (Fin j) (Fin j) ℂ → E := f - g with hh
  set c : ℂ → ℂ := fun τ => if τ = 0 then 1 else 0 with hc
  set U : Set (ℂ × (Fin j → Fin j → ℂ)) := Set.univ ×ˢ W with hUdef
  have hU : IsOpen U := isOpen_univ.prod hW
  have hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hWd hq.2
  have hsm : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (c q.1 • h) (Matrix.of q.2)) U := by
    refine (contDiffOn_const (c := (0 : E))).congr fun q hq => ?_
    simp [hh, hfg q.2 hq.2]
  obtain ⟨h1, -⟩ := hA U (fun τ => c τ • h) hU hUd hsm
  have hq0 : ((0 : ℂ), Z) ∈ U := ⟨trivial, hZ⟩
  have hca : ContinuousAt (fun q : ℂ × (Fin j → Fin j → ℂ) => A (c q.1 • h) (Matrix.of q.2)) ((0 : ℂ), Z) :=
    h1.continuousOn.continuousAt (hU.mem_nhds hq0)
  have hcomp : ContinuousAt (fun τ : ℂ => A (c τ • h) (Matrix.of Z)) 0 :=
    hca.comp (f := fun τ : ℂ => (τ, Z)) (continuous_id.prodMk continuous_const).continuousAt
  have t1 := hcomp.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  have t2 : Filter.Tendsto (fun τ : ℂ => A (c τ • h) (Matrix.of Z)) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have : τ ≠ 0 := hτ
    simp [hc, this]
  have := tendsto_nhds_unique t1 t2
  simp only [hc, if_true, one_smul] at this
  have e : A h (Matrix.of Z) = A f (Matrix.of Z) - A g (Matrix.of Z) := by
    rw [hh, map_sub]; rfl
  rw [← sub_eq_zero, ← e, this]

theorem dz_family_smooth {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U) {F : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (hF : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => F q.1 (Matrix.of q.2)) U) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => PBP.dz (fun τ => F τ (Matrix.of q.2)) q.1) U ∧
      ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => PBP.dzb (fun τ => F τ (Matrix.of q.2)) q.1) U := by
  set G : ℂ × (Fin j → Fin j → ℂ) → E := fun q => F q.1 (Matrix.of q.2) with hG
  have hD : ContDiffOn ℝ ∞ (fun q => fderiv ℝ G q) U := hF.fderiv_of_isOpen hU (by simp)
  have key : ∀ q ∈ U, ∀ v : ℂ, fderiv ℝ (fun τ => F τ (Matrix.of q.2)) q.1 v = fderiv ℝ G q (v, 0) := by
    intro q hq v
    have hGd : HasFDerivAt G (fderiv ℝ G q) q :=
      ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)).hasFDerivAt
    have hin : HasFDerivAt (fun τ : ℂ => (τ, q.2)) (ContinuousLinearMap.inl ℝ ℂ (Fin j → Fin j → ℂ)) q.1 :=
      hasFDerivAt_prodMk_left q.1 q.2
    have hc := hGd.comp q.1 hin
    rw [show (fun τ => F τ (Matrix.of q.2)) = G ∘ (fun τ : ℂ => (τ, q.2)) from rfl, hc.fderiv]
    rfl
  constructor
  · refine (((hD.clm_apply (contDiffOn_const (c := ((1 : ℂ), (0 : Fin j → Fin j → ℂ))))).sub
      ((hD.clm_apply (contDiffOn_const (c := (Complex.I, (0 : Fin j → Fin j → ℂ))))).const_smul Complex.I)).const_smul
        (1 / 2 : ℂ)).congr fun q hq => ?_
    simp only [PBP.dz, key q hq]
  · refine (((hD.clm_apply (contDiffOn_const (c := ((1 : ℂ), (0 : Fin j → Fin j → ℂ))))).add
      ((hD.clm_apply (contDiffOn_const (c := (Complex.I, (0 : Fin j → Fin j → ℂ))))).const_smul Complex.I)).const_smul
        (1 / 2 : ℂ)).congr fun q hq => ?_
    simp only [PBP.dzb, key q hq]

section lin

variable {X : Type} (A : (X → E) →ₗ[ℂ] (X → E))

theorem linP (a b c : ℂ) (u v w : X → E) :
    A (fun Z => a • u Z + b • v Z - c • w Z) = a • A u + b • A v - c • A w := by
  rw [show (fun Z => a • u Z + b • v Z - c • w Z) = a • u + b • v - c • w from rfl, map_sub, map_add (f := _),
    map_smul, map_smul, map_smul]

theorem linM (a b c : ℂ) (u v w : X → E) :
    A (fun Z => a • u Z - b • v Z - c • w Z) = a • A u - b • A v - c • A w := by
  rw [show (fun Z => a • u Z - b • v Z - c • w Z) = a • u - b • v - c • w from rfl, map_sub, map_sub,
    map_smul, map_smul, map_smul]

theorem linS (d : ℂ) (u : X → E) : A (fun Z => d • u Z) = d • A u := by
  rw [show (fun Z => d • u Z) = d • u from rfl, map_smul]

end lin

theorem two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  exact h i

theorem row_family (κ : ℂ) (pl : Bool) (Y : ℂ) {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hU0 : U ⊆ {q | q.1 ≠ 0}) {Fa Fb : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (ha : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fa q.1 (Matrix.of q.2)) U)
    (hb : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fb q.1 (Matrix.of q.2)) U) (s : Fin 2) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
      row κ pl Y (fun τ => Fa τ (Matrix.of q.2)) (fun τ => Fb τ (Matrix.of q.2)) s q.1) U := by
  obtain ⟨hdz, hdzb⟩ := dz_family_smooth hU ha
  have hm : Set.MapsTo (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1) U {τ | τ ≠ 0} := fun q hq => hU0 hq
  have h1 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1) U := contDiffOn_fst
  have h2 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => conj q.1) U := cd_conj.comp contDiffOn_fst hm
  have h3 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1⁻¹) U := cd_inv.comp contDiffOn_fst hm
  have h4 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (conj q.1)⁻¹) U := cd_conjinv.comp contDiffOn_fst hm
  unfold row
  rcases two_cases s with hs | hs <;> cases pl <;> simp only [hs, if_true, Bool.false_eq_true, if_false, one_ne_zero]
  · exact ((contDiffOn_const.smul ha).sub (h2.smul hdzb)).sub (h2.smul hb)
  · exact ((contDiffOn_const.smul ha).add (h1.smul hdz)).sub (h1.smul hb)
  · exact h4.smul ha
  · exact h3.smul ha

theorem row_comm {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A)
    (κ : ℂ) (pl : Bool) (Y : ℂ) {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0}) {Fa Fb : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (ha : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fa q.1 (Matrix.of q.2)) U) (s : Fin 2)
    {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    A (fun Z => row κ pl Y (fun τ => Fa τ Z) (fun τ => Fb τ Z) s q.1) (Matrix.of q.2) =
      row κ pl Y (fun τ => A (Fa τ) (Matrix.of q.2)) (fun τ => A (Fb τ) (Matrix.of q.2)) s q.1 := by
  obtain ⟨-, hc⟩ := hA U Fa hU hUd ha
  obtain ⟨hz, hzb⟩ := hc q hq
  unfold row
  rcases two_cases s with hs | hs <;> cases pl <;> simp only [hs, if_true, Bool.false_eq_true, if_false, one_ne_zero]
  · rw [linM A _ _ _ (Fa q.1) (fun Z => PBP.dzb (fun τ => Fa τ Z) q.1) (Fb q.1)]
    simp only [Pi.sub_apply, Pi.smul_apply, hzb]
  · rw [linP A _ _ _ (Fa q.1) (fun Z => PBP.dz (fun τ => Fa τ Z) q.1) (Fb q.1)]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hz]
  · rw [linS A _ (Fa q.1)]; rfl
  · rw [linS A _ (Fa q.1)]; rfl

section words

variable {S : Type} [Fintype S] [DecidableEq S]

theorem comm_rawBT {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A)
    {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U) (hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0})
    (hU0 : U ⊆ {q | q.1 ≠ 0}) (κ : ℂ) (L : List (Wd.Letter ℂ S)) (h : Wd.Ix S → ℂ → Matrix (Fin j) (Fin j) ℂ → E)
    (hs : ∀ b, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => h b q.1 (Matrix.of q.2)) U) :
    (∀ e, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
        rawBT κ L (fun b τ => h b τ (Matrix.of q.2)) e q.1) U) ∧
      ∀ e, ∀ q ∈ U, A (fun Z => rawBT κ L (fun b τ => h b τ Z) e q.1) (Matrix.of q.2) =
        rawBT κ L (fun b τ => A (h b τ) (Matrix.of q.2)) e q.1 := by
  induction L with
  | nil => exact ⟨hs, fun _ _ _ => rfl⟩
  | cons l L ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro e
      exact row_family κ l.plus l.pt hU hU0 (Fa := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ)
        (Fb := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ) (ih1 _) (ih1 _) _
    · intro e q hq
      show A (fun Z => row κ l.plus l.pt _ _ _ q.1) (Matrix.of q.2) = row κ l.plus l.pt _ _ _ q.1
      rw [row_comm hA κ l.plus l.pt hU hUd (Fa := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ)
        (Fb := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ) (ih1 _) _ hq]
      have hV : IsOpen {τ : ℂ | (τ, q.2) ∈ U} :=
        hU.preimage (continuous_id.prodMk continuous_const)
      exact row_congr κ l.plus l.pt hV (fun τ hτ => ih2 _ (τ, q.2) hτ) (fun τ hτ => ih2 _ (τ, q.2) hτ) _ hq

end words

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
end
end

open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def BasePointSmoothAndMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (γ : B.Mat k (r - (j + 1))), γ ∈ B.GV k (r - (j + 1)) →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
      {q | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} ∧
    ∀ q : ℂ × (Fin j → Fin j → ℂ), q.1 ≠ 0 → (Matrix.of q.2).det ≠ 0 →
      x0 k r j hj (Matrix.of q.2) q.1 γ ∈ Q.Glev k r 0

def Om (k r j : ℕ) (hj : j + 1 ≤ r) (Dm : Set (Q.Mx k r)) (γ : B.Mat k (r - (j + 1))) :
    Set (ℂ × (Fin j → Fin j → ℂ)) :=
  {q | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} ∩ (fun q => x0 k r j hj (Matrix.of q.2) q.1 γ) ⁻¹' Dm

theorem isOpen_O (j : ℕ) : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
  have h1 : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2).det := Continuous.matrix_det continuous_snd
  have h2 : IsOpen {q : ℂ × (Fin j → Fin j → ℂ) | (Matrix.of q.2).det ≠ 0} := isOpen_ne.preimage hd
  exact h1.inter h2

section geom

variable {k r j : ℕ} {hj : j + 1 ≤ r} {Dm : Set (Q.Mx k r)} {γ : B.Mat k (r - (j + 1))}

theorem isOpen_Om (hX : BasePointSmoothAndMem) (hγ : γ ∈ B.GV k (r - (j + 1))) (hDm : IsOpen Dm) : IsOpen (Om k r j hj Dm γ) :=
  (hX k r j hj γ hγ).1.continuousOn.isOpen_inter_preimage (isOpen_O j) hDm

theorem Om_sub {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ Om k r j hj Dm γ) :
    q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0 ∧ x0 k r j hj (Matrix.of q.2) q.1 γ ∈ Dm :=
  ⟨hq.1.1, hq.1.2, hq.2⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem family_smooth (hX : BasePointSmoothAndMem) (hγ : γ ∈ B.GV k (r - (j + 1))) {F : Q.Mx k r → E}
    (hF : Q.SmoothLev k r 0 Dm F) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => F (x0 k r j hj (Matrix.of q.2) q.1 γ)) (Om k r j hj Dm γ) := by
  intro q hq
  obtain ⟨hsm, hG⟩ := hX k r j hj γ hγ
  obtain ⟨U', F', hU', hg0, hF', hag⟩ := hF _ ⟨hG q hq.1.1 hq.1.2, hq.2⟩
  have hx : ContDiffWithinAt ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
      (Om k r j hj Dm γ) q := (hsm q hq.1).mono Set.inter_subset_left
  have hc := (hF'.contDiffAt (hU'.mem_nhds hg0)).comp_contDiffWithinAt q hx
  refine hc.congr_of_eventuallyEq ?_ (hag _ hg0 (hG q hq.1.1 hq.1.2))
  have hca : ContinuousAt (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ) q :=
    hsm.continuousOn.continuousAt ((isOpen_O j).mem_nhds hq.1)
  have h1 : (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ) ⁻¹' U' ∈ nhds q :=
    hca.preimage_mem_nhds (hU'.mem_nhds hg0)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with q' h1' h2'
  exact hag _ h1' (hG q' h2'.1.1 h2'.1.2)

end geom

section main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rules_uw (hR : RulesClosed) {k r j : ℕ} (hj : j + 1 ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ}
    {Dm : Set (Q.Mx k r)} {Φ : Q.Mx k r → E} (hz : inWb k r z) (hz' : inWb k r z') (hDm : IsOpen Dm)
    (hDs : Dm ⊆ domJ k r j hj z z') (hΦ : RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ r) (hor : i = j ∨ i = j + 1) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), RulesOn k r j hj z z' Dm (D.uwG k r z z' Φ i hi w e) := by
  intro w
  induction w with
  | nil => intro e; exact hΦ
  | cons l w ih =>
    intro e
    exact hR k r j hj z z' E Dm _ hz hz' hDm hDs (ih _) i (by omega) hor l (e 0)

theorem core (hH : HeadLetter) (hZ : ZOnly) (hR : RulesClosed) (hX : BasePointSmoothAndMem) {k r j : ℕ} (hj : j + 1 ≤ r)
    {z z' : Fin (2 * r + k + 1) → ℂ} {Dm : Set (Q.Mx k r)} {Φ : Q.Mx k r → E} (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDs : Dm ⊆ domJ k r j hj z z') (hΦ : RulesOn k r j hj z z' Dm Φ)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) :
    ∀ (w : List C.Letter), ∀ q ∈ Om k r j hj Dm γ, ∀ e,
      D.uwG k r z z' Φ (j + 1) hj w e (x0 k r j hj (Matrix.of q.2) q.1 γ) =
        rawBT (levelZeroKernel k r j) (D.positionted w)
          (fun b τ => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj (Matrix.of q.2) τ γ)) e q.1 := by
  have hO := isOpen_Om (hj := hj) hX hγ hDm
  have hOd : Om k r j hj Dm γ ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hq.1.2
  have hO0 : Om k r j hj Dm γ ⊆ {q | q.1 ≠ 0} := fun q hq => hq.1.1
  intro w
  induction w with
  | nil => intro q _ e; rfl
  | cons l w ih =>
    intro q hq e
    obtain ⟨pl, Y⟩ := l
    set κ := levelZeroKernel k r j with hκ
    set Ψ := D.uwG k r z z' Φ (j + 1) hj w (Fin.tail e) with hΨ
    have hRΨ : RulesOn k r j hj z z' Dm Ψ := rules_uw hR hj hz hz' hDm hDs hΦ (j + 1) hj (Or.inr rfl) w _
    have hV : IsOpen {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ} := hO.preimage (continuous_id.prodMk continuous_const)

    have key : ∀ s : Fin 2, ∀ τ ∈ {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ},
        D.vLet k r z z' j (by omega) (pl, Y) s Ψ (x0 k r j hj (Matrix.of q.2) τ γ) =
          rawBT κ (D.positionted w) (fun b τ' => D.vLet k r z z' j (by omega) (pl, Y) s
            (D.uwG k r z z' Φ j (by omega) w b) (x0 k r j hj (Matrix.of q.2) τ' γ)) (Fin.tail e) τ := by
      intro s τ hτ
      obtain ⟨Aop, hPC, hAz⟩ := hZ k r j hj z z' E (pl, Y) s hz hz'
      obtain ⟨hτ0, hτd, hτx⟩ := Om_sub hτ
      rw [hAz Dm Ψ hDm hDs hRΨ.1 (Matrix.of q.2) τ γ hτd hτ0 hγ hτx]
      have hW : IsOpen {Z' : Fin j → Fin j → ℂ | (τ, Z') ∈ Om k r j hj Dm γ} :=
        hO.preimage (continuous_const.prodMk continuous_id)
      rw [paramComm_local hPC hW (fun Z' hZ' => hZ'.1.2)
        (g := fun Z' => rawBT κ (D.positionted w)
          (fun b τ' => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj Z' τ' γ)) (Fin.tail e) τ)
        (fun Z' hZ' => ih (τ, Z') hZ' (Fin.tail e)) q.2 hτ]
      have hsm : ∀ b, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
          D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj (Matrix.of q.2) q.1 γ)) (Om k r j hj Dm γ) :=
        fun b => family_smooth hX hγ (rules_uw hR hj hz hz' hDm hDs hΦ j (by omega) (Or.inl rfl) w b).1
      rw [(comm_rawBT hPC hO hOd hO0 κ (D.positionted w)
        (fun b τ' Z' => D.uwG k r z z' Φ j (by omega) w b (x0 k r j hj Z' τ' γ)) hsm).2 (Fin.tail e) (τ, q.2) hτ]
      refine rawBT_congr κ (D.positionted w) hV (fun b τ' hτ' => ?_) (Fin.tail e) τ hτ
      obtain ⟨h0', hd', hx'⟩ := Om_sub hτ'
      exact (hAz Dm _ hDm hDs (rules_uw hR hj hz hz' hDm hDs hΦ j (by omega) (Or.inl rfl) w b).1
        (Matrix.of q.2) τ' γ hd' h0' hγ hx').symm
    obtain ⟨hq0, hqd, hqx⟩ := Om_sub hq
    have hHL := hH k r j hj z z' E Dm Ψ hz hz' hDm hDs hRΨ (Matrix.of q.2) γ q.1 hqd hq0 hγ hqx Y
    show D.vLet k r z z' (j + 1) hj (pl, Y) (e 0) Ψ (x0 k r j hj (Matrix.of q.2) q.1 γ) = _
    rw [rawBT_indexed_cons]
    have hcons : ∀ s : Fin 2, (fun b : Wd.Ix (Fin w.length) => fun τ =>
        D.uwG k r z z' Φ j (by omega) ((pl, Y) :: w) (Fin.cons s b : Wd.Ix (Fin (w.length + 1)))
          (x0 k r j hj (Matrix.of q.2) τ γ)) =
        fun b τ => D.vLet k r z z' j (by omega) (pl, Y) s (D.uwG k r z z' Φ j (by omega) w b)
          (x0 k r j hj (Matrix.of q.2) τ γ) := by
      intro s
      funext b τ
      simp only [D.uwG, Fin.cons_zero, Fin.cons_succ]
    simp only [hcons]
    have hq' : q.1 ∈ {τ : ℂ | (τ, q.2) ∈ Om k r j hj Dm γ} := hq
    rw [← row_congr κ pl (Y : ℂ) hV (key 0) (key 1) (e 0) hq']
    unfold row
    rcases two_cases (e 0) with h | h <;> cases pl <;>
      simp only [h, if_true, Bool.false_eq_true, if_false, one_ne_zero, Complex.conj_ofReal] <;>
      (try simp only [hκ]) <;> first | exact hHL.2.2.1 | exact hHL.1 | exact hHL.2.2.2 | exact hHL.2.1

theorem wordIndOfParts_of (hX : BasePointSmoothAndMem) : WordIndOfParts := by
  intro hH hZ hR k r j hj z z' E _ _ Dm Φ hz hz' hDm hDs hΦ Z γ hZd hγ hline w φ hφ t ht e
  have hq : ((t, Matrix.of.symm Z) : ℂ × (Fin j → Fin j → ℂ)) ∈ Om k r j hj Dm γ :=
    ⟨⟨ht, by simpa only [Equiv.apply_symm_apply] using hZd⟩,
      by simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hline t ht⟩
  have h1 := core hH hZ hR hX hj hz hz' hDm hDs hΦ hγ w _ hq e
  simp only [Equiv.apply_symm_apply] at h1
  unfold oneBT
  rw [h1, oneBT_eq_raw (levelZeroKernel k r j) (D.positionted w) φ e t ht]
  exact rawBT_congr _ _ (isOpen_ne (x := (0 : ℂ))) (fun b τ hτ => (hφ b τ hτ).symm) e t ht

end main

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
end
end

open scoped ContDiff ComplexConjugate Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section es

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {s : Set P}

def ES {m n : Type} (f : P → Matrix m n ℂ) (s : Set P) : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s

theorem es_const {m n : Type} (M : Matrix m n ℂ) (s : Set P) : ES (fun _ => M) s := fun _ _ => contDiffOn_const

theorem es_mul {m n o : Type} [Fintype n] {f : P → Matrix m n ℂ} {g : P → Matrix n o ℂ} (hf : ES f s) (hg : ES g s) :
    ES (fun x => f x * g x) s := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hf a c).mul (hg c b)

theorem es_conjTranspose {m n : Type} {f : P → Matrix m n ℂ} (hf : ES f s) : ES (fun x => (f x)ᴴ) s := by
  intro a b
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hf b a)

theorem es_det {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s) :
    ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf (σ i) i

theorem es_updateRow {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s) (r : n) (v : n → ℂ) :
    ES (fun x => (f x).updateRow r v) s := fun a b => by
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf a b

theorem es_inv {n : Type} [Fintype n] [DecidableEq n] {f : P → Matrix n n ℂ} (hf : ES f s)
    (hd : ∀ x ∈ s, (f x).det ≠ 0) : ES (fun x => (f x)⁻¹) s := fun a b => by
  have hd' : ContDiffOn ℝ ∞ (fun x => ((f x).det)⁻¹) s := (es_det hf).inv hd
  have hu : ES (fun x => (f x).updateRow b (Pi.single a 1)) s := es_updateRow hf b _
  have hm := hd'.mul (es_det hu)
  refine hm.congr fun x hx => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]

theorem es_reindex {m n m' n' : Type} (e : m ≃ m') (e' : n ≃ n') {f : P → Matrix m n ℂ} (hf : ES f s) :
    ES (fun x => Matrix.reindex e e' (f x)) s := by
  intro a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact hf _ _

theorem es_fromBlocks {l m n o : Type} {A : P → Matrix n l ℂ} {B' : P → Matrix n m ℂ} {C : P → Matrix o l ℂ}
    {D' : P → Matrix o m ℂ} (hA : ES A s) (hB : ES B' s) (hC : ES C s) (hD : ES D' s) :
    ES (fun x => Matrix.fromBlocks (A x) (B' x) (C x) (D' x)) s := fun a b => by
  rcases a with a | a <;> rcases b with b | b
  · simpa using hA a b
  · simpa using hB a b
  · simpa using hC a b
  · simpa using hD a b

theorem es_fromRows {m₁ m₂ n : Type} {A : P → Matrix m₁ n ℂ} {B' : P → Matrix m₂ n ℂ} (hA : ES A s) (hB : ES B' s) :
    ES (fun x => Matrix.fromRows (A x) (B' x)) s := fun a b => by
  rcases a with a | a
  · simpa using hA a b
  · simpa using hB a b

theorem es_fromCols {m n₁ n₂ : Type} {A : P → Matrix m n₁ ℂ} {B' : P → Matrix m n₂ ℂ} (hA : ES A s) (hB : ES B' s) :
    ES (fun x => Matrix.fromCols (A x) (B' x)) s := fun a b => by
  rcases b with b | b
  · simpa using hA a b
  · simpa using hB a b

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem es_contDiffOn {m n : Type} [Fintype m] [Fintype n] {f : P → Matrix m n ℂ} (hf : ES f s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => hf a b

end es

section x0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  simp [zfull, U.blk2, Matrix.det_fromBlocks_zero₂₁]

theorem es_zfull (j : ℕ) (s : Set (ℂ × (Fin j → Fin j → ℂ))) :
    ES (fun q : ℂ × (Fin j → Fin j → ℂ) => zfull (Matrix.of q.2) q.1) s := by
  have h1 : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => Matrix.of q.2) s := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  have h4 : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of fun _ _ : Fin 1 => q.1)) s := fun a b => by
    simp only [Matrix.of_apply]
    exact contDiff_fst.contDiffOn
  simp only [zfull, U.blk2]
  exact es_reindex _ _ (es_fromBlocks h1 (es_const _ _) (es_const _ _) h4)

theorem castM_mem {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h
  have e : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [e]
  exact hg

private theorem mMap_mem_GV {k j ρ : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (hZ : Z.det ≠ 0) {γ : B.Mat k ρ}
    (hγ : γ ∈ B.GV k ρ) : U.mMap k j ρ Z γ ∈ B.GV k (j + ρ) := by
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
  have hu' : IsUnit Zᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hZ)
  have hγ' : γᴴ * Hpk k ρ * γ = Hpk k ρ := hγ
  have hW : ∀ M : Matrix (Fin j) (Fin j) ℂ, G.wMat j * (G.wMat j * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Ux2.wMat_sq, Matrix.one_mul]
  show (U.mMap k j ρ Z γ)ᴴ * Hpk k (j + ρ) * U.mMap k j ρ Z γ = Hpk k (j + ρ)
  rw [Ux2.hpkBlocks k j ρ]
  simp only [U.mMap, Ux2.block3_conjTranspose, Ux2.block3_mul]
  refine Ux2.block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.conjTranspose_mul, Ux2.wMat_ct, Matrix.mul_assoc, Matrix.conjTranspose_nonsing_inv, hγ', hW,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]

theorem base_point_facts_holds : BasePointSmoothAndMem := by
  intro k r j hj γ hγ
  refine ⟨?_, ?_⟩
  · have hZ := es_zfull j {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0}
    have hdet : ∀ q ∈ {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0},
        (zfull (Matrix.of q.2) q.1)ᴴ.det ≠ 0 := by
      rintro q ⟨h1, h2⟩
      rw [Matrix.det_conjTranspose, det_zfull]
      exact star_ne_zero.mpr (mul_ne_zero h2 h1)
    have hI := es_inv (es_conjTranspose hZ) hdet
    have hM : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => U.mMap k (j + 1) (r - (j + 1)) (zfull (Matrix.of q.2) q.1) γ)
        {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
      simp only [U.mMap, U.blk3]
      exact es_reindex _ _ (es_fromBlocks (es_const _ _) (es_fromRows (es_mul hI (es_const _ _)) (es_const _ _))
        (es_fromCols (es_mul (es_const _ _) hZ) (es_const _ _)) (es_const _ _))
    have hX : ES (fun q : ℂ × (Fin j → Fin j → ℂ) => x0 k r j hj (Matrix.of q.2) q.1 γ)
        {q : ℂ × (Fin j → Fin j → ℂ) | q.1 ≠ 0 ∧ (Matrix.of q.2).det ≠ 0} := by
      simp only [x0, D.castM]
      exact es_reindex _ _ hM
    exact es_contDiffOn hX
  · intro q h1 h2
    apply PBF.mem_level_zero_of_mem_group
    simp only [x0]
    apply castM_mem
    apply mMap_mem_GV _ _ hγ
    rw [det_zfull]
    exact mul_ne_zero h2 h1

end x0

theorem word_induction_of_parts_holds : WordIndOfParts := wordIndOfParts_of base_point_facts_holds

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
end
end

namespace Formalism.FourierDecayAlt.P

theorem word_induction_of_parts : LevelPointCoordinates.WordIndOfParts := LevelPointCoordinates.WordIndPf.word_induction_of_parts_holds

end Formalism.FourierDecayAlt.P
