module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLoc

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ImageProdLoc
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableInvCube
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCChain
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem re_mix_le (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (U : Finset (List C.Letter))
    (θ : List C.Letter → ℝ) (hθ : ∀ a, 0 ≤ θ a) (p : C.LPt) (B : List C.Letter → ℝ)
    (hB : ∀ u ∈ U, ‖KB.gN S v ε i u p p‖ ≤ B u) :
    (KB.mix S v ε i U θ p p).re ≤ ∑ u ∈ U, θ u * max (B u) 0 := by
  unfold KB.mix
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left
    ((Complex.re_le_norm _).trans ((hB u hu).trans (le_max_left _ _))) (hθ u)

private lemma two_mul_norm_le_add_of_psdOn_pair {α : Type} [DecidableEq α] (G : α → α → ℂ) (p q : α) (hpq : p ≠ q)
    (h : TB.PSDOn ({p, q} : Finset α) G) : 2 * ‖G p q‖ ≤ ‖G p p‖ + ‖G q q‖ := by
  set Y : Finset α := {p, q} with hY
  let e : Fin 2 → Y := ![⟨p, by simp [Y]⟩, ⟨q, by simp [Y]⟩]
  have hN := Matrix.PosSemidef.submatrix h e
  have hqp : G q p = conj (G p q) := by
    have h0 := hN.1.apply 1 0
    simp [e] at h0
    rw [← h0]
  by_cases hw : G p q = 0
  · rw [hw, norm_zero, mul_zero]
    positivity
  set w := G p q with hwdef
  set ζ : ℂ := conj w / (‖w‖ : ℂ) with hζ
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  have hcw : conj w * w = (‖w‖ : ℂ) ^ 2 := Complex.conj_mul' w
  have h1 : ζ * w = ‖w‖ := by
    rw [hζ, div_mul_eq_mul_div, hcw, pow_two, mul_div_assoc, div_self hw', mul_one]
  have h2 : conj ζ * conj w = ‖w‖ := by
    rw [← map_mul, h1, Complex.conj_ofReal]
  have hnz : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]
  have h3 : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hnz]
    simp
  have key := hN.re_dotProduct_nonneg ![1, -ζ]
  have hform : star (![1, -ζ] : Fin 2 → ℂ) ⬝ᵥ
      Matrix.mulVec ((Matrix.of fun x y : Y => G x y).submatrix e e) ![1, -ζ] =
      G p p - ζ * w - conj ζ * G q p + conj ζ * ζ * G q q := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e, w]
    try ring
  rw [hform, hqp, h1, h2, h3, one_mul] at key
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at key
  have ha := Complex.re_le_norm (G p p)
  have hb := Complex.re_le_norm (G q q)
  linarith

theorem gN_entry (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (p q : C.LPt) (B : ℝ) (hp : ‖KB.gN S v ε j (w.1 v) p p‖ ≤ B)
    (hq : ‖KB.gN S v ε j (w.1 v) q q‖ ≤ B) : ‖KB.gN S v ε j (w.1 v) p q‖ ≤ B := by
  by_cases hpq : p = q
  · subst hpq
    exact hp
  have hps := hpos v ε hε j hj w {p, q}
  have hcs := two_mul_norm_le_add_of_psdOn_pair (S.gramLoc v ε j (w.1 v)) p q hpq hps
  unfold KB.gN at hp hq ⊢
  rw [norm_div] at hp hq ⊢
  rcases (norm_nonneg (S.sizeAt v (w.1 v) : ℂ)).eq_or_lt with h0 | hs
  · rw [← h0, div_zero] at hp ⊢
    exact hp
  · rw [div_le_iff₀ hs] at hp hq ⊢
    linarith

theorem locSup_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛ0 : 0 ≤ Λ b (n - 1) v) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (hIH : ∀ u, D.AdmAt S v u → u.length + (n - 2) * C.Kst ≤ S.Ntop → LocSup S v ε (n - 1) b u h)
    (a : List C.Letter) (ha : D.AdmAt S v a) (hlen : a.length + (n - 1) * C.Kst ≤ S.Ntop) :
    LocSup S v ε n b a h := by
  have hk : (n - 1) * C.Kst = (n - 2) * C.Kst + C.Kst := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, add_mul, one_mul]
  have hl2 : b + (n - 1) - 1 = b + n - 2 := by omega
  obtain ⟨Ba, hBa⟩ := hIH a ha (by omega)
  rw [hl2] at hBa
  obtain ⟨w, rfl⟩ := exists_word_of_admissible_at_place S ha

  have hsup : ∃ B : ℝ, ∀ p ∈ ({h} : Finset C.LPt), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w.1 v) (p ++ [(n - 1, t)]) (p ++ [(n - 1, t)])‖ ≤ B :=
    ⟨Ba, fun p hp t ht => by rw [Finset.mem_singleton] at hp; subst hp; exact hBa t ht⟩
  obtain ⟨hcont, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩ :=
    hGL ε hε b n hb hn hbn (w.1 v) ha {h} (by simp [hh]) hsup

  obtain ⟨Up, θp, Um, θm, hUp, hUm, hLB⟩ := hLL b (n - 1) hb (by omega) (by omega) (w.1 v) ha (by omega)
  have hBu : ∀ u ∈ Up ∪ Um, LocSup S v ε (n - 1) b u h := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact hIH u (hUp.2 u hu).1 (by have := (hUp.2 u hu).2; omega)
    · exact hIH u (hUm.2 u hu).1 (by have := (hUm.2 u hu).2; omega)
  choose! Bu hBu' using hBu
  set Bp := ∑ u ∈ Up, θp u * max (Bu u) 0 with hBp
  set Bq := ∑ u ∈ Um, θm u * max (Bu u) 0 with hBq
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg fun u _ => mul_nonneg (hUp.1.1 u) (le_max_right _ _)
  have hBq0 : 0 ≤ Bq := Finset.sum_nonneg fun u _ => mul_nonneg (hUm.1.1 u) (le_max_right _ _)
  set Bt := max (max Ba 0) (Bp + Bq) with hBt
  have hBt0 : 0 ≤ Bt := (le_max_right _ _).trans (le_max_left _ _)

  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts 1 1 one_pos
  have := i1; have := i2
  have hgR : (0 : ℝ) < S.g := by exact_mod_cast hg
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem (Lstd 1 1) (S.g : ℝ) hgR.ne'
  have := j1; have := j2
  obtain ⟨Cs, -, hCsum⟩ := pbc_lstdSum
  obtain ⟨hsm, -⟩ := hCsum 1 1 (S.g : ℝ) (fun _ => Λ b (n - 1) v) one_pos hgR (fun _ => hΛ0)
  let D : Fin 1 → C.LPt → C.LPt → ℂ → ℂ := fun _ p q c =>
    KB.gN S v ε (b + n - 1) (w.1 v) (p ++ [(n, c)]) (q ++ [(n, c)])
  let U : Fin 1 → C.LPt × ℂ → C.LPt × ℂ → ℂ := fun _ p q =>
    KB.gN S v ε (b + n - 2) (w.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])
  have hGD : GermData {h} U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) := by
    refine ⟨fun _ Xs hXs => hblk Xs hXs, ⟨max Ba B' ⊔ 0, le_max_right _ _, fun _ p hp x hx => ?_⟩,
      fun _ p hp q hq σ => (hlim p hp q hq σ).1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.1,
      fun _ p hp q hq σ => (hlim p hp q hq σ).2.2⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨(hBa x⁻¹ (inv_ne_zero hx)).trans ?_, (hB' p (Finset.mem_singleton_self p) x hx).trans ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hD : ∀ (v' : Fin 1) (z : ℂ), z ≠ 0 → TB.PSDOn ({h} : Finset C.LPt) (fun p q => D v' p q z) := by
    intro v' z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w (({h} : Finset C.LPt).image fun p => p ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this {h} (fun p => p ++ [(n, z)]) (fun p hp => Finset.mem_image_of_mem _ hp)

  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd 1 1), ∀ x : crystallineComparison.V 1, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ)‖ ≤
        Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ) := by
    intro σ _ x hx hx'
    set t := (x 0)⁻¹ with ht_def
    set t' := ((x + (S.g : ℝ) • σ) 0)⁻¹ with ht'_def
    have ht : t ≠ 0 := inv_ne_zero (hx 0)
    have ht' : t' ≠ 0 := inv_ne_zero (hx' 0)
    have ephi : phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ) =
        KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')]) := by
      simp [phi, U, t, t']
    rw [ephi, mL_one]
    set a0 := ‖((S.g : ℝ) • σ) 0‖
    have ediff : t⁻¹ - t'⁻¹ = -(((S.g : ℝ) • σ) 0) := by
      simp only [t, t', inv_inv, Pi.add_apply]; ring

    have hcs : ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ ≤ Ba :=
      gN_entry S hpos v ε hε _ (by omega) w _ _ Ba (hBa t ht) (hBa t' ht')

    obtain ⟨u, hu, hB⟩ := hLB ε hε t t' {h} ht ht' (by simp [hh])
    have hob := offdiag_bound _ _ _ h {h} (Finset.mem_singleton_self h) hB
      (Λ b (n - 1) v ^ C.Kst * Bp) (Λ b (n - 1) v ^ C.Kst * Bq) ?_ ?_
    rotate_left
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Up θp hUp.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_left _ hu) t ht; rwa [hl2] at this
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')])
          (h ++ [(n - 1, t')])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Um θm
          (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Um θm hUm.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_right _ hu) t' ht'; rwa [hl2] at this
    rw [hl2, norm_mul, norm_mul, hu, one_mul, norm_pow, ediff, norm_neg] at hob
    set X := ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    have hl : a0 ^ C.Kst * X ≤ Λ b (n - 1) v ^ C.Kst * (Bp + Bq) := by
      have h1 : (a0 ^ C.Kst * X) ^ 2 ≤ (Λ b (n - 1) v ^ C.Kst * (Bp + Bq)) ^ 2 := by
        refine hob.trans ?_
        have hL := pow_nonneg hΛ0 C.Kst
        nlinarith [mul_nonneg hL hBp0, mul_nonneg hL hBq0, mul_nonneg (mul_nonneg hL hL) (mul_nonneg hBp0 hBq0)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rw [mul_one]; exact hcs.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have ha0 : 0 < a0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [mul_min_of_nonneg _ _ hBt0, mul_one]
      refine le_min (hcs.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
      have h2 : X ≤ (Λ b (n - 1) v / a0) ^ C.Kst * (Bp + Bq) := by
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 _)]
        linarith [hl]
      refine h2.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hΛ0 ha0.le) _)
  refine ⟨(∏ _v : Fin 1, KB.dlB S b n) *
    ∑' σ : crystallineComparison.dualSet (Lstd 1 1), Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V 1)),
    fun t ht => ?_⟩
  have hH := herglotz_germ (H := C.LPt) (f := 1) {h} (fun _ _ => 1) (psd_single_one h) D hD
    (fun _ p hp q hq => (hcont p hp q hq).1) (fun _ p hp q hq => (hcont p hp q hq).2) (S.g : ℝ) hgR
    (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U (fun _ => Pua) (fun _ => Paa)
    (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) hGD (fun _ _ _ _ => rfl) (Lstd 1 1) Lm hLm
    (fun σ => Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ)) (hsm.mul_left Bt) hF
    (fun _ => t) {fun _ => t} (by simp)
  rw [hcov, Finset.sum_singleton] at hH
  have hgood : Good (fun _ : Fin 1 => t) := fun _ => ht
  have hN : Nz {h} (fun _ _ => (1 : ℂ)) D (fun _ => t) =
      (KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re := by
    simp [Nz, hgood, Fz, D]
  rw [hN, one_pow, one_mul] at hH
  have h0 := psd_diag _ _ (PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w {h ++ [(n, t)]})
    (Finset.mem_singleton_self _)
  have hc := Complex.nonneg_iff.1 h0
  have e : KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)]) =
      ((KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re : ℂ) :=
    Complex.ext (by simp) (by simp [hc.2.symm])
  rw [e, Complex.norm_real, Real.norm_of_nonneg hc.1]
  exact hH

theorem locSup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) :
    ∀ n, 1 ≤ n → ∀ b, 1 ≤ b → b + n ≤ S.G.r + 2 → ∀ h, D.ptSize h = b - 1 → ∀ a, D.AdmAt S v a →
      a.length + (n - 1) * C.Kst ≤ S.Ntop → LocSup S v ε n b a h := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ m ih =>
    intro _ b hb hbn h hh a ha hlen
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact locSup_one S hI v ε hε b hb (by omega) a ha h hh
    · refine locSup_step S hpos hg v Λ hLL hGL ε hε (m + 1) (by omega) b hb hbn
        (by rw [Nat.add_sub_cancel]; exact hΛ0 b m hb hm (by omega)) h hh ?_ a ha hlen
      intro u hu hulen
      have e1 : m + 1 - 2 = m - 1 := by omega
      rw [e1] at hulen
      rw [Nat.add_sub_cancel]
      exact ih hm b hb (by omega) h hh u hu hulen

end

end Formalism.FourierDecayAlt.P.PBC
end

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem tsum_mix {ι W : Type} (Wd : Finset W) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hms : Summable m)
    (hM : 0 < ∑' i, m i) (q : ι → W → ℝ) (hq : ∀ i, TB.IsProb Wd (q i)) :
    ∃ θ : W → ℝ, TB.IsProb Wd θ ∧ ∀ N : W → ℝ,
      Summable (fun i => m i * ∑ u ∈ Wd, q i u * N u) ∧
      ∑' i, m i * ∑ u ∈ Wd, q i u * N u = (∑' i, m i) * ∑ u ∈ Wd, θ u * N u := by
  set M := ∑' i, m i with hMdef
  have hq1 : ∀ i u, q i u ≤ 1 := by
    intro i u
    by_cases hu : u ∈ Wd
    · rw [← (hq i).2.2]
      exact Finset.single_le_sum (fun a _ => (hq i).1 a) hu
    · rw [(hq i).2.1 u hu]
      exact zero_le_one
  have hsu : ∀ u, Summable (fun i => m i * q i u) := fun u =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm0 i) ((hq i).1 u))
      (fun i => mul_le_of_le_one_right (hm0 i) (hq1 i u)) hms
  refine ⟨fun u => (∑' i, m i * q i u) / M, ⟨fun u => div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (hm0 i) ((hq i).1 u)) hM.le, fun u hu => ?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · simp [(hq _).2.1 u hu]
  · rw [← Finset.sum_div, div_eq_one_iff_eq hM.ne', ← Summable.tsum_finsetSum (fun u _ => hsu u)]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, (hq i).2.2, mul_one]
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    exact summable_sum fun u _ => (hsu u).mul_right (N u)
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum (fun u _ => (hsu u).mul_right (N u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_mul_right]
    field_simp

theorem mL_pat {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L σ * ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K = ∏ v ∈ crystallineComparison.pat L σ, L v ^ K := by
  have h1 : ∀ v ∈ crystallineComparison.pat L σ, crystallineComparison.mfac K (L v) ‖σ v‖ * ‖σ v‖ ^ K = L v ^ K := by
    intro v hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ha : 0 < ‖σ v‖ := lt_of_le_of_lt (hL v) hv
    have hle : (L v / ‖σ v‖) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg (hL v) ha.le) ((div_le_one ha).mpr hv.le)
    unfold crystallineComparison.mfac
    rw [if_neg ha.ne', min_eq_right hle, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ ha.ne'
  have h2 : ∀ v ∈ (Finset.univ : Finset (Fin f)), v ∉ crystallineComparison.pat L σ → crystallineComparison.mfac K (L v) ‖σ v‖ = 1 := by
    intro v _ hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rfl
    · have ha : 0 < ‖σ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact min_eq_left (one_le_pow₀ ((one_le_div ha).mpr hv))
  unfold crystallineComparison.mL
  rw [← Finset.prod_subset (Finset.subset_univ _) h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl h1

theorem bound_mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) (X Y : ℝ)
    (h : (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X ≤ (∏ v ∈ crystallineComparison.pat L σ, L v ^ K) * Y) : X ≤ crystallineComparison.mL K L σ * Y := by
  have hP : 0 < ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K := by
    refine Finset.prod_pos fun v hv => pow_pos ?_ _
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact lt_of_le_of_lt (hL v) hv
  rw [← mL_pat K L hL σ] at h
  refine le_of_mul_le_mul_left ?_ hP
  calc (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X
      ≤ crystallineComparison.mL K L σ * (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * Y := h
    _ = (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * (crystallineComparison.mL K L σ * Y) := by ring

theorem mL_nonneg {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) : 0 ≤ crystallineComparison.mL K L σ := Finset.prod_nonneg fun v _ => by
    unfold crystallineComparison.mfac
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (pow_nonneg (div_nonneg (hL v) (norm_nonneg _)) _)

theorem mL_zero {f : ℕ} (K : ℕ) (L : Fin f → ℝ) : crystallineComparison.mL K L 0 = 1 := by
  unfold crystallineComparison.mL crystallineComparison.mfac
  simp

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_gN (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (p q : Fin S.f → C.LPt) :
    ∏ v, KB.gN S v ε i (w.1 v) (p v) (q v) =
      (∏ v, S.gramLoc v ε i (w.1 v) (p v) (q v)) / (C.Word.size S.P w.1 : ℂ) := by
  unfold KB.gN C.Word.size
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rfl

theorem nstV_eq (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : Fin S.f → ℂ) :
    KB.NstV S ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' *
      ∏ v, KB.gN S v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)]) (C.loc (S.σ v) h' ++ [(s, t' v)]) := by
  unfold KB.NstV
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have e := prod_gN S ε i w (fun v => C.loc (S.σ v) h ++ [(s, t v)]) (fun v => C.loc (S.σ v) h' ++ [(s, t' v)])
  rw [e, mul_div_assoc]

end setting

end

end Formalism.FourierDecayAlt.P.PBC
end

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GSup (S : C.HidaSetting E Wp Wq) (ε : ℝ) (b n : ℕ) (P : ℝ) : Prop :=
  ∀ w' ∈ S.base.Wall, S.base.cnt w' + n * C.Kst ≤ S.Ntop →
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : crystallineComparison.V S.f, Good t →
          (KB.NstV S ε (b + n - 1) n w' Y κ t t).re ≤
            P * ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ

theorem integrable_inv_cube : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem zero_mem_dual {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) : (0 : crystallineComparison.V f) ∈ crystallineComparison.dualSet La := by
  intro z _; simp [Lat.psi_zero]

theorem one_le_tsum_mL {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (g : ℝ)
    (hs : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :
    1 ≤ ∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := by
  have := hs.le_tsum (⟨0, zero_mem_dual La⟩ : crystallineComparison.dualSet La) (fun σ _ => mL_nonneg K L hL _)
  simpa [mL_zero] using this

theorem gN_one_reg (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (w : S.W) (h h' : C.LPt) (hh : D.ptSize h = b - 1)
    (hh' : D.ptSize h' = b - 1) :
    ContinuousOn (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) {0}ᶜ ∧
    Integrable (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) := by
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hC⟩, -⟩ := hI v ε hε b hb hbr w h h' hh hh'
  have e : b + 1 - 1 = b := by omega
  rw [e]
  have hcongr : ∀ c ∈ ({0}ᶜ : Set ℂ), φ c / (S.sizeAt v (w.1 v) : ℂ) =
      KB.gN S v ε b (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
    intro c hc
    unfold KB.gN
    rw [hφ c hc]
  have hφi : Integrable φ :=
    Integrable.mono' (integrable_inv_cube.const_mul Cφ) hφc.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hφc.div_const _).continuousOn.congr fun c hc => (hcongr c hc).symm, ?_⟩
  refine (hφi.div_const (S.sizeAt v (w.1 v) : ℂ)).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with c hc
  exact hcongr c hc

def SumBound (f : ℕ) (Cs : ℝ) : Prop :=
  ∀ (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2)

theorem size_step (f : ℕ) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (dl R g : ℝ) (hdl : 0 ≤ dl) (hR : 0 < R) (hg : 0 < g)
    (L thr : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v ∧ L v ≤ thr v) (M V : ℝ) (hM : M ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2))
    (hV : dl * (∏ v, Cs * (1 + (R * thr v / g) ^ 2)) / R ^ (2 * f) ≤ V) : dl * M / R ^ (2 * f) ≤ V := by
  refine le_trans ?_ hV
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (hM.trans ?_) hdl
  refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have h1 : R * L v / g ≤ R * thr v / g := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL v).2 hR.le) hg.le
  have h0 : 0 ≤ R * L v / g := div_nonneg (mul_nonneg hR.le (hL v).1) hg.le
  nlinarith

theorem gsup_one (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hpos : C.ThmPPos S) (hI : KB.IntAll S)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v) (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hbr : b ≤ S.G.r + 1) (hX : ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v) (Cs : ℝ) (hCs1 : 1 ≤ Cs)
    (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b 1) * (∏ v, Cs * (1 + (R * thr S b 1 v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b 1) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b 1 ∧ GSup S ε b 1 P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ X b v := fun v => (hX v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => X b v) hR hg' hL0
  have hM1 := one_le_tsum_mL (Lstd S.f R) C.Kst (fun v => X b v) hL0 (S.g : ℝ) hsm
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) with hMdef
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b 1 := Finset.prod_nonneg fun v _ => (dlB_pos S hg b 1).le
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b 1) * M / R ^ (2 * S.f), by positivity,
    size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b 1) hX M _ hsle hRB, ?_⟩
  intro w' hw' hcnt
  simp only [one_mul] at hcnt ⊢
  obtain ⟨θ, hθ, hWV⟩ := Formalism.FourierDecayAlt.P.plane_wave_bound E Wp Wq S X hW ε hε b hb hbr w' hw' hcnt
  obtain ⟨θ', hθ', hmix⟩ := tsum_mix (S.base.Wb (S.base.cnt w' + C.Kst))
    (fun σ : crystallineComparison.dualSet (Lstd S.f R) => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith)
    (fun σ => θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))) (fun σ => hθ _)
  refine ⟨θ', hθ', fun Y hY κ hκ t ht => ?_⟩
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + 1 - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(1, c)]) (C.loc (S.σ v) h' ++ [(1, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + 1 - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(1, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(1, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  have hreg := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) =>
    gN_one_reg S hI v ε hε b hb hbr w' (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [JCx1.needs.ptSize_loc]; exact hY h hh) (by rw [JCx1.needs.ptSize_loc]; exact hY h' hh')
  set N0 : S.W → ℝ := fun u => S.base.N0 ε (b - 1) u Y κ
  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd S.f R),
      ‖Hh Y κ (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h'))
        ((S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
          ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u := by
    intro σ _
    exact bound_mL C.Kst (fun v => X b v) hL0 _ _ _ (hWV Y hY κ hκ _ _)
  have hH := herglotz_plain (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b 1)
    (fun _ => dlB_pos S hg b 1)
    (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h')) (fun _ _ _ _ => rfl)
    (Lstd S.f R)
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
      ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u)
    (hmix N0).1 (fun σ hσ => hF σ hσ)
    t {t} (by simp)
  rw [(hmix N0).2, hcov, Finset.sum_singleton] at hH
  have hN : Nz Y κ D t = (KB.NstV S ε (b + 1 - 1) 1 w' Y κ t t).re := by
    simp only [Nz, if_pos ht]
    rw [nstV_eq]
    rfl
  rw [hN] at hH
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  linarith [hH]

end

end Formalism.FourierDecayAlt.P.PBC
end

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
