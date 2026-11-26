module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicDatumWithLawsAtJoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepsOfCls
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.exists_finset_reps_of_cls {T Γ C : Type} [Finite C] (P : T → Prop) (sm : Γ → T → T) (cls : T → C)
    (h : ∀ L L', P L → P L' → cls L = cls L' → ∃ γ, L' = sm γ L) :
    ∃ R : Finset T, (∀ L ∈ R, P L) ∧ ∀ L, P L → ∃ L₀ ∈ R, ∃ γ : Γ, L = sm γ L₀ := by
  classical
  let S : Set C := {x | ∃ L, P L ∧ cls L = x}
  have hS : ∀ x : S, ∃ L, P L ∧ cls L = x.1 := fun x => x.2
  choose f hf using hS
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hL
    exact (hf x).1
  · intro L hL
    let x : S := ⟨cls L, L, hL, rfl⟩
    exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), h (f x) L (hf x).1 hL (hf x).2⟩


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.finClasses_sysS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j c
  change (Lv.lev j c).FinClasses
  by_cases hj : j ≤ D.R.m
  · exact GlobalTheory.TwV.exists_finset_reps_of_cls (C := (D.chTw u μ).cls j) _ (Lv.lev j c).smul ((labAt X H).cls j c)
      (fun L L' hL hL' e => (((labAt X H).cls_iff j hj c c L L' hL hL').1 e).2)
  · exact (J.empty j (by omega)).elim c
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinStabSite
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem finStab_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), FinStab (sysS H X std).Lv := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  show FinStab Lv
  intro j c La hLa
  by_cases hj : j ≤ D.R.m
  · exact Nat.finite_of_card_ne_zero ((labAt X H).stab_dvd j hj c La hLa).1.ne'
  · exact (J.empty j (by omega)).elim c

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCEmbCLam
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SigWSubPowDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrime
namespace GlobalTheory

open _root_.Formalism.L2.G.Pend in
theorem wittKbar_eq_zero_of_forall_dvd (p : ℕ) [Fact p.Prime] (z : WW p)
    (h : ∀ N : ℕ, (p : WW p) ^ N ∣ z) : z = 0 := by
  have hc : wToC p z = wToC p 0 := by
    rw [map_zero]
    apply eq_of_close
    intro N
    obtain ⟨b, hb⟩ := h N
    rw [sub_zero, hb]
    exact norm_wToC_pow_mul p N b
  exact wToC_injective p hc

theorem dvd_pow_pow_sub_self_of_dvd {W : Type} [CommRing W] (p n : ℕ)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (x : W) :
    ∀ j : ℕ, (p : W) ∣ x ^ (p ^ (n * j)) - x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n) := by
      rw [← pow_mul, ← pow_add, mul_add, mul_one]
    rw [e]
    have := dvd_add (h (x ^ (p ^ (n * j)))) ih
    simpa [sub_add_sub_cancel] using this

theorem ringHom_wittKbar_eq_of_modp (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W] (hn : 0 < n)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (f g : W →+* Formalism.L2.G.Pend.WW p)
    (hfg : ∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) : f = g := by
  have key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := dvd_pow_pow_sub_self_of_dvd p n h x k
      have hx : x = x ^ (p ^ (n * k)) - (p : W) * y := by rw [← hy]; ring
      have h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k)) :=
        dvd_sub_pow_of_dvd_sub (hfg x) (n * k)
      have hk : k + 1 ≤ n * k + 1 := by
        have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
        omega
      have h1' := (pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1
      have h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        rw [pow_succ']
        exact mul_dvd_mul_left _ (ih y)
      have e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        conv_lhs => rw [hx]
        simp only [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e]
      exact dvd_sub h1' h2
  refine RingHom.ext fun x => ?_
  have := wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)
  exact sub_eq_zero.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrimeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → ∀ f g : W →+* Formalism.L2.G.Pend.WW p, (∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) → f = g := by
  first | exact @GlobalTheory.ringHom_wittKbar_eq_of_modp | exact GlobalTheory.ringHom_wittKbar_eq_of_modp | (intros; apply GlobalTheory.ringHom_wittKbar_eq_of_modp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHom
open Filter Topology

noncomputable section

namespace GlobalTheory.TeichImage

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_pow_sub_one {n : ℕ} (hn : 0 < n) : Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have h2 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have h3 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub h1 h
  rw [show p ^ n - (p ^ n - 1) = 1 by omega] at h3
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_range_of_pow_eq {n : ℕ} (hn : 0 < n) {τ : ℂ_[p]} (hτ : τ ^ (p ^ n) = τ) :
    τ ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  by_cases h0 : τ = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hq : 2 ≤ p ^ n := le_trans hp.out.two_le (Nat.le_self_pow hn.ne' p)
  have h1 : τ ^ (p ^ n - 1) = 1 := by
    have : τ ^ (p ^ n - 1) * τ = 1 * τ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hτ, one_mul]
    exact mul_right_cancel₀ h0 this
  exact Formalism.L2.G.Pend.root_mem_range p (by omega) (coprime_pow_sub_one hn) h1

theorem exists_lim {n : ℕ} (hn : 0 < n) (a : ℂ_[p])
    (ha : ∀ M : ℕ, ‖a ^ ((p ^ n) ^ (M + 1)) - a ^ ((p ^ n) ^ M)‖ ≤ ((p : ℝ)⁻¹) ^ (M + 1)) :
    ∃ τ ∈ Set.range (Formalism.L2.G.Pend.wToC p), ∀ N : ℕ, ‖a ^ ((p ^ n) ^ N) - τ‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) := by
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := Formalism.L2.G.Pend.r_nonneg p
  have hr1 : r < 1 := Formalism.L2.G.Pend.r_lt_one p
  set u : ℕ → ℂ_[p] := fun M => a ^ ((p ^ n) ^ M) with hu
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric r r hr1 fun m => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact ha m
  obtain ⟨τ, hτ⟩ := cauchySeq_tendsto_of_complete hcau
  have hball : ∀ N M : ℕ, N ≤ M → ‖u M - u N‖ ≤ r ^ (N + 1) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; exact pow_nonneg hr0 _
    | succ M hNM ih =>
      have : u (M + 1) - u N = (u (M + 1) - u M) + (u M - u N) := by ring
      rw [this]
      refine Formalism.L2.G.Pend.nadd p ((ha M).trans ?_) ih
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hlim : ∀ N : ℕ, ‖u N - τ‖ ≤ r ^ (N + 1) := by
    intro N
    have hmem : τ ∈ Metric.closedBall (u N) (r ^ (N + 1)) :=
      Metric.isClosed_closedBall.mem_of_tendsto hτ
        (eventually_atTop.2 ⟨N, fun M hM => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball N M hM⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    rw [norm_sub_rev]; exact hmem
  have hsucc : ∀ M, u (M + 1) = u M ^ (p ^ n) := by
    intro M
    show a ^ ((p ^ n) ^ (M + 1)) = (a ^ ((p ^ n) ^ M)) ^ (p ^ n)
    rw [← pow_mul a ((p ^ n) ^ M) (p ^ n), ← pow_succ]
  have h1 : Tendsto (fun M => u (M + 1)) atTop (𝓝 τ) := hτ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M => u (M + 1)) atTop (𝓝 (τ ^ (p ^ n))) := by
    simp only [hsucc]; exact hτ.pow _
  have hfix : τ ^ (p ^ n) = τ := tendsto_nhds_unique h2 h1
  exact ⟨τ, mem_range_of_pow_eq hn hfix, hlim⟩

section Ring

variable {W : Type} [CommRing W] {n : ℕ}

theorem dvd_pow_iter (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (N : ℕ) (x : W) :
    (p : W) ∣ x ^ ((p ^ n) ^ N) - x := by
  induction N with
  | zero => rw [pow_zero, pow_one, sub_self]; exact dvd_zero _
  | succ N ih =>
    have e : x ^ ((p ^ n) ^ (N + 1)) = (x ^ ((p ^ n) ^ N)) ^ (p ^ n) := by
      rw [← pow_mul x ((p ^ n) ^ N) (p ^ n), ← pow_succ]
    rw [e, show (x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x =
      ((x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x ^ ((p ^ n) ^ N)) + (x ^ ((p ^ n) ^ N) - x) by ring]
    exact dvd_add (hW _) ih

theorem dvd_pow_iter_succ (hn : 0 < n) (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (M : ℕ) (x : W) :
    (p : W) ^ (M + 1) ∣ x ^ ((p ^ n) ^ (M + 1)) - x ^ ((p ^ n) ^ M) := by
  have h := dvd_sub_pow_of_dvd_sub (hW x) (n * M)
  have e1 : (x ^ (p ^ n)) ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ (M + 1)) := by
    rw [← pow_mul, pow_succ, ← pow_mul, mul_comm]
  have e2 : x ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ M) := by rw [← pow_mul]
  rw [e1, e2] at h
  exact (pow_dvd_pow _ (by have := Nat.le_mul_of_pos_left M hn; omega)).trans h

theorem norm_map_pow_mul (φ : W →+* ℂ_[p]) (hφ : ∀ x, ‖φ x‖ ≤ 1) (k : ℕ) (c : W) :
    ‖φ ((p : W) ^ k * c)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (Formalism.L2.G.Pend.r_nonneg p) k) (hφ c)

end Ring

end GlobalTheory.TeichImage

namespace GlobalTheory

theorem mem_range_wToC_of_pow_congr : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n →
    (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W →
    ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  intro p _ n W _ hn hW _ φ hφ x
  have hr0 : 0 ≤ ((p : ℝ)⁻¹) := Formalism.L2.G.Pend.r_nonneg p
  have key : ∀ k : ℕ, ∀ x : W, ∃ w, ‖φ x - Formalism.L2.G.Pend.wToC p w‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [map_zero, sub_zero, pow_zero]; exact hφ x⟩
    | succ k ih =>
      intro x
      obtain ⟨τ, ⟨wτ, hwτ⟩, hτ⟩ := TeichImage.exists_lim hn (φ x) (fun M => by
        obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter_succ hn hW M x
        rw [← map_pow, ← map_pow, ← map_sub, hc]
        exact TeichImage.norm_map_pow_mul φ hφ (M + 1) c)
      obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter hW k x
      obtain ⟨w₁, hw₁⟩ := ih (-c)
      refine ⟨wτ + (p : Formalism.L2.G.Pend.WW p) * w₁, ?_⟩
      have hx : x = x ^ ((p ^ n) ^ k) + (p : W) * (-c) := by linear_combination -hc
      have e : φ x - Formalism.L2.G.Pend.wToC p (wτ + (p : Formalism.L2.G.Pend.WW p) * w₁) =
          (φ x ^ ((p ^ n) ^ k) - τ) + (p : ℂ_[p]) * (φ (-c) - Formalism.L2.G.Pend.wToC p w₁) := by
        conv_lhs => rw [hx]
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_natCast, map_natCast, hwτ]
        ring
      rw [e]
      refine Formalism.L2.G.Pend.nadd p ((hτ k)) ?_
      rw [norm_mul, Formalism.L2.G.Pend.norm_p_C, pow_succ']
      exact mul_le_mul_of_nonneg_left hw₁ hr0
  apply Formalism.L2.G.Pend.mem_range_of_closure p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Formalism.L2.G.Pend.r_lt_one p)
  obtain ⟨w, hw⟩ := key N x
  exact ⟨_, ⟨w, rfl⟩, by rw [dist_eq_norm]; exact lt_of_le_of_lt hw hN⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHomStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W → ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  first | exact @GlobalTheory.mem_range_wToC_of_pow_congr | exact GlobalTheory.mem_range_wToC_of_pow_congr | (intros; apply GlobalTheory.mem_range_wToC_of_pow_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplex
open IsLocalRing

namespace GlobalTheory

theorem nonempty_cEmb_of_pos_nV : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV →
    Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  intro p _ G hV
  let v : Fin G.P.nV := ⟨0, hV⟩
  have S := G.P.setting v
  haveI := S.frac_alt
  haveI := S.frac_O
  haveI : IsAdicComplete (maximalIdeal G.O) G.O := S.complete_O

  haveI hW0 : CharZero (G.P.W v) := by
    obtain ⟨l, hl⟩ := CharP.exists (G.P.W v)
    rcases CharP.char_is_prime_or_zero (G.P.W v) l with hlp | hl0
    · exfalso
      by_cases hlpe : l = p
      · subst hlpe
        exact S.p_unif.ne_zero (CharP.cast_eq_zero _ l)
      · have hcop : Nat.Coprime p l := (Nat.coprime_primes (Fact.out) hlp).2 (Ne.symm hlpe)
        have h := Nat.gcd_eq_gcd_ab p l
        rw [hcop] at h
        have h' := congrArg (fun z : ℤ => (z : G.P.W v)) h
        simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h'
        exact S.p_unif.not_isUnit (IsUnit.of_mul_eq_one _ h'.symm)
    · subst hl0
      exact CharP.charP_to_charZero _
  haveI : CharZero (G.P.Qq v) :=
    (RingHom.charZero_iff (IsFractionRing.injective (G.P.W v) (G.P.Qq v))).1 hW0
  haveI : CharZero G.Kf := (RingHom.charZero_iff (G.P.ι v).injective).1 inferInstance

  letI : Algebra (G.P.W v) G.O := (G.P.j v).toAlgebra
  haveI : Module.Finite (G.P.W v) G.O := S.finite
  have hcomap : (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) = Ideal.span {(p : G.P.W v)} := by
    have hmax : ((maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := G.P.W v) _
    rw [IsLocalRing.eq_maximalIdeal hmax, S.p_unif.maximalIdeal_eq]
  have hpO : (p : G.O) ∈ maximalIdeal G.O := by
    have : (p : G.P.W v) ∈ (maximalIdeal G.O).comap (algebraMap (G.P.W v) G.O) :=
      hcomap ▸ Ideal.subset_span rfl
    simpa using this

  haveI : Finite (ResidueField (G.P.W v)) := by
    have h := S.res_card
    rw [← S.p_unif.maximalIdeal_eq] at h
    exact Nat.finite_of_card_ne_zero (h ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Finite (ResidueField G.O) := by
    haveI : Module.Finite (G.P.W v) (ResidueField G.O) := inferInstance
    haveI : Algebra.IsIntegral (G.P.W v) (ResidueField G.O) := inferInstance
    exact Module.finite_of_finite (ResidueField (G.P.W v))

  obtain ⟨p', hp', K₀, e, e₀, hfd, he⟩ := exists_ringEquiv_integralClosure_padicInt G.O G.Kf
  have hpp : p' = p := by
    have h1 : e₀ (p : G.O) ∈ maximalIdeal (integralClosure ℤ_[p'] K₀) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hpO (by simpa using hu.map e₀.symm)
    rw [mem_maximalIdeal_integralClosure_iff, map_natCast] at h1
    have h2 : (((p : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') =
        algebraMap ℚ_[p'] (PadicAlgCl p') p := by simp
    rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp'.out Fact.out).1 h1
  subst hpp

  refine ⟨⟨(algebraMap (PadicAlgCl p') ℂ_[p']).comp (K₀.val.toRingHom.comp e.toRingHom), fun x => ?_⟩⟩
  have hx : ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p') = (((e₀ x : integralClosure ℤ_[p'] K₀) : K₀) : PadicAlgCl p') := by
    rw [he x]
  simp only [RingHom.comp_apply]
  show ‖algebraMap (PadicAlgCl p') ℂ_[p'] ((e (algebraMap G.O G.Kf x) : K₀) : PadicAlgCl p')‖ ≤ 1
  rw [hx, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  exact (mem_integralClosure_padicInt_iff K₀ _).1 (e₀ x).2
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplexStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV → Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  first | exact @GlobalTheory.nonempty_cEmb_of_pos_nV | exact GlobalTheory.nonempty_cEmb_of_pos_nV | (intros; apply GlobalTheory.nonempty_cEmb_of_pos_nV <;> assumption)
end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwU

variable {p : ℕ} [Fact p.Prime]

theorem pow_card_sub_dvd {n : ℕ} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (hirr : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n) (x : W) :
    (p : W) ∣ x ^ (p ^ n) - x := by
  haveI : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  haveI : Finite (W ⧸ Ideal.span {(p : W)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI := Fintype.ofFinite (W ⧸ Ideal.span {(p : W)})
  have h := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {(p : W)}) x)
  rw [← Nat.card_eq_fintype_card, hcard, ← map_pow, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  exact h

theorem sigW_sub_pow_dvd (y : Formalism.L2.G.Pend.WW p) : (p : Formalism.L2.G.Pend.WW p) ∣ Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p := by
  have h0 : WittVector.constantCoeff (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) = 0 := by
    rw [map_sub, map_pow]
    show (WittVector.frobenius y).coeff 0 - y.coeff 0 ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  have hnu : ¬ IsUnit (Formalism.MainNotions.FormalGroupSystem.sigW p y - y ^ p) := fun hu => by
    have := hu.map (WittVector.constantCoeff (p := p) (R := Formalism.L2.G.Pend.kb p))
    rw [h0] at this
    exact not_isUnit_zero this
  have hm := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rwa [(WittVector.irreducible p (k := Formalism.L2.G.Pend.kb p)).maximalIdeal_eq, Ideal.mem_span_singleton] at hm

abbrev sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) : G.P.W v →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) (G.P.setting v).frob

theorem sigRes_spec (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (x : G.P.W v) :
    algebraMap (G.P.W v) (G.P.Qq v) (sigRes G v x) = G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x) :=
  haveI := (G.P.setting v).frac_alt
  PI.WittUnramWork.sigW_spec _ _ _ x

theorem sigRes_pow (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v) :
    (G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x) = algebraMap (G.P.W v) (G.P.Qq v) ((sigRes G v)^[s] x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ]
    show (G.P.σ v ^ s) (G.P.σ v (algebraMap (G.P.W v) (G.P.Qq v) x)) = _
    rw [← sigRes_spec, ih, ← Function.iterate_succ_apply]

theorem map_sigRes (G : Formalism.MainNotions.G.GAtP p) (v : Fin G.P.nV) (r : G.P.W v →+* Formalism.L2.G.Pend.WW p) (x : G.P.W v) :
    r (sigRes G v x) = Formalism.MainNotions.FormalGroupSystem.sigW p (r x) := by
  have hS := G.P.setting v
  have hq : ∀ x : G.P.W v, (p : G.P.W v) ∣ x ^ (p ^ G.P.n' v) - x := pow_card_sub_dvd hS.p_unif hS.res_card
  have h := GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) hq (r.comp (sigRes G v)) ((Formalism.MainNotions.FormalGroupSystem.sigW p).comp r)
    (fun y => by
      obtain ⟨z, hz⟩ := haveI := hS.frac_alt
        PI.WittUnramWork.sigW_lift (IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (G.P.σ v) hS.frob y
      obtain ⟨c, hc⟩ := sigW_sub_pow_dvd (r y)
      refine ⟨r z - c, ?_⟩
      simp only [RingHom.comp_apply]
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      ring)
  exact congrArg (fun f => f x) h

theorem nonempty_cEmbC : ∀ (p : ℕ) [Fact p.Prime] (G : GAtP p), 0 < G.P.nV → Nonempty (CEmbC G) := by
  intro p _ G hV
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex p G hV
  let φ : ∀ v, G.P.W v →+* ℂ_[p] := fun v => (E.iK.comp (G.P.ι v)).comp (algebraMap (G.P.W v) (G.P.Qq v))
  have hφ1 : ∀ v x, ‖φ v x‖ ≤ 1 := fun v x => by
    show ‖E.iK (G.P.ι v (algebraMap _ _ x))‖ ≤ 1
    rw [(G.P.setting v).ι_comp]
    exact E.int _
  have hφr : ∀ v x, φ v x ∈ (Formalism.L2.G.Pend.wToC p).range := fun v x => by
    have hS := G.P.setting v
    exact GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom p (G.P.n' v) (G.P.W v) (by have := hS.two_le; omega) (pow_card_sub_dvd hS.p_unif hS.res_card)
      hS.eq_sum_herm_smul_frame_of_inW (φ v) (hφ1 v) x
  let eW : Formalism.L2.G.Pend.WW p ≃+* (Formalism.L2.G.Pend.wToC p).range :=
    RingEquiv.ofBijective (Formalism.L2.G.Pend.wToC p).rangeRestrict
      ⟨fun a b h => Formalism.L2.G.Pend.wToC_injective p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let rd : ∀ v, G.P.W v →+* Formalism.L2.G.Pend.WW p := fun v =>
    eW.symm.toRingHom.comp ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v))
  have hrd : ∀ v x, Formalism.L2.G.Pend.wToC p (rd v x) = φ v x := fun v x => by
    have := congrArg Subtype.val (eW.apply_symm_apply ((φ v).codRestrict (Formalism.L2.G.Pend.wToC p).range (hφr v) x))
    exact this
  refine ⟨⟨E, rd, ?_⟩⟩
  intro v s x
  have hit : ∀ y, rd v ((sigRes G v)^[s] y) = (Formalism.MainNotions.FormalGroupSystem.sigW p)^[s] (rd v y) := by
    induction s with
    | zero => intro y; rfl
    | succ s ih => intro y; rw [Function.iterate_succ_apply, ih, map_sigRes, ← Function.iterate_succ_apply]
  rw [sigRes_pow, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap, ← hit, hrd]
  rfl

end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldEmbMemAlgebraicClosure
namespace GlobalTheory

open IntermediateField

theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem exists_cEmbC_lam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ (E : CEmbC (sysS H X std).G) (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]), ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  have hV : 0 < (sysS H X std).G.P.nV := (Gl.vOf u w hg 0).pos
  obtain ⟨E⟩ := GlobalTheory.TwU.nonempty_cEmbC _ (sysS H X std).G hV
  obtain ⟨lam, hlam⟩ := GlobalTheory.padic_emb_extends_algebraicClosure (D.what₂.places.resChar w) D.what₂.LL D.what₂.embLL
    (E.iK.comp (ex.cmp.embW u w hg))
  exact ⟨E, lam, fun z hz => hlam z hz⟩

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonempty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem joint_at_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  intro hC D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  obtain ⟨E, lam, hK⟩ := GlobalTheory.TwV.exists_cEmbC_lam t std J
  have hin := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨g, hLT, curve⟩ := hC D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) J.cop hin.1 hin.2.1 lam
  obtain ⟨Xi, muT, law⟩ := GlobalTheory.T.exists_adelicDatum_with_laws_at_joint t std J
  exact ⟨{ E := E, lam := lam, hK := hK, g := g, hLT := hLT, curve := curve, hfin := GlobalTheory.TwV.finClasses_sysS t std J, hst := GlobalTheory.TwV.finStab_site t std J, Xi := Xi, muT := muT, law := law }⟩

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonemptyStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  first | exact @GlobalTheory.TwV.joint_at_nonempty | exact GlobalTheory.TwV.joint_at_nonempty | (intros; apply GlobalTheory.TwV.joint_at_nonempty <;> assumption)
end
