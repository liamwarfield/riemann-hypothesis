module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermStep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCFinal
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gsup_succ (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛt : ∀ v, 0 ≤ Λ b (n - 1) v ∧ Λ b (n - 1) v ≤ thr S b n v) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b n) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b n * P' ∧ GSup S ε b n P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ Λ b (n - 1) v := fun v => (hΛt v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => Λ b (n - 1) v) hR hg' hL0
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
  have hM0 : 0 ≤ M := tsum_nonneg fun σ => mL_nonneg _ _ hL0 _
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b n := Finset.prod_nonneg fun v _ => (dlB_pos S hg b n).le
  have hsz := size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b n) hΛt M _ hsle hRB
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b n) * M / R ^ (2 * S.f) * P', by positivity,
    mul_le_mul_of_nonneg_right hsz hP'0, ?_⟩
  intro w' hw' hcnt
  obtain ⟨θ, hθ, H⟩ := germ_step S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn P' hP' hP'0 w' hw' hcnt
    (Lstd S.f R) hsm
  refine ⟨θ, hθ, fun Y hY κ hκ t ht => ?_⟩
  have h1 := H Y hY κ hκ t {t} (by simp) (by simpa using ht)
  rw [hcov, Finset.sum_singleton] at h1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [h1]

theorem gsup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ thr S b (s + 1) v)
    (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hX : b ≤ S.G.r + 1 → ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v)
    (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B : ℝ) (hB1 : 1 ≤ B)
    (hSz : ∀ n, 1 ≤ n → ∃ R : ℝ, 0 < R ∧
      (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
        B ^ S.f * S.base.vol b n)
    (hvol : ∀ n, 0 ≤ S.base.vol b n) :
    ∀ n, 1 ≤ n → b + n ≤ S.G.r + 1 →
      ∃ P, 0 ≤ P ∧ P ≤ B ^ (S.f * n) * ∏ m ∈ Finset.Ico 1 (n + 1), S.base.vol b m ∧ GSup S ε b n P := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro hbn
    obtain ⟨R, hR, hRB⟩ := hSz 1 le_rfl
    obtain ⟨P, hP0, hPle, hP⟩ := gsup_one S hg hpos hI X hW ε hε b hb (by omega) (hX (by omega)) Cs hCs1 hCs
      B R hR hRB
    refine ⟨P, hP0, ?_, hP⟩
    simpa using hPle
  | succ n hn ih =>
    intro hbn
    obtain ⟨P', hP'0, hP'le, hP'⟩ := ih (by omega)
    obtain ⟨R, hR, hRB⟩ := hSz (n + 1) (by omega)
    have hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v :=
      fun b s hb hs hbs v => (hΛ b s hb hs hbs v).1
    have hΛt : ∀ v, 0 ≤ Λ b (n + 1 - 1) v ∧ Λ b (n + 1 - 1) v ≤ thr S b (n + 1) v := by
      intro v
      have := hΛ b n hb hn (by omega) v
      simpa using this
    have hP'' : GSup S ε b (n + 1 - 1) P' := by simpa using hP'
    obtain ⟨P, hP0, hPle, hP⟩ := gsup_succ S hpos hI hg Λ hLL hGL hΛ0 ε hε (n + 1) (by omega) b hb (by omega)
      hΛt P' hP'' hP'0 Cs hCs1 hCs B R hR hRB
    refine ⟨P, hP0, hPle.trans ?_, hP⟩
    rw [Finset.prod_Ico_succ_top (by omega), mul_add, mul_one, pow_add]
    have hBf : 0 ≤ B ^ S.f := pow_nonneg (by linarith) _
    have hv := hvol (n + 1)
    calc B ^ S.f * S.base.vol b (n + 1) * P' ≤ B ^ S.f * S.base.vol b (n + 1) *
        (B ^ (S.f * n) * ∏ m ∈ Finset.Ico 1 (n + 1), S.base.vol b m) :=
          mul_le_mul_of_nonneg_left hP'le (mul_nonneg hBf hv)
      _ = _ := by ring

theorem embV_ne (S : C.HidaSetting E Wp Wq) (t : E) (ht : t ≠ 0) : Good (embV S t) := fun v => (map_ne_zero (S.σ v)).mpr ht

theorem embV_inj (S : C.HidaSetting E Wp Wq) [Nonempty (Fin S.f)] : Function.Injective (embV S) := by
  intro a c h
  obtain ⟨v⟩ := ‹Nonempty (Fin S.f)›
  have h1 := congrFun h v
  exact (S.σ v).injective h1

theorem nst_eq_nstV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (hi : i ≤ S.G.r + 1) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t : E) :
    S.base.Nst ε i s w Y κ t t = KB.NstV S ε i s w Y κ (embV S t) (embV S t) := by
  unfold TB.Data.Nst KB.NstV
  simp only [C.HidaSetting.base, C.HidaSetting.mkData, C.HidaSetting.gram, if_pos hi, TB.join, C.loc, List.map_append,
    List.map_cons, List.map_nil]
  rfl

theorem sumFormConcrete_of (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hU : S6.Unram E)
    (hpos : C.ThmPPos S) (hI : KB.IntAll S) (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v)
    (hXt : JC.HidaCurvatureBarriers S X) (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v)
    (hΛt : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v)
    (hthr : ∀ b s v, 1 ≤ b → 1 ≤ s → 0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v))
    (hGL : ∀ v, KB.GermLoc S v) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (hCs : SumBound S.f Cs) (B : ℝ) (hB1 : 1 ≤ B)
    (hSz : ∀ b n, 1 ≤ b → 1 ≤ n → ∃ R : ℝ, 0 < R ∧
      (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
        B ^ S.f * S.base.vol b n)
    (A : ℝ) (hA1 : 1 ≤ A)
    (hBL : ∀ b s, 1 ≤ b → 1 ≤ s →
        ∃ (_ : DiscreteTopology (latV S (J.LaB E S.g S.G.r b s)))
          (_ : IsZLattice ℝ (latV S (J.LaB E S.g S.G.r b s))),
          ZLattice.covolume (latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s ∧
          (∃ (Lm : Submodule ℤ (crystallineComparison.V S.f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
            ∀ σ ∈ crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)), (S.g : ℝ) • σ ∈ Lm) ∧
          ∀ Λ : Fin S.f → ℝ, (∀ v, 0 ≤ Λ v ∧ Λ v ≤ thr S b s v) → S.base.vol b s ≤ 1 →
            Summable (fun σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)) =>
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) ∧
            ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ A ^ S.f)
    (C₄ : ℝ) (hCA : A ≤ C₄) (hCB : B ≤ C₄) : JC.SumFormConcrete S C₄ := by
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hne : Nonempty (Fin S.f) := ⟨S.pl.symm (Classical.arbitrary _)⟩
  have hΛ : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ thr S b (s + 1) v := by
    intro b s hb hs hbs v
    have := hΛt b s hb hs hbs v
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    show (if b + s ≤ S.G.r + 1 then J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b (s + 1) (S.pl v)
      else 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l b (S.pl v)) = _
    rw [if_pos hbs]; rfl
  have hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v :=
    fun b s hb hs hbs v => (hΛ b s hb hs hbs v).1
  have hvol : ∀ b n, 0 ≤ S.base.vol b n := by
    intro b n
    show 0 ≤ (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w) ^ 2 /
      (FractionalIdeal.absNorm (S6.dualIdl E S.g (S6.nuBlock S.G.r b n)) : ℝ)
    exact div_nonneg (sq_nonneg _) (by first | exact_mod_cast FractionalIdeal.absNorm_nonneg _ | exact Rat.cast_nonneg.2 (FractionalIdeal.absNorm_nonneg _) | positivity)
  intro ε hε i s hs hsi hir w hw hbud hvolS
  have hir' : i ≤ S.G.r + 1 := hir
  set b := i - s + 1 with hbdef
  have hb : 1 ≤ b := by omega
  have hbi : b + s - 1 = i := by omega

  obtain ⟨P', hP'0, hP'le, hP'⟩ := gsup_all S hpos hI hg X hW Λ hLL hGL hΛ ε hε b hb
    (fun hbr v => hXt b hb hbr v) Cs hCs1 hCs B hB1 (fun n hn => hSz b n hb hn) (hvol b) (s - 1) (by omega)
    (by omega)

  obtain ⟨i1, i2, hcov, ⟨Lm, j1, j2, hLm⟩, hsum⟩ := hBL b s hb (by omega)
  have := i1; have := i2
  have hΛs : ∀ v, 0 ≤ Λ b (s - 1) v ∧ Λ b (s - 1) v ≤ thr S b s v := by
    intro v
    have := hΛ b (s - 1) hb (by omega) (by omega) v
    rwa [show s - 1 + 1 = s by omega] at this
  obtain ⟨hsm, hsle⟩ := hsum (fun v => Λ b (s - 1) v) hΛs hvolS
  have hcnt : S.base.cnt w + s * C.Kst ≤ S.Ntop := by
    have h1 : S.base.cnt w + (s + 1) * S.base.K ≤ S.base.Ntop := hbud
    have h2 : S.base.K = C.Kst := rfl
    have h3 : S.base.Ntop = S.Ntop := rfl
    rw [h2, h3] at h1
    have : s * C.Kst ≤ (s + 1) * C.Kst := Nat.mul_le_mul_right _ (by omega)
    omega
  have hP'' : GSup S ε b (s - 1) P' := hP'
  obtain ⟨θ, hθ, H⟩ := germ_step S hpos hI hg Λ hLL hGL hΛ0 ε hε s hs b hb (by omega) P' hP'' hP'0 w hw hcnt
    (latV S (J.LaB E S.g S.G.r b s)) hsm
  set M := ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
    crystallineComparison.mL C.Kst (fun v => Λ b (s - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
  have hM0 : 0 ≤ M := tsum_nonneg fun σ => mL_nonneg _ _ (fun v => (hΛs v).1) _
  refine ⟨M * P', ?_, θ, hθ, fun Y hY κ hκ t₀ Ss hS => ?_⟩
  · have hpv : 0 ≤ ∏ m ∈ Finset.Ico 1 s, S.base.vol b m := Finset.prod_nonneg fun m _ => hvol b m
    have e1 : s - 1 + 1 = s := by omega
    rw [e1] at hP'le
    have hC0 : 0 ≤ C₄ := by linarith
    calc M * P' ≤ A ^ S.f * (B ^ (S.f * (s - 1)) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m) :=
          mul_le_mul hsle hP'le hP'0 (pow_nonneg (by linarith) _)
      _ ≤ C₄ ^ S.f * (C₄ ^ (S.f * (s - 1)) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m) := by
          gcongr
      _ = C₄ ^ (S.base.f * s) * ∏ m ∈ Finset.Ico 1 s, S.base.vol b m := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          show S.f + S.f * (s - 1) = S.f * s
          have : s = (s - 1) + 1 := by omega
          conv_rhs => rw [this]
          ring
  · have hY' : ∀ h ∈ Y, TB.level h = b - 1 := by
      intro h hh; rw [hY h hh]; omega
    have hmem : ∀ z ∈ Ss.image (embV S), z - embV S t₀ ∈ latV S (J.LaB E S.g S.G.r b s) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
      rw [← map_sub]
      exact Submodule.mem_map_of_mem (hS t ht).2
    have hgd : ∀ z ∈ Ss.image (embV S), Good z := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
      exact embV_ne S t (hS t ht).1
    have h1 := H Y hY' κ hκ (embV S t₀) (Ss.image (embV S)) hmem hgd
    rw [hcov, Finset.sum_image fun a _ b _ h => embV_inj S h] at h1
    have hdl : 0 < ∏ _v : Fin S.f, KB.dlB S b s := Finset.prod_pos fun v _ => dlB_pos S hg b s
    have e2 : ∀ t ∈ Ss, (S.base.Nst ε i s w Y κ t t).re =
        (KB.NstV S ε (b + s - 1) s w Y κ (embV S t) (embV S t)).re := by
      intro t _
      rw [hbi, nst_eq_nstV S ε i s hir' w Y κ t]
    rw [Finset.sum_congr rfl e2]
    have e3 : i - s = b - 1 := by omega
    rw [e3]
    have h1' : (∏ _v : Fin S.f, KB.dlB S b s) *
        ∑ x ∈ Ss, (KB.NstV S ε (b + s - 1) s w Y κ ((embV S) x) ((embV S) x)).re ≤
        (∏ _v : Fin S.f, KB.dlB S b s) * ((M * P') *
          ∑ u ∈ S.base.Wb (S.base.cnt w + s * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ) := by
      rw [← mul_assoc]; exact h1
    exact le_of_mul_le_mul_left h1' hdl

end setting

theorem sumFormOfLoc : KB.SumFormOfLoc := by
  obtain ⟨Cs, hCs1, hCs⟩ := pbc_lstdSum
  obtain ⟨B, hB1, hSzAll⟩ := pbc_sizesSup Cs hCs1
  obtain ⟨A, hA1, hBLall⟩ := pbc_blockLatV
  refine ⟨max A B, le_max_of_le_left hA1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S X Λ hg1 hg2 hU hpos hG hI hW hXt hL hΛt hthr hGL
  exact sumFormConcrete_of S hg1 hg2 hU hpos hI X hW hXt Λ hL hΛt hthr hGL Cs hCs1
    (fun R g L hR hg hL => hCs S.f R g L hR hg hL) B hB1
    (fun b n hb hn => hSzAll E Wp Wq S hg1 hg2 hU b n hb hn fun v => hthr b n v hb hn) A hA1
    (fun b s hb hs => hBLall E Wp Wq S hg1 hg2 hU b s hb hs) (max A B) (le_max_left _ _) (le_max_right _ _)

end

end Formalism.FourierDecayAlt.P.PBC

namespace Formalism.FourierDecayAlt.P

theorem sum_form_of_local_statements : Formalism.FourierDecayAlt.KB.SumFormOfLoc := PBC.sumFormOfLoc

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCSecMove
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sm_inner_conj {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r Bs.z)
    (hh' : h' ∈ UWset k r Bs.z') (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec ((Bs.π h).comp (A.comp (Bs.π' h')))) (B.hsVec ((Bs.π h).comp (C.comp (Bs.π' h')))) =
      inner ℂ (B.hsVec A) (B.hsVec C) := by
  have h1 := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left (Bs.π h) (Bs.π_unitary h hh) (C.comp (Bs.π' h')) (A.comp (Bs.π' h'))
  have h2 := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right (Bs.π' h') (Bs.π'_unitary h' hh') C A
  unfold B.hsInner at h1 h2
  rw [h1, h2]

theorem sm_slev {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h ∈ Q.Slev k r z (Fin.last r) :=
  ⟨h, hh, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, (Matrix.mul_one h).symm⟩

end

theorem section_move_holds : SecMove := by
  intro hSE hGS Wp Wq _ _ _ _ _ _ P Bs hpl hk
  obtain ⟨μ0, hC⟩ := hSE Wp Wq P Bs hpl hk
  let Bs0 : B.RealPlaceData P.k P.r Wp Wq := { Bs with μsec := μ0, sec := hC.1 }
  obtain ⟨e0, he0, hid0⟩ := hGS Wp Wq P Bs0 hpl hk hC
  have hz := Bs.z_mem
  have hz' := Bs.z'_mem
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hTT : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    intro ζ hζ
    rw [hT, hT']
    exact hζ
  set c1 : Fin P.r → ℂ := fun _ => 1 with hc1def
  have hc1 : c1 ∈ OmX P.r := fun _ => one_ne_zero

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' :=
    ⟨Bs.k_pos, hz, hz', Bs.T_pos, Bs.T'_pos, hC.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩

  have hφ : ∀ ρ : M.Ty P, (NF.QR P.k P.r Bs.z Bs.z').indicator (fun q => e0 ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' := by
    intro ρ
    refine ⟨?_, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun q : (Fin P.r → ℂ) × ℂ => e0 ρ q.2) (NF.QR P.k P.r Bs.z Bs.z') := by
        refine (he0.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_
        show P.TT < Complex.normSq q.2
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact hc.congr fun q hq => Set.indicator_of_mem hq _
    · intro q hq
      rw [Set.indicator_of_mem hq]
      have hq2 : P.TT < Complex.normSq q.2 := by
        have := hq.2
        rw [hT, hT'] at this
        exact this
      exact (he0.2 q.2 hq2).1 ρ
    · intro q hq
      exact Set.indicator_of_notMem hq _
  choose Φr hΦr hrad using fun ρ => Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' hRB _ (hφ ρ)
  obtain ⟨e, he_def⟩ : ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp),
      e = fun ρ ζ => (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) := ⟨_, rfl⟩

  have hdom : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      (c1, NF.muZ P.k P.r Bs.μsec ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdom0 : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → (c1, NF.muZ P.k P.r μ0 ζ) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    fun ζ hζ => Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hC.1 (q := (c1, ζ)) ⟨hc1, hTT ζ hζ⟩
  have hdec : ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' := by
    intro ζ hζ
    obtain ⟨h, hh, h', hh', he⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos hz hz' Bs.T_pos Bs.T'_pos hC.1
      (hdom ζ hζ).2.1 (hdom ζ hζ).2.2
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec (hTT ζ hζ)] at he
    exact ⟨h, hh, h', hh', he⟩

  have hrad0 : ∀ ρ ζ, P.TT < Complex.normSq ζ → (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r μ0 ζ) = e0 ρ ζ := by
    intro ρ ζ hζ
    have hq : (c1, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc1, hTT ζ hζ⟩
    have h1 := congrFun (hrad ρ) (c1, ζ)
    unfold NF.radR at h1
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq] at h1
    exact h1

  have htr : ∀ ρ ζ, P.TT < Complex.normSq ζ → ∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z',
      NF.muZ P.k P.r Bs.μsec ζ = h * NF.muZ P.k P.r μ0 ζ * h' →
      e ρ ζ = (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) := by
    intro ρ ζ hζ h hh h' hh' hd
    rw [he_def]
    show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ) = _
    rw [hd, ← hrad0 ρ ζ hζ]
    exact (hΦr ρ).2.2 (c1, NF.muZ P.k P.r μ0 ζ) (hdom0 ζ hζ) h hh h' hh'

  have hsmooth : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ} := by
    intro ρ
    rw [he_def]
    have hmZ : ContDiffOn ℝ ∞ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      contDiffOn_const.prodMk ((Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).mono fun ζ hζ => hTT ζ hζ)
    have hopen : IsOpen {ζ : ℂ | P.TT < Complex.normSq ζ} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    refine contDiffOn_of_locally_contDiffOn fun ζ₀ hζ₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := (hΦr ρ).2.1 _ (hdom ζ₀ hζ₀)
    refine ⟨{ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U,
      hmZ.continuousOn.isOpen_inter_preimage hopen hU, ⟨hζ₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun ζ : ℂ => F (c1, NF.muZ P.k P.r Bs.μsec ζ))
        ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩
          ({ζ : ℂ | P.TT < Complex.normSq ζ} ∩ (fun ζ : ℂ => (c1, NF.muZ P.k P.r Bs.μsec ζ)) ⁻¹' U)) :=
      hF.comp (hmZ.mono fun ζ hζ => hζ.1) fun ζ hζ => hζ.2.2
    exact hc.congr fun ζ hζ => hΦF _ hζ.2.2 (hdom ζ hζ.1).2.1

  have hrep := Bs.π_rep
  have hrep' := Bs.π'_rep
  have pmi : ∀ h ∈ UWset P.k P.r Bs.z, (Bs.π h).comp (Bs.π h⁻¹) = 1 := by
    intro h hh
    rw [← hrep.2 h hh h⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh), Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, hrep.1]
  have pim' : ∀ h' ∈ UWset P.k P.r Bs.z', (Bs.π' h'⁻¹).comp (Bs.π' h') = 1 := by
    intro h' hh'
    rw [← hrep'.2 h'⁻¹ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh') h' hh', Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', hrep'.1]

  have hframe : IsFrameB P Bs e := by
    refine ⟨hsmooth, fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
    · intro ρ p hp
      rw [he_def]
      show (Bs.π p.1).comp (((Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)).comp (Bs.π' p.2)) =
        (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (NF.muZ P.k P.r Bs.μsec ζ)
      rw [← (hΦr ρ).2.2 (c1, NF.muZ P.k P.r Bs.μsec ζ) (hdom ζ hζ) p.1 hp.1 p.2 hp.2.1]
      show (Φr ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c1 (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) = _
      rw [hp.2.2]
    · intro ρ ρ'
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      rw [htr ρ ζ hζ h hh h' hh' hd, htr ρ' ζ hζ h hh h' hh' hd, sm_inner_conj Bs hh hh']
      exact (he0.2 ζ hζ).2.1 ρ ρ'
    · intro X hX
      obtain ⟨h, hh, h', hh', hd⟩ := hdec ζ hζ
      have hhi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hhi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
      set X0 := (Bs.π h⁻¹).comp (X.comp (Bs.π' h'⁻¹)) with hX0def
      have e1 : ∀ Y : B.Mat P.k P.r, h⁻¹ * (h * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul]
      have e2 : ∀ Y : B.Mat P.k P.r, h' * (h'⁻¹ * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.one_mul]
      have hX0 : X0 ∈ NF.Fib P.k P.r Bs.z Bs.z' μ0 Bs.π Bs.π' ζ := by
        intro p hp
        have hp1 := hp.1
        have hp2 := hp.2.1
        have hp3 := hp.2.2
        have ht1 : h * p.1 * h⁻¹ ∈ UWset P.k P.r Bs.z :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hh hp1) hhi
        have ht2 : h'⁻¹ * p.2 * h' ∈ UWset P.k P.r Bs.z' :=
          Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul hhi' hp2) hh'
        have e3 : ∀ Y : B.Mat P.k P.r, p.1 * (NF.muZ P.k P.r μ0 ζ * (p.2 * Y)) = NF.muZ P.k P.r μ0 ζ * Y := by
          intro Y
          conv_rhs => rw [← hp3]
          simp only [Matrix.mul_assoc]
        have ht : (h * p.1 * h⁻¹, h'⁻¹ * p.2 * h') ∈ NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ := by
          refine ⟨ht1, ht2, ?_⟩
          show h * p.1 * h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * (h'⁻¹ * p.2 * h') = NF.muZ P.k P.r Bs.μsec ζ
          rw [hd]
          simp only [Matrix.mul_assoc, e1, e2, e3]
        have hXt := hX _ ht
        have hA : (Bs.π p.1).comp (Bs.π h⁻¹) = (Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹)) := by
          rw [← hrep.2 _ hp1 _ hhi, ← hrep.2 _ hhi _ ht1]
          congr 1
          simp only [Matrix.mul_assoc, e1]
        have hB : (Bs.π' h'⁻¹).comp (Bs.π' p.2) = (Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹) := by
          rw [← hrep'.2 _ hhi' _ hp2, ← hrep'.2 _ ht2 _ hhi']
          congr 1
          simp only [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
        calc (Bs.π p.1).comp (X0.comp (Bs.π' p.2))
            = ((Bs.π p.1).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' p.2))) := by
              simp only [hX0def, ContinuousLinearMap.comp_assoc]
          _ = ((Bs.π h⁻¹).comp (Bs.π (h * p.1 * h⁻¹))).comp
                (X.comp ((Bs.π' (h'⁻¹ * p.2 * h')).comp (Bs.π' h'⁻¹))) := by rw [hA, hB]
          _ = (Bs.π h⁻¹).comp (((Bs.π (h * p.1 * h⁻¹)).comp (X.comp (Bs.π' (h'⁻¹ * p.2 * h')))).comp
                (Bs.π' h'⁻¹)) := by simp only [ContinuousLinearMap.comp_assoc]
          _ = X0 := by rw [hXt]
      have hXX : X = (Bs.π h).comp (X0.comp (Bs.π' h')) := by
        have : (Bs.π h).comp (X0.comp (Bs.π' h')) =
            ((Bs.π h).comp (Bs.π h⁻¹)).comp (X.comp ((Bs.π' h'⁻¹).comp (Bs.π' h'))) := by
          simp only [hX0def, ContinuousLinearMap.comp_assoc]
        rw [this, pmi h hh, pim' h' hh']
        ext v
        rfl
      have hc : ∀ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) = inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) := by
        intro ρ
        rw [htr ρ ζ hζ h hh h' hh' hd]
        conv_lhs => rw [hXX]
        exact sm_inner_conj Bs hh hh' _ _
      have hsp0 := (he0.2 ζ hζ).2.2 X0 hX0
      have hrhs : ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ =
          ∑ ρ, inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec X0) • (Bs.π h).comp ((e0 ρ ζ).comp (Bs.π' h')) :=
        Finset.sum_congr rfl fun ρ _ => by rw [hc ρ, htr ρ ζ hζ h hh h' hh' hd]
      rw [hrhs]
      conv_lhs => rw [hXX, hsp0]
      ext v
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]

  have hfam0 : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ → FamR P Bs0 Dc Φ := by
    intro Dc Φ hF
    obtain ⟨hO, hD, hM, hFF⟩ := hF
    refine ⟨hO, hD, fun q => ?_, hFF⟩
    have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
    obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
    have hg : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1 :=
      ⟨(hdom q.1.2 hζ).2.1, hM q⟩
    have h1 := (hD q.1.1 q.2.1).2 _ hg h⁻¹ (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh)) h'⁻¹
      (sm_slev (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'))
    have e3 : h⁻¹ * NF.muZ P.k P.r Bs.μsec q.1.2 * h'⁻¹ = NF.muZ P.k P.r μ0 q.1.2 := by
      rw [hd]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc h⁻¹ h, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    rw [e3] at h1
    exact h1
  have hraw : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ → ∀ ρ, rawR P Bs.μsec e Φ ρ = rawR P μ0 e0 Φ ρ := by
    intro Dc Φ hF ρ
    have hF0 := hfam0 Dc Φ hF
    funext q
    have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
    obtain ⟨h, hh, h', hh', hd⟩ := hdec q.1.2 hζ
    unfold rawR
    congr 1
    rw [htr ρ q.1.2 hζ h hh h' hh' hd, hd]
    have hg : NF.muZ P.k P.r μ0 q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∩ Dc q.1.1 :=
      ⟨(hdom0 q.1.2 hζ).2.1, hF0.2.2.1 q⟩
    rw [(hF.2.2.2.2 q.1.1 q.2.1).2.2.2 _ hg h hh h' hh']
    exact sm_inner_conj Bs hh hh' _ _
  refine ⟨e, hframe, fun Dc Φ hF Y a b ρ => ?_⟩
  have hQF := Formalism.FourierDecayAlt.P.CutMP.Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hF Y a b
  rw [hraw Dc _ hQF ρ]
  have hfun : (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) = fun ρ' => MA.toSm P (rawR P μ0 e0 Φ ρ') :=
    funext fun ρ' => by rw [hraw Dc Φ hF ρ']
  rw [hfun]
  exact hid0 Dc Φ (hfam0 Dc Φ hF) Y a b ρ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
