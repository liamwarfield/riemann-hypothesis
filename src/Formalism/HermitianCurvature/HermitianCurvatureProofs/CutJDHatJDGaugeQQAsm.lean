module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQCore
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdg_gauge_of_core {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (hcore : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) :
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs), ∀ Y : ℝ,
      Gauge.trJB P Bs e (Q.CV P.k P.r (Y : ℂ) J) =
        MA.actA P (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ)) (Gauge.trJB P Bs e J) := by
  intro J hJ Y
  obtain ⟨hF, hres, hcv⟩ := Gauge.gauge_transition_chain_holds Wp Wq P Bs hpl hk J hJ
  set Φ := Q.resG P.k P.r (Fin.last P.r) J with hΦ
  have hJe : Gauge.trJB P Bs e J = fun ρ => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) := by
    funext ρ
    exact congrArg (MA.toSm P) (hres e ρ)
  have hpair : ∀ a b : Fin 2,
      (∀ ρ, Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ ∈ MA.smSub P.r P.TT) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ) =
        MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
          Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) ρ := by
    intro a b
    obtain ⟨hF1, hV1⟩ := Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he _ Φ hF Y b
    have hF2 := Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk _ _ hF1 Y a b
    obtain ⟨hF3, hV2⟩ := Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he _ _ hF2 Y a
    refine ⟨fun ρ => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he _ _ hF3 ρ, fun ρ => ?_⟩
    have hin : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ')) =
        MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) := by
      funext ρ'
      rw [hV1 ρ', hJe]
    have hmid : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J)) := by
      funext ρ'
      rw [hcore _ _ hF1 Y a b ρ', hin]
    rw [hV2 ρ, Gauge.actA_mul, Gauge.actA_mul, hmid]
  funext ρ
  show MA.toSm P (Gauge.rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ) = _
  rw [hcv e ρ Y]
  rw [show Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ) =
      ∑ a, ∑ b, star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
        Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b from rfl]
  simp only [Gauge.actA_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ((hpair a b).2 ρ).symm]
  rw [Gauge.toSm_of_mem P (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => (hpair a b).1 ρ)]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Gauge.toSm_of_mem P ((hpair a b).1 ρ)]

theorem jdg_exists_of_gCore (hK : Gauge.GCore) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (hB : BuiltOW Cc S T f χ ν' m₀ top A₀) (v : Fin S.f) :
    ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e := by
  obtain ⟨hBP, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIB, -, -, -, -, -, -, hk2, -, -⟩ := hBP
  obtain ⟨-, -, -, hpl, -, -⟩ := hIB.2 v
  obtain ⟨e, he, hc⟩ := hK (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hpl hk2
  exact ⟨e, he, jdg_gauge_of_core (D.parOf S v) (T v).base hpl hk2 e he hc, hc⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLam
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by
  have hD := hok.hDel
  have hi' : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_v_lt (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_b_lt (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith

theorem cfg_b_ge_one (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1

theorem cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by
  have hk4 := hok.hk
  have hD := hok.hDel
  have hv0 := hok.hv0
  have hb1 := hok.hb1
  have ha := hok.ha
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s := fun s hs => by
    rw [Sz.Cfg.lam, if_pos hs]
  have hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k) := fun s hs => by
    rw [Sz.Cfg.lam, if_neg hs]
  have hu1 : c.u de 1 = c.a := by rw [Sz.Cfg.u, if_pos rfl]
  have huk : c.u de c.k = c.ulast := by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]
  have hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del :=
    fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]
  have hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del := fun j => by
    rcases hde j with h | h <;> simp [h] <;> linarith
  have hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2 := rfl
  have hvk : c.v (c.k - 1) = c.vlast := by
    simp only [Sz.Cfg.v]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro s t hst
    have hst' : (s : ℕ) < t := hst
    have ht := t.isLt
    show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)
    by_cases h1 : (t : ℕ) + 1 < c.k
    · rw [hlamv _ h1, hlamv _ (by omega)]
      exact cfg_v_lt c hok (by omega)
    · rw [hlamb _ h1]
      by_cases h2 : (s : ℕ) + 1 < c.k
      · rw [hlamv _ h2]
        have := cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)
        have := cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)
        linarith
      · rw [hlamb _ h2]
        have := cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k)
          (by omega) (by omega) (by omega)
        linarith
  · show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, zero_add, hlamv 1 (by omega), hu1]
      have : 0 < 4 * (c.k : ℝ) * c.Del := by
        have := mul_le_mul hkR hD zero_le_one (by linarith)
        linarith
      linarith
    · by_cases h2 : (i : ℕ) + 1 < c.k
      · rw [hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]
        have := cfg_v_sub c (i : ℕ)
        have := hde0 (i : ℕ)
        linarith
      · have e : (i : ℕ) + 1 = c.k := by omega
        rw [hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]
        split_ifs with htp
        · have := (hok.htop htp).2
          linarith
        · linarith
  · show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)
    rw [hlamv _ (by omega)]
    by_cases h2 : (i : ℕ) + 2 = c.k
    · have e : (i : ℕ) + 1 = c.k - 1 := by omega
      rw [h2, huk, hul, e, hvk]
      split_ifs with htp
      · have := (hok.htop htp).1
        linarith
      · linarith
    · have e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1 := by omega
      rw [hum _ (by omega) h2, e]
      have := hde0 ((i : ℕ) + 1)
      linarith

end cfg

theorem eigenvalue_configuration_interlaces : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAdm
namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt

theorem admissible_in_truncation_holds : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this

end Formalism.FourierDecayAlt.P.CutMP
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GaugeExistsQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

def JDecayTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

def JAdjTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JAdj (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem gaugeExistsQQ_of_gCore (hK : Gauge.GCore) : GaugeExistsQQ := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  exact jdg_exists_of_gCore hK 0 E Wp Wq S T f χ ν' m₀ top A₀ hB v

theorem modelPlaceBuilt3_of_leavesQQ (hMF : MA.ModelFrameAn) (h1 : LamCfgInterlaces) (h2 : AdmInCut)
    (h3 : GaugeExistsQQ) (h4 : RegFF3) (h5 : CVPresFF) (h6 : BesselEigen) (h7 : EnergyTr) (h8 : CutTr)
    (h9 : EnergyReal) (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : ModelPlaceBuilt3 := by
  obtain ⟨K3, g3⟩ := h3
  obtain ⟨K4, g4⟩ := h4
  obtain ⟨K5, g5⟩ := h5
  obtain ⟨K6, g6⟩ := h6
  obtain ⟨K7, g7⟩ := h7
  obtain ⟨K8, g8⟩ := h8
  obtain ⟨K9, g9⟩ := h9
  obtain ⟨K10, g10⟩ := h10
  obtain ⟨LastRowCutoff, g11⟩ := h11
  refine ⟨max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ hOk hW hW' c hc v
  have hOW : ∀ C', C' ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) →
      BuiltOW C' S T f χ ν' m₀ top A₀ := fun C' h => ⟨isBuiltPlace_mono h hB, hOk, hW, hW'⟩
  obtain ⟨_, _, _, hIB, hl1, hlk, hGr, hLC, _, _, hk2, _, hOn⟩ := hB
  obtain ⟨e, hF, hG, hQQ⟩ := g3 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K3 (by simp)) v
  have hR := g4 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K4 (by simp)) hJ v
  have hP := g5 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K5 (by simp)) v
  have hE := g6 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K6 (by simp)) v
  have hPOK : (D.parOf S v).OK := (hIB.2 v).2.2.2.1.1
  obtain ⟨L, hL, -⟩ := hMF (D.parOf S v) hPOK (S.l + 1) (by omega) (show S.l + 1 ≤ S.G.k by omega)
  have hI := h1 E Wp Wq S hk2 hOk hW hW' v
  have hlt : S.cutLo v < S.cutHi v := by
    have hv := hLC v
    have hN : (0 : ℝ) < S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; positivity
    have hX : 0 < (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    have h1le : (1 : ℝ) ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) :=
      le_max_left _ _
    nlinarith
  refine ⟨L, trJ S T v e (B.JF (T v).base (f v)), lamCfg S v, 1, 1, hc, one_pos, one_pos,
    ⟨hPOK, by omega, show S.l + 1 ≤ S.G.k by omega, hL, hI.1, hI.2, hlt, hOn v⟩,
    g10 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K10 (by simp)) v e L hF hG hQQ hL hR.1,
    g11 E Wp Wq S T f χ ν' m₀ top A₀ (hOW LastRowCutoff (by simp)) v e L hF hG hQQ hL hR.1, ?_, ?_, ?_⟩
  ·
    intro Y
    rw [← hG _ hR.1 Y, trJ_congr S T v e _ (((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v)) (hE Y), trJ_smul]
    funext π
    rw [Pi.smul_apply, ← prod_lamCfg S v Y]
    push_cast
    rfl
  ·
    intro ε hε a ha
    have key : C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
        MA.ipA (D.parOf S v)
          (MA.actA (D.parOf S v) ((a.reverse.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v))
            (S.l + 1)).QQ (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod)
            (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε))
          (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε) := by
      rw [g7 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K7 (by simp)) v e hF hP ε hε (hR.2 ε hε) a ha,
        (trJ_foldr S T v e hG hP a.reverse _ (hR.2 ε hε)).2,
        g8 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K8 (by simp)) v e hF hR.1 c hc ε hε]
    have hre := g9 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K9 (by simp)) v ε hε a ha
    rw [key] at hre
    rw [key]
    clear g3 g4 g5 g6 g7 g8 g9 g10 g11 hOW key hE hP hR hG hF hI hQQ
    unfold MA.cutoffEnergyForm
    simp only [one_mul]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact hre
  ·
    intro Lb a ha
    exact level_system_admissible_size S v a ha (h2 E Wp Wq S hGr v a ha) (S.l + 1) L _ c Lb

theorem modelPlaceBuilt3_of_openQQ (h3 : GaugeExistsQQ) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_leavesQQ Formalism.FourierDecayAlt.Final.ma_modelFrameAn eigenvalue_configuration_interlaces admissible_in_truncation_holds h3
    regularity_smooth_forms_holds coefficient_vector_preserves_form bessel_eigenvalue_equation_holds h7 cutoff_transport_to_model h9 h10 h11

theorem modelPlaceBuilt3_of_openGC (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_openQQ (gaugeExistsQQ_of_gCore hK) h7 h9 h10 h11

theorem modelPlaceBuilt2_of_openQQ (hJ : JfSmoothDS) (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal)
    (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3 hJ (modelPlaceBuilt3_of_openGC hK h7 h9 h10 h11)

end

end Formalism.FourierDecayAlt.P.CutMP
