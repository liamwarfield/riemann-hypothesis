module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicitParametersStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CloudRec

def ScaleOK (K : Ctx) : Prop :=
  ∀ R : Ranks, RankVal K.s R →
    16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) + R.k + 2 ≤ K.s.w'' R.n ∧ K.s.w'' R.n ≤ K.s.b

theorem scaleOK_large (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (cD : ℝ) (hcD : 0 ≤ cD) :
    ∃ x1 : ℝ, ∀ K : Ctx, K.s.eps = eps → K.cD = cD → x1 ≤ K.s.x → ScaleOK K := by
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) (1 / 2) he (by norm_num)
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨max 35 (max x2 x3), fun K e1 e2 hx R hR => ?_⟩
  have h35 : 35 ≤ K.s.x := le_trans (le_max_left _ _) hx
  have hxa : x2 ≤ K.s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x3 ≤ K.s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, -, hr, hkr, -⟩ := hx3 K.s R e1 hxb hR
  have hx0 : 0 < K.s.x := by linarith
  have hx1 : 1 ≤ K.s.x := by linarith
  have hn1 : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hn3 : (R.n : ℝ) ≤ K.s.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast
    have : (0:ℝ) ≤ R.n := Nat.cast_nonneg _
    linarith
  have H := hx2 K.s e1 hxa
  obtain ⟨-, -, -, hb'b, -, hw, -⟩ := H
  obtain ⟨hw1, hw2, -⟩ := hw R.n hn1 hn3
  have hL0 : 0 ≤ K.s.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ K.s.b := by unfold Scale.b; exact Real.one_le_exp hL0
  have hbk : 1 ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) := Real.one_le_rpow hb1 (by norm_num)
  have hxc0 : 0 ≤ K.s.x ^ (cD + 6) := by positivity
  have hxc : K.s.x ^ (cD + 6) ≤ K.s.w'' R.n := by
    calc K.s.x ^ (cD + 6) = 1 * K.s.x ^ (cD + 6) := by ring
      _ ≤ K.s.b ^ (1 - (1 / 2 : ℝ)) * K.s.x ^ (cD + 6) := by gcongr
      _ ≤ _ := hw1
  have hxc1 : 1 ≤ K.s.x ^ (cD + 0) := by rw [add_zero]; exact Real.one_le_rpow hx1 hcD
  have hD : (Delv K.s K.cD : ℝ) ≤ 2 * K.s.x ^ cD := by
    unfold Delv
    rw [e2]
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le cD)
    rw [add_zero] at hxc1
    linarith
  have hk5 : (R.k : ℝ) ≤ K.s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hsplit : K.s.x ^ (cD + 6) = K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; ring_nf
  have hxcD : 1 ≤ K.s.x ^ cD := by rw [add_zero] at hxc1; exact hxc1
  have hx5 : 1 ≤ K.s.x ^ (5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hk0 : (0 : ℝ) ≤ R.k := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, le_trans hw2 ?_⟩
  · have h1 : 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 32 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) := by
      calc 16 * (R.k : ℝ) * (Delv K.s K.cD : ℝ) ≤ 16 * K.s.x ^ (5 : ℝ) * (2 * K.s.x ^ cD) := by gcongr
        _ = _ := by ring
    have h2 : 1 ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := one_le_mul_of_one_le_of_one_le hxcD hx5
    have h3 : (R.k : ℝ) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) := le_trans hk5 (le_mul_of_one_le_left (by linarith) hxcD)
    have h4 : 35 * (K.s.x ^ cD * K.s.x ^ (5 : ℝ)) ≤ K.s.x ^ cD * K.s.x ^ (5 : ℝ) * K.s.x := by
      rw [mul_comm 35]; gcongr
    linarith
  · have := hb'b
    have h0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
    have hx6 : 1 ≤ K.s.x ^ (cD + 6) := Real.one_le_rpow hx1 (by linarith)
    nlinarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem facts_pre {K : Ctx} (hS : ScaleOK K) {Bp : Pre} (hO : K.Over Bp) :
    (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) ∧
    (∀ u (τ : Tau Bp.R) (i : Fin Bp.R.k), 1 ≤ i.1 → i.1 + 1 < Bp.R.k →
      3 * (Delv K.s K.cD : ℝ) - 1 / 2 ≤ (((Bp.hcW u τ).u i : ℚ) : ℝ) ∧
      (((Bp.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ)) ∧
    (∀ u (τ : Tau Bp.R) (hk : 0 < Bp.R.k), (τ : Bp.R.GG) ∉ Bp.host.topPlaces →
      (((Bp.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) =
        ((Bp.R.k - 2 : ℕ) : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + (Bp.R.k : ℝ) * (4 * (Delv K.s K.cD : ℝ)) + 1 / 2 ∧
      (((Bp.hcW u τ).u ⟨Bp.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2) ∧
    (∀ u (τ : Tau Bp.R) (hm : 0 < Bp.R.m),
      16 * (Bp.R.k : ℝ) * (Delv K.s K.cD : ℝ) + ((Bp.R.k : ℝ) + Bp.R.t + 1) / 2 + 1 ≤ (((Bp.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ)) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := hO
  dsimp only [Pre.ofCh]
  have ok := K.ok
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have hx0 : 0 < K.s.x := by linarith
  have hD1 : (1 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by
    unfold Delv
    have h : 0 < K.s.x ^ K.cD := Real.rpow_pos_of_pos hx0 _
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
  obtain ⟨hS1, hS2⟩ := hS K.P.R ok.rank
  refine ⟨hD1, ?_, ?_, ?_⟩
  · intro u τ i hi1 hi2
    have hv := (ok.hc u).1
    have hcode := ok.code u τ (i.1 - 1) (by omega)
    have e : (⟨i.1 - 1 + 1, by omega⟩ : Fin K.P.R.k) = i := Fin.ext (by simp only; omega)
    rw [e, hv τ ⟨i.1 - 1, by omega⟩] at hcode
    have hcR := congrArg (Rat.cast (K := ℝ)) hcode
    rw [hcR]
    have hl1 : 1 ≤ K.P.R.k - 2 - (i.1 - 1) := by omega
    have hl2 : K.P.R.k - 2 - (i.1 - 1) ≤ K.P.R.k := by omega
    have c1 : (1 : ℝ) ≤ ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) := by exact_mod_cast hl1
    have c2 : ((K.P.R.k - 2 - (i.1 - 1) : ℕ) : ℝ) ≤ K.P.R.k := by exact_mod_cast hl2
    have hD0 : (0 : ℝ) ≤ (Delv K.s K.cD : ℝ) := by linarith
    split_ifs <;> push_cast <;> constructor <;> nlinarith
  · intro u τ hk htop
    have h := (ok.hc u).2.1 τ hk htop
    constructor
    · have := congrArg (Rat.cast (K := ℝ)) h.1
      rw [this]; push_cast; ring
    · have := congrArg (Rat.cast (K := ℝ)) h.2
      rw [this]; push_cast; ring
  · intro u τ hm
    obtain ⟨b1, hb, htopb, hthick, hthin⟩ := (ok.hc u).2.2.1
    have hgap := (K.P.hcW u τ).gap_be ⟨0, hm⟩
    have hb0 := (hb τ ⟨0, hm⟩).1
    simp only [Nat.cast_zero, zero_mul, add_zero] at hb0
    rw [hb0] at hgap
    have hgapR : ((K.P.R.t : ℝ) + 3) / 2 ≤ (((K.P.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ) - (b1 τ : ℝ) := by
      have h' := (Rat.cast_le (K := ℝ)).2 hgap
      push_cast at h'
      linarith
    have hwb : K.s.w'' K.P.R.n ≤ (b1 τ : ℝ) + 1 := by
      by_cases ht : (τ : K.P.R.GG) ∈ K.P.H.topPlaces
      · obtain ⟨t, htT, hte⟩ := Finset.mem_image.1 ht
        have e1 := htopb τ ⟨t, htT⟩ hte.symm
        have hwin := (ok.win t htT).2.1
        rw [e1]
        push_cast
        have hfl := Int.sub_one_lt_floor (K.s.b' / K.s.x)
        have hb'0 : 0 ≤ K.s.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
        have hn1 : (1 : ℝ) ≤ K.P.R.n := by exact_mod_cast (Formalism.HC.Frame.ord_pos _ : 1 ≤ K.P.R.n)
        have hw'' : K.s.w'' K.P.R.n ≤ K.s.b' / K.s.x := by
          unfold Scale.w''
          rw [div_le_div_iff₀ (by positivity) hx0]
          have : K.s.b' * K.s.x ≤ K.s.b' * (K.s.x * K.P.R.n) := by
            apply mul_le_mul_of_nonneg_left _ hb'0; nlinarith
          linarith
        have hbt : K.s.b' ≤ ((K.b t : ℤ) : ℝ) := hwin
        nlinarith
      · by_cases hth : (τ : K.P.R.GG) ∈ K.P.H.thickPlaces
        · have h1 := (hthick τ hth).1
          have hc : K.s.b ≤ (⌈K.s.b⌉ : ℝ) := Int.le_ceil _
          have h2 : ((⌈K.s.b⌉ : ℤ) : ℝ) ≤ ((b1 τ : ℤ) : ℝ) := by exact_mod_cast h1
          linarith
        · have := hthin τ ⟨τ.2, ht, hth⟩
          rw [this]
          have := Int.le_ceil (K.s.w'' K.P.R.n)
          linarith
    have hk0 : (0 : ℝ) ≤ K.P.R.k := Nat.cast_nonneg _
    linarith

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem cloudBound_of (D : D7) (Δ : ℕ) (hD1 : 1 ≤ Δ)
    (hmid : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      3 * (Δ : ℝ) - 1 / 2 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * Δ)
    (hoff : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hk : 0 < D.R.k),
      ((D.eTau τ : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
      (((D.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) = ((D.R.k - 2 : ℕ) : ℝ) * (4 * (Δ : ℝ)) + (D.R.k : ℝ) * (4 * (Δ : ℝ)) + 1 / 2 ∧
      (((D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -1 / 2)
    (hfill : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau) (hm : 0 < D.R.m),
      16 * (D.R.k : ℝ) * Δ + ((D.R.k : ℝ) + D.R.t + 1) / 2 + 1 ≤ (((D.hcW u τ).e ⟨0, hm⟩ : ℚ) : ℝ))
    (u : D.what₂.Word) : Formalism.L2.G.CloudBound D u (16 * D.R.k * Δ) := by
  have hD1R : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hD1
  have hk5 : 5 ≤ D.R.k := by have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k; omega
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hc : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) = 16 * (D.R.k : ℝ) * (Δ : ℝ) := by push_cast; ring
  have hmidL : ∀ (g : D.R.Psi) (i : Fin (D.R.k - 1 + 1)), 0 < i.val → i.val < D.R.k - 1 →
      |Formalism.L2.G.lamRec D u g i| ≤ ((16 * D.R.k * Δ : ℕ) : ℤ) := by
    intro g i h0 h1
    have hi : i.1 < D.R.k := by omega
    have h := Formalism.L2.G.lamRec_real D u g i hi
    have hb := hmid u (D.eTau.symm g) ⟨i.1, hi⟩ h0 (by show i.1 + 1 < D.R.k; omega)
    have hiR : (i.1 : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
      rw [h, hc, abs_le]
      constructor <;> nlinarith [hb.1, hb.2]
    exact_mod_cast h2
  refine ⟨fun g _ i h0 h1 => hmidL g i h0 h1, fun g hg i => ?_, fun g => ?_⟩
  · have hg' : ((D.eTau (D.eTau.symm g) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces := by
      rwa [Equiv.apply_symm_apply]
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨e0, e1⟩ := hoff u (D.eTau.symm g) hk0 hg'
    by_cases h0 : i.val = 0
    · have hi : i.1 < D.R.k := by omega
      have h := Formalism.L2.G.lamRec_real D u g i hi
      have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨0, hk0⟩ := Fin.ext h0
      rw [e, e0, h0] at h
      have hk2 : ((D.R.k - 2 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast Nat.sub_le _ _
      have hk2' : (0 : ℝ) ≤ ((D.R.k - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
        rw [h, hc, abs_le]
        push_cast
        constructor <;> nlinarith
      exact_mod_cast h2
    · by_cases h1 : i.val < D.R.k - 1
      · exact hmidL g i (Nat.pos_of_ne_zero h0) h1
      · have hi1 : i.val = D.R.k - 1 := by have := i.2; omega
        have hi : i.1 < D.R.k := by omega
        have h := Formalism.L2.G.lamRec_real D u g i hi
        have e : (⟨i.1, hi⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hi1
        have hkR1 : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [e, e1, hi1, hkR1] at h
        have h2 : |((Formalism.L2.G.lamRec D u g i : ℤ) : ℝ)| ≤ (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) := by
          rw [h, hc, abs_le]
          constructor <;> nlinarith
        exact_mod_cast h2
  · have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
    have h1 : (1 : ℕ) ∈ SizeData₂.lifts D := Finset.mem_Icc.2 ⟨le_rfl, by have := D.R.two_le_m; omega⟩
    have hw := Formalism.L2.G.wRec_eq D u g 1 h1
    have hf := hfill u (D.eTau.symm g) hm
    have hfe : (((D.hcW u (D.eTau.symm g)).e ⟨0, hm⟩ : ℚ) : ℝ) = Formalism.BasicNotions.wj D 1 (D.eTau.symm g) := by
      unfold Formalism.BasicNotions.wj
      rw [dite_eq_left (by omega), D.hcW_e]
    rw [hfe] at hf
    have hka : Formalism.MainNotions.G.kaJ D 1 = ((D.R.k : ℝ) + D.R.t + 1) / 2 := by
      unfold Formalism.MainNotions.G.kaJ; push_cast; ring
    have h2 : (((16 * D.R.k * Δ : ℕ) : ℤ) : ℝ) ≤ ((Formalism.L2.G.wRec D u g 1 : ℤ) : ℝ) := by
      rw [hw, hka, hc]; linarith
    exact_mod_cast h2

theorem cloudBound_rec {K : Ctx} (hS : ScaleOK K) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (Z : w.Lt) (u : (w.D Z).what₂.Word) :
    Formalism.L2.G.CloudBound (w.D Z) u (16 * (w.D Z).R.k * Delv K.s K.cD) := by
  obtain ⟨hD1, hmid, hoff, hfill⟩ := facts_pre hS hO
  exact cloudBound_of (w.D Z) (Delv K.s K.cD) (by exact_mod_cast hD1) (fun u τ i h1 h2 => hmid u τ i h1 h2)
    (fun u τ hk h => hoff u τ hk h) (fun u τ hm => hfill u τ hm) u

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl.CloudRec

theorem evG_scaleOK : EvG ScaleOK := by
  obtain ⟨ε0, hε0, H⟩ := evG_good
  refine ⟨ε0, hε0, fun eps C8 C5 c6 Cb he h1 h2 h3 => ?_⟩
  obtain ⟨K0, HK⟩ := H eps C8 C5 c6 Cb he h1 h2 h3
  refine ⟨K0, fun C hC h4 h5 => ?_⟩
  obtain ⟨c1, H1⟩ := HK C hC h4 h5
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, H2⟩ := H1 cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, -⟩ := H2 ch hch
  obtain ⟨x1, hx1⟩ := scaleOK_large eps he h2 cD (le_trans (le_max_right _ _) hcD)
  exact ⟨max x0 x1, fun K _ e2 _ e4 e5 _ => hx1 K e4 e2 (le_trans (le_max_right _ _) e5)⟩

end GlobalTheory.Mem.Top.Bl.CloudRec

namespace GlobalTheory.Mem.Top.Bl

theorem cloudBound_step : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
    ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L :=
  Step.of_evG (CloudRec.evG_scaleOK.imp fun K _ _ _ _ hS B _ _ hO _ _ _ w _ Z =>
    ⟨16 * (w.D Z).R.k * Delv K.s K.cD, CloudRec.cloudBound_rec hS w hO Z, fun L hL hV => by
      unfold G.cG
      rw [L.Sc_eq, hV.Del_eq, hL]
      push_cast
      linarith⟩)

end GlobalTheory.Mem.Top.Bl
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnChoice_cloudBound_le_cG : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := by
  first | exact @GlobalTheory.Mem.Top.Bl.cloudBound_step | exact GlobalTheory.Mem.Top.Bl.cloudBound_step | (intros; apply GlobalTheory.Mem.Top.Bl.cloudBound_step <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumns
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem gyLay_kerT_entC : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  have hcl : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := GlobalTheory.T.columnChoice_cloudBound_le_cG
  refine (StepW.and hcl (StepW.of_all (q := fun K B f T w => (∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧
      ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L) → _) ?_)).trans
    (StepW.of_all fun _ _ _ _ _ _ _ h => h.2 h.1)
  intro K B f T w hO hF hP hC Z t Wt nch n Y hMu hQp
  obtain ⟨cp⟩ := hP
  obtain ⟨O, hstd, hunf⟩ := TC.lift_objects w.I w.ok w.pins w.l Z Y.Qp
  let Pl : Examples₂.EntPl (w.D Z) := Classical.choice (Formalism.BasicNotions.Examples₂.entPl_nonempty _)
  obtain ⟨Bs, hB, hok⟩ := GlobalTheory.T.trueColumnChoices_kernelDatum_adaptedBases w.I w.ok w.pins w.l Z w.l0 Y O Pl hQp hstd hunf cp.jets
  obtain ⟨vOf, Fl, htm, hw, hled⟩ := GlobalTheory.T.latticeLayer_trueColumns_intrinsic w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp (hC Z)
  choose Lv KD hK using GlobalTheory.T.levels_kernelData_at_served_place w hO hF ⟨cp⟩ Z t Wt nch n Y hMu hQp O hstd hunf _ hok Fl htm hw
  let Y0 : G.LatInst (w.D Z) := ⟨vOf, Fl, Lv, fun _ _ _ => ⟨fun _ => 0⟩, fun _ _ _ => ⊥⟩
  exact ⟨Formalism.L2.G.Cmp.withFirst t.cmp (w.tw Z) Y0 fun u v hg =>
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (KD u v hg).up.maps,
    Formalism.L2.G.Cmp.kerAll t.Gt t.cmp (w.tw Z) Y0 KD, ⟨Formalism.L2.G.Cmp.withFirst_vram _ _ _ _, hw,
      fun L a b c X d e g h => hled Lv _ _ L a b c X d e g h⟩, ⟨O, hstd, hunf, _, hok, fun u v hg => (hK u v hg).1,
      fun u v hg => (hK u v hg).2.1, fun u v hg => (hK u v hg).2.2.1, fun u v hg => (hK u v hg).2.2.2⟩, Pl, Bs, hB, rfl⟩

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeLayerKernelDatumTrueColumnsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)), V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp → ∃ (Gy : G.LatInst (w.D Z)) (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy), GyLay K (w.D Z) t.Gt t.cmp Gy ∧ ∃ kt : KerT t.toColT Y Gy ker, ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs Y (w.tw Z)), kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h := by
  first | exact @GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | exact GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC | (intros; apply GlobalTheory.Mem.Top.Bl.gyLay_kerT_entC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersForcedContentEqScaleAtResidueCharStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forcedContent_eq_scale_at_residueChar : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl), Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  first | exact @GlobalTheory.Mem.Top.Bl.Fval_eq_FK | exact GlobalTheory.Mem.Top.Bl.Fval_eq_FK | (intros; apply GlobalTheory.Mem.Top.Bl.Fval_eq_FK <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStages
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.CoreAsm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {𝒮 : Slots} {w : ColW B f T} {Z : w.Lt}

theorem fval_off (l : Lv4 𝒮 K w Z) (L : SizeData₂ (w.D Z)) (hL : L.sc = K.s) (v : B.places.Pl) (hv : v ∉ l.Wt)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts (w.D Z)) : Fval L j v = 0 := by
  refine (GlobalTheory.T.forcedContent_eq_scale_at_residueChar (w.D Z) L j v).trans ?_
  rw [hL]
  rw [l.what₂.exact] at hv
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hv' := fun (i : Fin (w.D Z).R.m) h => hv ⟨i, (w.D Z).plEq v, Or.inl rfl, Or.inr (Or.inr h)⟩
  have key : F0K K.s (w.D Z) ((w.D Z).plEq v) ⟨j - 1, by omega⟩ = 0 := by
    by_contra h
    exact hv' _ h
  unfold F0K at key
  simp only [Equiv.symm_apply_apply] at key
  have e : j - 1 + 1 = j := by omega
  rw [e] at key
  exact key

theorem not_mem_of_untw (l : Lv4 𝒮 K w Z) (v : B.places.Pl) (hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0) : v ∉ l.Wt := by
  intro hvW
  have h1 := l.what₂.mu.on v hvW
  have h2 := l.what₂.mu.tw v
  have h3 := l.what₂.mu.mu0
  have hne := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).2.1 v
  apply hne
  rw [← h2, ← h1]
  change w.I.xi ((w.D Z).what₂.muAt v) = 1
  rw [hv]
  exact h3

theorem rowLay_of (l : Lv4 𝒮 K w Z) (Y : DivX (w.D Z)) (hMj : MjAre l.what₂.r.Z Y)
    (hk : ∀ σ, Y.kapR σ = kapSharp (w.D Z)) : V4.RowLay (w.D Z) l.p0 Y :=
  { rrDef := (Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_RRDef _).1 l.what₂.r.Z.rr
    rationalRoots_def := l.what₂.r.Z.rr0
    kap_def := l.what₂.r.Y.kap
    lam_def := l.what₂.r.Y.lam
    bu_def := l.what₂.r.Y.bu
    ft_occ := l.what₂.r.Y.occ
    untw := fun v hv j h1 h2 => l.what₂.untw v (not_mem_of_untw l v hv) j h1 h2
    idx := l.what₂.idx Y hMj
    kapR_def := hk _ }

theorem stepW_core (_h2b : StandardLattice.SiegelMassRatioCM) : ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
    StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  intro 𝒮 hA hD hT
  have hp : StepW (pinAnd (Has4 𝒮)) Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h.1
  have hAll := hp.trans (((hA.and hD).and hT).and GlobalTheory.T.exists_latticeLayer_kernelDatum_trueColumns)
  refine (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ h => h) hAll).trans (StepW.of_all ?_)
  rintro K B f T w hO hF ⟨⟨⟨pin⟩, Z, ⟨l⟩⟩, ⟨⟨hAm, hDv⟩, hTh⟩, hGy⟩
  obtain ⟨a, a0, ha⟩ := hAm Z l
  obtain ⟨Y, ⟨dv⟩, hMj, hk, hox⟩ := hDv Z l
  obtain ⟨th, ⟨tt⟩⟩ := hTh Z l
  obtain ⟨Gy, ker, hgy, kt, Pl, Bs, hh, he⟩ := hGy Z l.col l.Wt l.nch l.n Y l.what₂.mu dv.Qp
  obtain ⟨G, hG⟩ := GlobalTheory.GaugeEx.exists_isGauge (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm
  let O : Obj2 (w.D Z) :=
    { gatT := l.col.Gt, th := th, cmp := l.col.cmp, tw := w.tw Z, Gy := Gy, errX := Formalism.L2.Herm.toErrXS l.col.full.1,
      nch := l.nch, xd := l.xd, lev := l.col.full.1.base.lev0, X := Y, p0 := l.p0, ker := ker, amb := a, amb0 := a0,
      gauge := G }
  obtain ⟨ox⟩ := hox O l.what₂ rfl rfl HEq.rfl
  let c : V4.Core K (w.st Z) f T :=
    { isOver := hO
      xi := w.I.xi
      Wt := l.Wt
      mu := l.what₂.mu
      forced := hF
      fval := fun L hL _ _ v hv j hj => fval_off l L hL v hv j hj
      O := O
      col := GlobalTheory.T.columnLayerConditions_trueColumns_laterStages B f T w Z l.col.toColT
      gatNum := (l.g Z.W Z.V Z.S Z.N).2.1
      gy := hgy
      row := rowLay_of l Y hMj hk
      mtStable := l.what₂.r.Y.stable
      th_io := tt.io
      gauge_def := hG
      real := l.real
      dsig_eq := l.dsig_eq
      del := l.del
      etaF := l.what₂.etaF
      chiT := l.chiT
      nch_tie := l.n.tie
      nch_Q := l.n.Q }
  let bt : Built 𝒮 K w Z c :=
    { pin := pin
      coh := l.coh
      g := l.g
      col := l.col
      what₂ := l.what₂
      rx := l.rx
      xi := rfl
      lev := rfl
      errX := rfl
      n := l.n
      nx := l.nx
      sx := l.sx
      ker0 := ker
      ker_eq := rfl
      ker := kt
      div := dv
      th := tt
      obj := ⟨ha, hMj, hk⟩
      ox := ox }
  exact ⟨Z, c, bt, Pl, Bs, hh, he⟩

end GlobalTheory.Mem.Top.Bl.CoreAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constructedCore_of_all_construction_stages : StandardLattice.SiegelMassRatioCM → ∀ 𝒮 : Slots, AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 → StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | exact GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core | (intros; apply GlobalTheory.Mem.Top.Bl.CoreAsm.stepW_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPinned
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.PinW

theorem valsRoots (K : Ctx) : large₂ K fun B f T => ∀ (px : PreX B.toPre) (I : ColIn B px), I.Ok →
    I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} → Set.range I.xi = T.set f →
    (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => GlobalTheory.Mem.Col2.InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ z hz => hZ B Ξ z hz, fun B f T _ hH _ _ => ?_⟩
  intro px I h hS hxi
  refine ⟨fun a P _ => ⟨_, (h.xi_reads a _).symm⟩, fun a P hP => ?_⟩
  have hm : I.xi a ∈ T.set f := hxi ▸ Set.mem_range_self a
  have ht := GlobalTheory.Mem.Col2.InEx.isTwist_of_mem_set B f T _ hm
  have hf := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
  have hold := gZ B.toPre _ hf B.LL B.embLL (fun z hz => B.mem_LLC.1 (hH.2 z hz)) _ hm ht.1
  have ht' : Chr.IsTwist B.host I.S (I.xi a) := by rw [hS]; exact ht
  obtain ⟨P', a1, a2⟩ := GlobalTheory.Mem.Col2.InEx.exists_ram_of_mem_QE B h.sel_ok (I.tup a) ht' (h.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := (hold.2 P' a1).2
  refine ⟨ζ, ?_⟩
  rw [pow_one] at hζ
  have e : Nat.card (𝓞 B.fields.E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, a2]
  exact hζ

theorem step_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) (fun K B f T => ∃ w : ColW B f T, Pinned K B f T w) := by
  have e1 := evG_of_ev (ev_preX_frame h2b)
  have e2 := evG_of_ev GlobalTheory.Mem.Col2.TwIdxEx.evLg_canonical
  have e3 := evG_all fun K => (valsRoots K).inter (GlobalTheory.Mem.Col2.InEx.lg_colIn K)
  refine ((e1.inter e2).inter e3).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hfr, h41⟩, hv⟩ := H
  refine (h41.inter hv).imp fun B f T hO G hk _ _ => ?_
  obtain ⟨H, V, Lc⟩ := G
  obtain ⟨⟨δ, hδ⟩, hp⟩ := hk
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := GlobalTheory.T.exists_half_selection_split_places_base B
  obtain ⟨X, I, hok, hpins, htw, hjets, hsel', hC, hS, hxi, hval⟩ := H hp (hfr _ hO).1 Pv hsel
  obtain ⟨hv1, hv2⟩ := V X I hok hS hxi
  subst hsel'
  exact ⟨⟨X, I, hok, hC, hS, hxi, hpins, GlobalTheory.Mem.Col2.TC.laws_of_ok I hok, StepZero.law0 I hok _, δ, hδ, Lc.2.2,
      fun C W V S N G => (hval C W V S N G).1⟩,
    ⟨⟨htw, hjets, GlobalTheory.Mem.FieldsLaws.fields_ok B, habove, hhalf, d, ⟨hd1, hd2⟩, hv1, hv2⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.PinW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PassStepCongr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem pass_step_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem pass_step : ∀ (KP : BaseP) (Q : V4.Slot) (r r' : AtP), BaseCond KP → Pass KP Q r → Step KP r r' → Pass KP Q r' := by
  classical
  intro KP Q r r' hK hR hS
  refine (EvG.inter hS hR).imp fun K _ _ _ _ H => ?_
  obtain ⟨hs, hr⟩ := H
  have hs' : large₂ K fun B f T => KP B f → r K B f T → r' K B f T :=
    (hs.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hr.inter hb).imp ?_
  rintro B f T hO ⟨hr, h₁, hp⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hr'⟩ := hr hKP hT C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have r'' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, pass_step_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, pass_step_congr P₁ hP hf, hpl]; exact hp)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, pass_step_congr A₀ hP hf] at hA; exact hA)))
    (hK.enl B B' f f' e hf hKP) hr'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), r''⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrePin
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsCondExact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld

namespace GlobalTheory.Mem.Top.Bl.KPxCond

theorem exists_prePin (K : Ctx) : ∃ P : Pre, K.Over P ∧ PrePin P :=
  ⟨GlobalTheory.StdFrameObj.coordPre K.P K.Lv, ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩,
    fun a b h => PinsCoord.extTo_basis _ _ a b h⟩

theorem baseCond_KPx : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM → BaseCond KPx := by
  intro hR hP hA h2b
  exact baseCond_of (PP := fun P _ => PrePin P) (GlobalTheory.Mem.KsExactCond.ksCond_exact hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      obtain ⟨P, hO, hp⟩ := exists_prePin K
      obtain ⟨f⟩ := (hfr P hO).2
      exact ⟨P, f, hO, hp⟩)

end GlobalTheory.Mem.Top.Bl.KPxCond
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.MemberEx2

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) (fun K B f T => ∃ w : ColW B f T, Start K B f T w) :=
  (Step.and (Step.of_all fun _ _ _ _ _ _ _ h => h)
      ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (PinW.step_pinned h2b))).trans
    (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨w, hw⟩ := H.2
      ⟨w, hw, supp_of_untw w H.1, coh_of_untw H.1⟩)

theorem stepW_builtE {𝒮 : Slots} {p : WP} (hp : ∀ K B f T w, p K B f T w → Pinned K B f T w)
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (hc : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)))
    (h3 : StepW p (Has3 𝒮)) : StepW p (HasC (BuiltE 𝒮)) :=
  have q : StepW p Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => hp _ _ _ _ _ h
  (q.and ((q.and h3).trans h4)).trans hc

end GlobalTheory.Mem.Top.Bl.MemberEx2

namespace GlobalTheory.Mem.Top.Bl

theorem memberE_of_steps2 : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  intro hR hP hC h2b 𝒮 𝒮' h3 h4 hA hD hT hE hPass h4' hA' hD' hT' hL
  have hB : BaseCond KPx := KPxCond.baseCond_KPx hR hP hC h2b
  have h1 : FirstG KPx (IsBuiltE 𝒮) :=
    step_hasCore (MemberEx2.step_start h2b)
      (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1) h4 (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮 hA hD hT) h3)
  have hW : StepW (fun K B f T w => Start K B f T w ∧ Has3 𝒮' K B f T w)
      (HasC fun K B f T w Z c => GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) :=
    (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1.1) h4' (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮' hA' hD' hT')
      (StepW.of_all fun _ _ _ _ _ _ _ h => h.2)).trans
      (StepW.of_all fun _ _ _ _ _ _ _ H => let ⟨Z, c, hc⟩ := H; ⟨Z, c, hL _ _ _ _ _ _ _ hc⟩)
  have hS := step_hasCore (admitted := fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w)
    (Step.of_all fun _ _ _ _ _ _ _ h => h) hW
  have h2 : SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) :=
    GlobalTheory.Mem.Top.GroupRetwisting.pass_step KPx _ _ _ hB hPass (hS.trans (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨C, W, V, S, N, G, c, hc⟩ := H
      ⟨C, W, V, S, N, G, c, positionOf_ind (R := fun K X f T c => IsBuiltE 𝒮 K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧
        IsGoodE 𝒮 K X f T c) (fun _ _ _ _ _ _ _ h => ⟨positionOf_intro h.1.1, h.2, positionOf_intro h.1⟩) hc⟩))
  exact ⟨hB, h1, hE, h2⟩

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPassStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_member_of_construction_steps_secondPass : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | exact GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | (intros; apply GlobalTheory.Mem.Top.Bl.memberE_of_steps2 <;> assumption)

end GlobalTheory.Mem.Top.Bl
end
