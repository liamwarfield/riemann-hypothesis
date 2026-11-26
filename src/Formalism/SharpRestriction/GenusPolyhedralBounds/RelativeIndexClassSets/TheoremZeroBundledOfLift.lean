module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthBaseT0
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthPoleInLift
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PvsDimYPos
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalCOfLen

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLengths
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocal
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VanishingOrderLeWeightSize
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.SizeBoundsAlt

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem deepPacketP (large₂ : SizeData₂ D) (X : PJ D B P j)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (th : Fin ρ → B.Cusp j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ)
    (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (c : HeightOneSpectrum (𝓞 B.KO) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe (B.Mlat j ka) z c)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH)
    (hT : ∀ Ctr, ((finrank B.KO (B.Cusp j ka) * finrank ℚ B.KO : ℕ) : ℝ) < Ctr → Trans (B.Mlat j ka) Hm Ctr)
    (hSM : SubMul X) (tableDegreeThreeBase : ℝ)
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(tableDegreeThreeBase * ka.size) ≤ WeightFamilies.meanLogSup B F) (G Prw Pd : ℝ)
    (hS2 : ∀ σ (F : B.Cusp j ka), B.supN j ka σ F ^ 2 ≤ Real.exp Pd * B.l2NormAlt j ka σ F ^ 2)
    (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, B.supN j wL σ (w k) ≤ Real.exp (mx σ))
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => c la * X.lN la) ∧
      ∑' la, c la * X.lN la ≤
        ρ * ((2 * G + Prw + tableDegreeThreeBase + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  subst hwt
  set d : ℕ := finrank B.KO (B.Cusp j (wtIter wadd wL w0 a0)) with hddef
  have hnK : 1 ≤ finrank ℚ B.KO := Module.finrank_pos (R := ℚ) (M := B.KO)
  have hlognK : 0 ≤ Real.log (finrank ℚ B.KO : ℝ) := Real.log_natCast_nonneg _
  have hPd0 : 0 ≤ Pd := (Real.log_natCast_nonneg _).trans hd
  have hPO0 : 0 ≤ PO D large₂ := hlognK.trans hO.1
  have hE : ∀ σ k, ∑ γ ∈ (z k).support, B.l2NormAlt j _ σ (z k γ) ≤
      Real.exp ((a0 : ℝ) * (Real.log N + mx σ) + Real.log (B.supN j w0 σ (th k))) := by
    intro σ k
    have hk := hal k
    have h3 : ∑ γ ∈ (z k).support, B.supN j _ σ (z k γ) ≤
        (∑ i, B.supN j wL σ (w i)) ^ a0 * B.supN j w0 σ (th k) := by
      have hzk := hz k
      revert hzk
      generalize z k = zk
      revert zk
      rw [← hk]
      intro zk hzk
      exact polynomial_coefficient_l1_bound X hSM w (al k) (th k) σ zk hzk
    refine (Finset.sum_le_sum fun γ _ => B.l2Norm_le_supNorm_alt j _ σ (z k γ)).trans (h3.trans ?_)
    have h4 : ∑ i, B.supN j wL σ (w i) ≤ Real.exp (Real.log N + mx σ) := by
      calc ∑ i, B.supN j wL σ (w i) ≤ ∑ _i : Fin N, Real.exp (mx σ) := Finset.sum_le_sum fun i _ => hmx σ i
        _ = N * Real.exp (mx σ) := by simp
        _ ≤ Real.exp (Real.log N) * Real.exp (mx σ) :=
            mul_le_mul_of_nonneg_right (Real.le_exp_log _) (Real.exp_pos _).le
        _ = _ := (Real.exp_add _ _).symm
    rw [Real.exp_add, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => B.supN_nonneg j wL σ _) h4 _)
      (Real.le_exp_log _) (B.supN_nonneg j w0 σ _) (pow_pos (Real.exp_pos _) _).le
  have hC0 : Real.log (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1) ≤
      1 * (Real.log (d : ℝ) + Real.log (finrank ℚ B.KO : ℝ)) := by
    rw [one_mul]
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h]; simpa using hlognK
    · have h5 : (1 : ℝ) ≤ ((d * finrank ℚ B.KO : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h hnK
      rw [max_eq_left h5, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have := deepSum (B.Mlat j _) z c hc0 hG hW Hm (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (fun Ctr h => hT Ctr (lt_of_le_of_lt (le_max_left _ _) h))
    (fun σ => B.supN j _ σ)
    (fun σ f hf => lt_of_le_of_ne (B.supN_nonneg j _ σ f) (fun h => hf ((B.supN_eq_zero j _ σ f).mp h.symm)))
    tableDegreeThreeBase (wtIter wadd wL w0 a0).size Pd
    (fun f hf hf0 => hLAM f hf hf0)
    hS2
    (a0 : ℝ) (Real.log N) mx (fun σ k => Real.log (B.supN j w0 σ (th k))) hE (Nat.cast_nonneg _)
    1 G Prw (PO D large₂) wL.size w0.size (Real.log (d : ℝ)) le_rfl hG0 hPrw hPd0 hPO0
    (WeightFamilies.Wt.one_le_size _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)) hmxm hth
    (by rw [size_wtIter]; ring) ha hrw hd hC0 hO.1 hO.2
  have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [e] at this
  exact this

theorem n_le_sizeW (ka : WeightFamilies.Wt D j) : (ka.n : ℝ) ≤ ka.size := by
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 : 0 ≤ ∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ)) := by positivity
  have h2 : 1 ≤ D.R.f * max (D.R.sigW j).2 1 * D.R.r :=
    Nat.mul_pos (Nat.mul_pos (by omega) (lt_of_lt_of_le Nat.one_pos (le_max_right _ _))) (by omega)
  have h3 : (1 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) := by exact_mod_cast h2
  have h4 : (ka.n : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) h3
  unfold WeightFamilies.Wt.size
  linarith

theorem vanishingOrder_le_weight_size (ka : WeightFamilies.Wt D j) (T nP nW : ℕ) (hk : ka.n = nP + T * nW) (hW : 0 < nW) :
    (a0 D j T : ℝ) ≤ ka.size := by
  have h1 : a0 D j T ≤ ka.n := by
    rw [hk]
    exact (Nat.sub_le _ _).trans ((Nat.le_mul_of_pos_right T hW).trans (Nat.le_add_left _ _))
  exact (Nat.cast_le.mpr h1).trans (n_le_sizeW ka)

end Formalism.MainNotions.Gaps.EtaleWeightGaps

end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem deepC (large₂ : SizeData₂ D) (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T nP nW : ℕ) (h0 CK C1 A1 Gc Prw CG AG p Pd : ℝ)
    (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (dH : DeepHerm X ka) (dS : DeepSubMul X) (dL : DeepLogD X ka Pd)
    (pG : PageGd X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : Submodule.IsFullLattice B.KO (B.Mlat j ka))
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(p * ka.size) ≤ WeightFamilies.meanLogSup B F)
    (hS2 : ∀ (F : B.Cusp j ka) (σ : B.KO →+* ℂ), B.supN j ka σ F ^ 2 ≤
      Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * B.l2NormAlt j ka σ F ^ 2) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + p + 3 / 2 * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -, -, hD, -, -, h40, -, -, hO, -⟩ := hC
  obtain ⟨-, hwM, hrw, hmx, hmxm⟩ := tW
  obtain ⟨hz0, hz, hWd⟩ := tZ
  obtain ⟨dd, Hm, hconj⟩ := dH
  have hwt := SizeBoundsAlt.hwt_of X ka wL wF T nP nW hIF hIL.1 (hk.trans hV) hD
  obtain ⟨z', hz1, hz2⟩ := SizeBoundsAlt.exists_zFam X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w hwM G.th0 (fun k => (hz0 k).2.1)
    G.alz (fun k => (hz0 k).2.2.2)
  have hzM : ∀ k β, G.zc k β ∈ B.Mlat j ka := by
    intro k β
    have : G.zc k β = z' k β := X.inc_inj ka ((hz k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  letI := hlat
  exact deepPacketP large₂ X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w G.th0 G.alz (fun k => (hz0 k).2.2.2) G.zc hz _
    (fun la => SizeBoundsAlt.gaussC_nonneg _ G.zc la) (SizeBoundsAlt.gaussC_gaussLe hzM) hWd Hm
    (fun Ctr hC => SizeBoundsAlt.trans_of_minima _root_.transference_successive_minima _ (Submodule.IsFullLattice.span_eq_top (A := B.KO) (M := B.Mlat j ka)) Hm hconj Ctr hC)
    dS p hLAM Gc Prw Pd
    (fun σ F => (hS2 F σ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr pG) (sq_nonneg _)))
    hG0 hP0 G.mx (fun σ k => (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (hmx σ k))) hmxm
    (fun k => (hz0 k).2.2.1) (vanishingOrder_le_weight_size ka T nP nW (hk.trans hV) (lt_of_lt_of_le (by norm_num) h40)) hrw dL hO

theorem quotC {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {Gc PH Prw Pet Pd : ℝ}
    (hQ : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (hH : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF)
    (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    Summable (fun la => lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la) ∧
      ∑' la, lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la ≤ 2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  by_cases hj : j < D.R.m
  · obtain ⟨-, hS, -, -, -, h3, -, -⟩ := hH
    obtain ⟨hrq, -, hspan, hsup⟩ := tQ
    have hT : 0 < T := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact (quotCoreE large₂ ka (T : ℝ) (cc D large₂ C2 A2 CR wL)
      (hQ hj (le_trans (by norm_num) hP.1) hP.2.2.2.2.2.1 hS.1 (lastPos_of_SetC hS) hS.2.2.2.2.2.2.2.1
        (by exact_mod_cast hT) (cc_pos_of hS h3 hP) (T_mul_cc_le_one h3 hP)) G.rq hrq G.th hspan hsup).2
  · obtain ⟨hs, h0'⟩ := lenQ_tsum_of_ge (X := X) G (not_lt.1 hj) K.CRm T (cc D large₂ C2 A2 CR wL)
    refine ⟨hs, ?_⟩
    have hrq : G.rq = 0 := by
      rw [tQ.1]
      exact rhoP_eq_zero_of_rho (rho_eq_zero_of_ge (not_lt.1 hj)) _ _ _ ka
    rw [h0', hrq]
    simp

theorem rLa_tsum_le_comb (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j}
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (lA : LatAt B j ka) (sA : SupBoundByL2AtWeight large₂ B j ka K.CG K.AG) (mA : LAMwAt large₂ B j ka K.CL K.AL)
    (qA : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (dH : DeepHerm (X j h1 h2) ka) (dS : DeepSubMul (X j h1 h2)) (dL : DeepLogD (X j h1 h2) ka Pd)
    (pG : PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    ∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la ≤
      (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * (X j h1 h2).lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * (X j h1 h2).lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  obtain ⟨hCs, hCb⟩ := deepC large₂ (X j h1 h2) G S T nP nW h0 H.CK H.C1 H.A1 Gc Prw K.CG K.AG
    (WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size)) Pd hH.2.1 tW tZ dH dS dL pG hP.2.2.1 hP.2.2.2.1 lA mA sA
  obtain ⟨hQs, hQb⟩ := quotC qA hH G tQ hP
  obtain ⟨hs, he⟩ := rLa_tsum_split Qf K.CRm T (cc D large₂ C2 A2 CR wL) hHt.2.1 (fun hj => (hHt.2.2.2 hj).1) hCs hQs
  refine ⟨hs, ?_⟩
  rw [he]
  linarith

theorem sumC : SumC D B P := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  obtain ⟨hs, hb⟩ := rLa_tsum_le_comb large₂ X K H Ch Ah Cq Aq C2 A2 CR CT h1 h2 S T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tZ tQ dH dS dL pG hP Qf hHt
  exact ⟨hs, hb.trans (sumGC large₂ (X j h1 h2) h1 K H Ch Ah Cq Aq C2 A2 CR CT S T nP nW h0 nus hH G Gc PH Prw Pet Pd
    tTh dL sRd sRho sRhoP hP Qf hHt)⟩

theorem theorem_zero_split_of_local (hL : LocalC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := theorem_zero_split_of_local_and_sum hL sumC

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def LenBaseAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF)

def LenPoleLAll (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) : Prop :=
  ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF)

theorem theorem_zero_split_of_lengths (hLB : LenBaseAll D B P) (hLP : LenPoleLAll D B P) :
    Conclusion1OfComb (D := D) (B := B) (P := P) := theorem_zero_split_of_local (localC_of_len hLB hLP)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem lenBase_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  fun _ _ _ _ _ => length_base_t0

theorem lenPoleL_all {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} :
    ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro j X ka wL wF G la Q S CRm T e c hOk hLift hW
  exact length_pole_t0 G la Q S CRm T e c hOk hW hLift

theorem theorem_zero_of_named_inputs {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} : Conclusion1OfComb (D := D) (B := B) (P := P) :=
  theorem_zero_split_of_lengths lenBase_all lenPoleL_all

end Formalism.MainNotions.Gaps.EtaleWeightGaps
