module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimET

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut
namespace Formalism.FourierDecayAlt.P.CutBP

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section loc

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_congr_level (Bs : B.RealPlaceData k r Wp Wq) {X Y : B.Mat k r → (Wq →L[ℂ] Wp)} {g : B.Mat k r}
    (hg : g ∈ B.GV k r) (h : ∀ x ∈ B.GV k r, Gf k r Bs.z Bs.z' x = Gf k r Bs.z Bs.z' g → X x = Y x) :
    B.JF Bs X g = B.JF Bs Y g := by
  rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs X g, ← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs Y g]
  unfold B.Jtau
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
  simp only [B.rho]
  rw [h _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hq hg) (Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hq g)]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_inter {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} (n : ℕ)
    (hf : B.CkOn ⊤ (B.GV k r) f) (U : Set (B.Mat k r)) : B.CkOn (n : ℕ∞) (U ∩ B.GV k r) f := by
  intro g₀ hg₀
  obtain ⟨V, f', hV, hgV, hf', hff⟩ := hf g₀ hg₀.2
  open scoped Matrix.Norms.Elementwise in
    exact ⟨V, f', hV, hgV, hf'.of_le (by exact_mod_cast le_top), hff⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fold_ckOn (s : ℂ) : ∀ (w : List C.Letter) (H : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H →
    B.CkOn ⊤ (B.GV k r) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) H)
  | [], _, h => h
  | a :: w, H, h => Formalism.FourierDecayAlt.P.CutMP.ER.coefficient_vector_smoothness k r Wp Wq s (a.2 : ℂ) _ (fold_ckOn s w H h)

theorem fold_congr_open (s : ℂ) {U : Set (B.Mat k r)} (hU : IsOpen U) {X Y : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hX : B.CkOn ⊤ (B.GV k r) X) (hY : B.CkOn ⊤ (B.GV k r) Y) (he : ∀ x ∈ U ∩ B.GV k r, X x = Y x) :
    ∀ (w : List C.Letter), ∀ x ∈ U ∩ B.GV k r,
      w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) X x = w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) Y x
  | [], x, hx => he x hx
  | a :: w, x, hx => by
    show (s • Q.CV k r (a.2 : ℂ) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) X)) x =
      (s • Q.CV k r (a.2 : ℂ) (w.foldr (fun a G => s • Q.CV k r (a.2 : ℂ) G) Y)) x
    simp only [Pi.smul_apply]
    rw [Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_locality k r _ U _ _ (a.2 : ℂ) hU (ckOn_inter _ (fold_ckOn s w X hX) U)
      (ckOn_inter _ (fold_ckOn s w Y hY) U) (fold_congr_open s hU hX hY he w) x hx]

end loc

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bigCell_pos (p : KB.Pl P Wp Wq) (q : (Fin P.r → ℂ) × ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q ≠ 0) :
    bigCell P.k P.r q.1 (p.T.base.μsec q.2) ∈ B.GV P.k P.r ∧
      0 < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) := by
  set c : Fin (P.r + 1) → ℂ := Fin.snoc q.1 q.2 with hcdef
  have hq1 : (fun j : Fin P.r => c j.castSucc) = q.1 := funext fun j => by simp [c]
  have hq2 : c (Fin.last P.r) = q.2 := by simp [c]
  have hqc : q = ((fun j => c j.castSucc), c (Fin.last P.r)) := by rw [hq1, hq2]
  rw [hqc] at hw
  rw [← hq1, ← hq2]
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG' : 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    have hsec := p.T.base.sec.2 _ hlt
    have hγ' : bigCell P.k P.r (fun i => c i.castSucc) (p.T.base.μsec (c (Fin.last P.r))) ∈ B.GV P.k P.r :=
      bigCellMem P.k P.r _ _ hc hsec.1
    have hZγ' := Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base c hlt
    refine ⟨hγ', ?_⟩
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZγ']
    exact hG'
  · exact absurd rfl hw'


end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopD
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem norm_sum_le_of_gram' {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (v : ι → H) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, ⟪v (P j), v (P l)⟫_ℂ = ∑ i, (c i : ℂ) * ⟪Y i (P j), Y i (P l)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, a j • Y i (P j)‖ := by
  set u := ∑ j ∈ J, a j • v (P j) with hu
  set y : I → W := fun i => ∑ j ∈ J, a j • Y i (P j) with hy
  have hinner : ⟪u, u⟫_ℂ = ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ := by
    have e1 : ⟪u, u⟫_ℂ = ∑ j ∈ J, ∑ l ∈ J, ∑ i,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      show ⟪∑ j ∈ J, a j • v (P j), ∑ j ∈ J, a j • v (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
      rw [hk j hj l hl, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e2 : ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ = ∑ i, ∑ j ∈ J, ∑ l ∈ J,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      show (c i : ℂ) * ⟪∑ j ∈ J, a j • Y i (P j), ∑ j ∈ J, a j • Y i (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [e1, e2]
    calc _ = ∑ j ∈ J, ∑ i, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hsq : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E), ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    intro E _ _ x
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hle : ‖u‖ ^ 2 ≤ ∑ i, (√(c i) * ‖y i‖) ^ 2 := by
    rw [← hsq u, hinner]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, hsq, mul_pow, Real.sq_sqrt (hc i), Complex.norm_real, Real.norm_of_nonneg (hc i)]
  have hsum : ∑ i, (√(c i) * ‖y i‖) ^ 2 ≤ (∑ i, √(c i) * ‖y i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnn : 0 ≤ ∑ i, √(c i) * ‖y i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((∑ i, √(c i) * ‖y i‖) ^ 2) := Real.sqrt_le_sqrt (hle.trans hsum)
    _ = ∑ i, √(c i) * ‖y i‖ := Real.sqrt_sq hnn

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

theorem cvec_utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x : ℂ) (hx : x ≠ 0) (cc : ℂ) :
    PBK.cvec s (utT p N c Fi L s h) x cc = vecT p N c Fi L ((h ++ [(s - 1, x⁻¹)]) ++ [(1, cc)]) := by
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
    Complex.ofReal_one, one_smul]
  simp

theorem inner_vecT_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq)
    (hV : VecHyp p nn F w c Fi L) (Q Q' : C.LPt) :
    ⟪vecT p w.length c Fi L Q, vecT p w.length c Fi L Q'⟫_ℂ = TBB.NP p nn F (P.r + 1) w Q' Q := by
  rw [inner_vecT p w.length c hV.hc Fi L Q Q', hV.gram Q' Q]

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopFields
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

theorem vecT_cont (hV : VecHyp p nn F w c Fi L) {h : C.LPt} (hh : ∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) {m : ℕ}
    (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) :
    ContinuousOn (fun z : ℂ => vecT p w.length c Fi L (h ++ [(m, z)])) {0}ᶜ := by
  have hcomp : ∀ i, ContinuousOn (fun z : ℂ =>
      ((√(c i) * omT p w.length (h ++ [(m, z)]) : ℝ) : ℂ) • L i (p.V (Fi i) (h ++ [(m, z)]))) {0}ᶜ := by
    intro i
    have := ((L i).continuous.comp_continuousOn (hV.cont i m h hh hm hsz)).const_smul ((√(c i) : ℝ) : ℂ)
    refine this.congr fun z _ => ?_
    show _ = (((√(c i) : ℝ) : ℂ)) • L i ((omT p w.length (h ++ [(m, z)]) : ℂ) • p.V (Fi i) (h ++ [(m, z)]))
    rw [map_smul, smul_smul, Complex.ofReal_mul]
  exact (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 hcomp)

theorem norm_vecT_sq (hV : VecHyp p nn F w c Fi L) (Q : C.LPt) :
    ‖vecT p w.length c Fi L Q‖ ^ 2 = (TBB.NP p nn F (P.r + 1) w Q Q).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_vecT p w.length c hV.hc Fi L Q Q, hV.gram Q Q]
  rfl

def gT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

theorem gT_cont (hV : VecHyp p nn F w c Fi L) {b s : ℕ} (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = P.r + 2) {h : C.LPt}
    (hh : D.IsLocPt h (b - 1)) : ContinuousOn (gT p w.length c Fi L s h) {0}ᶜ := by
  have hv := vecT_cont hV hh.1 (m := s) (by omega) (by rw [hh.2]; omega)
  have hsc : ContinuousOn
      (fun u : ℂ => (((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ)) : ℂ)) {0}ᶜ := by
    refine Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_const.mul (continuous_norm.continuousOn.pow _)) fun u hu => ?_
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero _ (norm_ne_zero_iff.mpr hu))
  exact hsc.smul hv

theorem btT_eq_piecewise (s : ℕ) (h : C.LPt) :
    btT p w.length c Fi L s h = ({0}ᶜ : Set ℂ).piecewise (gT p w.length c Fi L s h) (fun _ => 0) := by
  funext u
  by_cases hu : u = 0
  · simp [btT, Set.piecewise, hu]
  · simp [btT, gT, Set.piecewise, hu]

end place

set_option maxHeartbeats 1000000 in
theorem field_measurability : FieldMeas := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh
  rw [btT_eq_piecewise]
  letI : MeasurableSpace (HT I Wp Wq) := borel _
  haveI : BorelSpace (HT I Wp Wq) := ⟨rfl⟩
  exact ((gT_cont hV hb hs hbs hh).measurable_piecewise continuousOn_const
    (measurableSet_singleton 0).compl).stronglyMeasurable

theorem field_locality : FieldLoc := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh K hK h0
  have hsub : K ⊆ {0}ᶜ := fun z hz hz0 => h0 (by rwa [Set.mem_singleton_iff.mp hz0] at hz)
  have hg := (gT_cont hV hb hs hbs hh).mono hsub
  refine ContinuousOn.integrableOn_compact hK ?_
  have hc : ContinuousOn
      (fun z => ‖(((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • gT p w.length c Fi L s h z‖ ^ 2) K := by
    have h1 : ContinuousOn (fun z : ℂ => ((((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ)) : ℂ)) K :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuous_norm.continuousOn.pow _))
    exact (h1.smul hg).norm.pow 2
  refine hc.congr fun z hz => ?_
  have hz0 : z ≠ 0 := fun e => h0 (e ▸ hz)
  simp only [PBK.bz, btT, gT, hz0, if_false]

theorem field_supremum : FieldSup := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  rw [← PBK.integral_norm_cvec_sq s (utT p w.length c Fi L s h) x hx]
  simp_rw [hcv, norm_vecT_sq hV]
  rw [TBB.Ew, hV.fibre a a hloc hloc]
  exact integral_re (hV.int a hloc)

theorem field_mem_unitary : FieldMemU := by
  intro P Wp Wq _ _ _ _ _ _ I _ p nn F w c Fi L hV b s hb hs hbs h hh x hx
  set a : C.LPt := h ++ [(s - 1, x⁻¹)] with ha
  have hloc : D.IsLocPt a P.r := by
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hh.1 q hq
      · rw [List.mem_singleton.mp hq]
        exact ⟨show 1 ≤ s - 1 by omega, show x⁻¹ ≠ 0 from inv_ne_zero hx⟩
    · have := hh.2
      simp [ha, D.ptSize] at this ⊢
      omega
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcv : ∀ cc, PBK.cvec s (utT p w.length c Fi L s h) x cc = vecT p w.length c Fi L (a ++ [(1, cc)]) := by
    intro cc
    rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
      Complex.ofReal_one, one_smul]
    simp [ha]
  refine (PBK.memLp_cvec s (utT p w.length c Fi L s h) x hx).2 ?_
  have hfun : PBK.cvec s (utT p w.length c Fi L s h) x = fun cc => vecT p w.length c Fi L (a ++ [(1, cc)]) :=
    funext hcv
  rw [hfun]
  have hcont := vecT_cont hV hloc.1 (m := 1) le_rfl (by rw [hloc.2])
  have hmeas : AEStronglyMeasurable (fun cc => vecT p w.length c Fi L (a ++ [(1, cc)])) volume := by
    have := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℂ)).compl
    first
      | rwa [restrict_compl_singleton] at this
      | rwa [Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))] at this
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine ((hV.int a hloc).re).congr (Filter.Eventually.of_forall fun cc => ?_)
  exact (norm_vecT_sq hV _).symm

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
  {p : KB.Pl P Wp Wq} {nn : ℝ → ℝ} {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List C.Letter} {c : I → ℝ}
  {Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq}

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end
