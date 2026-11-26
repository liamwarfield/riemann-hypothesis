module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrSymm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransportPlus
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem lintegral_zWeight_closedBall_ne_infty (k : ℕ) (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hb : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    unfold B2.zWeight
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      have h1 : Complex.normSq ζ ≤ R ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        have := mem_closedBall_zero_iff.mp hζ
        have h0 : 0 ≤ ‖ζ‖ := norm_nonneg _
        nlinarith
      have h2 : -(T * T') ≤ |T * T'| := neg_le_abs _
      linarith
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono measurable_const (fun ζ hζ => hb ζ hζ)
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem ph_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k n z z' π π')
        (c : Fin n → ℂ) (c₀ : Fin ρ → ℂ),
        P5.ph L st μ ⟨0, by omega⟩ w x y c t =
          ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
            P5.RRform Ls sts μs 0 w (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a))
              (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) y a)) c₀ := by
  subst hn
  have ez : z = liftVec k 1 ρ zs := by
    rw [hz]; funext i; simp [D.castV]
  have ez' : z' = liftVec k 1 ρ zs' := by
    rw [hz']; funext i; simp [D.castV]
  have eπ : πs = fun y => π (ιLev k 1 ρ y) := by
    funext y; rw [hπ y]; congr 1
  have eπ' : πs' = fun y => π' (ιLev k 1 ρ y) := by
    funext y; rw [hπ' y]; congr 1
  subst ez ez' eπ eπ'
  have hmap : μs.map (B2.levM k ρ) = μ := by
    refine map_levM_eq hμ hμs (fun ζ => ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ))
      (fun R => lintegral_zWeight_closedBall_ne_infty k _ _ R) ?_ hlaws
    intro ψ hψ
    rw [hlaw ψ hψ, tz_iota, tz_iota]
  refine ⟨trL ht zs zs' π π', ?_, ?_⟩
  · intro Φ c g
    (try simp [D.castM]) <;> rfl
  · intro S _ _ w x y c c₀
    exact ph_tr ht hzs hzs' hL hLs hst hsts hmap w x y c c₀

def RadTransportPl : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j + 1 ≤ P.r)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j))) (L) (st)
    (Xs : Q.ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z'
      (p.T.bs (j + 1)).π (p.T.bs (j + 1)).π')
    (μs : Measure (Mt P.k (P.r - (j + 1)))) (Ls) (sts),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    KB.ZetaNorm (p.T.bs j) μ →
    P5.IsData (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
      (p.T.bs (j + 1)).π' Xs μs Ls sts p.l0 →
    KB.ZetaNorm (p.T.bs (j + 1)) μs →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' →ₗ[ℂ]
          Q.RadSp P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
            (p.T.bs (j + 1)).π',
        (∀ Φ c g, (T Φ : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
          (Φ : Q.Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
            (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S))
          (x y : Wd.Ix S → Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
          (c : Fin (P.r - j) → ℂ) (c₀ : Fin (P.r - (j + 1)) → ℂ),
          P5.ph L st μ (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w x y c t =
            ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
              P5.RRform Ls sts μs 0 w
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) x a))
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) y a))
                c₀

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem radial_transport_plus : Formalism.FourierDecayAlt.P.PBH.RadTransportPl := by
  intro Wp Wq _ _ _ _ _ _ P p j hj X μ L st Xs μs Ls sts hD hZ hDs hZs t ht
  exact ph_cast (n := P.r - j) (ρ := P.r - (j + 1)) (by omega)
    (levTower_bs_z_eq_castV_liftVec p.T j hj) (levTower_bs_z'_eq_castV_liftVec p.T j hj) hDs.1.2.1 hDs.1.2.2.1
    (tower_π p.T j hj) (tower_π' p.T j hj) X Xs L st Ls sts _ μ μs
    hD.2.2.1 hDs.2.2.1 hD.2.2.2.1 (fun Y => (hDs.2.2.2.1 Y).trans rfl) hD.2.1 hDs.2.1 hZ.2 hZs.2 t ht

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreIntegralCells
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

theorem gPoly_of (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PBI.gPoly TT (Matrix.of (Matrix.of.symm M : G.Mat (r + 1))) = PBI.gPoly TT M := rfl

private theorem det_eq_one_of_lower_unitriangular' {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => h0 i j hij)]
  simp [h1]

private theorem det_eq_one_of_upper_unitriangular {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, j < i → U i j = 0)
    (h1 : ∀ i, U i i = 1) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem gPoly_LU (TT : ℝ) {L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L ∈ C2.LTset (r + 1))
    (hU : U ∈ C2.UTset (r + 1)) : PBI.gPoly TT (L * M * U) = PBI.gPoly TT M := by
  obtain ⟨hL0, hL1⟩ := hL
  obtain ⟨hU0, hU1⟩ := hU

  have hsub : (L * M * U).submatrix Fin.castSucc Fin.castSucc =
      L.submatrix Fin.castSucc Fin.castSucc * M.submatrix Fin.castSucc Fin.castSucc *
        U.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hL0 (Fin.castSucc i) (Fin.last r) (Fin.castSucc_lt_last i),
      hU0 (Fin.last r) (Fin.castSucc j) (Fin.castSucc_lt_last j), zero_mul, mul_zero, add_zero]
  have hL' : (L.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_lower_unitriangular' (fun i j h => hL0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hL1 _)
  have hU' : (U.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_upper_unitriangular (fun i j h => hU0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hU1 _)
  unfold PBI.gPoly
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_eq_one_of_lower_unitriangular' hL0 hL1,
    det_eq_one_of_upper_unitriangular hU0 hU1, hL', hU']
  simp

theorem gPoly_pt (TT : ℝ) (a : C.LPt) : PBI.gPoly TT (D.ptMatN a (r + 1)) = D.ptG TT r a := by
  have h : (D.ptMatN a (r + 1)).submatrix Fin.castSucc Fin.castSucc = D.ptMatN a r := by
    ext i j
    rfl
  unfold PBI.gPoly D.ptG
  rw [h]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

theorem fibre_integral_cells : PBI.FibIntCells := by
  intro Wp Wq _ _ _ _ _ _ P p
  set S := p.T.base with hS
  have hz : C2.StdZ P.k P.r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ P.k P.r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  obtain ⟨μ0, hμ0⟩ := exists_haar_stabilizer P.k P.r S.z hz
  obtain ⟨μ0', hμ0'⟩ := exists_haar_stabilizer P.k P.r S.z' hz'
  obtain ⟨c1, hc1, hN1⟩ := disintN P.k P.r S.z hz μ0 S.μN hμ0 S.haarN
  obtain ⟨c2, hc2, hN2⟩ := disintN P.k P.r S.z' hz' μ0' S.μN hμ0' S.haarN
  refine ⟨μ0, μ0', (((c1 * c2 : NNReal) : ℝ) : ℂ), hμ0, hμ0', ?_⟩
  intro sec hsec F hF a σ d ha hm
  obtain ⟨hw, hd0⟩ := Dx2.VV.ptMatN_monoP' a (P.r + 1) ha.2 ha.1
  set w := ha.2 ▸ D.ptPerm a with hwdef
  set d0 := ha.2 ▸ D.ptDiag a with hd0def
  obtain ⟨e, hemp, he⟩ := splitUT (P.r + 1) w
  have hPT := phiTopCoords (P.r + 1) σ w d d0 (Wq →L[ℂ] Wp)
    ((((c1 * c2 : NNReal) : ℝ) : ℂ) • PBI.phi0 S μ0 μ0' sec F) hd0 (hm.trans hw)
  rw [hPT]
  set TT := Tz P.k P.r S.z * Tz P.k P.r S.z' with hTT
  have hgP : ∀ Y : (C2.LPidx w → ℂ) × (G.UT (P.r + 1) → ℂ),
      PBI.gPoly TT (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) = D.ptG TT P.r a := by
    intro Y
    rw [FK.gPoly_LU TT (UC.lowerUnipotent_mem w Y.1).1 (UC.upper_mem Y.2), ← hw, FK.gPoly_pt]
  show D.vecV S p.ν' p.m₀ F a = _
  by_cases hG : 0 < D.ptG TT P.r a
  · obtain ⟨σ0, hE⟩ := Dx2.VV.exE S p.ν' p.m₀ p.hF a ha hG
    have hγe := hE.1
    have hZe := hE.2.1
    have hDe := hE.2.2.1
    set γ0 := p.m₀ * σ0 with hγ0
    have hV := isotropic_vectors_linear_indep P.k P.r Wp Wq S p.ν' p.m₀ F a ha γ0 p.hF hG hγe hZe hDe
    rw [hV]
    have hZw : Zhat P.k P.r S.z S.z' γ0 = C2.monoP w d0 := hZe.trans hw
    have hpos : 0 < Gf P.k P.r S.z S.z' γ0 := by
      rw [← ptG_spec P.k P.r S.z S.z' a _ ha hZe]; exact hG
    have hrel := relevant_points_holds P.k P.r Wp Wq S a γ0 ha hγe hZe
    obtain ⟨θ1, hθ1, hint1⟩ := CV.orbJConv_cpt S γ0 w d0 F hγe hrel hd0 hZw hpos hF
    have hex : ∃ θ, D.IsNormCut S γ0 (D.muR S γ0 w) θ ∧
        Integrable (fun q => θ q • D.orbIntegrand S γ0 F q) S.μSS := ⟨θ1, hθ1, hint1⟩
    unfold D.orbJ
    rw [dite_eq_left hex]
    obtain ⟨hθ, hint⟩ := hex.choose_spec
    obtain ⟨hI, hEq⟩ := OG.orb_int S hγe hd0 hZw hpos hrel e hemp he hμ0 hμ0' hc1 hc2 hN1 hN2 F _ hθ hint
    rw [hEq, OJ.cell_int S γ0 w hμ0 hμ0' F hI, RCLike.real_smul_eq_coe_smul (K := ℂ), ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply]
    rw [smul_comm]
    congr 2
    have hZp : 0 < PBI.gPoly TT (Matrix.of (Matrix.of.symm (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) :
        G.Mat (P.r + 1))) := by
      rw [FK.gPoly_of, hgP Y]; exact hG
    unfold PBI.phi0
    rw [if_pos hZp]
    obtain ⟨hsG, hsZ, hsD⟩ := hsec.2 _ hZp
    have hv := lowPH_UT (w := w) Y.1
    have hu := UC.upper_mem Y.2
    have hZ1 : Zhat P.k P.r S.z S.z' ((C2.tauM P.k P.r S.z (lowP w Y.1)ᴴ)⁻¹ * γ0 *
        C2.tauM P.k P.r S.z' (G.upper Y.2)) = lowP w Y.1 * C2.monoP w d0 * G.upper Y.2 := by
      rw [Formalism.FourierDecayAlt.P.zhat_equivalence P.k P.r S.z S.z' hz hz' _ (A.n_in_S (A.tau_N hz hv)) _
          (A.n_in_S (A.tau_N hz' hu)) γ0,
        (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z hz _ hv).2.2, (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z' hz' _ hu).2.2,
        Matrix.conjTranspose_conjTranspose, hZw]
    symm
    exact FB.fib_indep S p.ν' p.m₀ p.hF a ha hG hE hμ0 hμ0' F hv hu hsG (hsZ.trans hZ1.symm) hsD
  · have h0 : D.vecV S p.ν' p.m₀ F a = 0 := by
      unfold D.vecV; rw [dite_eq_right (fun h => hG h.2)]
    rw [h0]
    symm
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply, Pi.zero_apply]
    unfold PBI.phi0
    rw [if_neg (by rw [FK.gPoly_of, hgP Y]; exact hG), smul_zero, smul_zero]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerCoordinateProd
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section cut

variable {j : ℕ}

def blkU (M : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) : Matrix (Fin j) (Fin j) ℂ := M.submatrix Fin.castSucc Fin.castSucc

def x0c (w0 : Equiv.Perm (Fin j)) (W : Matrix (Fin j) (Fin j) ℂ) : C2.Lstidx w0 → ℂ :=
  ((StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc W)).1

def boxC : Set ℂ := Complex.equivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

def chiL (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : ℝ :=
  (Set.univ.pi fun _ : C2.Lstidx w0 => boxC).indicator (fun _ => (1 : ℝ)) x

theorem boxR_meas : MeasurableSet (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc

theorem boxC_meas : MeasurableSet boxC := (Complex.measurable_re.prodMk Complex.measurable_im) boxR_meas

theorem boxC_vol : volume boxC = 1 := by
  have h := (Complex.volume_preserving_equiv_real_prod.measure_preimage boxR_meas.nullMeasurableSet)
  change volume (Complex.measurableEquivRealProd ⁻¹' _) = 1
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

theorem chiL_meas (w0 : Equiv.Perm (Fin j)) : Measurable (chiL w0) := measurable_const.indicator (MeasurableSet.univ_pi fun _ => boxC_meas)

theorem chiL_nonneg (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : 0 ≤ chiL w0 x := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem chiL_int (w0 : Equiv.Perm (Fin j)) : ∫ x, chiL w0 x = 1 := by
  unfold chiL
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => boxC_meas), Measure.real,
    volume_pi_pi]
  simp [boxC_vol]

end cut

section low

variable {r : ℕ} (w : Equiv.Perm (Fin (r + 1))) (w0 : Equiv.Perm (Fin r))

theorem w_last (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    w.symm (Fin.last r) = Fin.last r := by
  by_contra h
  obtain ⟨b, hb⟩ := Fin.exists_castSucc_eq.2 h
  have h2 : w.symm (w0 b).castSucc = b.castSucc := by rw [hw, Equiv.symm_apply_apply]
  rw [hb] at h2
  exact (Fin.castSucc_lt_last (w0 b)).ne (w.symm.injective h2)

theorem w_last' (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) : w (Fin.last r) = Fin.last r := by
  exact ((Equiv.symm_apply_eq w).1 (w_last w w0 hw)).symm

variable (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc)
include hw

theorem lst_ne_last (q : C2.Lstidx w) : q.1.1 ≠ Fin.last r ∧ q.1.2 ≠ Fin.last r := by
  refine ⟨fun h => ?_, ne_of_lt (lt_of_lt_of_le q.2.1 (Fin.le_last _))⟩
  have h2 := q.2.2
  rw [h, w_last w w0 hw] at h2
  exact absurd h2 (not_lt.2 (Fin.le_last _))

def eL : C2.Lstidx w0 ≃ C2.Lstidx w where
  toFun q := ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 q.2.1, by
    rw [hw, hw]; exact Fin.castSucc_lt_castSucc_iff.2 q.2.2⟩
  invFun q := ⟨((q.1.1).castPred (lst_ne_last w w0 hw q).1, (q.1.2).castPred (lst_ne_last w w0 hw q).2), by
    refine ⟨?_, ?_⟩
    · rw [← Fin.castSucc_lt_castSucc_iff]; simpa using q.2.1
    · have ha : ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc = q.1.1 := Fin.castSucc_castPred _ _
      have hb : ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc = q.1.2 := Fin.castSucc_castPred _ _
      have h2 : w.symm ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc <
          w.symm ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc := by rw [ha, hb]; exact q.2.2
      rw [hw, hw] at h2
      exact Fin.castSucc_lt_castSucc_iff.1 h2⟩
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

theorem low_blk (x : C2.Lstidx w → ℂ) : blkU (Dx2.Rad.low w x) = Dx2.Rad.low w0 (x ∘ eL w w0 hw) := by
  ext i j
  rw [← StabilizerDisintegration.UC.lowS_eq_low, ← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [blkU, Matrix.submatrix_apply, StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply,
    Function.comp_apply]
  rw [← (eL w w0 hw).sum_comp (fun q => if q.1 = (i.castSucc, j.castSucc) then x q else 0)]
  congr 1
  · simp [Matrix.one_apply]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have he : ((eL w w0 hw) q).1 = (q.1.1.castSucc, q.1.2.castSucc) := rfl
    simp only [he, Prod.ext_iff, Fin.castSucc_inj]

theorem low_last_row (x : C2.Lstidx w → ℂ) (a : Fin r) : Dx2.Rad.low w x (Fin.last r) a.castSucc = 0 := by
  rw [← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', zero_add]
  exact Finset.sum_eq_zero fun q _ => if_neg fun h => (lst_ne_last w w0 hw q).1 (congrArg Prod.fst h)

omit hw in
theorem blkU_mul (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hA : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0) :
    blkU (A * B) = blkU A * blkU B := by
  ext i j
  simp only [blkU, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hA, zero_mul, add_zero]

omit hw in
theorem blkU_ct (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : blkU Aᴴ = (blkU A)ᴴ := by
  ext i j
  rfl

omit hw in
theorem blkU_UT {A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : A ∈ C2.UTset (r + 1)) : blkU A ∈ C2.UTset r := ⟨fun i j h => hA.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), fun i => hA.2 _⟩

end low

section normcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def theta0 (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) (p : B.SS k r) : ℝ :=
  chiL w0 (x0c w0 (blkU (C2.uMap k r z (Matrix.of p.1.2))))

theorem theta0_meas (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) : Measurable (theta0 (k := k) z w0) := by
  have hU : Measurable fun p : B.SS k r => StabilizerDisintegration.utc (blkU (C2.uMap k r z (Matrix.of p.1.2))) := by
    refine Measurable.of_eval fun q => ?_
    have hc : Continuous fun p : B.SS k r =>
        C2.uMap k r z (Matrix.of p.1.2) q.1.1.castSucc q.1.2.castSucc := by
      simp only [C2.uMap, Formalism.QuantumDeterminants.herm, Fin.coe_castSucc, Fin.is_lt, dif_pos, dotProduct,
        Matrix.mulVec, Matrix.of_apply]
      fun_prop
    exact hc.measurable
  unfold theta0 x0c
  exact (chiL_meas w0).comp (measurable_fst.comp ((StabilizerDisintegration.UC.eSp w0).symm.measurable.comp hU))

theorem lower_coordinate_prod (w0 : Equiv.Perm (Fin r)) (x a : C2.Lstidx w0 → ℂ) (y : C2.LPidx w0 → ℂ) :
    x0c w0 ((StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ)) =
      StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x) := by
  have hL := ((StabilizerDisintegration.UC.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) a).2 x)
  have hM : (StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ) =
      (StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ := by
    rw [← hL, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hE : StabilizerDisintegration.utc ((StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ *
      (StabilizerDisintegration.lowP w0 y)ᴴ) = StabilizerDisintegration.UC.eSp w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x), y) := rfl
  unfold x0c
  rw [hM, hE, MeasurableEquiv.symm_apply_apply]

theorem theta0_normCut (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (w0 : Equiv.Perm (Fin r))
    (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    D.IsNormCut S γ (D.muR S γ w) (theta0 S.z w0) := by
  have hB : w (Fin.last r) = Fin.last r := w_last' w w0 hw
  have hG : Dx2.Rad.Good S γ w d :=
    ⟨Dx2.Rad.ex_degen S hγ hd hZ hB, Dx2.Rad.inj_degen S hγ hd hZ hB, fun ρ hρ => Dx2.Rad.lst_gen S hγ hd hZ hρ⟩
  refine ⟨theta0_meas S.z w0, fun p => chiL_nonneg w0 _, fun p hp => ?_⟩
  have hmuR : D.muR S γ w = (volume : Measure (C2.Lstidx w → ℂ)).map
      (fun x => (Matrix.of.symm (Dx2.Rad.rhoF S γ w x) : Mt k r)) := rfl
  have hact : Measurable fun x : Mt k r => theta0 S.z w0 (C6.actR γ (Matrix.of x) p) := by
    refine (theta0_meas S.z w0).comp ?_
    unfold C6.actR
    refine Measurable.prodMk (Measurable.prodMk measurable_const ?_) (Measurable.prodMk measurable_const ?_)
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
  rw [hmuR, integral_map (Dx2.Rad.rhoF_meas S hγ hd hG).aemeasurable hact.aestronglyMeasurable]

  have hn : Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r := hp.2.1
  have hUT : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) ∈ C2.UTset r :=
    blkU_UT ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z ⟨S.z_mem, S.T_pos⟩).1 _ (Dx2.Rad.N_sub_S S.z hn)).2.1
  set pa := (StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc (blkU (C2.uMap k r S.z (Matrix.of p.1.2)))) with hpa
  have hsplit : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) = (StabilizerDisintegration.lowS w0 pa.1)ᴴ * (StabilizerDisintegration.lowP w0 pa.2)ᴴ := by
    rw [← StabilizerDisintegration.UC.upper_fSp, ← StabilizerDisintegration.UC.upper_utc hUT]
    congr 1
    show _ = StabilizerDisintegration.UC.eSp w0 pa
    rw [hpa, (StabilizerDisintegration.UC.eSp w0).apply_symm_apply]
  have hpt : ∀ x : C2.Lstidx w → ℂ, theta0 S.z w0 (C6.actR γ (Matrix.of (Matrix.of.symm (Dx2.Rad.rhoF S γ w x))) p) =
      chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) := by
    intro x
    obtain ⟨hρR, hρu⟩ := Dx2.Rad.rhoF_spec S hγ hd hG x
    unfold theta0
    simp only [C6.actR, Equiv.apply_symm_apply]
    rw [Dx2.Rad.uMap_mul S hρR.1 hn, hρu,
      blkU_mul _ _ (fun a => by rw [Matrix.conjTranspose_apply, low_last_row w w0 hw, star_zero]),
      blkU_ct, low_blk w w0 hw, hsplit, ← StabilizerDisintegration.UC.lowS_eq_low, lower_coordinate_prod]
  simp_rw [hpt]
  have hmp1 := (MeasureTheory.measurePreserving_piCongrLeft (fun _ : C2.Lstidx w => (volume : Measure ℂ))
    (eL w w0 hw)).symm
  have hmp2 := (StabilizerDisintegration.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) pa.1).1
  have e1 : ∫ x : C2.Lstidx w → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) =
      ∫ x' : C2.Lstidx w0 → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 x')) := by
    have h := hmp1.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun y : C2.Lstidx w0 → ℂ => chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 y)))
    exact h
  rw [e1, ← integral_map hmp2.measurable.aemeasurable (chiL_meas w0).aestronglyMeasurable, hmp2.map_eq,
    chiL_int]

end normcut

end Formalism.FourierDecayAlt.P.PBM
end
end
