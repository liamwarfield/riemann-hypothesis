module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section pts

theorem bigPt_eq_map {n : ℕ} (d : Fin n → ℂ) : bigPt d = (List.ofFn d).map fun c => (1, c) := by
  rw [bigPt, List.map_ofFn]
  rfl

theorem ptPartner_ones (l : List ℂ) (a : ℕ) : D.ptPartner (l.map fun c => (1, c)) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih =>
    simp only [List.map_cons, D.ptPartner, ih]
    split_ifs with h <;> omega

theorem ptPerm_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.ptPerm (bigPt d) = 1 := by
  unfold D.ptPerm
  split_ifs with h
  · ext i
    have hp : ∀ a : ℕ, D.ptPartner (bigPt d) a = a := fun a => by
      rw [bigPt_eq_map]
      exact ptPartner_ones _ _
    simp only [Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq, D.ptPartnerF]
    split_ifs
    · exact hp i
    · rfl
  · rfl

theorem cast_perm_eq_one {n m : ℕ} (e : n = m) (σ : Equiv.Perm (Fin n)) (hσ : σ = 1) :
    (e ▸ σ : Equiv.Perm (Fin m)) = 1 := by
  subst e
  exact hσ

theorem hMat_one {n : ℕ} (d : Fin n → ℂ) : U.hMat (1 : Equiv.Perm (Fin n)) d = Matrix.diagonal d := by
  have hw : U.wP (1 : Equiv.Perm (Fin n)) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [U.wP, Matrix.one_apply, hab]
  simp only [U.hMat, hw, one_mul]

private lemma ptEntry_map_one_eq_ite_getD (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    rcases a with _ | a <;> rcases b with _ | b <;> simp [D.ptEntry, ih]

private lemma list_ofFn_getD_of_lt {n : ℕ} (d : Fin n → ℂ) (i : ℕ) (hi : i < n) :
    (List.ofFn d).getD i 0 = d ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private lemma ptMatN_bigPt_eq_diagonal' {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = Matrix.diagonal d := by
  ext a b
  simp only [D.ptMatN, bigPt_eq_map, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply, Fin.ext_iff]
  split_ifs with h
  · exact list_ofFn_getD_of_lt d a a.isLt
  · rfl

theorem ptMatN_bigPt_head {r : ℕ} (d : Fin (r + 1) → ℂ) :
    D.ptMatN (bigPt d) r = Matrix.diagonal fun a : Fin r => d a.castSucc := by
  ext a b
  simp only [D.ptMatN, bigPt_eq_map, ptEntry_map_one_eq_ite_getD, Matrix.diagonal_apply, Fin.ext_iff]
  split_ifs with h
  · exact list_ofFn_getD_of_lt d a (by omega)
  · rfl

theorem zeta_big {r : ℕ} (TT : ℝ) (d : Fin (r + 1) → ℂ) (h : 0 < D.ptG TT r (bigPt d)) :
    TT < Complex.normSq (d (Fin.last r)) := by
  have h1 := h
  simp only [D.ptG, ptMatN_bigPt_eq_diagonal', ptMatN_bigPt_head, Matrix.det_diagonal, Fin.prod_univ_castSucc,
    map_mul] at h1
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (Complex.normSq_nonneg (∏ a : Fin r, d a.castSucc))]

end pts

section orb

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem zhat_bigCell_pt (Bs : B.RealPlaceData k r Wp Wq) (d : Fin (r + 1) → ℂ)
    (hζ : Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (d (Fin.last r))) :
    Zhat k r Bs.z Bs.z' (bigCell k r (fun i => d i.castSucc) (Bs.μsec (d (Fin.last r)))) =
      D.ptMatN (bigPt d) (r + 1) := by
  rw [ptMatN_bigPt_eq_diagonal', bigCellZhat k r _ _ _ _ Bs.z_mem Bs.z'_mem,
    Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ Bs.z_mem Bs.z'_mem, (Bs.sec.2 _ hζ).2]
  congr 1
  funext a
  split_ifs with h
  · rfl
  · have ha := a.isLt
    have hl : a = Fin.last r := Fin.ext (by rw [Fin.val_last]; omega)
    rw [hl]

theorem orbJ_one_zero (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r S.z S.z' γ) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hJ : B.JF S F γ = 0) : D.orbJ S γ (D.muR S γ 1) F = 0 := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (r + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k r) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (r + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k r)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    have hrow : (Matrix.of (row 1) : B.Mat k r) = 1 := by
      ext i j
      simp
    simpa [hrow, hact] using h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq S F γ
      _ = 0 := hJ
  · rfl

end orb

section jf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jf_bigCell_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hR : Top.IsRadOf P Bs 0 F) (c : Fin P.r → ℂ) (hc : ∀ a, c a ≠ 0) (ζ : ℂ)
    (hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ) :
    B.JF Bs F (bigCell P.k P.r c (Bs.μsec ζ)) = 0 := by
  have hsec := Bs.sec.2 ζ hζ
  have hμ : Bs.μsec ζ ∈ UH (Hb P.k) := hsec.1
  have hg : B2.embWb P.k P.r (Bs.μsec ζ) ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb hμ)
  have e : herm (Hpk P.k P.r) (bigCell P.k P.r c (Bs.μsec ζ) *ᵥ Bs.z') Bs.z =
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (B2.embWb P.k P.r (Bs.μsec ζ)) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hz : Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (B2.embWb P.k P.r (Bs.μsec ζ)) = ζ := by
    rw [← e, Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ Bs.z_mem Bs.z'_mem, hsec.2]
  have hdom : ((c, B2.embWb P.k P.r (Bs.μsec ζ)) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈
      Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, by unfold Q.GGl; rw [hz]; linarith⟩
  have h0 := hR _ hdom
  have hz0 : ((0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
      (B2.embWb P.k P.r (Bs.μsec ζ)) = 0 := rfl
  rw [hz0] at h0
  unfold Q.resG at h0
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r c _).1] at h0
  rcases smul_eq_zero.1 h0.symm with h | h
  · exfalso
    rw [Complex.ofReal_eq_zero, Finset.prod_eq_zero_iff] at h
    obtain ⟨a, -, ha⟩ := h
    split_ifs at ha
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a)) ha
    · exact one_ne_zero ha
  · exact h

end jf

theorem bigCellVan : PBJ.BigCellVan := by
  intro Wp Wq _ _ _ _ _ _ P p F _ hR d hd
  show D.vecV p.T.base p.ν' p.m₀ F (bigPt d) = 0
  unfold D.vecV
  split_ifs with h h'
  · obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
      zeta_big _ d h.2
    have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
    have hsec := p.T.base.sec.2 _ hζ
    have hγ' : bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))) ∈ B.GV P.k P.r :=
      bigCellMem P.k P.r _ _ hc hsec.1
    have hZγ' := zhat_bigCell_pt p.T.base d hζ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (bigPt d) _ h.1 hZγ]; exact h.2
    have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z'
        (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))) := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (bigPt d) _ h.1 hZγ']; exact h.2
    obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
      ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
      _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
    obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
    obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
    have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (bigPt d) h.1 hγ hZγ hpos hhA hnA hfA hhB hnB hfB F
    rw [← hγs] at hlaw
    rw [← hlaw]
    have hw : (h.1.2 ▸ D.ptPerm (bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      cast_perm_eq_one _ _ (ptPerm_bigPt d hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (bigPt d) (P.r + 1) h.1.2 h.1.1
    rw [hw] at hmono
    rw [hw, orbJ_one_zero p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F
      (jf_bigCell_zero P p.T.base F hR _ hc _ hζ), map_zero]
  · rfl
  · rfl

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem vector_vanishes_big_cell : PBJ.BigCellVan := PBM.bigCellVan

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

def sig (TT : ℝ) (ζ : ℂ) : ℂ := ((Real.sqrt (Complex.normSq ζ - TT) : ℝ) : ℂ)

def gg (TT : ℝ) (ζ : ℂ) : ℂ := ((Complex.normSq ζ - TT : ℝ) : ℂ)

def PS (TT : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (m : ℕ) (p : MvPolynomial (Fin 3) ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ →
    gg TT ζ ^ m * f ζ = MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] p

def PSV (TT : ℝ) {V : Type*} [AddCommGroup V] [Module ℂ V] (f : ℂ → V) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ → ℂ) (v : Fin n → V), (∀ i, PS TT (a i)) ∧
    ∀ ζ : ℂ, TT < Complex.normSq ζ → f ζ = ∑ i, a i ζ • v i

def rot (θ : ℝ) (ζ : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * ζ

def PolynomialRadialAtSection : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Real.sqrt (Complex.normSq ζ - P.TT) : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def Transfer : Prop := SSn.Rep.ThtFacts → PolynomialRadialAtSection → PolyRadialS

def DatumConst : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ ζ₁ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ₁ →
      SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ = SSn.nu0' k r z z' (TheSec.theSection k r z z') ζ₁ ∧
      SSn.io0 k r z z' (TheSec.theSection k r z z') ζ = SSn.io0 k r z z' (TheSec.theSection k r z z') ζ₁

def KapLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), Gauge.GC.KapPt P Bs d Qr ∧
      ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf.comp (Qr ρ)

def FibStable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, ∀ ρ : M.Ty P,
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧
      (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ

def AlgSS : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜), d.Rel →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ Y : ℂ,
      d.κ (Pi.single ρ 1) * d.QQ Y 1 0 * d.κ (Pi.single π 1) = M.xEx P {l} π Y • (d.SS l * d.κ (Pi.single π 1))

def CorePoly : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ Y : ℂ, PSV P.TT (fun ζ =>
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y 1 0 ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def PhaseInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ θ : ℝ, ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (S (rot θ ζ) Xf) = c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) ∧
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ))
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec (rot θ ζ)) Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def PhaseExtract : Prop :=
  ∀ (TT : ℝ) (f : ℂ → ℂ), 0 < TT → PS TT f → (∀ θ : ℝ, ∀ ζ : ℂ, TT < Complex.normSq ζ → f (rot θ ζ) = f ζ) →
    ∃ (m : ℕ) (q : Polynomial ℂ), ∀ ζ : ℂ, TT < Complex.normSq ζ → gg TT ζ ^ m * f ζ = q.eval (sig TT ζ)

def TWNe : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ π ρ : M.Ty P, M.Up P l π ρ → ∀ ζ ∈ Gauge.GC.Ann P,
    ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf → Xf ≠ 0 →
      (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) ≠ 0

def PolynomialRadialAtSectionOfPhaseInvariance : Prop :=
  DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe → PolynomialRadialAtSection

def PolyRadialSOfCut : Prop :=
  SSn.Rep.ThtFacts → Transfer → DatumConst → KapLine → FibStable → AlgSS → CorePoly → PhaseInv → PhaseExtract → TWNe →
    PolyRadialS

theorem polynomialRadial_of_base (h0 : PolynomialRadialAtSectionOfPhaseInvariance) : PolyRadialSOfCut :=
  fun hT hTr hD hK hF hA hC hP hE hW => hTr hT (h0 hD hK hF hA hC hP hE hW)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_space_smoothness : RadSpSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Φ ρ
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
  have hz : inWb P.k P.r Bs.z := hpl.2.1
  have hz' : inWb P.k P.r Bs.z' := hpl.2.2.1
  set Qs := MA.Qset P.r P.TT with hQs
  have hζ : ∀ x ∈ Qs, Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq x.2 := by
    intro x hx
    rw [hT, hT']
    exact hx.2
  have hmZ : ContDiffOn ℝ ∞ (fun x : MA.E P.r => NF.muZ P.k P.r Bs.μsec x.2) Qs :=
    (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_contDiffOn Bs.sec).comp contDiff_snd.contDiffOn fun x hx => hζ x hx
  have hm : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) Qs :=
    contDiffOn_fst.prodMk hmZ
  have hGl : ∀ x ∈ Qs, NF.muZ P.k P.r Bs.μsec x.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec (hζ x hx))
  have hD : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' := fun x hx =>
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec (q := x) ⟨hx.1, hζ x hx⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := Φ.2.2.1 _ (hD x₀ hx₀)
    refine ⟨Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U,
      hm.continuousOn.isOpen_inter_preimage (MA.Qset_open P.r P.TT) hU, ⟨hx₀, hx₀U⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E P.r => F (x.1, NF.muZ P.k P.r Bs.μsec x.2))
        (Qs ∩ (Qs ∩ (fun x : MA.E P.r => (x.1, NF.muZ P.k P.r Bs.μsec x.2)) ⁻¹' U)) :=
      hF.comp (hm.mono fun x hx => hx.1) fun x hx => hx.2.2
    exact hc.congr fun x hx => hΦF _ hx.2.2 (hGl x hx.1)
  have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) Qs :=
    (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
  have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => ((wR P.k P.TT x.2 : ℝ) : ℂ)) Qs := by
    refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
    unfold wR
    refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
      fun x hx => ?_
    have h2 : P.TT < Complex.normSq x.2 := hx.2
    exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
  have hin : ContDiffOn ℝ ∞ (fun x : MA.E P.r =>
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jdc_thrW (o : ℕ) (A d : ℝ) (hd : 0 ≤ d)
    (h : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  unfold Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  rw [hn] at h
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) <
      12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by
    nlinarith [pow_nonneg hr 3, mul_nonneg hr (mul_nonneg hk hk), mul_nonneg (mul_nonneg hr hr) hk,
      mul_nonneg hr hr, mul_nonneg hr hk, mul_nonneg hk hk]
  have hpos : 0 < 12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  constructor <;> linarith

theorem jdc_om_sub_gpos (Db : B.RealPlaceData k r Wp Wq) : JF.Om k r Db.z Db.z' ⊆ B.GPos Db := by
  intro g hg
  unfold JF.Om Q.OmPlus at hg
  unfold B.GPos
  exact ⟨hg.1, hg.2.2⟩

theorem jdc_om_of (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (h : 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0) :
    g ∈ JF.Om k r z z' := by
  refine ⟨hg, ?_, h.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | h0
  · have e : l = ⟨0, by omega⟩ := Fin.ext h0
    rw [e]
    unfold Formalism.QuantumDeterminants.Dmin
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have e : l = ⟨((⟨l.val - 1, by omega⟩ : Fin r) : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact h.2 _

theorem jdc_of_om (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0 := by
  unfold JF.Om Q.OmPlus at hg
  obtain ⟨_, hD, hG⟩ := hg
  exact ⟨hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩

end gen

section gen2

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem jdc_ckOn_mono {m : ℕ∞} {UU VV : Set (B.Mat k r)} (h : UU ⊆ VV) {f : B.Mat k r → E₁} (hf : B.CkOn m VV f) :
    B.CkOn m UU f := by
  intro g₀ hg₀
  exact hf g₀ (h hg₀)

theorem jdc_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  unfold B.CkOn at *
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', hea⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hg₂, hΦ', heΦ⟩ := hΦ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have hr : ContDiffOn ℝ _ (fun g => (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ) (a' g)) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (ha'.mono Set.inter_subset_left)
    exact hr.clm_apply (hΦ'.mono Set.inter_subset_right)
  · intro g hg hgG
    simp only [hea g hg.1 hgG, heΦ g hg.2 hgG]

theorem jdc_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end gen2

section gen3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem jdc_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (jdc_ckOn_ap (h T (by simp)) (jdc_ckOn_Rw T.word_lie hJ))
      (jdc_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem jdc_ckOn_om (z z' : Fin (2 * r + k + 1) → ℂ) {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : Q.SmoothLev k r 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} J) :
    B.CkOn ⊤ (JF.Om k r z z') J := by
  unfold B.CkOn
  unfold Q.SmoothLev at hJ
  intro g₀ hg₀
  unfold JF.Om Q.OmPlus at hg₀
  obtain ⟨hgG, hD, hG⟩ := hg₀
  have hmem : g₀ ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    ⟨⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ g₀ hmem
  refine ⟨U, F, hU, hgU, hF, ?_⟩
  intro g hg hgV
  exact hJF g hg ⟨hgV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

variable [FiniteDimensional ℂ Wp]

theorem jdc_ffl (Db : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hSC : B.SmoothCoef (B.GPos Db) Θ)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (hH : ∀ g ∈ JF.Om k r Db.z Db.z', B.opApply Θ J g = B.JF Db H g) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := jdc_om_of _ _ hg₀.1.1 hg₀.2
    have hck := jdc_ckOn_opApply (jdc_ckOn_om Db.z Db.z' hJ.1) Θ
      (fun T hT => jdc_ckOn_mono (jdc_om_sub_gpos Db) (hSC T hT).1)
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hck g₀ hg₀O
    refine ⟨U ∩ Q.OmPlus k r Db.z Db.z', f', hU.inter (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _), ⟨hgU, hg₀O.2⟩,
      hc.mono Set.inter_subset_left, ?_⟩
    intro g hg hgG
    have hgO : g ∈ JF.Om k r Db.z Db.z' := ⟨hgG.1, hg.2⟩
    rw [← hH g hgO]
    exact he g hg.1 hgG.1
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

end gen3

theorem transfer_commutation_holds : JDJComm := by
  refine ⟨12, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d A hd hSC hC _hG hA F _hCk hCC hJF
  have hT := jdc_thrW (k := S.G.k) (r := S.G.r) (B.opOrder Θ) A d hd hA
  have hCOm : B.Commutes (T v).base (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') Θ :=
    fun p hp f' hf' g hg => hC p hp f' hf' g (jdc_om_sub_gpos _ hg)
  have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ (T v).base A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT (hCC _) hCOm
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨jdc_ffl (T v).base Θ hSC hJF _ hth, ?_⟩
  intro x hx
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  exact hth _ (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def rcAct {k p ρ : ℕ} (y : B.Mat k ρ) (x : U.RC k p ρ) : U.RC k p ρ := (fun v a => (y * Matrix.of x.1) v a, x.2)

def lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  U.wP σ * U.lowW σ v * (U.wP σ)⁻¹

def MMapEmbG : Prop := ∀ (k p ρ : ℕ) (Z : Matrix (Fin p) (Fin p) ℂ) (γ y₁ y₂ : B.Mat k ρ),
  U.mMap k p ρ Z (y₁ * γ * y₂) = U.embG k p ρ y₁ * U.mMap k p ρ Z γ * U.embG k p ρ y₂

def MMapLZU : Prop := ∀ (k p ρ : ℕ) (l Z u : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ), IsUnit l.det →
  U.mMap k p ρ (l * Z * u) γ = U.muP k p ρ (lᴴ)⁻¹ * U.mMap k p ρ Z γ * U.muP k p ρ u

def EmbGMuP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (q : Matrix (Fin p) (Fin p) ℂ),
  U.embG k p ρ y * U.muP k p ρ q = U.muP k p ρ q * U.embG k p ρ y

def EmbGRn : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (x : U.RC k p ρ), yᴴ * Hpk k ρ * y = Hpk k ρ →
  U.embG k p ρ y * U.Rn k p ρ x = U.Rn k p ρ (rcAct y x) * U.embG k p ρ y

def HeadHEq : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : U.LW σ → ℂ) (u : G.UT p → ℂ),
  U.headH σ d v u = lhOf σ v * U.hMat σ d * G.upper u ∧ G.IsLowerUni (lhOf σ v)

def ZjHZero : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0),
  U.ZjH σ d η Z = U.headH σ d η.2.1 η.2.2

def GaXiSplit : Prop := ∀ (k p ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
  (h ν h' ν' g : B.Mat k ρ), IsUnit h.det → IsUnit ν.det → h'ᴴ * Hpk k ρ * h' = Hpk k ρ →
  U.gaXi k ρ σ d ξ Z (h⁻¹ * ν⁻¹ * g * ν' * h') =
    (U.Rn k p ρ (-ξ.1.1) * U.muP k p ρ (lhOf σ ξ.2.2.1)ᴴ⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)) *
      U.mMap k p ρ (U.hMat σ d) g *
      (U.embG k p ρ ν' * U.muP k p ρ (G.upper ξ.2.2.2) * U.Rn k p ρ (rcAct h' ξ.1.2)) * U.embG k p ρ h'

def LeftMem : Prop := ∀ (k p ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.RC k p ρ) (l : Matrix (Fin p) (Fin p) ℂ)
  (h ν : B.Mat k ρ), inWb k ρ z → G.IsLowerUni l → h ∈ UWset k ρ z → ν ∈ Nset k ρ →
  U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹) ∈ Sset k (p + ρ) (liftVec k p ρ z)

def PsiRight : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (ν' : B.Mat k ρ) (u : G.UT p → ℂ)
  (x : U.RC k p ρ), inWb k ρ z' → ν' ∈ Nset k ρ →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.embG k p ρ ν' * U.muP k p ρ (G.upper u) * U.Rn k p ρ x) =
    psi k ρ z' cStd ν' * psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u)) *
      psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiRnAct : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (h' : B.Mat k ρ) (x : U.RC k p ρ),
  inWb k ρ z' → h' ∈ UWset k ρ z' →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ (rcAct h' x)) = psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiMuP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (u : G.UT p → ℂ), inWb k ρ z' →
  star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u))) = G.psi U.betaU (U.supS (G.upper u))

def MuNLeft : Prop := ∀ (k p ρ : ℕ),
  D.muN k (p + ρ) = ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))).map
    (fun x => Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1))

def RcActMP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ), ‖y.det‖ = 1 →
  MeasurePreserving (rcAct (p := p) y) (U.muRC k p ρ) (U.muRC k p ρ)

def RightMP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (μj : Measure (Mt k ρ)) (μ0' : Measure (Mt k (p + ρ))),
  B.IsHaarOn (UWset k ρ z') μj → μj Set.univ = 1 → μ0' = μj.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
  MeasurePreserving
    (fun y : (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ)) =>
      (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1,
        Matrix.of.symm (U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) *
          U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1))))
    ((μj.prod (D.muN k ρ)).prod ((U.muRC k p ρ).prod volume)) (μ0'.prod (D.muN k (p + ρ)))

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSplit
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
end
end

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def pairLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

variable {μ : Measure (Mt k r)} {i : Fin (r + 1)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem pairLev_swap (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairLev μ i Ψ Φ c = conj (pairLev μ i Φ Ψ c) := by
  unfold pairLev
  rw [← integral_conj]
  congr 1
  funext c'
  rw [pairAt_swap, map_mul, Complex.conj_ofReal]

theorem pairLev_smul_left (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i (a • Φ) Ψ c = a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_left]
  ring

theorem pairLev_zero_left (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairLev μ i 0 Ψ c = 0 := by
  unfold pairLev
  have h0 : ∀ c', pairAt μ (0 : RadSp k r z z' π π') Ψ c' = 0 := fun c' => by
    have := pairAt_smul_left μ (0 : RadSp k r z z' π π') Ψ c' 0
    rwa [zero_smul, zero_mul] at this
  simp [h0]

theorem act_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := U.sum_mem fun b _ => (hM a b).1 _ (hx b)

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end
