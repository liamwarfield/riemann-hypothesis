module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExh
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section eqv

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem psi_star_mul (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : B.Mat k r) :
    star (psi k r z c x) * psi k r z c x = 1 := by
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (Complex.I * (((c * ell k r z x).re : ℝ) : ℂ)) +
      Complex.I * (((c * ell k r z x).re : ℝ) : ℂ) = 0 := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [h, Complex.exp_zero]

def oneP : B.SS k r := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), (1 : B.Mat k r)))

theorem oneP_inSS (D : B.RealPlaceData k r Wp Wq) : D.inSS oneP :=
  ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one⟩

theorem sgs_oneP (g : B.Mat k r) : B.sgs oneP g = g := by
  show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * g * 1 * 1 = g
  simp

theorem eqv_of_FFl (D : B.RealPlaceData k r Wp Wq) (X : B.Mat k r → (Wq →L[ℂ] Wp))
    (hX : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z'))
    {p : B.SS k r} (hp : D.inSS p) {y : B.Mat k r} (hy : y ∈ JF.Om k r D.z D.z') :
    JF.xiP D p • B.rho D p X y = X y := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hnN : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv h2
  have mem : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hg.1, hg.2⟩
  have nlev : ∀ m ∈ Nset k r, m ∈ Q.Nlev k r 0 := fun m hm => ⟨hm, (Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 m).2 hm.1⟩
  have hyn : y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), (1 : B.Mat k r)), ((1 : B.Mat k r), p.2.2)) y =
        y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (1 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  have hnyn : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) ∈ JF.Om k r D.z D.z' := by
    have := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D (p := (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)))
      ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h2, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, h4⟩ hy
    have e : B.sgs (((1 : B.Mat k r), p.1.2), ((1 : B.Mat k r), p.2.2)) y =
        (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) := by
      show (1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) * 1 = _
      simp
    rwa [e] at this
  obtain ⟨_, hL, hR, hU⟩ := hX
  have e1 : X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) =
      (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) • X y := by
    rw [Matrix.mul_assoc, hL _ (mem _ hyn) _ (nlev _ hnN), hR _ (mem _ hy) _ (nlev _ h4), smul_smul]
  have e2 : X ((Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r)) *
      (Matrix.of p.2.1 : B.Mat k r)) =
      (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹).comp ((X ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
        (Matrix.of p.2.2 : B.Mat k r))).comp (D.π' (Matrix.of p.2.1 : B.Mat k r))) :=
    hU _ (mem _ hnyn) _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3
  have hsgs : B.sgs p y = (Matrix.of p.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * y *
      (Matrix.of p.2.2 : B.Mat k r)) * (Matrix.of p.2.1 : B.Mat k r) := by
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * y * (Matrix.of p.2.2 : B.Mat k r) *
      (Matrix.of p.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  have hπ : ∀ w, D.π (Matrix.of p.1.1 : B.Mat k r) (D.π (Matrix.of p.1.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π_rep.2 _ h1 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1)
    rw [Matrix.mul_nonsing_inv _ hu1, D.π_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hπ' : ∀ w, D.π' (Matrix.of p.2.1 : B.Mat k r) (D.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹ w) = w := by
    intro w
    have := D.π'_rep.2 _ h3 _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h3)
    rw [Matrix.mul_nonsing_inv _ hu3, D.π'_rep.1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]; rfl
  have hc : JF.xiP D p * (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ *
      psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) = 1 := by
    unfold JF.xiP
    have a1 := BesselUnipotentEquiv.star_psi_inv D.z cStd D.z_mem _ h2
    have a2 := psi_star_mul D.z cStd ((Matrix.of p.1.2 : B.Mat k r)⁻¹)
    have a3 := psi_star_mul D.z' cStd (Matrix.of p.2.2 : B.Mat k r)
    rw [a1] at a2
    calc psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) *
          (psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r))
        = (psi k r D.z cStd (Matrix.of p.1.2) * psi k r D.z cStd (Matrix.of p.1.2 : B.Mat k r)⁻¹) *
          (star (psi k r D.z' cStd (Matrix.of p.2.2)) * psi k r D.z' cStd (Matrix.of p.2.2 : B.Mat k r)) := by ring
      _ = 1 := by rw [a2, a3, one_mul]
  unfold B.rho
  rw [hsgs, e2, e1]
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, hπ', hπ, smul_smul, hc, one_smul]

end eqv

theorem sAExh_of_avgCutoff (hA : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff) : SAExh := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v X hX Cs hCs hCsQ
  set Db := (T v).base with hDb
  have hplace : Q.IsPlace (D.parOf S v) Db.z Db.z' Db.π Db.π' := (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hX' : X ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (Q.OmPlus S.G.k S.G.r Db.z Db.z') := by
    have := hX
    unfold smoothFormsPositiveCone at this
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v] at this
  obtain ⟨K', hK'c, hCsK', hK'Q⟩ := exists_compact_between hCs (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open Db.z Db.z')
    (fun x hx => hQ x (hCsQ hx))
  obtain ⟨φ, hφ, ⟨C, hCc, hCO, hCφ⟩, hint⟩ := hA S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C := by
    refine closure_minimal (fun g hg => ?_) hCc.isClosed
    by_contra hgC
    exact hg (by simp [hCφ g hgC])
  refine ⟨fun g => φ g • X g, interior K', isOpen_interior, hCsK', ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus S.G.k S.G.r Db.z Db.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨Cᶜ, fun _ => 0, hCc.isClosed.isOpen_compl, fun h => hO (hCO h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hCφ g hg]
  · exact hCc.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
    exact fun g hg => (hCO (hsuppC hg)).2
  · intro y hy
    have hgy : B.gq Db y ∈ JF.Om S.G.k S.G.r Db.z Db.z' :=
      Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db y (hQ y hy)
    have hJ : B.JF Db (fun g => φ g • X g) (B.gq Db y) =
        (∫ p, φ (B.sgs p (B.gq Db y)) ∂Db.μSS) • X (B.gq Db y) := by
      change ∫ p, JF.xiP Db p • B.rho Db p (fun g => φ g • X g) (B.gq Db y) ∂Db.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Db] with p hp
      have hr : B.rho Db p (fun g => φ g • X g) (B.gq Db y) =
          φ (B.sgs p (B.gq Db y)) • B.rho Db p X (B.gq Db y) := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, eqv_of_FFl Db X hX' hp hgy]
    refine ⟨fun hyU => ?_, fun h0 => ?_⟩
    · have h1 := hint oneP (oneP_inSS Db) y (interior_subset hyU)
      simp only [sgs_oneP] at h1
      rw [hJ, h1, one_smul]
    · rw [hJ, h0, smul_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ACProper : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (C C' : Set (B.Mat k r)),
    IsCompact C → IsCompact C' → C' ⊆ JF.Om k r D.z D.z' →
    ∃ P : Set (B.SS k r), IsCompact P ∧ ∀ p, D.inSS p → ∀ g ∈ C', B.sgs p g ∈ C → p ∈ P

def ACBump : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ JF.QDom k r D.z D.z' →
    ∃ φ₀ : B.Mat k r → ℝ, ContDiff ℝ ∞ φ₀ ∧ (∀ g, 0 ≤ φ₀ g) ∧ HasCompactSupport φ₀ ∧
      tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' ∧ ∀ q ∈ K, 0 < φ₀ (B.gq D q)

def ACInv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ →
    ∀ p₀, D.inSS p₀ → ∀ g : B.Mat k r, ∫ p, φ₀ (B.sgs p (B.sgs p₀ g)) ∂D.μSS = ∫ p, φ₀ (B.sgs p g) ∂D.μSS

def ACInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ), Continuous φ₀ → HasCompactSupport φ₀ →
    ∀ g ∈ JF.Om k r D.z D.z', Integrable (fun p => φ₀ (B.sgs p g)) D.μSS

def ACHaarPos : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (O : Set (B.SS k r)), IsOpen O → oneP ∈ O → 0 < D.μSS O

def ACSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (φ₀ : B.Mat k r → ℝ),
    ContDiff ℝ ∞ φ₀ → HasCompactSupport φ₀ → tsupport φ₀ ⊆ Q.OmPlus k r D.z D.z' →
    ∀ g₀ ∈ JF.Om k r D.z D.z', ∃ (U : Set (B.Mat k r)) (I' : B.Mat k r → ℝ), IsOpen U ∧ g₀ ∈ U ∧
      ContDiffOn ℝ ∞ I' U ∧ ∀ g ∈ U, g ∈ B.GV k r → ∫ p, φ₀ (B.sgs p g) ∂D.μSS = I' g

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def FormOne : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev P0 j).k (JC.parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π')) (JC.parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    KB.ZetaNorm (T.bs j) μ →
    ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) →
        Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, JC.NiceCoef (T.bs j) ε (F a)) → (∀ a, JC.NiceCoef (T.bs j) ε (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0

def ZetaNormExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq), ∃ μ : Measure (Mt k r), KB.ZetaNorm Bs μ

theorem integrable_of_decay4 {φ : ℂ → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) : Integrable φ := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine Integrable.mono' (hd.const_mul C) hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have e : (1 + ‖t‖) ^ (-4 : ℤ) = (1 + ‖t‖) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [← e]; exact hC t

theorem nice_common {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq)
    {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ a, KB.CptCoef Bs (x a)) :
    ∃ ε, 0 < ε ∧ ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  choose R hR using fun a => (h a).2.1
  choose εf hεf0 hεf using fun a => (h a).2.2
  let Sε : Finset ℝ := insert 1 (Finset.univ.image εf)
  have hne : Sε.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨Sε.min' hne, ?_, fun a => ⟨(h a).1, fun A m => ?_, fun g hg hg0 => ?_⟩⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεf0 a
  · refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (h a).1 (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (R a)) (fun g hg hgC => ?_) A m
    by_contra h0
    exact hgC (hR a g hg h0)
  · exact le_trans (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
      (hεf a g hg hg0)

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section consts

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_const (a : E) : ∀ v : List (B.Mat k r),
    B.Rw v (fun _ => a) = (fun _ => a) ∨ B.Rw v (fun _ => a) = (fun _ => (0 : E))
  | [] => Or.inl rfl
  | X :: v => by
    right
    funext g
    simp only [B.Rw, List.foldr_cons]
    rcases rw_const a v with h | h
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]
    · simp only [B.Rw] at h
      rw [h]; simp [RdV]

theorem dLR_const (a : E) (u v : List (B.Mat k r)) :
    B.dLR u v (fun _ => a) = (fun _ => a) ∨ B.dLR u v (fun _ => a) = (fun _ => (0 : E)) := by
  induction u with
  | nil => exact rw_const a v
  | cons X u ih =>
    right
    simp only [Formalism.FourierDecayAlt.B.dLR, List.foldr_cons] at ih ⊢
    rcases ih with h | h <;> (rw [h]; funext g; simp [Formalism.FourierDecayAlt.B.LdV])

theorem norm_dLR_const_le (a : E) (u v : List (B.Mat k r)) (g : B.Mat k r) : ‖B.dLR u v (fun _ => a) g‖ ≤ ‖a‖ := by
  rcases dLR_const a u v with h | h <;> simp [h]

theorem ckOn_const' {m : ℕ∞} {UU : Set (B.Mat k r)} (a : E) : B.CkOn m UU (fun _ => a) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => a, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

end consts

theorem mem_capOp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (s : ℂ)
    (Lw : List (ℂ × List (B.Mat k r))) {T : B.DTerm k r Wp Wq} (hT : T ∈ TLB.capOp k r Wp Wq s Lw) :
    ∃ (c : ℂ) (w : List (B.Mat k r)), T = TLB.cTerm c w := by
  unfold TLB.capOp at hT
  rcases List.mem_cons.1 hT with h | h
  · exact ⟨0, _, h⟩
  · obtain ⟨cw, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, _, rfl⟩

theorem capacity_theta_facts : CapThFacts := by
  intro k r Wp Wq _ _ _ _ _ _ D s Y ε m
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw h X hX => ((hLw cw h).1 X hX).1
  have hlen : ∀ cw ∈ capLw k r Y, cw.2.length ≤ 2 * r + k + 1 := fun cw h => (hLw cw h).2
  have hord : B.opOrder (capTh k r Wp Wq s Y) = 2 * r + k + 1 := TLB.opOrder_capOp s _ hlen
  have hApp : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GV k r, B.opApply (capTh k r Wp Wq s Y) F g = s • Q.CV k r Y F g := by
    intro F hF g hg
    unfold capTh
    rw [TLB.opApply_capOp s _ hLie, hCV _ _ F hF g hg hg]
    rfl
  refine ⟨hord, ?_, ?_, ?_, hApp⟩
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  · intro p hp f hf g hg
    rw [hord] at hf
    have hgG : g ∈ B.GV k r := hg.1
    have hs' := Formalism.FourierDecayAlt.P.B7.sgs_mem D hp hgG
    rw [hApp _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) g hgG,
      Formalism.FourierDecayAlt.P.capelli_rho_commute k r Wp Wq D Y f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp s _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v _ _ _ g _ _ => ?_⟩
    rw [Real.rpow_zero, mul_one]
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩

theorem beta_form_congr_holds : BetaCongr := by
  intro k r Wp Wq _ _ _ _ _ _ D F F₁ F' F₁' hF hF'
  unfold B.beta
  refine Formalism.FourierDecayAlt.P.JFxG.betaBig_congr D (fun g hg => ?_) (fun g hg => ?_)
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := F₁) (a := 1) (fun g hg => by rw [one_smul, hF g hg]) hg.1
    rw [h, one_smul]
  · have h := Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F') (F' := F₁') (a := 1) (fun g hg => by rw [one_smul, hF' g hg]) hg.1
    rw [h, one_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def JDHatOpQQ : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDecayTrQQd : Prop :=
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

theorem jDecayTrQQd_of_leaves (h1 : JDHatBdd) (h2 : JDHatOpQQ) (h3 : JDJComm) (h4 : JDCCLower) (h5 : TransferSquareIntegrable)
    (h6 : BoundedOperatorsSquareIntegrable) : JDecayTrQQd := by
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C5, H5⟩ := h5
  unfold JDecayTrQQd
  refine ⟨8 * C2 + |C3| + |C5|, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL hJf
  have hmono : ∀ c, c ≤ 8 * C2 + |C3| + |C5| → BuiltOW c S T f χ ν' m₀ top A₀ := fun c hc =>
    ⟨isBuiltPlace_mono hc hB.1, hB.2⟩
  have hB2 := hmono C2 (by linarith [abs_nonneg C3, abs_nonneg C5])
  have hB3 := hmono C3 (by linarith [le_abs_self C3, abs_nonneg C5])
  have hB5 := hmono C5 (by linarith [le_abs_self C5, abs_nonneg C3])
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hInCC : ∀ m : ℕ, B.InCC A₀ m (f v) := (hB.1.2.2.2.1.2 v).2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hCk, -, hA, -⟩ := hB.1

  have hR : (0 : ℝ) ≤ (S.G.r : ℝ) := Nat.cast_nonneg _
  have hnE : nDim S.G.k S.G.r = 2 * (S.G.r : ℝ) + S.G.k + 1 := by unfold nDim; push_cast; ring
  have hn : (1 : ℝ) ≤ nDim S.G.k S.G.r := by
    rw [hnE]; have := Nat.cast_nonneg (α := ℝ) S.G.k; linarith
  have hA' : (8 * C2 + |C3| + |C5|) * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * nDim S.G.k S.G.r ^ 2 + nDim S.G.k S.G.r ^ 3) ≤ A₀ := by rw [hnE]; exact hA
  obtain ⟨hK3', hK5'⟩ := jd_arith C2 C3 C5 _ _ _ A₀ hC2 hR hn (Nat.cast_nonneg _) hA'
  have hdm0 : 0 ≤ C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
    have := le_trans zero_le_one hn; positivity
  have hK3 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 1 → ∀ o : ℝ, o ≤ C2 * nDim S.G.k S.G.r →
      C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * o +
      C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi o ho
    refine hK3' _ _ ?_ ho
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith
  have hK5 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 2 → C5 * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤
      A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi
    refine hK5' _ ?_
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 2 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith

  let Good : ℕ → (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → Prop := fun i F =>
    B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ (∀ m : ℕ, B.InCC (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) m F) ∧
      B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  let tr : (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → M.Ty (D.parOf S v) →
      MA.SmQ (D.parOf S v).r (D.parOf S v).TT := fun F => trJ S T v e (B.JF (T v).base F)
  have hStep : ∀ i, i < 2 * S.Ntop + 2 → ∀ F, Good i F → ∀ X ∈ MA.hatSet (D.parOf S v) L,
      ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good (i + 1) t.2) ∧
        MA.actA (D.parOf S v) X (tr F) = (ts.map fun t => MA.actA (D.parOf S v) t.1 (tr t.2)).sum := by
    intro i hi F hF X hX
    obtain ⟨hCkF, hCCF, hFF⟩ := hF
    obtain ⟨ts, hts, hid⟩ := H2 E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e L hFr hGa hQQ hL X hX
    have hthr : ∀ t ∈ ts, C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder t.2 : ℝ) +
        C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) :=
      fun t ht => hK3 i (by omega) _ (hts t ht).2.2.2.2
    have l3 : ∀ t ∈ ts, _ := fun t ht =>
      H3 E Wp Wq S T f χ ν' m₀ top A₀ hB3 v t.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0
        (hts t ht).2.1 (hts t ht).2.2.1 (hts t ht).2.2.2.1 (hthr t ht) F hCkF hCCF hFF
    refine ⟨ts.map fun t => (t.1, B.opApply t.2 F), ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
      have l4 := h4 _ _ _ _ t0.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0 (hts t0 ht0).2.2.2.1 F hCkF hCCF
      refine ⟨(hts t0 ht0).1, l4.1, fun m => ?_, (l3 t0 ht0).1⟩
      have e : A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) - (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) = A₀ - ((i + 1 : ℕ) : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by push_cast; ring
      rw [← e]; exact l4.2 m
    · rw [hid (B.JF (T v).base F) hFF, List.map_map]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      simp only [Function.comp]
      congr 1
      exact trJ_congr S T v e _ _ (l3 t ht).2
  intro w hw hwh π
  have hG0 : Good 0 (f v) := ⟨hCk v, fun m => by simpa using hInCC m, hJf⟩
  have hmem := jd_word_span L Good tr (2 * S.Ntop + 2) (h1 _ L hTTpos.le hL) hStep w hw hwh (f v) hG0
  have hgen : ∀ u ∈ {u | ∃ b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L), ∃ F', Good w.length F' ∧
      u = MA.actA (D.parOf S v) b (tr F')}, componentwiseL2 (D.parOf S v) u := by
    rintro u ⟨b, hb, F', ⟨hCk', hCC', hFF'⟩, rfl⟩
    have l5 := H5 E Wp Wq S T f χ ν' m₀ top A₀ hB5 v e hFr (A₀ - (w.length : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) (hK5 _ hw) F' hCk' hCC' hFF'
    exact (componentwiseL2_iff_integrable _ _).2 (h6 _ L hTTpos hL b hb _ l5)
  exact (componentwiseL2_iff_integrable _ _).1 (componentwiseL2_of_span _ _ hgen _ hmem) π

theorem jDecayTrQQd_of_open (h2 : JDHatOpQQ) : JDecayTrQQd :=
  jDecayTrQQd_of_leaves hat_bounded_decay_holds h2 transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

def gramH (h : α → H) : α → α → ℂ := fun P Q => ⟪h Q, h P⟫_ℂ

theorem qf_gramH (Y : Finset α) (h : α → H) (c : α → ℂ) :
    PBA.qf Y (gramH h) c = ⟪∑ P ∈ Y, conj (c P) • h P, ∑ P ∈ Y, conj (c P) • h P⟫_ℂ := by
  unfold PBA.qf gramH
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring

theorem psd_gramH (Y : Finset α) (h : α → H) : TB.PSDOn Y (gramH h) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun P _ Q _ => (inner_conj_symm (𝕜 := ℂ) (h P) (h Q)).symm, fun c => ?_⟩
  rw [qf_gramH]
  exact inner_self_nonneg (𝕜 := ℂ)

def Loe (Y : Finset α) (A B : α → α → ℂ) : Prop := TB.PSDOn Y fun P Q => B P Q - A P Q

theorem loe_iff (Y : Finset α) (A B : α → α → ℂ) :
    Loe Y A B ↔ (∀ x ∈ Y, ∀ y ∈ Y, B y x - A y x = conj (B x y - A x y)) ∧
      ∀ c, (PBA.qf Y A c).re ≤ (PBA.qf Y B c).re := by
  unfold Loe
  rw [PBA.psd_iff_qf]
  have e : ∀ c, PBA.qf Y (fun P Q => B P Q - A P Q) c = PBA.qf Y B c - PBA.qf Y A c := by
    intro c; unfold PBA.qf; simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  simp only [e, Complex.sub_re, sub_nonneg]

theorem loe_trans {Y : Finset α} {A B C : α → α → ℂ} (h1 : Loe Y A B) (h2 : Loe Y B C) : Loe Y A C := by
  rw [loe_iff] at h1 h2 ⊢
  refine ⟨fun x hx y hy => ?_, fun c => (h1.2 c).trans (h2.2 c)⟩
  have a := h1.1 x hx y hy
  have b := h2.1 x hx y hy
  have : C y x - A y x = (C y x - B y x) + (B y x - A y x) := by ring
  rw [this, a, b, ← map_add (f := _)]; ring_nf

theorem loe_zero_of_psd {Y : Finset α} {B : α → α → ℂ} (h : TB.PSDOn Y B) : Loe Y (fun _ _ => 0) B := by
  unfold Loe; simpa using h

theorem psd_of_loe_zero {Y : Finset α} {B : α → α → ℂ} (h : Loe Y (fun _ _ => 0) B) : TB.PSDOn Y B := by
  unfold Loe at h; simpa using h

theorem qf_mix {N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ) (c : α → ℂ) :
    PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c = (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
  unfold PBA.qf
  have e' : ∀ x y, conj (c x) * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n x y) * c y =
      ∑ n, (M : ℂ) * ((θ n : ℂ) * (conj (c x) * A n x y * c y)) := by
    intro x y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [e']
  rw [swap3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

theorem norm_mix_sq {N : Type} [Fintype N] (lam : N → ℂ) (W : N → H) :
    ‖∑ n, lam n • W n‖ ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
  have h1 : ‖∑ n, lam n • W n‖ ≤ ∑ n, ‖lam n‖ * ‖W n‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_smul _ _).le)
  have h2 : (∑ n, ‖lam n‖ * ‖W n‖) ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt ‖lam n‖)
      (fun n => Real.sqrt ‖lam n‖ * ‖W n‖)
    have e1 : ∀ n, Real.sqrt ‖lam n‖ * (Real.sqrt ‖lam n‖ * ‖W n‖) = ‖lam n‖ * ‖W n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ n, Real.sqrt ‖lam n‖ ^ 2 = ‖lam n‖ := fun n => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ n, (Real.sqrt ‖lam n‖ * ‖W n‖) ^ 2 = ‖lam n‖ * ‖W n‖ ^ 2 := fun n => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem loe_convex {N : Type} [Fintype N] (Y : Finset α) (lam : N → ℂ) (h : N → α → H) :
    Loe Y (gramH fun P => ∑ n, lam n • h n P)
      (fun P Q => ((∑ n, ‖lam n‖ : ℝ) : ℂ) * ∑ n, ((‖lam n‖ : ℝ) : ℂ) * gramH (h n) P Q) := by
  rw [loe_iff]
  constructor
  · intro x _ y _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramH, map_sub, map_mul, map_sum, Complex.conj_ofReal, inner_conj_symm]
  · intro c
    have eW : ∑ P ∈ Y, conj (c P) • ∑ n, lam n • h n P = ∑ n, lam n • ∑ P ∈ Y, conj (c P) • h n P := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun P _ => by rw [mul_comm]
    rw [qf_gramH, eW, qf_mix]
    simp only [qf_gramH]
    have hre : ∀ x : H, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x; simpa using this
    rw [Complex.re_ofReal_mul, Complex.re_sum, hre]
    simp only [Complex.re_ofReal_mul, hre]
    exact norm_mix_sq lam _

theorem loe_congr {Y : Finset α} {A A' B B' : α → α → ℂ} (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' x y)
    (hB : ∀ x ∈ Y, ∀ y ∈ Y, B x y = B' x y) (h : Loe Y A B) : Loe Y A' B' :=
  psd_congr (fun x hx y hy => by rw [hA x hx y hy, hB x hx y hy]) h

theorem loe_refl (Y : Finset α) (A : α → α → ℂ) : Loe Y A A := by
  unfold Loe
  refine psd_congr (k := fun _ _ => (0 : ℂ)) (fun x _ y _ => by ring) ?_
  rw [PBA.psd_iff_qf]; exact ⟨fun _ _ _ _ => by simp, fun c => by simp [PBA.qf]⟩

theorem loe_add {Y : Finset α} {A B A' B' : α → α → ℂ} (h : Loe Y A B) (h' : Loe Y A' B') :
    Loe Y (fun x y => A x y + A' x y) (fun x y => B x y + B' x y) := by
  rw [loe_iff] at h h' ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy; have b := h'.1 x hx y hy
    have : B y x + B' y x - (A y x + A' y x) = (B y x - A y x) + (B' y x - A' y x) := by ring
    rw [this, a, b, ← map_add (f := _)]; ring_nf
  · have e : ∀ K K' : α → α → ℂ, PBA.qf Y (fun x y => K x y + K' x y) c = PBA.qf Y K c + PBA.qf Y K' c := by
      intro K K'; unfold PBA.qf; simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.add_re, Complex.add_re]
    linarith [h.2 c, h'.2 c]

theorem loe_smul {Y : Finset α} {A B : α → α → ℂ} (r : ℝ) (hr : 0 ≤ r) (h : Loe Y A B) :
    Loe Y (fun x y => (r : ℂ) * A x y) (fun x y => (r : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    rw [← mul_sub, ← mul_sub, a, map_mul, Complex.conj_ofReal]
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (r : ℂ) * K x y) c = (r : ℂ) * PBA.qf Y K c := by
      intro K; unfold PBA.qf; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (h.2 c) hr

theorem loe_sum {ι : Type} (s : Finset ι) {Y : Finset α} {A B : ι → α → α → ℂ} (h : ∀ i ∈ s, Loe Y (A i) (B i)) :
    Loe Y (fun x y => ∑ i ∈ s, A i x y) (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loe_refl Y (fun _ _ => (0 : ℂ))
  | insert b t hb ih =>
    have h1 := loe_add (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine loe_congr (fun x _ y _ => ?_) (fun x _ y _ => ?_) h1
    · rw [Finset.sum_insert hb]
    · rw [Finset.sum_insert hb]

theorem loe_diag {Y : Finset α} {A B : α → α → ℂ} (ω : α → ℝ) (h : Loe Y A B) :
    Loe Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * A x y) (fun x y => (ω x : ℂ) * (ω y : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    have : (ω y : ℂ) * (ω x : ℂ) * B y x - (ω y : ℂ) * (ω x : ℂ) * A y x = (ω y : ℂ) * (ω x : ℂ) * (B y x - A y x) := by
      ring
    rw [this, a]; simp only [map_mul, map_sub, Complex.conj_ofReal]; ring
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * K x y) c =
        PBA.qf Y K (fun x => (ω x : ℂ) * c x) := by
      intro K; unfold PBA.qf
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e, e]
    exact h.2 _

theorem loe_scale {Y : Finset α} {K : α → α → ℂ} (hK : TB.PSDOn Y K) {r r' : ℝ} (hr : 0 ≤ r' - r) :
    Loe Y (fun x y => (r : ℂ) * K x y) (fun x y => (r' : ℂ) * K x y) := by
  have h := loe_smul (r' - r) hr (loe_zero_of_psd hK)
  unfold Loe at h ⊢
  refine psd_congr (fun x _ y _ => ?_) h
  push_cast; ring

theorem gramH_smul (c : ℂ) (h : α → H) :
    gramH (fun P => c • h P) = fun P Q => ((‖c‖ ^ 2 : ℝ) : ℂ) * gramH h P Q := by
  funext P Q
  unfold gramH
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  push_cast; ring

end gram

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CapAdjInt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s Y : ℂ) (μ : Measure (Mt k r)),
    B.IsHaarOn (B.GV k r) μ → ∀ φ ψ : B.Mat k r → (Wq →L[ℂ] Wp),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
    (∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) ∂μ

def CapAdjFromInt : Prop := CapAdjInt → CapAdj

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniOfCore
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniReduction

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leftFubini_of_core (hC : LeftFubiniLemmas.CoreLF) : LeftFubiniLemmas.LeftFubini := by
  intro k r Wp Wq _ _ _ _ _ _ T hT j hj hj1 a ha
  obtain ⟨hab, rfl⟩ := ha
  have e : D.ptSize a + (r - D.ptSize a) = r := by omega
  have hd : ∀ q, D.ptDiag a q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hab q q.2
  obtain ⟨X, hX, μ, ℓ, sx, hsx, hmain⟩ := hC k (D.ptSize a) (r - D.ptSize a) r e hj1 (D.ptPerm a) (D.ptDiag a) hd
    Wp Wq (T.bs (D.ptSize a)) T.base (T.z_lev _ hj) (T.z'_lev _ hj) (T.π'_lev _ hj) (hT _ hj).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' T hT _ hj e) (hT _ hj).2.2 (hT 0 (Nat.zero_le r)).2.2
  refine ⟨X, hX, μ, ℓ, sx, hsx, fun g hg H hH hR => ?_⟩
  have hx : ∀ (h1 : D.ptSize a ≤ r) (h2 : r - D.ptSize a = r - D.ptSize a),
      LeftFubiniLemmas.levelZeroPointOver a h1 (D.castM h2 g) = D.castM e (U.mMap k (D.ptSize a) (r - D.ptSize a)
        (U.hMat (D.ptPerm a) (D.ptDiag a)) g) := by
    intro h1 h2
    unfold LeftFubiniLemmas.levelZeroPointOver
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hs : ∀ h2 : r - D.ptSize a = r - D.ptSize a,
      D.castF h2 (D.sliceAt k r T.base.z T.base.z' H a) =
        U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm T.base.z)
          (D.castV e.symm T.base.z') (D.castF e H) (fun a => a.elim0) := by
    intro h2
    funext y
    unfold D.castF
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dite_eq_left hj]
    rfl
  simp only [hx, hs]
  exact hmain g hg H hH hR

end Formalism.FourierDecayAlt.P.LeftFubiniReduction
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERHaarPos
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

theorem haar_open_pos {k r : ℕ} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (B.GV k r) μ) {O : Set (Mt k r)}
    (hO : IsOpen O) {g₀ : Mt k r} (hg₀ : Matrix.of g₀ ∈ B.GV k r) (hg₀O : g₀ ∈ O) : μ O ≠ 0 := by
  intro h0
  have hnull : ∀ b ∈ B.GV k r, μ (lmulM (k := k) (r := r) b ⁻¹' O) = 0 := by
    intro b hb
    have hm : Measurable (lmulM (k := k) (r := r) b) := (BesselUnitaryEquiv.continuous_lmulM b).measurable
    rw [← Measure.map_apply hm hO.measurableSet, hμ.left b hb, h0]
  let U : {b : B.Mat k r // b ∈ B.GV k r} → Set (Mt k r) := fun b => lmulM (k := k) (r := r) b.1 ⁻¹' O
  have hUo : ∀ i, IsOpen (U i) := fun i => hO.preimage (BesselUnitaryEquiv.continuous_lmulM i.1)
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hcov : {x : Mt k r | Matrix.of x ∈ B.GV k r} ⊆ ⋃ i, U i := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨Matrix.of g₀ * (Matrix.of x)⁻¹,
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hg₀ (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem hx)⟩, ?_⟩
    have hx' : Matrix.of x ∈ B.GV k r := hx
    have e : lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x = g₀ := by
      unfold lmulM
      rw [mul_assoc, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hx').2, mul_one]
      rfl
    show lmulM (k := k) (r := r) (Matrix.of g₀ * (Matrix.of x)⁻¹) x ∈ O
    rw [e]
    exact hg₀O
  have hGV0 : μ {x : Mt k r | Matrix.of x ∈ B.GV k r} = 0 := by
    refine measure_mono_null (hcov.trans hT.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun i _ => hnull i.1 i.2
  have hsub : (Set.univ : Set (Mt k r)) ⊆ {x : Mt k r | Matrix.of x ∈ B.GV k r} ∪ (B.GV k r)ᶜ := by
    intro x _
    by_cases hx : Matrix.of x ∈ B.GV k r
    · exact Or.inl hx
    · exact Or.inr hx
  have huniv : μ Set.univ = 0 := measure_mono_null hsub (measure_union_null hGV0 hμ.conc)
  exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

end Formalism.FourierDecayAlt.P.CutMP.ER
end
