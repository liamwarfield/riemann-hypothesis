module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLIsoAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
namespace Formalism.FourierDecayAlt.P.PBI

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

noncomputable section

section unit

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inner_map_of_norm (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖) (v v' : Wp) :
    inner ℂ (A v) (A v') = inner ℂ v v' := (LinearMap.norm_map_iff_inner_map_map A).1 hA v v'

theorem hsInner_comp_left [FiniteDimensional ℂ Wq] (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (U V : Wq →L[ℂ] Wp) : B.hsInner (A.comp U) (A.comp V) = B.hsInner U V := by
  simp only [Formalism.FourierDecayAlt.P.Topx1.hsInner_eq, ContinuousLinearMap.comp_apply, inner_map_of_norm A hA]

theorem sum_inner_onb [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ Wq) (U V : Wq →L[ℂ] Wp) :
    ∑ i, inner ℂ (V (b i)) (U (b i)) =
      LinearMap.trace ℂ Wq ((ContinuousLinearMap.adjoint V).comp U).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsInner_comp_right [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bm : Wq →L[ℂ] Wq)
    (hB : ∀ v, ‖Bm v‖ = ‖v‖) (U V : Wq →L[ℂ] Wp) :
    B.hsInner (U.comp Bm) (V.comp Bm) = B.hsInner U V := by
  let e : Wq ≃ₗᵢ[ℂ] Wq := LinearIsometry.toLinearIsometryEquiv ⟨Bm.toLinearMap, hB⟩ rfl
  let b := stdOrthonormalBasis ℂ Wq
  have h1 : B.hsInner (U.comp Bm) (V.comp Bm) = ∑ i, inner ℂ (V ((b.map e) i)) (U ((b.map e) i)) := by
    rw [Formalism.FourierDecayAlt.P.Topx1.hsInner_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b, e, OrthonormalBasis.map_apply]
  rw [h1, sum_inner_onb, ← sum_inner_onb b, ← Formalism.FourierDecayAlt.P.Topx1.hsInner_eq]

end unit

section lev0

theorem unipotent_level_zero_eq_one {k r' : ℕ} (hr : r' = 0) (m : B.Mat k r') (hm : m ∈ Nset k r') : m = 1 := by
  subst hr
  ext i j
  have hj := j.isLt
  have := hm.2.2 i j (by omega) (by omega) (by omega)
  simpa [Matrix.one_apply] using this

theorem zetaL_eq_zhat {k r' : ℕ} (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    Q.zetaL k r' z z' (Fin.last r') g = Zhat k r' z z' g (Fin.last r') (Fin.last r') := by
  simp only [Q.zetaL, Zhat]

theorem corner_matrix_level_zero_eq {k r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g g' : B.Mat k r')
    (h : Q.zetaL k r' z z' (Fin.last r') g = Q.zetaL k r' z z' (Fin.last r') g') :
    Zhat k r' z z' g = Zhat k r' z z' g' := by
  subst hr
  ext a b
  have ha : a = Fin.last 0 := Fin.ext (by have := a.isLt; first | simp | omega)
  have hb : b = Fin.last 0 := Fin.ext (by have := b.isLt; first | simp | omega)
  subst ha hb
  rw [← zetaL_eq_zhat, ← zetaL_eq_zhat, h]

theorem gram_function_level_zero {k r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    Gf k r' z z' g = Complex.normSq (Q.zetaL k r' z z' (Fin.last r') g) - Tz k r' z * Tz k r' z' := by
  subst hr
  rw [gf_eq_gPoly k 0 z z' g, zetaL_eq_zhat]
  unfold gPoly
  rw [Matrix.det_fin_one, Matrix.det_isEmpty]
  simp

end lev0

def HeadTypesAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) ∧
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix

theorem head_types_of_types_at : PBI.HeadTypesAt → PBI.HeadTypes := by
  intro hAt Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγ hζ hfr
  obtain ⟨hex0, hd0⟩ := hAt Wp Wq P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγ hζ hfr
  set Bs := p.T.bs P.r with hBs
  have hr0 : P.r - P.r = 0 := Nat.sub_self _
  have hstd : C2.Std P.k (P.r - P.r) Bs.z Bs.z' := ⟨Bs.k_pos, ⟨Bs.z_mem, Bs.T_pos⟩, ⟨Bs.z'_mem, Bs.T'_pos⟩⟩
  have hx2G : x.2 ∈ B.GV P.k (P.r - P.r) := hx.2.1.1
  have hGG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) Bs.z Bs.z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) Bs.z * Tz P.k (P.r - P.r) Bs.z' := hx.2.2
  have hGpos : 0 < Gf P.k (P.r - P.r) Bs.z Bs.z' γ₀ := by
    rw [PBI.gram_function_level_zero hr0, hζ]; exact hGG
  have hZ : Zhat P.k (P.r - P.r) Bs.z Bs.z' γ₀ = Zhat P.k (P.r - P.r) Bs.z Bs.z' x.2 :=
    PBI.corner_matrix_level_zero_eq hr0 _ _ _ _ hζ
  obtain ⟨s0, hs0, s0', hs0', hgs⟩ :=
    Formalism.FourierDecayAlt.P.fibre_orbit_description P.k (P.r - P.r) Bs.z Bs.z' hstd γ₀ hγ x.2 hx2G hGpos hZ
  obtain ⟨⟨h1, hh1, m1, hm1, rfl⟩, -⟩ := hs0
  obtain ⟨⟨h2, hh2, m2, hm2, rfl⟩, -⟩ := hs0'
  rw [PBI.unipotent_level_zero_eq_one hr0 m1 hm1, PBI.unipotent_level_zero_eq_one hr0 m2 hm2, Matrix.mul_one, Matrix.mul_one] at hgs
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k (P.r - P.r) Bs.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed P.k (P.r - P.r) Bs.z'
  have hsi : h1⁻¹ ∈ UWset P.k (P.r - P.r) Bs.z := hW.inv_mem _ hh1
  have hs'i : h2⁻¹ ∈ UWset P.k (P.r - P.r) Bs.z' := hW'.inv_mem _ hh2
  have hu1 : IsUnit h1.det := hW.unit _ hh1
  have hu2 : IsUnit h2.det := hW'.unit _ hh2
  have hπ1 : ∀ v, Bs.π h1 (Bs.π h1⁻¹ v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hh1 _ hsi, Matrix.mul_nonsing_inv _ hu1, Bs.π_rep.1]
    rfl
  have hπ2 : ∀ v, Bs.π h1⁻¹ (Bs.π h1 v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π_rep.2 _ hsi _ hh1, Matrix.nonsing_inv_mul _ hu1, Bs.π_rep.1]
    rfl
  have hπ'1 : ∀ v, Bs.π' h2 (Bs.π' h2⁻¹ v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← Bs.π'_rep.2 _ hh2 _ hs'i, Matrix.mul_nonsing_inv _ hu2, Bs.π'_rep.1]
    rfl
  have hx0 : (x.1, γ₀) ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r Bs.z Bs.z' := by
    have hpr : (JC.parLev P P.r).r = 0 := Nat.sub_self P.r
    refine ⟨hx.1, ⟨hγ, fun a _ => absurd a.isLt (by omega)⟩, ?_⟩
    change 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) Bs.z Bs.z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) Bs.z * Tz P.k (P.r - P.r) Bs.z'
    rw [hζ]; exact hGG
  have heq : ∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r Bs.z Bs.z' Bs.π Bs.π',
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        (Bs.π h1⁻¹).comp (((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀).comp
          (Bs.π' h2)) := by
    intro Ψ
    have := Ψ.2.2.2 (x.1, γ₀) hx0 h1⁻¹ hsi h2 hh2
    rw [hgs]; exact this
  have hidem : ∀ ρ u, p.TP.E ρ (p.TP.E ρ u) = p.TP.E ρ u := fun ρ u => by
    rw [← ContinuousLinearMap.comp_apply, p.TP.idem ρ]
  refine ⟨fun U => (Bs.π h1).comp (U.comp (Bs.π' h2⁻¹)),
    fun ρ => (Bs.π h1⁻¹).comp ((p.TP.E ρ).comp (Bs.π h1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U V
    rw [PBI.hsInner_comp_left _ (Bs.π_unitary _ hh1), PBI.hsInner_comp_right _ (Bs.π'_unitary _ hs'i)]
  · intro ρ U
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1]
  · intro ρ
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1, hidem]
  · intro ρ v v'
    simp only [ContinuousLinearMap.comp_apply]
    calc inner ℂ (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v))) v'
        = inner ℂ (Bs.π h1 (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v)))) (Bs.π h1 v') :=
          (PBI.inner_map_of_norm _ (Bs.π_unitary _ hh1) _ _).symm
      _ = inner ℂ (p.TP.E ρ (Bs.π h1 v)) (Bs.π h1 v') := by rw [hπ1]
      _ = inner ℂ (Bs.π h1 v) (p.TP.E ρ (Bs.π h1 v')) := p.TP.selfAdj ρ _ _
      _ = inner ℂ (Bs.π h1 v) (Bs.π h1 (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v')))) := by rw [hπ1]
      _ = inner ℂ v (Bs.π h1⁻¹ (p.TP.E ρ (Bs.π h1 v'))) := PBI.inner_map_of_norm _ (Bs.π_unitary _ hh1) _ _
  · intro y e
    rw [heq (y e)]
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, hπ1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    have := congrArg (fun T : Wq →L[ℂ] Wp => T (Bs.π' h2 v)) (hex0 (y e))
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply] using this
  · intro h hh y e
    rw [heq (P5.act _ y e), hd0 h hh y e, heq (y e)]
    ext v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, hπ1]
  · intro Ψ
    rw [heq Ψ]
    ext v
    simp only [ContinuousLinearMap.comp_apply, hπ1, hπ'1]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Rad

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_uEquiv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : Mx k r) {h h' : Mx k r} (hh : h ∈ UWset k r D.z)
    (hh' : h' ∈ UWset k r D.z') : B.JF D F (h * g * h') = (D.π h).comp ((B.JF D F g).comp (D.π' h')) := by
  have := P.B5.haar_sigmaFinite D.haarW
  have := P.B5.haar_sigmaFinite D.haarN
  have := P.B5.haar_sigmaFinite D.haarW'
  exact bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

theorem radJFExists : RadJFExists := by
  intro Wp Wq _ _ _ _ _ _ Pa z z' π π' D F _hP hz hz' hπ hπ' hF
  subst hz hz' hπ hπ'
  classical
  let Φf : Fn Pa.k Pa.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) c g else 0
  have hsm := sf_resG (jf_smoothLev D F hF.1)
  have hmem : Φf ∈ RadSp Pa.k Pa.r D.z D.z' D.π D.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = 0
      rw [if_neg (by simpa using hx)]
    · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
        ⟨hx₀.1, wCell_mem_omPlus D.z_mem D.z'_mem hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
      have hV : IsOpen {x : (Fin Pa.r → ℂ) × Mx Pa.k Pa.r | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2} :=
        ((P.Qx3.isOpen_OmX Pa.r).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((P.Qx5.GGl_continuous Pa.k Pa.r D.z D.z').comp continuous_snd))
      refine ⟨U ∩ {x | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2}, Fe, hU.inter hV,
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
      rw [if_pos hxD]
      exact hΦ x hx.1 hxG
    · have hx' : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := by simpa using hx
      show (if (x.1, h * x.2 * h') ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 (h * x.2 * h') else 0) =
        (D.π h).comp ((if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0).comp (D.π' h'))
      rw [if_pos (domR_uw hx hh hh'), if_pos hx']
      unfold resG
      have e : wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * (h * x.2 * h') =
          h * (wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) * h' := by
        have hc := P.Qx3.wlist_comm (k := Pa.k) (Fin.last Pa.r) x.1
          ((List.finRange Pa.r).filter fun a => a.val < (Fin.last Pa.r).val)
          (fun a ha => by simpa using (List.mem_filter.1 ha).2) (P.Qx3.uw_glev (Fin.last Pa.r) hh)
        change wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * h = h * wCell Pa.k Pa.r (Fin.last Pa.r) x.1 at hc
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
      rw [e, jf_uEquiv D F _ hh hh']
      ext v
      simp
  exact ⟨⟨Φf, hmem⟩, fun x hx => by
    show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
    rw [if_pos (by simpa using hx)]⟩

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raw_gauge_smoothness_holds : GRawSmooth := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ e he Dc Φ hF ρ
  obtain ⟨-, -, hM, hS, -⟩ := hF
  have hT : Tz P.k P.r Bs.z = P.T := hpl.2.2.2.1
  have hT' : Tz P.k P.r Bs.z' = P.T' := hpl.2.2.2.2.1
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
  have hU0 : ∀ x ∈ Qs, (x.1, NF.muZ P.k P.r Bs.μsec x.2) ∈
      {y : (Fin P.r → ℂ) × Q.Mx P.k P.r | y.1 ∈ OmX P.r ∧ y.2 ∈ Dc y.1} :=
    fun x hx => ⟨hx.1, hM ⟨x, hx⟩⟩
  have hΦq : ContDiffOn ℝ ∞ (fun x : MA.E P.r => Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)) Qs := by
    refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
    obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hS _ (hU0 x₀ hx₀) (hGl x₀ hx₀)
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
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (Φ x.1 (NF.muZ P.k P.r Bs.μsec x.2)))) Qs :=
    (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn hΦq)
  have hall := hw.mul hin
  show ContDiffOn ℝ MA.sm (MA.ext _) Qs
  refine hall.congr fun x hx => ?_
  exact dif_pos hx

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
open Matrix Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ

def bigPt {n : ℕ} (d : Fin n → ℂ) : C.LPt := List.ofFn fun i => (1, d i)

def BigCellVan : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → Top.IsRadOf P p.T.base 0 F →
    ∀ d : Fin (P.r + 1) → ℂ, (∀ i, d i ≠ 0) → p.V F (bigPt d) = 0

def DensCOfParts : Prop := KB.PhiZero → KB.KloostDens → BigCellVan → KB.DensC

namespace Dens

theorem ptEntry_ones (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b ∧ a < l.length then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    cases a <;> cases b <;> simp [D.ptEntry, ih]

theorem ptMatN_bigPt {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = U.hMat 1 d := by
  ext a b
  have h : bigPt d = (List.ofFn d).map fun c => ((1 : ℕ), c) := by
    simp [bigPt, List.map_ofFn, Function.comp_def]
  simp only [D.ptMatN, h, ptEntry_ones, U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply,
    Equiv.Perm.one_apply, List.length_ofFn]
  by_cases hab : a = b
  · subst hab
    simp [List.getD_eq_getElem?_getD]
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [hab, hab']

theorem isLocPt_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.IsLocPt (bigPt d) n := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [bigPt, List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hd i⟩
  · simp [D.ptSize, bigPt, List.map_ofFn, Function.comp_def, List.sum_ofFn]

end Dens

theorem density_constant_of_parts : DensCOfParts := by
  intro hPZ hKD hBV Wp Wq _ _ _ _ _ _ P p F hC hR a
  obtain ⟨Φ0, hs, hcs, hdet, hV⟩ := hPZ Wp Wq P p F hC
  by_cases ha : D.IsLocPt a (P.r + 1)
  · have key : ∀ n, D.ptSize a = n →
        ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
      rintro n rfl
      obtain ⟨σ, d, -, h⟩ := Asm.exists_hMat a ha.1
      exact ⟨σ, d, h⟩
    obtain ⟨σ, d, hσd⟩ := key _ ha.2
    rw [hV a σ d ha hσd]
    refine hKD (P.r + 1) (Wq →L[ℂ] Wp) Φ0 hs hcs hdet ?_ a σ d ha hσd
    intro d' hd'
    rw [← hV (bigPt d') 1 d' (Dens.isLocPt_bigPt d' hd') (Dens.ptMatN_bigPt d').symm]
    exact hBV Wp Wq P p F hC hR d' hd'
  · unfold KB.Pl.V D.vecV
    rw [dite_eq_right (fun h => ha h.1)]

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

theorem pb_densC_of (hPZ : Formalism.FourierDecayAlt.KB.PhiZero) (hBV : PBJ.BigCellVan) : Formalism.FourierDecayAlt.KB.DensC :=
  PBJ.density_constant_of_parts hPZ kloosterman_density hBV

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Pres

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def presAlg (U : Submodule ℂ V) : StarSubalgebra ℂ (Pr V) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ ∀ Φ ∈ U, a.2.unop Φ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ)⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ)⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) a) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · show (algebraMap ℂ (Module.End ℂ V) (conj a)) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
  star_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, ha1⟩

end Pres

section Words

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem entries_mem_transpose {M : M2 (SlopeTestRemainingChoices S A)} (h : E2 𝒜 M) : E2 𝒜 Mᵀ := fun i j => h j i

theorem transfer_word_entries_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : star Y = Y) : E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ Y hY a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := transfer_word_entries_mem QQ hQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

end Words

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem matrix_two_entries_mem {𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))} {a b c d : Pr (RadSp k r z z' π π')}
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (hd : d ∈ 𝒜) : ∀ i j, (!![a, b; c, d] : M2 _) i j ∈ 𝒜 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')))
    (Y : ℂ) (i : ℕ) (hS : ∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    tprod L Y i a b ∈ 𝒜 := by
  suffices H : ∀ n i, r - i = n → (∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) →
      ∀ a b, tprod L Y i a b ∈ 𝒜 from H _ i rfl hS a b
  intro n
  induction n with
  | zero =>
    intro i hi _ a b
    unfold tprod
    rw [dite_eq_right (by omega), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ n ih =>
    intro i hi hS a b
    unfold tprod
    rw [dite_eq_left (by omega), Matrix.mul_apply]
    refine sum_mem fun e _ => 𝒜.mul_mem (ih (i + 1) (by omega) (fun l hl => hS l (by omega)) a e) ?_
    obtain ⟨hp, hc, hci⟩ := hS ⟨i, by omega⟩ le_rfl
    have h00 : algebraMap ℂ _ Y + L.p ⟨i, by omega⟩ ∈ 𝒜 := add_mem (𝒜.algebraMap_mem Y) hp
    fin_cases e <;> fin_cases b <;> simp [Ts, Formalism.YangianSpanCharacter.T.Tm, site, h00, hc, hci]

theorem QQi_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) :
    ∀ Y : ℂ, star Y = Y → ∀ a b, QQi L st i Y a b ∈ 𝒜 := by
  intro Y hY a b
  unfold QQi
  rw [Matrix.mul_apply]
  refine sum_mem fun e _ => 𝒜.mul_mem ?_ (tprod_mem L 𝒜 Y i.val hS e b)
  rw [Matrix.mul_apply]
  refine sum_mem fun f _ => 𝒜.mul_mem ?_ (hQ Y hY f e)
  rw [Matrix.conjTranspose_apply]
  exact star_mem (s := 𝒜) (tprod_mem L 𝒜 (star Y) i.val hS f a)

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (a : ℂ) (X : Wq →L[ℂ] Wp) : B.hsVec (a • X) = a • B.hsVec X := by
  simp only [B.hsVec, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  rfl

theorem tc_hsVec_sum {ι : Type} (s : Finset ι) (X : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [B.hsVec, ContinuousLinearMap.zero_apply]
    exact WithLp.toLp_zero 2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [B.hsVec, ContinuousLinearMap.add_apply]
    exact WithLp.toLp_add 2 _ _

theorem tc_gq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    B.gq Bs x = Q.wCell P.k P.r (Fin.last P.r) x.1 * NF.muZ P.k P.r Bs.μsec x.2 := by
  show bigCell P.k P.r x.1 (Bs.μsec x.2) = _
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r x.1 (Bs.μsec x.2)).1, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  rfl

theorem tc_sqrt_wq (k r : ℕ) (TT : ℝ) (x : MA.E r) :
    Real.sqrt (MA.wq k x TT) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) *
        wR k TT x.2 := by
  unfold MA.wq wR
  rw [Real.sqrt_mul (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)]
  congr 1
  have h : ∏ l : Fin r, Complex.normSq (x.1 l) ^ (MA.Mdim k r l - 1) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hM : MA.Mdim k r a = Formalism.QuantumDeterminants.Mdim k r a := rfl
    rw [if_pos (by simp), Complex.normSq_eq_norm_sq, hM, ← pow_mul, ← pow_mul, mul_comm]
  rw [h, Real.sqrt_sq (Finset.prod_nonneg fun a _ => by split_ifs <;> positivity)]

theorem tc_rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ := by
  funext q
  simp only [rawJ, rawR, Q.resG, tc_gq, tc_sqrt_wq]
  rw [tc_hsVec_smul, inner_smul_right]
  push_cast
  ring

theorem tc_mu (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∧
      Q.wCell P.k P.r (Fin.last P.r) q.1.1 * NF.muZ P.k P.r Bs.μsec q.1.2 ∈ OmB Bs := by
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hTT]; exact q.2.2
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
    linarith
  have h := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hG hGG
  exact ⟨hG, h.2, fun a => h.1 ⟨(a : ℕ) + 1, by omega⟩ (by show (a : ℕ) + 1 ≤ P.r; omega)⟩

theorem tc_famR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) :
    FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs})
      (Q.resG P.k P.r (Fin.last P.r) J) := by
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  refine ⟨?_, ?_, fun q => (tc_mu P Bs hpl q).2, ?_⟩
  · have hw : ContDiffOn ℝ ∞ (fun c : Fin P.r → ℂ => Q.wCell P.k P.r (Fin.last P.r) c) (OmX P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
    have hm : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
        {x | x.1 ∈ OmX P.r} :=
      Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
    exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1
  · intro c hc
    refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
    rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hhm : h * m ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
    have hcomm : Q.wCell P.k P.r (Fin.last P.r) c * (h * m) = (h * m) * Q.wCell P.k P.r (Fin.last P.r) c :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last P.r) c _ (fun a _ => a.isLt) hhm
    have hwg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
    have e : Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) =
        h * m * (Q.wCell P.k P.r (Fin.last P.r) c * g) * (h' * m') := by
      rw [← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c), ← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c),
        hcomm, Matrix.mul_assoc (h * m)]
    show Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) ∈ OmB Bs
    rw [e]
    exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
      ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩
  · exact Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
      (Fin.last P.r)

end

theorem gauge_transition_chain_holds : GTrChain := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ J hJ
  refine ⟨tc_famR P Bs hpl J hJ, fun e ρ => tc_rawJ P Bs e J ρ, fun e ρ Y => ?_⟩
  rw [tc_rawJ]
  funext q
  have hmu := tc_mu P Bs hpl q
  have hcv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) (OmB Bs) (Y : ℂ)
    Bs.z_mem Bs.z'_mem (isDom_omP Bs.z_mem Bs.z'_mem) J hJ q.1.1 q.2.1 _ hmu.1 hmu.2
  simp only [rawR, Finset.sum_apply]
  rw [hcv]
  simp only [Finset.sum_apply, tc_hsVec_sum, inner_sum, Finset.mul_sum, Fin.val_last]

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def Line {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (π : M.Ty P) (ζ : ℂ) : Set (Wq →L[ℂ] Wp) :=
  {X | X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧ (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp X = X}

def LineAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∀ X ∈ Line P Bs Pr π ζ, ∀ Y ∈ Line P Bs Pr π ζ, X ≠ 0 → ∃ c : ℂ, Y = c • X

def DatumTransit : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ ∧
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

def SRaise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π ρ : M.Ty P, M.Up P l π ρ →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, S ζ Xf ∈ Line P Bs Pr ρ ζ

def SNorm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π : M.Ty P,
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, ‖B.hsVec (S ζ Xf)‖ ^ 2 = M.Nrm P l π * ‖B.hsVec Xf‖ ^ 2

def ModConstOfCut : Prop :=
  LineNonzero → LineAtMost → DatumTransit → SRaise → SNorm → SSn.Rep.ThtFacts → ModConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCLineNonzero
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

theorem line_nonvanishing_holds : LineNonzero := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk Pr hPr π ζ hζ
  have hζT : P.TT < Complex.normSq ζ := hζ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζT
  have hT := Bs.T_pos
  obtain ⟨hνfix, hνν, -, -⟩ := DU.base hz hz' Bs.T_pos Bs.T'_pos Bs.sec hζ'
  set ν := SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ with hνdef

  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hy : inWb P.k P.r (μ *ᵥ Bs.z') := Qx8.inWb_mulVec hG hz'
  have hνW : inWb P.k P.r ν := by
    show inWb P.k P.r (SSn.unitH P.k P.r (SSn.prWv P.k P.r Bs.z (μ *ᵥ Bs.z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνz : herm (Hpk P.k P.r) ν Bs.z = 0 := by
    rw [← hνfix]; exact DU.prWv_perp hT hνW
  obtain ⟨Fr, hFr⟩ := Topx1.typ_frame_exists P.k P.r (by omega) Bs.z ν hz hT hνW hνz hνν
  obtain ⟨hFr', hpass⟩ := PRho.GL.gauge_left_line_holds Wp Wq P Bs hpl hk ζ hζT Fr hFr
  have hq : ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  obtain ⟨-, hg, hGG⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq
  have hEx := Gauge.GC.lie_existence_of_iso_group Gauge.GC.KLIso.lie_algebra_isomorphism_holds Gauge.GC.lie_group_realization
  obtain ⟨E, hEfib, hEeig, hE0⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk _ hg hGG.ne' _ hFr' π
  have hEF : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ :=
    fun p hp => hEfib p.1 hp.1 p.2 hp.2.1 hp.2.2
  have hgl' := (Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k P.r (P.k - 1) Bs.z' Bs.π'
    (fun a => μ⁻¹ *ᵥ Fr a) ⟨Bs.π'_rep, Bs.π'_cont⟩
    (Formalism.FourierDecayAlt.P.Qx8.frame_sub hFr' (by simp))).2
  have hπrep : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨Bs.π_rep, Bs.π_cont⟩
  refine ⟨E, hEF, ?_, hE0⟩
  have hpos : 0 < PRho.nrmW P.k P.r Bs.z ν := by
    unfold PRho.nrmW
    rw [hνfix, hνν]; simp
  have hrange := ((hPr.2.2 ν hpos).2.2.2 π)
  ext v
  rw [ContinuousLinearMap.comp_apply]
  refine (hrange (E v)).2 ?_
  intro Fr2 hFr2 w
  rw [hνfix] at hFr2
  rw [Topx1.typ_frame_change P.k P.r (by omega) Bs.z ν Bs.π Fr2 Fr hz hT hνW hνz hνν hπrep hFr2 hFr w (E v),
    hpass E hEF w v, hgl']
  have hw : w = (w - ((P.k : ℂ) - 2) / 2) + ((P.k : ℂ) - 2) / 2 := by ring
  conv_lhs => rw [hw]
  exact hEeig _ v

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Formalism.FourierDecayAlt.TL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConstS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadialS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
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

def ThConstOfCutS : Prop := PolyRadialS → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end
