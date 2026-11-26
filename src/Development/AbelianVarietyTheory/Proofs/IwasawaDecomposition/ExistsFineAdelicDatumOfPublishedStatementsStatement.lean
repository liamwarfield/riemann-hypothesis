module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def GeoExV (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Formalism.L2.Host.ValLL D R.C → GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

end GlobalTheory.Mem.R3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineAdelicDatumOfHyp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharWSeedStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.StandardWeightCharacter


set_option maxHeartbeats 8000000 in
theorem charW_seed_std : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (C : Formalism.L2.Pj.CoreJ X.toD7) [Algebra C.Q.c.F X.toD7.what₂.LL] (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Inputs X.toD7 → IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A → (∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A C.Q.c.F, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt) → GeoExV (famR X I hX U Xg tr₀) C (face0 X I hX U Xg tr₀).lv2 → Formalism.L2.Host.ValLL X.toD7 R₀.C → C.pb = R₀.C.P.pb → R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2 → R₀.IsInert → R₀.IsTup → R₀.AllPlaces → Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG → ∃ (tr : TrI X.B px) (dict : _) (mu : _) (chiW : _) (x₀ : _) (cE : _) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd), Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr R.toRealDat) ∧ Nonempty (@GlobalTheory.RealGeo.GeoHalf X.toD7 _ _ _ _ _ (famR X I hX U Xg tr).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) (inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL)) R.toRealDat fun _ => 1) := by
  intro X px I hX U Xg tr₀ C _ R₀ cG hI hXi hEx hGeo hVal hpb p0 i0 t0 a0 k0
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A C.Q.c.F (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, q1⟩ := analyticW_exists hI hXi hL hF
    (fun R => RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.ψ = R₀.ψ ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ R) ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    (fun R a1 a2 a3 a4 a5 a6 h => by
      rcases h with ⟨i, t, a, l, e, s, m, w, b, k⟩
      exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
        fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩)
    R₀.toRealDat p0 ⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, rfl, id, fun c hc => by cases eq_of_heq hc; exact k0⟩
  have e1 : R1.ExAt := hEx R1 p1 c1 t1 f1 g1
  have l1 : R1.toLevCh = R₀.toLevCh := q1.2.2.2.1
  have hC : R1.C = R₀.C := congrArg (fun L => L.C) l1
  obtain ⟨cutoffDeriv, hcG1⟩ : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  have pc1 : GlobalTheory.RealGeo.PreChar R1 := ⟨p1.1.lev, p1.1.red_R, p1.1.red_L, p1.1.record, p1.1.fam, p1.2,
    RealDat.chain_of_weak c1 e1, RealDat.thP_of_weak t1 e1⟩
  have hV1 : Formalism.L2.Host.ValLL X.toD7 R1.C := by rw [hC]; exact hVal
  have hpb1 : C.pb = R1.C.P.pb := by rw [hC]; exact hpb
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨geo⟩, hrat⟩ := hGeo R1 cutoffDeriv hV1 pc1 p1.1.levels hpb1 (q1.2.2.2.2.2.2.2.2.2 cutoffDeriv hcG1)
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨tr, htr⟩ : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) C.Q.c.F := ⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have q5 : RealDat3.IsInert (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.IsTup (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      RealDat3.AllPlaces (⟨R1.upd5 nW FW R1.mu R1.twPl R1.err0, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) C.Q.c.F) ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).toLevCh = R₀.toLevCh ∧ HEq (R1.upd5 nW FW R1.mu R1.twPl R1.err0).eG R₀.eG ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).ψ = R₀.ψ ∧ (R1.upd5 nW FW R1.mu R1.twPl R1.err0).mu = R₀.mu ∧
      (R1.upd5 nW FW R1.mu R1.twPl R1.err0).twPl = R₀.twPl ∧
      (BrgStd X I hX U Xg tr₀ R₀.toRealDat → BrgStd X I hX U Xg tr₀ (R1.upd5 nW FW R1.mu R1.twPl R1.err0)) ∧
      ∀ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (face0 X I hX U Xg tr₀).lv2 c := by
    rcases q1 with ⟨i, t, a, l, e, s, m, w, b, k⟩
    exact ⟨⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩, ⟨t.mu_off, t.mu_used, t.mu_ne, t.mu_conj, t.mu_on⟩, a, l, e, s, m, w, b,
      fun c hc => ⟨(k c hc).std, (k c hc).signs, (k c hc).frames, (k c hc).beta, (k c hc).prX, (k c hc).grp, (k c hc).psi, (k c hc).guard, (k c hc).valKs, (k c hc).frameKs, (k c hc).levKs⟩⟩
  obtain ⟨i1, u1, a1, l6, e6, s6, m6, w6, b6, k6⟩ := q5
  have p6 := RealDat.preliminary_of_scalar_update (RealDat.preliminary_of_index_update p1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update (RealDat.full_Y_of_index_update f1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update (RealDat.weak_chain_of_index_update c1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update (RealDat.weak_theta_props_of_index_update t1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update (RealDat.full_P_of_index_update g1 nW FW R1.mu R1.twPl R1.err0) kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, hy.trans ?_⟩
    show _ = Formalism.IndefR.Links.cj _ (1 : ℂ) • _
    rw [map_one]
    exact (one_smul ℂ _).symm
  have kv := k6 cutoffDeriv hcG1
  obtain ⟨g', -, -, -⟩ := GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ (famR X I hX U Xg tr₀).A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
    (R1.upd5 nW FW R1.mu R1.twPl R1.err0) (fun _ => 1) kap R1.lam R1.err0 geo
  refine ⟨tr, dict, mu, chiW, x₀, cE, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, hchi⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6 f6 g6, l6, e6, hcG1, s6, m6, w6, fun hb => b6 hb, ⟨g'⟩⟩

end GlobalTheory.StandardWeightCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChange
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

noncomputable section

namespace GlobalTheory.BaseFrameChange

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x m : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (x * m) = mᵀ * gram τ G x * m.map (starRingEnd ℂ) := by
  simp only [gram_eq, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]

def Orth (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem Orth.dom {X : Data E r} {x : Frame X.Ψ r} (h : Orth X x) : x ∈ X.dom :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).1

theorem Orth.unit {X : Data E r} {x : Frame X.Ψ r} (h : Orth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 :=
  ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular E r X.p0 X.Ψ X.Gm X.Gm_herm).2.1 x h).2 τ i

theorem isUnit_det_of_x0Orth {X : Data E r} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h : IsOrthogonalFrame X x₀) (τ : X.Ψ) :
    IsUnit (x₀ τ.1).det :=
  isUnit_iff_ne_zero.2 ((Orth.dom (X := X) (x := fun τ => x₀ τ.1) (fun τ => h τ.1 τ.2)) τ).1

def pass (Ψ : Finset (E →+* ℂ)) (x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Frame Ψ r :=
  fun τ => ((x₀ τ.1)⁻¹ * x₁ τ.1 : Matrix (Fin r) (Fin r) ℂ)

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem mat_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) (τ : Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl

theorem mat_pass {Ψ : Finset (E →+* ℂ)} (x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (τ : Ψ) :
    mat (pass Ψ x₀ x₁) τ = (x₀ τ.1)⁻¹ * x₁ τ.1 := rfl

theorem frame_ext {Ψ : Finset (E →+* ℂ)} {x y : Frame Ψ r} (h : ∀ τ, mat x τ = mat y τ) : x = y :=
  funext fun τ => h τ

theorem rmul_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    rmul (lact γ x) b = lact γ (rmul x b) :=
  frame_ext fun τ => by simp only [mat_rmul, mat_lact, Matrix.mul_assoc]

theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) :=
  frame_ext fun τ => by simp only [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem Orth.pass {X : Data E r} {x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀) (h₁ : IsOrthogonalFrame X x₁)
    {x : Frame X.Ψ r} (h : Orth X x) : Orth X (rmul x (pass X.Ψ x₀ x₁)) := by
  intro τ
  rw [mat_rmul, gram_mul, h τ, ← h₀ τ.1 τ.2, ← gram_mul, mat_pass,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₀ τ), h₁ τ.1 τ.2, h₀ τ.1 τ.2]

theorem rmul_pass_pass {X : Data E r} {x₀ x₁ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀)
    (h₁ : IsOrthogonalFrame X x₁) (x : Frame X.Ψ r) : rmul (rmul x (pass X.Ψ x₀ x₁)) (pass X.Ψ x₁ x₀) = x :=
  frame_ext fun τ => by
    rw [mat_rmul, mat_rmul, mat_pass, mat_pass, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth h₁ τ),
      Matrix.nonsing_inv_mul _ (isUnit_det_of_x0Orth h₀ τ), Matrix.mul_one]

end Frames

variable {D : D7} {r : ℕ} {Comp : Type}

def moveDict {V : HSp D} {X : Comp → Data D.host.E r} (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : GA D V → Σ k, Frame (X k).Ψ r :=
  fun g => ⟨(dict g).1, rmul (dict g).2 (pass _ x₀ x₁)⟩

theorem moveDict_eq {V : HSp D} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    (x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) {g : GA D V} {k : Comp} {x : Frame (X k).Ψ r}
    (h : dict g = ⟨k, x⟩) : moveDict dict x₀ x₁ g = ⟨k, rmul x (pass _ x₀ x₁)⟩ := by
  unfold moveDict
  rw [h]

theorem unitary_iff {n : ℕ} (u J : Matrix (Fin n) (Fin n) ℂ) :
    uᵀ * (-Jᵀ) * u.map (starRingEnd ℂ) = -Jᵀ ↔ (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj, ← Matrix.transpose_inj]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gm_map {V : HSp D} {X : Data D.host.E V.rank} (hW : ModelW V rfl X) (τ : D.host.E →+* ℂ) :
    X.Gm.map τ = -(V.gram.map τ)ᵀ := by
  rw [hW.1]
  ext a b
  simp

theorem dictIsUnif_move {V : HSp D} {X : Comp → Data D.host.E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : DictIsUnif V dict Kf th hr) (hW : ∀ k, ModelW V hr (X k))
    (ho : ∀ g, Orth (X (dict g).1) (dict g).2) {x₀ x₁ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (h₀ : ∀ k, IsOrthogonalFrame (X k) x₀) (h₁ : ∀ k, IsOrthogonalFrame (X k) x₁) : DictIsUnif V (moveDict dict x₀ x₁) Kf th hr := by
  subst hr
  obtain ⟨dL, dR, ⟨y, dy, dI⟩, dD, dO, dF⟩ := hd
  have hy : ∀ c, Orth (X c) (y c) := fun c => by
    obtain ⟨g, e⟩ := (dy c).2
    have := ho g
    rwa [e] at this
  have hyd : ∀ c τ, IsUnit (mat (y c) τ).det := fun c τ => isUnit_iff_ne_zero.2 ((dy c).1 τ).1
  refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, ⟨fun c => rmul (y c) (pass _ x₀ x₁), fun c => ?_, fun g h hh => ?_⟩,
    fun g => ((ho g).pass (h₀ _) (h₁ _)).dom, fun c x hx => ?_, fun g g' hg => ?_⟩
  · obtain ⟨γ', h1, e⟩ := dL γ hγ g
    exact ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩
  · obtain ⟨γ', h1, e⟩ := dR k hk g
    exact ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans (by rw [rmul_lact]; rfl)⟩
  · obtain ⟨g, e⟩ := (dy c).2
    exact ⟨((hy c).pass (h₀ _) (h₁ _)).dom, g, moveDict_eq x₀ x₁ e⟩
  · obtain ⟨γ', h1, e⟩ := dI g h hh
    refine ⟨γ', h1, (moveDict_eq x₀ x₁ e).trans ?_⟩
    rw [rmul_lact]
    refine congrArg (fun z => (⟨(dict g).1, lact γ' z⟩ : Σ k, Frame (X k).Ψ V.rank)) (frame_ext fun τ => ?_)
    have hm : IsUnit (mat (pass (X (dict g).1).Ψ x₀ x₁) τ).det := by
      rw [mat_pass, Matrix.det_mul]
      exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_x0Orth (h₀ _) τ)).mul (isUnit_det_of_x0Orth (h₁ _) τ)
    show mat (dict g).2 τ * ((mat (y _) τ)⁻¹ * _ * mat (y _) τ) * mat (pass _ x₀ x₁) τ =
      mat (dict g).2 τ * mat (pass _ x₀ x₁) τ * ((mat (y _) τ * mat (pass _ x₀ x₁) τ)⁻¹ * _ *
        (mat (y _) τ * mat (pass _ x₀ x₁) τ))
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hm]
    rfl
  · obtain ⟨g, γ, hγ, b, hb, e⟩ := dO c x hx
    obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (X c).p0
      (X c).Ψ (X c).Gm (X c).Gm_herm
    have hz := (hy c).pass (h₁ c) (h₀ c)
    choose u hu using fun τ : (X c).Ψ => h4 τ.1 (mat (y c) τ) (mat (rmul (y c) (pass _ x₁ x₀)) τ) (hy c τ)
      ((hz τ).trans (hy c τ).symm)
    obtain ⟨h, hh, ea⟩ := ((GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X c).Ψ (th c) (X c).cmType (hth c)).2.2.2 u
      fun τ => (unitary_iff _ _).1 (by rw [← gm_map (hW c)]; exact (hu τ).1)
    have hA : archMat V th rfl y h c = pass _ x₁ x₀ := frame_ext fun τ => by
      show (mat (y c) τ)⁻¹ * archM V (th c τ) h * mat (y c) τ = _
      rw [ea, Matrix.mul_assoc, ← (hu τ).2, mat_rmul, Matrix.nonsing_inv_mul_cancel_left _ _ (hyd c τ)]
    have hI := dI g h hh
    rw [e] at hI
    obtain ⟨γ', h1, e'⟩ := hI
    refine ⟨g * h, γ' * γ, mul_mem h1 hγ, b, hb, (moveDict_eq x₀ x₁ e').trans ?_⟩
    show (⟨c, rmul (lact γ' (rmul (rmul (lact γ x) b) (archMat V th rfl y h c))) (pass _ x₀ x₁)⟩ :
      Σ k, Frame (X k).Ψ V.rank) = _
    rw [hA, rmul_lact, rmul_pass_pass (h₁ c) (h₀ c), lact_mul, rmul_lact γ']
  · obtain ⟨γ', h1, e⟩ := hg
    refine dF g g' ⟨γ', h1, ?_⟩
    have e1 : moveDict (moveDict dict x₀ x₁) x₁ x₀ g' = dict g' :=
      (moveDict_eq x₁ x₀ (moveDict_eq x₀ x₁ (rfl : dict g' = ⟨(dict g').1, (dict g').2⟩))).trans
        (by rw [rmul_pass_pass (h₀ _) (h₁ _)])
    rw [← e1, moveDict_eq x₁ x₀ e, rmul_lact]
    show (⟨(dict g).1, lact γ' (rmul (rmul (dict g).2 (pass _ x₀ x₁)) (pass _ x₁ x₀))⟩ :
      Σ k, Frame (X k).Ψ V.rank) = _
    rw [rmul_pass_pass (h₀ _) (h₁ _)]

theorem orth_of_arch {V : HSp D} {hr : V.rank = r} {X : Data D.host.E r} (hW : ModelW V hr X)
    {th : X.Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hth : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ))
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h₀ : IsOrthogonalFrame X x₀) {x : Frame X.Ψ r} {g : GA D V}
    (hx : ∀ τ, mat x τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th τ) g) * x₀ τ.1) : Orth X x := by
  subst hr
  intro τ
  rw [hx, (GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular _ _ X.p0 X.Ψ X.Gm X.Gm_herm).2.2 τ.1 _ _ ?_]
  · exact h₀ τ.1 τ.2
  · rw [gm_map hW]
    exact (unitary_iff _ _).2 (GlobalTheory.RecDictModel.archM_unitary V (hth τ) g)


set_option maxHeartbeats 1000000 in
theorem exists_dict_of_x0Orth : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  intro D T x₀ hv hJ hC hx
  have ho : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ g, Orth ((T.U j σ).X (T.dict j σ g).1) (T.dict j σ g).2 := by
    intro j hj σ hσ g
    obtain ⟨hr, n, e, F, ik, φ, th, -, -, hth, -, hL⟩ := hJ.adPin j hj σ hσ
    obtain ⟨_, hW⟩ := hJ.modelW j hj σ hσ
    obtain ⟨γ, -, -, -, h3⟩ := hL g
    exact orth_of_arch (hr := hr) (hW _) (hth _) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) h3
  have hd : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.Kf j σ) th hr := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hJ.dictU j hj σ hσ
    obtain ⟨_, hW⟩ := hJ.modelW j hj σ hσ
    exact ⟨th, hr, hth, dictIsUnif_move hth h hW (ho j hj σ hσ) (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ) (hx j hj σ hσ)⟩
  have hm : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      MuUnit (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨h1, h2, h3, -⟩ := hJ.muUnit j hj σ hσ
    exact ⟨h1, h2, h3, fun g => ((ho j hj σ hσ g).pass (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) (hx j hj σ hσ _)).unit⟩
  have hA : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      AdelAut (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
    have hK := hJ.levelK j hj σ hσ
    exact GlobalTheory.OneEmbeddingProbe.adelAut_of_dominant (T.U j σ) (hJ.chiTriv j hj σ hσ) h (hm j hj σ hσ)
      (hJ.muCont j hj σ hσ) (GlobalTheory.DictLocTest.locClause_of_unif_places h (fun k hk => ((hK k).1 hk).1)
        (GlobalTheory.LevelOpen.level_mem_nhds D _ _ _ (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hK)
        fun k τ => ⟨τ.1, hth k τ⟩)
  have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
      CuspL2 (T.U j) σ (T.V j σ) (moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) (T.mu j σ) := by
    intro j hj σ hσ
    obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
    exact cusp_L2_of_measurable hσ (dict_dom_of h) (hm j hj σ hσ) (adelMeas_of_aut _ _ (hA j hj σ hσ))
  have hM : LawsM (reCore T (fun j σ => moveDict (T.dict j σ) (T.x₀ j σ) (x₀ j σ)) T.mu T.chiW x₀ T.cE).toCore :=
    { hJ.toLawsM with
      dictU := hd
      muUnit := hm
      cuspidalL2Subspace := hL
      l2Def := fun j hj σ hσ => by
        obtain ⟨th, hr, hth, h⟩ := hd j hj σ hσ
        refine l2Def_of_cusp hσ (hJ.supDef j hj) (aeDom_of (hA j hj σ hσ) (hJ.finVol j hj σ hσ)
          (volPair_of_tie hv _ ?_) (hm j hj σ hσ) h) (hL j hj σ hσ)
        rw [hJ.spaceW j hj σ hσ]
        exact D.sp.W_sig j }
  refine ⟨_, ⟨hM, hJ.cUnit, hJ.muVal, hJ.muConj, hJ.intAll, hJ.modelW, hx, hJ.kfHalf, fun j hj σ hσ => ?_⟩,
    ⟨hM, hC.cuspMul, hC.latZ, hC.cuNe, hC.expo⟩⟩
  obtain ⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, h4⟩ := hJ.adPin j hj σ hσ
  refine ⟨hr, n, e, F, ik, φ, th, h1, h2, hth, h3, fun g => ?_⟩
  obtain ⟨γ, k1, k2, k3, k4⟩ := h4 g
  refine ⟨γ, k1, k2, k3, fun τ => ?_⟩
  show mat (T.dict j σ g).2 τ * ((T.x₀ j σ τ.1)⁻¹ * x₀ j σ τ.1) = _
  rw [k4 τ, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det_of_x0Orth (hJ.familyUniformisationBasePointOrthogonal j hj σ hσ _) τ)]
  rfl

end GlobalTheory.BaseFrameChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDictionaryCoreLawsBaseFrameChangeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change : ∀ (D : D7) (T : CoreJ D) (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), VolTieG D → LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ)) → ∃ dict, LawsJ (reCore T dict T.mu T.chiW x₀ T.cE) ∧ LawsCore (reCore T dict T.mu T.chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | exact GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth | (intros; apply GlobalTheory.BaseFrameChange.exists_dict_of_x0Orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModelsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBaseFramesFlagDomainModels
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.BaseFrame

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ} (hr : V.rank = r) (ρ : D.what₂.Tau)
    {p q : ℕ} (hpq : r = p + q) (hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
      (Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  have hp : p ≤ V.rank := by omega
  have hq : nNeg (M.ε ρ) = q := (nNeg_shape hp hε).trans (by omega)
  have h0 : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := fun x => by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      conjTranspose_apply, gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring
  have hinv : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have h1 : ((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
    rw [← M.fr_gram ρ]
    calc _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ =
      (((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) := rfl
  show ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) = _
  rw [h0, h2, h1, hq]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [transpose_apply, Matrix.neg_apply, submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem exists_baseFrame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hL hA hF
  classical
  let x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ := fun j s τ =>
    if h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau, j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2 then
      Matrix.reindex (finCongr (rank_Wc h.choose.1)) (finCongr (rank_Wc h.choose.1))
        (x0Mat (R.MW h.choose.1 h.choose.2.1) h.choose.2.2)
    else T.x₀ j s τ
  have key : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ)) := by
    intro i σ ρ
    have h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        (i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2 := ⟨(i, σ, ρ), rfl, rfl, rfl⟩
    have aux : ∀ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        ((i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2) →
        Matrix.reindex (finCongr (rank_Wc p.1)) (finCongr (rank_Wc p.1)) (x0Mat (R.MW p.1 p.2.1) p.2.2) =
          Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (x0Mat (R.MW i σ) ρ) := by
      rintro ⟨i', σ', ρ'⟩ ⟨h1, h2, h3⟩
      obtain rfl : i = i' := Fin.ext (Nat.add_right_cancel h1)
      obtain rfl : ρ = ρ' := tauE_injective h3
      rw [hF.1 i σ σ' h2 ρ]
    exact (dif_pos h).trans (aux _ h.choose_spec)
  refine ⟨x₀, fun i σ _ => key i σ, fun j hj s hs k τ hτ => ?_⟩
  by_cases h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
      j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2
  · obtain ⟨⟨i, σ, ρ⟩, rfl, rfl, rfl⟩ := h
    dsimp only at hj hs k hτ ⊢
    have hU := hL.unf _ hj _ hs
    have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hL.pins.2.2.2 _ hj).1
    have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) (res T σ)).X k) := by
      obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hs
      have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hL.spaceW _ hj _ hs
      have h1 := hm k
      revert hr
      rw [hV]
      exact fun _ _ h => h
    have hε : ∀ a, (R.MW i σ).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun a => by
      rw [hF.2 i σ (fun ρ' => (GlobalTheory.HolRead.good_iff_labE_and_lab_conj D T hL hA σ ρ').1.1 hs) ρ a, hdp,
        show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    rw [key i σ ρ, hM.1, (hU.2.1 k).1]
    exact gram_x0Mat _ _ ρ hU.1 hε
  · have e : x₀ j s τ = T.x₀ j s τ := dif_neg h
    rw [e]
    exact hL.familyUniformisationBasePointOrthogonal j hj s hs k τ hτ

end GlobalTheory.RealGeo.BaseFrame
end

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  first | exact @GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | exact GlobalTheory.RealGeo.BaseFrame.exists_baseFrame | (intros; apply GlobalTheory.RealGeo.BaseFrame.exists_baseFrame <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

section Change

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ} {V : HSp D}
  {X : Comp → Data E r} {rd : C →ₛₗ[σ] FDSec X} {dict : GA D V → Σ c, Frame (X c).Ψ r} {mu mu' : GA D V → ℂ}

theorem norm_jFn_eq_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (f : C) (q : AutQ V) :
    ‖jFn V σ rd dict mu' f q‖ = ‖jFn V σ rd dict mu f q‖ := by
  show ‖mu' q.out * rd f (dict q.out).1 (dict q.out).2‖ = ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, norm_mul, h.2.1, h'.2.1]

theorem jMemL2_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hc : Continuous mu)
    (hc' : Continuous mu') (hL : JMemL2 V σ rd dict mu) : JMemL2 V σ rd dict mu' := by
  intro f
  have hne : ∀ g, mu g ≠ 0 := fun g h0 => by
    have := h.2.1 g
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => mu' g / mu g) (γ * g) = (fun g => mu' g / mu g) g := by
    intro γ hγ g
    show mu' (γ * g) / mu (γ * g) = mu' g / mu g
    rw [h.1, h'.1, h.2.2.1 γ hγ, h'.2.2.1 γ hγ, one_mul, one_mul]
  have hm : AEStronglyMeasurable (onQ V (fun g => mu' g / mu g)) (muQ1 V) := by
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    rw [onQ_eq_lift _ hinv]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_from_quotient.2 (hc'.div hc hne).measurable
  have he : jFn V σ rd dict mu' f = onQ V (fun g => mu' g / mu g) * jFn V σ rd dict mu f := by
    funext q
    show mu' q.out * rd f (dict q.out).1 (dict q.out).2 =
      mu' q.out / mu q.out * (mu q.out * rd f (dict q.out).1 (dict q.out).2)
    rw [← mul_assoc, div_mul_cancel₀ _ (hne _)]
  refine (hL f).congr_norm ?_ (Filter.Eventually.of_forall fun q => (norm_jFn_eq_of_muUnit h h' f q).symm)
  rw [he]
  exact hm.mul (hL f).aestronglyMeasurable

theorem peterson_norm_independent_of_unitary_character (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hL : JMemL2 V σ rd dict mu)
    (hL' : JMemL2 V σ rd dict mu') (f : C) : l2NormAlt V σ rd dict mu' hL' f = l2NormAlt V σ rd dict mu hL f := by
  show ‖(hL' f).toLp _‖ = ‖(hL f).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_congr_norm_ae (hL' f).aestronglyMeasurable (hL f).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_jFn_eq_of_muUnit h h' f q)]

end Change

theorem exists_mu_reCore : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D T chiW hJ hC hchi
    have hex : ∀ j σ, ∃ mu : GA D (T.V j σ) → ℂ, InR D j → GoodEmb T.Q.c σ →
        MuVal (T.V j σ) (chiW j σ) mu ∧ MuUnit (T.V j σ) (T.dict j σ) mu ∧ Continuous mu := by
      intro j σ
      by_cases h : InR D j ∧ GoodEmb T.Q.c σ
      · obtain ⟨mu, h1, h2, h3, h4, h5⟩ := GlobalTheory.Member.exists_muVal D (T.V j σ) (chiW j σ) (hchi j h.1 σ h.2).1
          (hchi j h.1 σ h.2).2.1
        exact ⟨mu, fun hj hσ => ⟨h1, ⟨h2, h3, h4, (hJ.muUnit j hj σ hσ).2.2.2⟩, h5⟩⟩
      · exact ⟨fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
    choose mu hmu using hex
    have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (mu j σ) :=
      fun j hj σ hσ a n hd => jMemL2_of_muUnit (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.muCont j hj σ hσ)
        (hmu j σ hj hσ).2.2 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
    have hLM : LawsM (reCore T T.dict mu chiW T.x₀ T.cE).toCore :=
      { pins := hJ.pins
        half := hJ.half
        evalWD := hJ.evalWD
        unf := hJ.unf
        unTest := hJ.unTest
        chiTriv := hJ.chiTriv
        dictU := hJ.dictU
        spaceW := hJ.spaceW
        levelK := hJ.levelK
        xiAbs := hJ.xiAbs
        muUnit := fun j hj σ hσ => (hmu j σ hj hσ).2.1
        muCont := fun j hj σ hσ => (hmu j σ hj hσ).2.2
        finVol := hJ.finVol
        cuspFD := hJ.cuspFD
        supDef := hJ.supDef
        cuspidalL2Subspace := hL
        l2Def := fun j hj σ hσ a n hd f h0 => hJ.l2Def j hj σ hσ a n hd f
          ((peterson_norm_independent_of_unitary_character (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
            (hL j hj σ hσ a n hd) f).symm.trans h0)
        unitIndep := hJ.unitIndep
        ptNe := hJ.ptNe }
    refine ⟨mu, ?_, ?_⟩
    · exact
        { toLawsM := hLM
          cUnit := hJ.cUnit
          muVal := fun j hj σ hσ => (hmu j σ hj hσ).1
          muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
          intAll := hJ.intAll
          modelW := hJ.modelW
          familyUniformisationBasePointOrthogonal := hJ.familyUniformisationBasePointOrthogonal
          kfHalf := hJ.kfHalf
          adPin := hJ.adPin }
    · exact
        { toLawsM := hLM
          cuspMul := hC.cuspMul
          latZ := hC.latZ
          cuNe := hC.cuNe
          expo := hC.expo }

end GlobalTheory.RealGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharactersStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_mu_reCore | exact GlobalTheory.RealGeo.exists_mu_reCore | (intros; apply GlobalTheory.RealGeo.exists_mu_reCore <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharacters
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_tieIn_reCore : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  intro D G _ _ Pl0 T0 A T _ R hvol hJ hC ha hlev hval hfr
  obtain ⟨chiW, hchi, hchi'⟩ := GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings D G Pl0 T0 A T R hJ.pins ha hlev hval
  obtain ⟨x₀, hx, hx'⟩ := GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models D G Pl0 T0 A T R hJ ha hfr
  obtain ⟨mu, hJ1, hC1⟩ := GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters D T chiW hJ hC hchi'
  obtain ⟨dict, hJ2, hC2⟩ := GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change D (reCore T T.dict mu chiW T.x₀ T.cE) x₀ hvol hJ1 hC1 hx'
  exact ⟨dict, mu, chiW, x₀, tieIn_top (reCore T dict mu chiW x₀ T.cE) R hJ2 ha
    (GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets D G Pl0 T0 A T.Q.c.F R) hchi hx, hC2⟩

end GlobalTheory.RealGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharactersStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_core_compatible_adelicData_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  first | exact @GlobalTheory.RealGeo.exists_tieIn_reCore | exact GlobalTheory.RealGeo.exists_tieIn_reCore | (intros; apply GlobalTheory.RealGeo.exists_tieIn_reCore <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicForms
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem omDat_updFW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ nW FW i Tp tup O
  refine ⟨{ O with }, rfl, rfl, fun h => ?_, fun cc ph h => h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end GlobalTheory.RealGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicFormsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  first | exact @GlobalTheory.RealGeo.omDat_updFW | exact GlobalTheory.RealGeo.omDat_updFW | (intros; apply GlobalTheory.RealGeo.omDat_updFW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoHalfTop

theorem exists_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  intro hC D G _ _ Pl0 T0 A T _ R hvol hJ hcore halg hpb hpre hval hfr hLL hfin hQ hstd hn
  obtain ⟨dict, mu, chiW, x₀, htie, hcore₁⟩ := GlobalTheory.T.exists_core_compatible_adelicData_characters D G Pl0 T0 A T R hvol hJ hcore halg hpre.lev hval hfr
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hpre.lev hpre.fam hpre.models hpre.thP
  obtain ⟨O, hO⟩ := GlobalTheory.T.exists_referenceTuple_thetaComparison_normalisedData D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) hpre hLL htie hpb hQ hstd
  choose cc hcc0 hcc using fun i => GlobalTheory.T.exists_constants_theta_comparison_all_tuples D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O hpre htie
    hpb hfin hQ hio i (hstd i) (hO i)
  obtain ⟨cE, hcE, htie₂, hO₂, hF⟩ := GlobalTheory.T.exists_core_constants_base_solution_equivariant D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O cc
    hpre.lev htie hpb hO hcc0
  obtain ⟨B, hκ, hv, hFB, hpre₂, hchi⟩ := GlobalTheory.T.exists_geometric_half_realisation_geometric_action D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O
    (fun _ => 1) hpre htie₂ hO₂ hF
  obtain ⟨hin, hU, hI⟩ := GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral hC D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) _ (fun _ => 1) B hpre₂ hchi hpb hn
  refine ⟨dict, mu, chiW, x₀, cE, _, _, B, hκ, hin, hFB, fun i => ⟨⟨_, _, hFB.1 i⟩, fun _ => ?_⟩,
    GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ _ hpre₂.lev hpre₂.fam hpre₂.models hpre₂.thP, hpre₂, hchi, hU, hI, hcore₁⟩
  obtain ⟨O', h1, h2, h3⟩ := hcc i
  obtain ⟨O'', e1, -, p1, p2⟩ := GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R)
    (nTop (reCore T dict mu chiW x₀ cE) (kapTop D)) (formsGeo (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O) i T0 id O'
  rw [hκ, hv]
  refine ⟨O'', ?_, p1 h2, ?_⟩
  · rw [e1]; exact h1
  · rw [← hcE i] at h3
    exact p2 _ _ h3

end GlobalTheory.GeoHalfTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCoreStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  first | exact @GlobalTheory.GeoHalfTop.exists_geoHalf | exact GlobalTheory.GeoHalfTop.exists_geoHalf | (intros; apply GlobalTheory.GeoHalfTop.exists_geoHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.GeoExProof


set_option maxHeartbeats 2000000 in
theorem geoExV_of_top : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  intro hRD D G _ _ Pl0 I0 T0 A3 C _ F hVol hL hLC hA hT hVS hn R cG hVal hPre _hlev hpb hK
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, B, -, -, hFired, -, -, hPre', hchi, hU, -, -⟩ :=
    GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core hRD D G Pl0 T0 A3.A C R hVol hL hLC hA hpb hPre hK.valKs hK.frameKs hVal hT hK.guard hVS hn
  refine ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨B⟩, fun i x => ?_⟩
  have hHW := hPre'.models.HW
  obtain ⟨m, a, f, hf⟩ := (hFired.1 i).2.2 x
  have hm : (1 : ℂ) • ((updFW R nW FW).HW i (sg0 D A3.A)).e (R.thG i A3.A.μ0 (jVx (updFW R nW FW) i A3.A.μ0 x)) ∈
      (updFW R nW FW).Wall i (sg0 D A3.A) :=
    ((updFW R nW FW).Wall i (sg0 D A3.A)).smul_mem 1 ((hHW i _).2.1.le (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := GlobalTheory.TwistedClassSum.exists_adForm B.fw hHW hU (B.O i).hV hm a f 1 fun q =>
    (hf q.out).trans (one_mul _).symm
  rw [one_smul, one_smul] at hy
  exact ⟨y, (hHW i _).1 hy.symm⟩

end GlobalTheory.Mem.R3.GeoExProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricExistenceCoreFormsAnalyticPhaseOneStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  first | exact @GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | exact GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top | (intros; apply GlobalTheory.Mem.R3.GeoExProof.geoExV_of_top <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

open Formalism.L2.Pj GlobalTheory.AtMember

namespace GlobalTheory.Mem.R3.Rw

theorem selHalf_of_pin {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (p : ColPin w) : SelHalf w.I := by
  intro a b P hP P' hP' hq
  obtain ⟨q, hq, hqP, hqP'⟩ := hq
  obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
  obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
  have hab : ∀ v, (w.I.sel v).under (𝓞 B.host.F) = v := fun v => by
    have h := p.above v
    unfold Formalism.L2.Host.aboveF at h
    rw [Set.Finite.mem_toFinset] at h
    exact h
  have hmem : ∀ v, ((q : 𝓞 B.host.E) ∈ (w.I.sel v).asIdeal) → (q : 𝓞 B.host.F) ∈ v.asIdeal := fun v h => by
    rw [← hab v]
    show (q : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal.comap (algebraMap _ _)
    rw [Ideal.mem_comap, map_natCast]
    exact h
  have := p.half v v' q hq (hmem v hqP) (hmem v' hqP')
  exact congrArg HeightOneSpectrum.asIdeal this

theorem isIdG_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (hP : Pg = Pg') (h : HEq e e') (h' : IsPlacewiseIdentity X (px := px) e') : IsPlacewiseIdentity X (px := px) e := by
  subst hP
  obtain rfl := eq_of_heq h
  exact h'

theorem trans_eq_of_heq' (X : Stages) {px : PreX X.B.toPre} {Pg Pg' : Finset (Pl X.toD7.host.E)} (e : Gc X.B px ≃* G0 Pg X.toD7.R.r)
    (e' : Gc X.B px ≃* G0 Pg' X.toD7.R.r) (c : G0 Pg X.toD7.R.r ≃* G0g X.toD7.nd) (c' : G0 Pg' X.toD7.R.r ≃* G0g X.toD7.nd)
    (hP : Pg = Pg') (h : HEq e e') (hc : HEq c c') : e.trans c = e'.trans c' := by
  subst hP
  obtain rfl := eq_of_heq h
  obtain rfl := eq_of_heq hc
  rfl


set_option maxHeartbeats 4000000 in
theorem datExS_evLg (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.CasselmanWallach) (h5 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h6 : GlobalTheory.Published.DiscreteSeriesExists)
    (h7 : GlobalTheory.Published.HarishChandraFinite) :
    EvLg fun K B f T => ∀ w : ColW B f T, Pinned K B f T w → ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f →
      R3.GrpAt (w.st Z) w.I → Formalism.L2.Theta.VolTieG (w.D Z) →
      ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
    (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.T.eventually_definiteSpaces_standard_and_large GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField))
  rintro K ⟨hK, hKC, hO⟩
  refine hO.imp ?_
  rintro B f T hOv hOB w ⟨pin⟩ Z hX _ hgrp hVol
  set X : Stages := w.st Z with hXd
  set I := w.I with hId
  set Wt : Set B.places.Pl := {v | B.places.resChar v ∈ T.pl} with hWt
  obtain ⟨hHH, -, -, hPos, hStd, hX', -, -⟩ := hK X hOv
  obtain ⟨hVS, hnV⟩ := hKC X hOv
  have hok := w.ok
  have hC := w.C_eq
  have hrange := w.xi_range
  have hsel : SelHalf I := selHalf_of_pin pin
  have hfin : Wt.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B T.pl
  have hconj : ∀ v ∈ Wt, B.places.conj v ∈ Wt :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f ≤ B.KsC := (GlobalTheory.Mem.Base.KsExact.lower w.exact).2.2.1
  have hval : Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) := w.val _ _ _ _ _ _
  obtain ⟨C, alg, hPin, hCe, hCL, hCK, hCE, hLJ, hAT, hVal, hmu⟩ := GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one X f hch hval hVol
  have hLC := hPin.laws
  have hpb := hPin.pb
  obtain ⟨hVals, hOk3⟩ := hOB w.px I hX hok hC hrange
  have hrange' : Set.range I.xi = T.set I.C := by rw [hC]; exact hrange
  obtain ⟨Xg, tr₀, R₀, cG, hLev, hIdG, hGood, hMu, hIdem, hPre0, hIn, hTup, hAll, hKeep, hBrg⟩ :=
    GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices X w.px I hX T Wt C.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hX' hPos hCK hCE
      (fun L hL hLC' => hmu _ L _ hL (hLC'.trans (by rw [hC])))
  have hValR : Formalism.L2.Host.ValLL X.toD7 R₀.C := by rw [hLev.C, hC]; exact hVal
  have hpbR : C.pb = R₀.C.P.pb := by rw [hLev.C, hC]; exact hpb
  have hExAt : ∀ R : RealDat X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀).A C.Q.c.F,
      R.Pre1 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.FullY → R.FullP → R.ExAt :=
    fun R hP hc ht _ _ => GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 X.toD7 _ _ _ _ _ R hP.1.lev hP.1.fam hP.2 hP.1.record hHH hc ht
  have hfinT : Finite (TupU I (usedOf I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))).1 ∨ τ ∈ tuOf I (usedOf I T Wt)} : Set _).Finite :=
      (Set.finite_singleton _).union (tuOf I (usedOf I T Wt)).finite_toSet
    exact hs.to_subtype
  have hGeoEx := GlobalTheory.T.geometricExistence_core_forms_analytic_phaseOne h3 X.toD7 _ _ _ _ _ C (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 hVol hLJ hLC hAT
    hfinT hVS hnV
  obtain ⟨tr, dict, mu, chiW, x₀, cE, R, cG', hPins, hEx, hLevEq, hEG, hCG, -, hmuEq, htw, hBrgI, hGeo⟩ :=
    GlobalTheory.StandardWeightCharacter.charW_seed_std X w.px I hX (usedOf I T Wt) Xg tr₀ C R₀ cG (GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra h5 h6 h7 h3 X.toD7) hIdem hExAt hGeoEx
      hValR hpbR hPre0 hIn hTup hAll hKeep
  have hPg : R.Pg = R₀.Pg := congrArg LevCh.Pg hLevEq
  have hRC : R.C = R₀.C := congrArg LevCh.C hLevEq
  have hgood : GoodSet X (px := w.px) (R.eG.trans cG') Xg := by
    rw [trans_eq_of_heq' X R.eG R₀.eG cG' cG hPg hEG hCG]; exact hGood
  let z : Dat X I hX T Wt :=
    { Xg := Xg, tr := tr, core := GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE,
      alg := inferInstanceAs (Algebra C.Q.c.F X.toD7.what₂.LL), alg_eq := hCe, R := R, cG := cG', geo := hGeo.some,
      pins := hPins, lev := by rw [hLevEq]; exact hLev, idG := isIdG_of_heq' X R.eG R₀.eG hPg hEG hIdG, good := hgood,
      mu := by rw [hmuEq, htw]; exact hMu, fieldValues_mem_fixedField := hCL, Ks_le := hCK }
  have hch' := hPins.char
  have hPre : GlobalTheory.RealGeo.PreChar R.toRealDat :=
    ⟨hch'.base.lev, hch'.base.grp.red_R, hch'.base.grp.red_L, hch'.base.grp.record, hch'.base.fam, hch'.base.models,
      RealDat.chain_of_weak hch'.base.chain hEx, RealDat.thP_of_weak hch'.base.thP hEx⟩
  have hP : CorePin (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE).toCore (Fr.at X f).P.pb :=
    hPin.reCore hGeo.some.fw.laws.toLawsM
  refine ⟨z, hEx, ?_, ⟨hP.laws, hP.canon, hP.rank, hP.pb⟩, hBrgI hBrg⟩
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral h3 X.toD7 _ _ _ _ (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE) R.toRealDat
    (fun _ => 1) hGeo.some hPre hch'.base.grp.chiW (by show C.pb = _; rw [hRC]; exact hpbR) hnV).1

theorem datExS_of_harishChandra_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → DatExS :=
  fun h1 h2 h3 h4 h5 h6 h7 =>
    GlobalTheory.Mem.Top.GroupRetwisting.Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg (datExS_evLg h1 h2 h3 h4 h5 h6 h7))

end GlobalTheory.Mem.R3.Rw

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fineAdelicDatum_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExS := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach | exact GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach | (intros; apply GlobalTheory.Mem.R3.Rw.datExS_of_harishChandra_casselmanWallach <;> assumption)
