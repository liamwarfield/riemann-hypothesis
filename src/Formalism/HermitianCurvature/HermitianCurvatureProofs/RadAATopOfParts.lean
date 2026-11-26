module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def JAAop : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (u : ℂ), KB.CptCoef Bs F → ∀ g ∈ JF.Om k r Bs.z Bs.z',
    B.JF Bs (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (B.JF Bs F) g

def AACell : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (u : ℂ) (c : Fin r → ℂ)
    (g : B.Mat k r), g ∈ Q.Glev k r (Fin.last r) →
    C3.AAop k r r le_rfl u f (Q.wCell k r (Fin.last r) c * g) =
      (∏ a, c a) • qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) u f
        (Q.wCell k r (Fin.last r) c * g)

def MinorCell : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℂ), KB.CptCoef Bs F → ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) (B.JF Bs F)) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2

def RadSideA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps k r z z' π π')
    (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r) (y : ℂ), Q.IsActualLevel X L →
    ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      (((L.Ar y).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.crd (Q.vAB r y r).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def AACpt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℝ),
    KB.CptCoef Bs F → KB.CptCoef Bs (aaTop Bs y F)

def RadAATopOfParts : Prop := JAAop → AACell → MinorCell → RadSideA → AACpt → RadAATop

end Formalism.FourierDecayAlt.P.PBN
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismCompactSupport
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.UInvZeroAt
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section Supp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_zero_at (s : ℂ) (g : B.Mat k r) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e', x e' g = 0) → ∀ e, KB.uInv s w x e g = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx e
    exact hx e
  | cons l w ih =>
    intro x hx e
    have h0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun e' => hx (Fin.cons (0 : Fin 2) e'))
    have h1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun e' => hx (Fin.cons (1 : Fin 2) e'))
    show (if e (0 : Fin (w.length + 1)) = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else (starRingEnd ℂ) s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ) g = 0
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, h0, h1, smul_zero, add_zero]

theorem waveG_bs (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (R : ℝ)
    (hx : ∀ e, ∀ g ∈ B.GV k r, x e g ≠ 0 → B.gN g ≤ R) :
    ∀ e, ∀ g ∈ B.GV k r, KB.waveG Bs s w x e g ≠ 0 → B.gN g ≤ R := by
  intro e g hg hne
  by_contra hR
  apply hne
  have hz : ∀ e', x e' g = 0 := fun e' => by
    by_contra h
    exact hR (hx e' g hg h)
  show P5.fsv s _ • KB.uInv s w x e g = 0
  rw [uInv_zero_at s g w x hz e, smul_zero]

theorem nice_mono {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : ε' ≤ ε)
    (hF : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε' F :=
  ⟨hF.1, hF.2.1, fun g hg hne => h.trans (hF.2.2 g hg hne)⟩

theorem common_R {ι : Type*} [Fintype ι] (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i, ∃ R : ℝ, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R) :
    ∃ R : ℝ, ∀ i, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R := by
  classical
  choose R hR using h
  refine ⟨∑ i, |R i|, fun i g hg hne => (hR i g hg hne).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end Supp

end Formalism.FourierDecayAlt.P.PBFV
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem vIsoCpt_main : Formalism.FourierDecayAlt.KB.VIsoCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hw s x x' hx hx'

  obtain ⟨ε, hε, hεall⟩ := Formalism.FourierDecayAlt.P.JCx2.exists_common_eps
    (fun (i : Bool × Wd.Ix (Fin w.length)) ε => JC.NiceCoef (p.T.bs j) ε (if i.1 then x i.2 else x' i.2))
    (fun i ε ε' _ h hF => nice_mono h hF)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx' e)
      · exact Formalism.FourierDecayAlt.P.TLB.nice_of_cpt (hx e))
  have hxN : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e) := fun e => by simpa using hεall (true, e)
  have hx'N : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e) := fun e => by simpa using hεall (false, e)
  obtain ⟨R, hR⟩ := common_R (fun i : Bool × Wd.Ix (Fin w.length) => if i.1 then x i.2 else x' i.2)
    (fun i => by
      rcases i with ⟨b, e⟩
      cases b
      · exact (hx' e).2.1
      · exact (hx e).2.1)
  have hxR : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (true, e)
  have hx'R : ∀ e, ∀ g ∈ B.GV P.k (P.r - j), x' e g ≠ 0 → B.gN g ≤ R := fun e => by simpa using hR (false, e)
  have hwN := waveG_nice (p.T.bs j) ε s w x hxN
  refine ⟨fun e => ⟨(hwN e).1, ⟨R, waveG_bs (p.T.bs j) s w x R hxR e⟩, ε, hε, (hwN e).2.2⟩, ?_⟩
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hJ : ∀ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), JC.NiceCoef (p.T.bs jF) ε F →
      (∃ R : ℝ, ∀ g ∈ B.GV P.k (P.r - j), F g ≠ 0 → B.gN g ≤ R) →
      ∃ Φ ∈ K 0, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Φ : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) F) y.1 y.2 := by
    rintro F hF ⟨R', hR'⟩
    exact Formalism.FourierDecayAlt.P.PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε hF hR'
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  choose Φ hΦK hΦ using fun a => hJ (x a) (hxN a) ⟨R, hxR a⟩
  choose Φ' hΦ'K hΦ' using fun a => hJ (x' a) (hx'N a) ⟨R, hx'R a⟩
  have hnx := waveG_nice (p.T.bs j) ε s w x hxN
  have hnx' := waveG_nice (p.T.bs j) ε s w x' hx'N
  show D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) (KB.waveG (p.T.bs j) s w x') =
    D.formLev p.T (M.sgn P p.l0) jF w x x'
  have hmem : ∀ (Wv Wv' : Module.End ℂ (RadSp (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z'
      (p.T.bs jF).π (p.T.bs jF).π')) (Ψ' : Ix (Fin w.length) → RadSp (JC.parLev P jF).k (JC.parLev P jF).r
      (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'),
      (∀ e, ∀ y ∈ DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        (Ψ' e : Fn (JC.parLev P jF).k (JC.parLev P jF).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _) (B.JF (p.T.bs jF) (KB.waveG (p.T.bs j) s w x' e))
            y.1 y.2) → InK (K 0) Ψ' := by
    intro _ _ Ψ' hΨ' e
    obtain ⟨Ψ0, hΨ0K, hΨ0⟩ := hJ (KB.waveG (p.T.bs j) s w x' e) (hnx' e) ⟨R, waveG_bs (p.T.bs j) s w x' R hx'R e⟩
    have : Ψ' e = Ψ0 := radSp_ext (fun y hy => (hΨ' e y hy).trans (hΨ0 y hy).symm)
    rw [this]
    exact hΨ0K
  by_cases hr : 0 < P.r - j
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_A (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))
  · have hr0 : P.r - j = 0 := by omega
    obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - j) → ℂ) (g : Mx P.k (P.r - j)) => fsv s (P5.zeta P.k (P.r - j) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [first_minor_top_eq_zeta hr0]
    have hΨ := radPic_wave (p.T.bs jF) ε s w x hxN Φ hΦ _ (by omega) hm Wv Wv' hW
    have hΨ' := radPic_wave (p.T.bs jF) ε s w x' hx'N Φ' hΦ' _ (by omega) hm Wv Wv' hW
    rw [hform w _ _ _ _ ε hε hnx hnx' hΨ hΨ', hform w x x' Φ Φ' ε hε hxN hx'N hΦ hΦ']
    congr 1
    have key := rr_wave_B (JC.parLev P jF) _ _ _ _ X μ L st K p.l0 hD hThm (D.positionted w) hwOK hr0 s Wv Wv' hW hW'
      Φ Φ' hΦK hΦ'K (hmem Wv Wv' _ hΨ') (fun _ => 1) (fun _ => one_ne_zero)
    unfold RRform at key
    exact (JCx2.form_zero_indep μ _ _ 0 (fun _ => 1)).trans (key.trans (JCx2.form_zero_indep μ _ _ (fun _ => 1) 0))

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

theorem vector_isomorphism_compact_support : Formalism.FourierDecayAlt.KB.VIsoCpt := Formalism.FourierDecayAlt.P.PBFV.vIsoCpt_main

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
namespace Formalism.FourierDecayAlt.P.TLB

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section mulAt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def MulAt (x : (Fin r → ℂ) × Q.Mx k r) (T : Module.End ℂ (Q.RadSp k r z z' π π')) (s : ℂ) : Prop :=
  ∀ Φ : Q.RadSp k r z z' π π', (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = s • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

theorem mulAt_one (x : (Fin r → ℂ) × Q.Mx k r) : MulAt (z := z) (z' := z') (π := π) (π' := π') x 1 1 := by
  intro Φ; simp

theorem mulAt_mul {x : (Fin r → ℂ) × Q.Mx k r} {T₁ T₂ : Module.End ℂ (Q.RadSp k r z z' π π')} {s₁ s₂ : ℂ}
    (h₁ : MulAt x T₁ s₁) (h₂ : MulAt x T₂ s₂) : MulAt x (T₁ * T₂) (s₁ * s₂) := by
  intro Φ
  rw [Module.End.mul_apply, h₁, h₂, smul_smul]

theorem pr_mul_fst (a b : Q.Pr (Q.RadSp k r z z' π π')) : (a * b).1 = a.1 * b.1 := rfl

theorem pr_one_fst : (1 : Q.Pr (Q.RadSp k r z z' π π')).1 = 1 := rfl

theorem mulAt_ofFn {x : (Fin r → ℂ) × Q.Mx k r} :
    ∀ {n : ℕ} (T : Fin n → Q.Pr (Q.RadSp k r z z' π π')) (s : Fin n → ℂ), (∀ i, MulAt x (T i).1 (s i)) →
      MulAt x (List.ofFn T).prod.1 (∏ i, s i)
  | 0, T, s, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, pr_one_fst]
    exact mulAt_one x
  | n + 1, T, s, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, pr_mul_fst]
    exact mulAt_mul (h 0) (mulAt_ofFn (fun i => T i.succ) (fun i => s i.succ) fun i => h i.succ)

end mulAt

section fns

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fibBound_one {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) : C6.FibBound D (fun _ => (1 : C6.EndH Wp Wq)) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 1, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun ε _ i => ⟨‖(1 : C6.EndH Wp Wq)‖, fun u v _ g hg _ => ?_⟩⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  calc ‖Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) (fun _ => (1 : C6.EndH Wp Wq)) g‖
      ≤ ‖(1 : C6.EndH Wp Wq)‖ := JCx2.pd_Dw_const _ _ _
    _ ≤ ‖(1 : C6.EndH Wp Wq)‖ * B.gN g ^ (3 * (r + 1) * i) :=
      le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg))

theorem liftScalar (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) (κ i j c : ℕ) (Pol : B.Mat Pa.k Pa.r → ℂ)
    (a : Q.Pr (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')) (hP : U.IsPolyDeg κ Pol)
    (hinv : ∀ p, Bs.inSS p → ∀ g, Pol (B.sgs p g) = Pol g)
    (hrad : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x a.1
      (Pol (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) *
        (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _))⁻¹ ^ i *
        (star (Dmin Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) (Fin.last _)))⁻¹ ^ j *
        ((Gf Pa.k Pa.r Bs.z Bs.z' (Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) : ℝ) : ℂ)⁻¹ ^ c)) :
    TL.Lifts Pa Bs 0 κ a := by
  refine Formalism.FourierDecayAlt.P.lift_zero_order Wp Wq Pa Bs κ i j c Pol (fun _ => 1) a hP (fibBound_one Bs) ?_ ?_
  · intro p hp g _ J
    simp only [_root_.smul_apply, one_apply_eq_self]
    rw [hinv p hp g, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · intro Φ x hx
    rw [hrad x hx Φ]
    simp

end fns

section acts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  (X : Q.ActualOps k r z z' π π') (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r)

theorem act_c (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.c l).1 (x.1 l) := by
  intro Φ
  rw [hL.2.2.1 l]
  show (X.op l 1 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_ci (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.ci l).1 (x.1 l)⁻¹ := by
  intro Φ
  rw [hL.2.2.2.1 l]
  show (X.op l 2 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_cb (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cb l).1 (star (x.1 l)) := by
  intro Φ
  rw [hL.2.2.2.2.1 l]
  show (X.op l 4 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_cbi (hL : Q.IsActualLevel X L) (x : (Fin r → ℂ) × Q.Mx k r) (l : Fin r) :
    MulAt x (L.cbi l).1 (star (x.1 l))⁻¹ := by
  intro Φ
  rw [hL.2.2.2.2.2.1 l]
  show (X.op l 5 Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.op_apply]; rfl

theorem act_fn (x : (Fin r → ℂ) × Q.Mx k r) (hx : x ∈ Q.DomR k r z z') (j : Fin 6) :
    MulAt x (X.fn j) (Q.fnVal k r z z' j x.2) := fun Φ => X.fn_apply j Φ x hx

end acts

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.TLB
open scoped ComplexConjugate

theorem lift_of_functions : TL.LiftFns := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X L hL
  have hcell := big_cell_values Pa.k Pa.r Wp Wq Bs
  have hpd1 : U.IsPolyDeg 0 (fun _ : B.Mat Pa.k Pa.r => (1 : ℂ)) := ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, (x.1 a)⁻¹) := fun x =>
    mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (∏ a, star (x.1 a)) := fun x =>
    mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (∏ a, (star (x.1 a))⁻¹) := fun x =>
    mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have inv_last : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) (Fin.last _) =
      Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _) := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  have inv_r : ∀ p, Bs.inSS p → ∀ g, Dmin Pa.k Pa.r Bs.z Bs.z' (B.sgs p g) ⟨Pa.r, by omega⟩ =
      Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩ := fun p hp g => Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine liftScalar Pa Bs 0 0 0 0 (fun _ => 1) 1 hpd1 (fun _ _ _ => rfl) fun x _ => ?_
    simp only [pow_zero, mul_one]
    exact mulAt_one x
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _)) L.D
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) inv_last fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1]
    exact mulAt_mul (hDr x) (hz x hx)
  · refine liftScalar Pa Bs (Pa.r + 1) 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g (Fin.last _))) L.Db
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' (Fin.last _)) (fun p hp g => by rw [inv_last p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.2.1, star_mul', star_prod]
    exact mulAt_mul (hDrb x) (hzb x hx)
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩) L.Dr
      (by simpa using minor_polynomial_property Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) inv_r fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1]
    exact hDr x
  · refine liftScalar Pa Bs Pa.r 0 0 0 (fun g => star (Dmin Pa.k Pa.r Bs.z Bs.z' g ⟨Pa.r, by omega⟩)) L.Drb
      (by simpa using dmin_star_pd Pa.k Pa.r Bs.z Bs.z' ⟨Pa.r, by omega⟩) (fun p hp g => by rw [inv_r p hp g])
      fun x hx => ?_
    simp only [pow_zero, mul_one]
    rw [(hcell x hx).2.1, star_prod]
    exact hDrb x
  · refine liftScalar Pa Bs 0 1 0 0 (fun _ => 1) L.Di hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  · refine liftScalar Pa Bs 0 0 1 0 (fun _ => 1) L.Dbi hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.1, star_mul', star_prod, mul_inv, ← Finset.prod_inv_distrib, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  · refine liftScalar Pa Bs 0 0 0 1 (fun _ => 1) (TL.gI L) hpd1 (fun _ _ _ => rfl) fun x hx => ?_
    simp only [pow_zero, pow_one, mul_one, one_mul]
    rw [(hcell x hx).2.2.2, Complex.ofReal_mul, ← Complex.mul_conj, mul_inv, mul_inv, ← Finset.prod_inv_distrib,
      map_prod, ← Finset.prod_inv_distrib]
    exact mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def capA (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X := C3.AAop k r r le_rfl (Q.uC k r 0 y) F

def capAv (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  C3.AAvop k r r le_rfl (y - ((2 * r + k : ℕ) : ℂ) / 2) F

def capBeta (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a))))

def capAlphaV (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l))

end defs

def JDACapRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (y : ℂ),
    ∃ Θ Θv : B.DiffOp k r Wp Wq,
      PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θ ∧ PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θv ∧
      B.opOrder Θ = r ∧ B.opOrder Θv = r ∧
      (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θ : ℕ∞) {g} F →
        B.opApply Θ F g = capA k r y F g) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θv : ℕ∞) {g} F →
        B.opApply Θv F g = capAv k r y F g

def JDACapInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq), P.r ≤ B.opOrder Θ →
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ)

def JDACapToda : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
          dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

def JDACapTodaV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
          dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem capa_J_ck (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r)
    {g : Q.Mx P.k P.r} (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) (m : ℕ∞) :
    Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r ∧ B.CkOn m {Q.wCell P.k P.r (Fin.last P.r) c * g} J := by
  have hGV : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hg
  refine ⟨hGV, fun g₀ hg₀ => ?_⟩
  rw [Set.mem_singleton_iff] at hg₀
  subst hg₀
  have hG0 : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
    ⟨hGV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  obtain ⟨U, F, hU, hmem, hF, hJF⟩ := hJ.1 _ ⟨hG0, hcg⟩
  refine ⟨U, F, hU, hmem, hF.of_le ?_, fun x hx hxG => hJF x hx ⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  exact_mod_cast le_top

end assembly

theorem jDAGrp_of_parts (hR : JDACapRep) (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDAGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) y
  refine ⟨Θ, Θv, hP, hPv, (hI _ _ (D.parOf S v) (T v).base hpl hk y Θ hO.ge).1 hA,
    (hI _ _ (D.parOf S v) (T v).base hpl hk y Θv hOv.ge).2 hAv, fun J hJ c hc g hg hcg => ⟨?_, ?_⟩⟩
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θ)
    rw [← hT _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θv)
    rw [← hTv _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vfw

variable {d : ℕ}

def vfD (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  fun x => fderiv ℝ u x (V x)

def vfW : List ((Fin d → ℝ) → (Fin d → ℝ)) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | V :: Vs, u => vfD V (vfW Vs u)

abbrev WOp (d : ℕ) := List (ℂ × List ((Fin d → ℝ) → (Fin d → ℝ)))

def WOp.app (P : WOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (P.map fun t => t.1 * vfW t.2 u x).sum

def WOp.symb (P : WOp d) (m : ℕ) (x ξ : Fin d → ℝ) : ℂ :=
  (P.map fun t => if t.2.length = m then t.1 * (t.2.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod else 0).sum

end vfw

def VOpToSOp : Prop :=
  ∀ (d m : ℕ) (P : WOp d) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = m ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (m : WithTop ℕ∞) u O → ∀ x ∈ O, S.app u x = WOp.app P u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb P m x ξ

def IsChart (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)) : Prop :=
  IsOpen O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def VR {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (κ x * X)

def VL {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (X * κ x)

def ChartSysW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → WOp d) (m : ι → ℕ),
      (∀ j, m j ≤ 2 * r + k + 1) ∧ (∀ j, ∀ t ∈ P j, t.2.length ≤ m j ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, WOp.app (P j) (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, WOp.symb (P j) (m j) x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

theorem chartEqs_of (hA : ChartSysW) (hB : VOpToSOp) : ChartEqs := by
  intro k r z z' d O U κ Φ u hk hz hz' hT hT' hO hU hκ hΦ hκO hΦU hOm hG
  obtain ⟨ι, hι, P, m, hm, hP, huc, hPu, hsym⟩ :=
    hA k r z z' d O U κ Φ u hk hz hz' hT hT' ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ hOm hG
  have hS : ∀ j, ∃ S : SOp d, S.ord = m j ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ v : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((m j : ℕ) : WithTop ℕ∞) v O → ∀ x ∈ O,
        S.app v x = WOp.app (P j) v x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb (P j) (m j) x ξ :=
    fun j => hB d (m j) (P j) O hO (hP j)
  choose S hSo hSc hSa hSs using hS
  refine ⟨ι, hι, S, fun j => hSc j, fun j => by rw [hSo j]; exact hm j, huc, ?_, ?_⟩
  · intro j x hx
    rw [hSa j _ (huc.of_le (by exact_mod_cast hm j)) x hx]
    exact hPu j x hx
  · intro x hx ξ hξ hall
    exact hsym x hx ξ hξ (fun j => by rw [← hSs j x hx ξ]; exact hall j)

def ChartCov : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ∃ Ξ₀ : B.Mat k r, B.inLie k r Ξ₀ ∧ (ξ ≠ 0 → Ξ₀ ≠ 0) ∧
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re

def RwChart : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
    (∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O ∧ ContDiffOn ℝ ∞ (VL κ Φ X) O) ∧
    ∀ Xs : List (B.Mat k r), (∀ X ∈ Xs, B.inLie k r X) → Xs.length ≤ 2 * r + k + 1 → ∀ x ∈ O,
      B.Rw Xs u (κ x) = vfW (Xs.map (VR κ Φ)) (fun y => u (κ y)) x ∧
      Xs.foldr Q.LdV u (κ x) = vfW (Xs.map (VL κ Φ)) (fun y => u (κ y)) x

def LieNFin : Prop :=
  ∀ (k r : ℕ), ∃ (q : ℕ) (Xs : Fin q → B.Mat k r), (∀ i, Xs i ∈ JfS.lieOf (Nset k r)) ∧
    ∀ X ∈ JfS.lieOf (Nset k r), B.inLie k r X ∧ ∃ a : Fin q → ℝ, X = ∑ i, ((a i : ℝ) : ℂ) • Xs i

def CapWords : Prop :=
  ∀ (k r j : ℕ), 1 ≤ j → j ≤ 2 * r + k + 1 →
    ∃ (Ys : Fin (2 * r + k + 2) → ℝ) (lam : Fin (2 * r + k + 2) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.CV k r (Ys i : ℂ) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * Ξ.charpoly.coeff (2 * r + k + 1 - j)

def cmp {k r : ℕ} (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b)

def CapRWords : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z'] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capR k r Bs (ws i) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CapLWords : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capLft k r Bs (ws i) f g = (L.map fun t => t.1 • t.2.foldr Q.LdV f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CmpZero : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    Q.IsFrameOf k r [z] Bs → ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
    (∀ j, 1 ≤ j → j ≤ k → (cmp Ξ Bs).charpoly.coeff (k - j) = 0) →
    ∀ X ∈ JfS.lieOf (UWset k r z), (Matrix.trace (Ξ * X)).re = 0

def FrameEx : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs

def ChartSysWOfParts : Prop :=
  ChartCov → RwChart → LieNFin → CapWords → CapRWords → CapLWords → CmpZero → FrameEx → ChartSysW

theorem chartEqs_of_parts (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hB : VOpToSOp) : ChartEqs :=
  chartEqs_of (hJ h1 h2 h3 h4 h5 h6 h7 h8) hB

def SOpField : Prop :=
  ∀ (d : ℕ) (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) → ContDiffOn ℝ ∞ V O →
    ∃ S' : SOp d, S'.ord = S.ord + 1 ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((S.ord + 1 : ℕ) : WithTop ℕ∞) u O → ∀ x ∈ O,
        S'.app u x = vfD V (S.app u) x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S'.symb x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) * S.symb x ξ

def SOpLift : Prop :=
  ∀ (d : ℕ) (S : SOp d) (m' : ℕ) (O : Set (Fin d → ℝ)), S.ord ≤ m' → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    ∃ S' : SOp d, S'.ord = m' ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧ (∀ u x, S'.app u x = S.app u x) ∧
      ∀ x ξ, S'.symb x ξ = if S.ord = m' then S.symb x ξ else 0

def SOpLin : Prop :=
  ∀ (d : ℕ) (S T : SOp d) (c : ℂ) (O : Set (Fin d → ℝ)), S.ord = T.ord → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    (∀ i w, ContDiffOn ℝ ∞ (T.a i w) O) →
    ∃ R : SOp d, R.ord = S.ord ∧ (∀ i w, ContDiffOn ℝ ∞ (R.a i w) O) ∧
      (∀ u x, R.app u x = c * S.app u x + T.app u x) ∧ ∀ x ξ, R.symb x ξ = c * S.symb x ξ + T.symb x ξ

def VOpToSOpOfSteps : Prop := SOpField → SOpLift → SOpLin → VOpToSOp

theorem chartEqs_of_all (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField)
    (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_parts hJ h1 h2 h3 h4 h5 h6 h7 h8 (hS s1 s2 s3)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInvariantCellAction
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ}

def lr (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem lr_succ (hr : 1 ≤ r) : (lr hr).succ = Fin.last r := Fin.ext (by simp [lr]; omega)

section Br1

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem br1 (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) :
    resG k r l.castSucc J c ∈ FFl k r z z' π π' l.castSucc (Qx6.Dcell D l.castSucc c) ∧
      IsDom k r z z' l.castSucc (Qx6.Dcell D l.castSucc c) :=
  ⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc,
    Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩

end Br1

theorem cell_preimage_mem_domain {D : Set (Mx k r)} {c : Fin r → ℂ} (l : Fin r) {g : Mx k r}
    (hg : wCell k r l.succ c * g ∈ D) : g ∈ Qx6.Dc1 l (Qx6.Dcell D l.castSucc c) c := by
  show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [← Matrix.mul_assoc, ← Qx6.wCell_succ]
  exact hg

section Br2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem br2 (l : Fin r) (Θ : (Mx k r → X) → (Mx k r → X)) (hS : Formalism.FourierDecayAlt.P5.SmulC Θ) (c : Fin r → ℂ)
    (hL : ∀ f : Mx k r → X,
      Θ (fun x => f (wCell k r l.castSucc c * x)) = fun x => Θ f (wCell k r l.castSucc c * x))
    (J : Mx k r → X) (g : Mx k r) :
    resG k r l.succ (Θ J) c g =
      ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Θ (resG k r l.castSucc J c) (w1 k r l (c l) * g) := by
  rw [Qx6.resG_succ]
  show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _
  congr 1
  have e : resG k r l.castSucc J c =
      ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x) := by
    funext x
    rfl
  rw [e, hS, hL]
  rfl

end Br2

theorem unipotent_fixes_base_vector (l : Fin r) (a : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    w1 k r l a *ᵥ z = z := by
  have hl := l.isLt
  have ze : z (eI k r l) = 0 := hz _ (Or.inl (by simp [eI]))
  have zs : z (esI k r l) = 0 := hz _ (Or.inr (by simp [esI]; omega))
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Qx3.sw k l p)]
  · rw [Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]
    rcases Qx3.tri l p with h | h | ⟨h1, h2⟩
    · subst h; rw [Qx3.sw_e, zs, ze, mul_zero]
    · subst h; rw [Qx3.sw_es, ze, zs, mul_zero]
    · rw [Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]
  · intro q _ hq
    have : p ≠ Qx3.sw k l q := fun h => hq (by rw [h, Qx3.sw_sw])
    rw [Qx3.w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wCell_fix_wb (i : Fin (r + 1)) (c : Fin r → ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    wCell k r i c *ᵥ z = z := by
  unfold wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]

theorem hermitian_invariant_unipotent (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((w1 k r l a * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← unipotent_fixes_base_vector l a hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _

theorem hermitian_invariant_cell_action (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((wCell k r i c * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← wCell_fix_wb i c hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
end
