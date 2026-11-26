module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem big_cell_values : TL.CellVals := by
  intro k r Wp Wq _ _ _ _ _ Bs x hx
  obtain ⟨hc, hg, hG⟩ := hx
  obtain ⟨μ, -, hμ⟩ := (TwoByOneBlock.UWb_iff x.2).1 (NFRadRedA.glev_uwb hg)
  have hGV : wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    have h1 : wCell k r (Fin.last r) x.1 ∈ Glev k r 0 := by
      unfold wCell
      exact Qx3.wlist_glev hc _
    exact (Qx5.Glev_mul h1 (Qx4.glev0 hg.1)).1
  have hM : wCell k r (Fin.last r) x.1 * x.2 = bigCell k r x.1 μ := by
    rw [P5.Rad.wCell_last_eq, hμ, ← (bruhat_big_cell_factorization k r x.1 μ).1]
  rw [hM] at hGV ⊢
  set ζ := zetaL k r Bs.z Bs.z' (Fin.last r) x.2 with hζdef
  have hz : ζ = herm (Hb k) (μ *ᵥ wbPart k r Bs.z') (wbPart k r Bs.z) := by
    rw [hζdef, P5.Rad.zetaL_last, hμ]
    have e1 : B2.embWb k r μ *ᵥ Bs.z' = TwoByOneBlock.jV k r (μ *ᵥ wbPart k r Bs.z') := by
      conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z'_mem]
      exact TwoByOneBlock.emb_mulVec_jV _ _
    rw [e1]
    conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z_mem]
    rw [TwoByOneBlock.herm_jV]
  let d : Fin (r + 1) → ℂ := fun a => if h : (a : ℕ) < r then x.1 ⟨a, h⟩ else ζ
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 μ) = diagonal d := by
    rw [bigCellZhat k r Bs.z Bs.z' x.1 μ Bs.z_mem Bs.z'_mem]
    congr 1
    funext a
    by_cases h : (a : ℕ) < r
    · simp [d, h]
    · simp only [d, h, dite_false]
      rw [BigCellHermitian.herm_bigCell x.1 μ Bs.z_mem Bs.z'_mem, hz]
  have hD := BruhatBigCell.dmin_diag Bs.z Bs.z' _ d hZ
  have hTT : 0 < Tz k r Bs.z * Tz k r Bs.z' := mul_pos Bs.T_pos Bs.T'_pos
  have hζ : ζ ≠ 0 := by
    intro h0
    have : GGl k r Bs.z Bs.z' x.2 = Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z' := rfl
    rw [this, h0, map_zero] at hG
    linarith
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a
    by_cases h : (a : ℕ) < r
    · simp only [d, h, dite_true]
      exact hc _
    · simp only [d, h, dite_false]
      exact hζ
  have hP : ∏ a : Fin r, x.1 a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  have hDr : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) ⟨r, by omega⟩ = ∏ a : Fin r, x.1 a := by
    rw [hD]
    refine Finset.prod_congr rfl ?_
    intro i _
    have hi : ((Fin.castLE (by omega) i : Fin (r + 1)) : ℕ) < r := i.isLt
    simp only [d, hi, dite_true]
    rfl
  have hDl : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) (Fin.last (r + 1)) = (∏ a : Fin r, x.1 a) * ζ := by
    rw [hD]
    show ∏ i : Fin (r + 1), d (Fin.castLE (by omega) i) = _
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i _
      have hi : ((Fin.castLE (by omega) i.castSucc : Fin (r + 1)) : ℕ) < r := i.isLt
      simp only [d, hi, dite_true]
      rfl
    · have hi : ¬ ((Fin.castLE (by omega) (Fin.last r) : Fin (r + 1)) : ℕ) < r := by simp
      simp only [d, hi, dite_false]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r x.1 μ) = Complex.normSq (∏ a : Fin r, x.1 a) * GGl k r Bs.z Bs.z' x.2 := by
    unfold Gf
    rw [hDl, hDr]
    show _ = _ * (Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z')
    rw [map_mul]
    ring
  refine ⟨⟨hGV, ?_, ?_⟩, hDr, hDl, hGf⟩
  · rw [hGf]
    exact mul_pos (Complex.normSq_pos.mpr hP) hG
  · intro l _
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {Φ Ψ : RadSp k r z z' π π'}
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : (c, g) ∈ DomR k r z z'
  · exact h (c, g) hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

end Formalism.FourierDecayAlt.P.PBFV

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStepT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (c : ℂ) (hh : D.IsLocPt h j) (hc : D.IsLocPt (h ++ [(1, c)]) (j + 1)),
    KB.CptCoef p.T.base F → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
    KB.slv p.T F (j + 1) hj [] _ hc.2 (fun a => a.elim0) γ =
      ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (p.T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
            star (psi P.k (P.r - j) (p.T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
          KB.slv p.T F j (by omega) [] h hh.2 (fun a => a.elim0)
            ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ *
              mc (by omega : P.r - (j + 1) + 1 = P.r - j) c γ * rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
        ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

theorem asm_castV_castV {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1; subst h2; rfl

theorem castM_castM' {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem sliceStep_of (hJ : JFStep) (hP : PointStepT) : KB.SliceStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hT := p.hT
  have key := hJ P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (p.T.bs j) (p.T.bs (j + 1))
    (by rw [levTower_bs_z_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (by rw [levTower_bs_z'_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (fun y => by rw [tower_π p.T j hj, lev1, castM_castM'])
    (fun y => by rw [tower_π' p.T j hj, lev1, castM_castM'])
    (hT j (by omega)).1 (hT j (by omega)).2.1 (hT (j + 1) hj).1 (hT (j + 1) hj).2.1
    (hT j (by omega)).2.2 (hT (j + 1) hj).2.2
    (KB.slv p.T F j (by omega) [] h hh.2 fun a => a.elim0)
    (KB.slv p.T F (j + 1) hj [] _ hc.2 fun a => a.elim0) c hc0
    (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j (by omega) [] h hh hF _)
    (fun γ' hγ' => hP Wp Wq P p F j hj h c hh hc hF γ' hγ') γ hγ hΩ
  rw [key, mc, castM_castM']

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
open Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAPairOne : Prop :=
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
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), IsAAOp S T v Θ →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ K ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
        (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (B.opApply Θ K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (B.opAdj Θ J))

def SAZero : Prop :=
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
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ X ∈ smoothFormsPositiveCone S T v, ∀ y (hy : y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
        (∀ π, ((trJ S T v e X π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) ⟨y, hy⟩ = 0) →
          X (B.gq (T v).base y) = 0

def SALocal : Prop :=
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
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ → ∀ K ∈ smoothFormsPositiveCone S T v,
      ∀ V : Set (MA.E (D.parOf S v).r), IsOpen V → V ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT → (∀ y ∈ V, K (B.gq (T v).base y) = 0) →
        ∀ y ∈ V, B.opApply Θ K (B.gq (T v).base y) = 0

def SAExh : Prop :=
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
    ∀ v, ∀ X ∈ smoothFormsPositiveCone S T v, ∀ Cs : Set (MA.E (D.parOf S v).r), IsCompact Cs → Cs ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT →
      ∃ (F : GFn S v) (U : Set (MA.E (D.parOf S v).r)), IsOpen U ∧ Cs ⊆ U ∧ B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧
        HasCompactSupport F ∧ tsupport F ⊆ OmP S T v ∧
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, (y ∈ U → B.JF (T v).base F (B.gq (T v).base y) = X (B.gq (T v).base y)) ∧
          (X (B.gq (T v).base y) = 0 → B.JF (T v).base F (B.gq (T v).base y) = 0)

def SAJCommC : Prop :=
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
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
      ∀ (U : Set (MA.E (D.parOf S v).r)) (X : GFn S v), IsOpen U → X ∈ smoothFormsPositiveCone S T v →
        (∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U → X (B.gq (T v).base y) = B.JF (T v).base F (B.gq (T v).base y)) →
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U →
          B.opApply Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base y) ∧
          B.opAdj Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opAdj Θ F) (B.gq (T v).base y)

def CompactSupportClassMembership : Prop :=
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
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F F' : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
        B.CkOn ⊤ (B.GV S.G.k S.G.r) F' → HasCompactSupport F' → tsupport F' ⊆ OmP S T v →
        B.InCC (B.AB S.G.k S.G.r) 5 F ∧ B.InCC (B.AB S.G.k S.G.r) 5 F' ∧
          B.InCC (B.AB S.G.k S.G.r) 5 (B.opApply Θ F) ∧ B.InCC (B.AB S.G.k S.G.r) 5 (B.opAdj Θ F') ∧
          B.beta (T v).base (B.opApply Θ F) F' = B.beta (T v).base F (B.opAdj Θ F')

theorem sAPairL_of_one (hF : JAFFStable) (h1 : SAPairOne) : SAPairL := by
  obtain ⟨C1, hF'⟩ := hF
  obtain ⟨C2, h1'⟩ := h1
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θs hΘs K hK J hJ hKt
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have stab := hF' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v
  have hmem : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      applyL S v Θs K ∈ smoothFormsPositiveCone S T v := by
    intro Θs
    induction Θs with
    | nil => intro _; exact hK
    | cons Θ Θs ih =>
      intro h
      exact (stab Θ (h Θ (by simp)) _ (ih fun Θ' hΘ' => h Θ' (by simp [hΘ']))).1
  have key : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ J ∈ smoothFormsPositiveCone S T v,
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J)) := by
    intro Θs
    induction Θs with
    | nil => intro _ J _; exact ⟨hKt, rfl⟩
    | cons Θ Θs ih =>
      intro h J hJ
      have hΘ : IsAAOp S T v Θ := h Θ (by simp)
      have hrest : ∀ Θ' ∈ Θs, IsAAOp S T v Θ' := fun Θ' hΘ' => h Θ' (by simp [hΘ'])
      have hX := hmem Θs hrest
      obtain ⟨ihT, ihE⟩ := ih hrest (B.opAdj Θ J) (stab Θ hΘ J hJ).2
      obtain ⟨hT, hE⟩ := h1' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he Θ hΘ (applyL S v Θs K) hX J hJ
        (stab Θ hΘ _ hX).1 (stab Θ hΘ J hJ).2 ihT
      exact ⟨hT, hE.trans ihE⟩
  exact key Θs hΘs J hJ

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lintegral_base_measure_le {r : ℕ} {TT : ℝ} (H : MA.E r → ENNReal) :
    ∫⁻ q : MA.Qp r TT, H q.1 ∂MA.mu0 r TT ≤ ∫⁻ x in MA.Qset r TT, MA.dens0 x * H x := by
  have hQ : MeasurableSet (MA.Qset r TT) := (MA.Qset_open r TT).measurableSet
  rw [MA.mu0, lintegral_subtype_comap hQ (fun x => H x), restrict_withDensity hQ]
  exact lintegral_withDensity_le_lintegral_mul _ Formalism.FourierDecayAlt.P.MAx2.Adj.density_measurable H

theorem jd_AB_le (k r : ℕ) : B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 2 * nDim k r := by
  have ha : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  unfold B.AB
  rw [hn]
  nlinarith [sq_nonneg (r : ℝ), mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) ha, mul_nonneg (mul_nonneg ha ha) hb,
    mul_nonneg (mul_nonneg ha hb) ha]

theorem transfer_square_integrable_holds : TransferSquareIntegrable := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr A hA F hCk hCC hFF π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  have hAB : B.AB S.G.k S.G.r ≤ A := (jd_AB_le S.G.k S.G.r).trans hA
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hCC 4
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hCC 5) (hCC 5) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr (B.JF Db F) hFF π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  refine ⟨((jd_evQ_meas _ _).norm).pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT,
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2) ≤ H q.1 := by
    intro q
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2)
          ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT
        ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          lintegral_mono p1
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CoreLF
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def CoreLF : Prop :=
  ∀ (k p m n : ℕ) (e : p + m = n), 1 ≤ p → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p m Bj.z) = B0.z → D.castV e (liftVec k p m Bj.z') = B0.z' →
    (∀ y : B.Mat k m, Bj.π' y = B0.π' (D.castM e (ιLev k p m y))) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p m e) →
    Bj.μN = D.muN k m → B0.μN = D.muN k n →
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k n),
      (∀ x, sx x ∈ Sset k n B0.z) ∧
      ∀ g ∈ JF.Om k m Bj.z Bj.z', ∀ H : B.Mat k n → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g)))) μ ∧
        B.JF Bj (U.PhiFun (s := 0) k m σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
            (fun a => a.elim0)) g =
          ∫ x, ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundedOperatorsSquareIntegrable
open Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem bounded_operators_square_integrable : BoundedOperatorsSquareIntegrable := by
  intro P L hTT hL b hb u hu π
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le
  have hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C := by
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx
    | one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩
    | mul x y _ _ h1 h2 =>
      obtain ⟨C1, h1⟩ := h1
      obtain ⟨C2, h2⟩ := h2
      exact ⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩
  obtain ⟨C, hC0, Mx, hMb, hMe⟩ := hPW
  have hmeas := jd_evQ_meas P (MA.actA P b u π)
  have hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT) := fun π' =>
    (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')
  have hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) :=
    memLp_finsetSum _ fun π' _ => (hL2u π').norm
  have hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) := hs.const_mul C
  refine (memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))
  rw [hMe u q π]
  calc ‖∑ π', Mx q π π' * MA.evQ P (u π') q‖ ≤ ∑ π', ‖Mx q π π' * MA.evQ P (u π') q‖ := norm_sum_le _ _
    _ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := Finset.sum_le_sum fun π' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)
    _ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRAsmPS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

noncomputable section

namespace Asm

def ggP (TT : ℝ) : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (TT : ℂ)

theorem gg_eval (TT : ℝ) (ζ : ℂ) : MvPolynomial.eval ![ζ, conj ζ, sig TT ζ] (ggP TT) = gg TT ζ := by
  simp only [ggP, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, gg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.mul_conj]
  push_cast
  ring

theorem PS.congr {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (h : ∀ ζ : ℂ, TT < Complex.normSq ζ → g ζ = f ζ) :
    PS TT g := by
  obtain ⟨m, p, hp⟩ := hf
  exact ⟨m, p, fun ζ hζ => by rw [h ζ hζ]; exact hp ζ hζ⟩

theorem PS.const (TT : ℝ) (a : ℂ) : PS TT (fun _ => a) :=
  ⟨0, MvPolynomial.C a, fun ζ _ => by simp⟩

theorem PS.mul {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ * g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * p', fun ζ hζ => ?_⟩
  rw [map_mul, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.add {TT : ℝ} {f g : ℂ → ℂ} (hf : PS TT f) (hg : PS TT g) : PS TT (fun ζ => f ζ + g ζ) := by
  obtain ⟨m, p, hp⟩ := hf
  obtain ⟨m', p', hp'⟩ := hg
  refine ⟨m + m', p * ggP TT ^ m' + p' * ggP TT ^ m, fun ζ hζ => ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, gg_eval, ← hp ζ hζ, ← hp' ζ hζ]
  ring

theorem PS.sum {TT : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, PS TT (f i)) :
    PS TT (fun ζ => ∑ i ∈ s, f i ζ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact PS.congr (PS.const TT 0) fun ζ _ => by simp
  | insert a s ha ih =>
    exact PS.congr (PS.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
      fun ζ _ => by rw [Finset.sum_insert ha]

theorem PSV.apply {TT : ℝ} {V : Type*} [AddCommGroup V] [Module ℂ V] {f : ℂ → V} (hf : PSV TT f)
    (L : V →ₗ[ℂ] ℂ) : PS TT (fun ζ => L (f ζ)) := by
  obtain ⟨n, a, v, ha, hf⟩ := hf
  refine PS.congr (PS.sum Finset.univ (fun i ζ => a i ζ * L (v i)) fun i _ => PS.mul (ha i) (PS.const TT _))
    fun ζ hζ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf ζ hζ, map_sum]
  simp only [map_smul, smul_eq_mul]

end Asm

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_fold (hC : CVInCC) {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (s : ℂ)
    (F : B.Mat k r → E) : ∀ (b : List C.Letter) (m : ℕ),
      B.InCC A (m + (2 * r + k + 1) * b.length) F → B.InCC A m (foldCV k r s b F)
  | [], m, h => by rw [foldCV_nil]; simpa using h
  | x :: b, m, h => by
    rw [foldCV_cons]
    refine hC k r E A m _ (x.2 : ℂ) s ?_
    refine inCC_fold hC A s F b (m + (2 * r + k + 1)) ?_
    have e : m + (2 * r + k + 1) + (2 * r + k + 1) * b.length = m + (2 * r + k + 1) * (x :: b).length := by
      simp [List.length_cons]; ring
    rw [e]; exact h

theorem weight_budget_L2_inequality (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 5)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) ≤ A₀ := by
  unfold B.AB
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  have hℓ' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) = j + n * ℓ := by rw [hn]; push_cast; ring
  rw [hcast]
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    nlinarith

  have hkr : 2 * ((k : ℝ) + r) ≤ 2 * n := by rw [hn]; linarith
  have hb : 2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ) ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have h1 : 2 * n * ℓ ≤ (N : ℝ) * n ^ 2 := by
      have : (ℓ : ℝ) * (2 * n) ≤ N * (n * n) := by
        apply mul_le_mul hℓ' (by nlinarith) (by positivity) (by positivity)
      nlinarith
    have h2 : 2 * n + 1 + 10 ≤ 100 * n ^ 3 := by nlinarith
    have hNn : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    nlinarith
  have hpos : 0 ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by positivity
  calc 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 + 2 * ((r : ℝ) + 1) * (j + n * ℓ)
      ≤ ((r : ℝ) + 1) * (2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ)) := by nlinarith
    _ ≤ ((r : ℝ) + 1) * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ ≤ ((r : ℝ) + 1) ^ 4 * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ = 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by ring
    _ ≤ A₀ := hA

theorem l2BoundAtBuiltPlace_of_cvInCC (hC : CVInCC) : L2BoundAtTowerPlace := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ε hε a hlen
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hχ, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  have hF : ∀ j ≤ 5, B.InCC (B.AB S.G.k S.G.r) (j + (2 * S.G.r + S.G.k + 1) * a.length)
      (D.cutF (T v).base χ (f v) ε) := fun j hj =>
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC (T v).base hχ hCC hε _ _ (weight_budget_L2_inequality S.G.k S.G.r S.Ntop A₀ hk2 j hj hA a.length hlen)
  have h5 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 5 (hF 5 le_rfl)
  have h4 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 4 (hF 4 (by norm_num))
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) le_rfl
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := h4
  exact (hC0 _ _ c4 c4 h5 h5 hc4 hc4).1

theorem L2_bound_at_built_place_holds : L2BoundAtTowerPlace := l2BoundAtBuiltPlace_of_cvInCC coefficient_vector_in_L2_class

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem foldCV_memB {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_memB hcl hJ s a) x.2 s

theorem mem_level_zero_of_mem_group {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem JF_smul' {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (c : ℂ)
    (G : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) : B.JF D (c • G) g = c • B.JF D G g := by
  show ∫ p, JF.xiP D p • B.rho D p (c • G) g ∂D.μSS = c • ∫ p, JF.xiP D p • B.rho D p G g ∂D.μSS
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [B.rho, Pi.smul_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

theorem thr_budget (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (m : ℕ) (hm : m ≤ (2 * r + k + 1) * (N + 1)) :
    JF.TransportedAlt k r (A₀ - 2 * ((r : ℝ) + 1) * (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ)) m := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set R : ℝ := (r : ℝ) + 1 with hRdef
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hMc : (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ) = n * ((N : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hmr : (m : ℝ) ≤ n * ((N : ℝ) + 1) := by rw [← hMc]; exact_mod_cast hm
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have h4 : R ≤ R ^ 4 := by
    have : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    calc R = R * 1 := by ring
      _ ≤ R * R ^ 3 := by gcongr
      _ = R ^ 4 := by ring
  set P : ℝ := (N : ℝ) * n ^ 2 + n ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have hA' : 100 * R * P ≤ A₀ := le_trans (by gcongr) hA
  have hnn : n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ n by linarith) hn0
    calc n = n * 1 := by ring
      _ ≤ n * n := this
      _ = n ^ 2 := by ring
  have hn23 : 3 * n ^ 2 ≤ n ^ 3 := by
    have := mul_le_mul_of_nonneg_right hn3 (sq_nonneg n)
    calc 3 * n ^ 2 ≤ n * n ^ 2 := this
      _ = n ^ 3 := by ring
  have hn1 : 3 * n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_right hn3 hn0
    calc 3 * n ≤ n * n := this
      _ = n ^ 2 := by ring
  have i1 : 8 * (n * (N : ℝ)) ≤ 100 * ((N : ℝ) * n ^ 2) := by
    have := mul_le_mul_of_nonneg_right hnn hN0
    nlinarith
  have i2 : 8 * n + 9 * n ^ 2 < 100 * n ^ 3 := by nlinarith
  have inner : 8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2 < 100 * P := by rw [hP]; nlinarith
  have key : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) < R * (100 * P) := mul_lt_mul_of_pos_left inner hR0
  have hrm : 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (n * ((N : ℝ) + 1)) := by
    have h6 : 6 * (r : ℝ) ≤ 6 * R := by rw [hRdef]; linarith
    calc 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (m : ℝ) := by gcongr
      _ ≤ 6 * R * (n * ((N : ℝ) + 1)) := by gcongr
  rw [hcast, hMc, lt_div_iff₀ (by positivity)]
  have e1 : R * (100 * P) = 100 * R * P := by ring
  have e2 : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) =
      2 * R * (n * ((N : ℝ) + 1)) + 6 * R * (n * ((N : ℝ) + 1)) + n ^ 2 * (9 * R) := by ring
  rw [e1, e2] at key
  linarith

theorem besselFoldBuilt_of (hC : CVInCC) : BesselFoldBuilt := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hcut, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set n : ℕ := 2 * S.G.r + S.G.k + 1 with hn
  set N : ℕ := S.Ntop with hN
  set A : ℝ := A₀ - 2 * ((S.G.r : ℝ) + 1) * ((n * (N + 1) : ℕ) : ℝ) with hAdef
  have hThr : ∀ m, m ≤ n * (N + 1) → JF.TransportedAlt S.G.k S.G.r A m := fun m hm =>
    thr_budget S.G.k S.G.r N A₀ hk2 hA m hm
  have hFcc : B.InCC A (n * (N + 1)) F :=
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC Db hcut hCC hε A (n * (N + 1)) (by rw [hAdef]; linarith)

  have hreg : ∀ a : List C.Letter, a.length ≤ N →
      B.InCC A (n * (N + 1 - a.length)) (foldCV S.G.k S.G.r s a F) := by
    intro a
    induction a with
    | nil => intro _; simp only [List.length_nil, Nat.sub_zero]; exact hFcc
    | cons x a ih =>
      intro hl
      simp only [List.length_cons] at hl
      have h1 := ih (by omega)
      have e : n * (N + 1 - a.length) = n * (N + 1 - (a.length + 1)) + (2 * S.G.r + S.G.k + 1) := by
        rw [← hn, ← Nat.mul_succ]; congr 1; omega
      rw [e] at h1
      have h2 := hC S.G.k S.G.r _ A _ _ (x.2 : ℂ) s h1
      simp only [List.length_cons]
      exact h2
  have hOp : IsOpen (Q.OmPlus S.G.k S.G.r Db.z Db.z') := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _
  intro a
  induction a with
  | nil => intro _ g _; rfl
  | cons x a ih =>
    intro hl g hg
    simp only [List.length_cons] at hl
    have ih' := ih (by omega)
    set H := foldCV S.G.k S.G.r s a F with hH
    set m : ℕ := n * (N + 1 - a.length) with hm
    have hHcc : B.InCC A m H := hreg a (by omega)
    have hnm : 2 * S.G.r + S.G.k + 1 ≤ m := by
      rw [hm, ← hn]; exact Nat.le_mul_of_pos_right n (by omega)
    have hmM : m ≤ n * (N + 1) := by rw [hm]; exact Nat.mul_le_mul_left n (by omega)
    have hThm := hThr m hmM
    have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) H :=
      Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast hnm) hHcc.choose_spec.1

    have hswap : B.JF Db (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = Q.CV S.G.k S.G.r (x.2 : ℂ) (B.JF Db H) g := by
      rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H (x.2 : ℂ) hnm hThm hHcc g hg]
      show ∫ p, JF.xiP Db p • B.rho Db p (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g ∂Db.μSS = _
      refine integral_congr_ae ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS Db] with p hp
      rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ Db (x.2 : ℂ) H p hp hCkn g hg.1]

    have hJHk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (B.JF Db H) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ :=
        (Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H hThm hHcc).1 g₀
          ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hfold : foldCV S.G.k S.G.r s a (B.JF Db F) ∈
        Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_memB hcl hJF s a
    have hfk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (foldCV S.G.k S.G.r s a (B.JF Db F)) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ := hfold.1 g₀
        ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1.2, fun b => hg₀.1.1 _ (by simp <;> omega)⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hloc := coefficient_vector_locality S.G.k S.G.r _ (Q.OmPlus S.G.k S.G.r Db.z Db.z') (B.JF Db H)
      (foldCV S.G.k S.G.r s a (B.JF Db F)) (x.2 : ℂ) hOp hJHk hfk
      (fun g' hg' => ih' g' ⟨hg'.2, hg'.1⟩) g ⟨hg.2, hg.1⟩
    show B.JF Db (s • Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = (s • Q.CV S.G.k S.G.r (x.2 : ℂ) (foldCV S.G.k S.G.r s a (B.JF Db F))) g
    rw [JF_smul', hswap, hloc, Pi.smul_apply]

end Formalism.FourierDecayAlt.P.CutMP.En
end
