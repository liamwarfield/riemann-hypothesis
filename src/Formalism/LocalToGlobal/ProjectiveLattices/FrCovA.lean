module

public import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FrCovA
noncomputable section

namespace Formalism.L2.Pj.FrCov

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

section Comb

variable {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
  {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}

theorem eps_dual (ψ : S →+* T) (a : S) : spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

end Comb

variable (hS' : Out.SecBaseChangeAnySt) (hT : Out.SecTwistSt) {R T T' : Type} [CommRing R] [Algebra c.F R] [CommRing T]
  [Algebra c.F T] [CommRing T'] [Algebra c.F T']

abbrev Mx (Dw : Datum H) (T : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T

variable {y : FrPt Xo c R} {a : R →ₐ[c.F] T} {M M' N : Mx Dw T} {t t' r : T} {z z' : FrPt Xo c T} {w : FrPt Xo c T'}

include hS' hT

end Formalism.L2.Pj.FrCov
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenSpecSep
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sepX (Xo : Moduli Dw l) : SepXSt Xo := by
  unfold SepXSt
  have hq := Xo.qproj
  unfold IsQProjOver at hq
  obtain ⟨N, i, hi, -, hcomp⟩ := hq
  rw [← hcomp]
  haveI := hi
  infer_instance

theorem spMap_isDominant {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (hφ : Function.Injective φ) :
    IsDominant (spMap φ) := by
  unfold spMap
  constructor
  have hd : DenseRange (PrimeSpectrum.comap φ) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact hd

theorem x_eq_of_inj (Xo : Moduli Dw l) {S T : Type} [CommRing S] [IsReduced S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Injective φ) {f g : Sp S ⟶ Xo.X} (hs : f ≫ Xo.s = g ≫ Xo.s)
    (h : spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  haveI : IsSeparated Xo.s := sepX Xo
  haveI : IsDominant (spMap φ) := spMap_isDominant φ hφ
  first
  | exact ext_of_isDominant_of_isSeparated Xo.s hs (spMap φ) h
  | exact ext_of_isDominant_of_isSeparated Xo.s hs h
  | exact ext_of_isDominant_of_isSeparated (s := Xo.s) hs (ι := spMap φ) h

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FnDefE
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.NrmTieDef
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def nrmTieDefRd (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ) :=
  (rdEx_of U hU hA hB σ y).choose

end Gen

section Rec

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)


variable {j} in
def NrmTieKC (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) (F : (recB hL).Cusp j ka),
    nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P =
      recNrm (Tc.U j (goodOf Tc.Q.c (sgOf P))) (xiR D) (wtA ka) ka.n (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

def nrmTieDefPt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c)
    (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ) (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) :
    SupPtAt j (goodOf Tc.Q.c (sgOf P)) :=
  ⟨(nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).1,
    (nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).2.1⟩

end Rec

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hconj : ∀ z : E, τ.1 (cc z) = starRingEnd ℂ (τ.1 z) := fun z =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ.1 z
  have hcc : ∀ (b q : Fin r), cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro b q
    by_cases h : q = b
    · subst h
      simp [cc]
    · simp [cc, Pi.single_eq_of_ne h]
  have hU : ∀ a b : Fin r, ∑ p, ∑ q, (γ : Matrix (Fin r) (Fin r) E) p a * X.Gm p q *
      cc ((γ : Matrix (Fin r) (Fin r) E) q b) = X.Gm a b := by
    intro a b
    have h := (X.Γ_stab γ hγ).1 (Pi.single a 1) (Pi.single b 1)
    simp only [herm, hcc] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hUm : Matrix.transpose (γ : Matrix (Fin r) (Fin r) E) * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
    ext a b
    rw [← hU a b]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hg : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Matrix.transpose M * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a b
    simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hmat : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp only [Matrix.map_apply, hconj]
  have e : X.Gm.map τ.1 = (Matrix.transpose (γ : Matrix (Fin r) (Fin r) E)).map τ.1 * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    conv_lhs => rw [← hUm]
    rw [Matrix.map_mul, Matrix.map_mul]
  have key : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hg, hg, hmat, Matrix.transpose_mul, Matrix.map_mul, hc, ← Matrix.transpose_map]
    conv_rhs => rw [e]
    simp only [Matrix.mul_assoc]
  unfold dmin
  rw [key]

theorem dmin_ne_of_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
    first
      | exact (hx τ).2 i
      | (simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
         exact (hx τ).2 i)
  rw [h0] at h1
  simp at h1

theorem continuousOn_pnorm (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom) :
    ContinuousOn (X.pnorm la P) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    simp only [dmin, lminor, gram, hermC, col, mat, Matrix.det_apply, Matrix.submatrix_apply,
      Matrix.of_apply, starRingEnd_apply, Units.smul_def, zsmul_eq_mul]
    first | fun_prop | continuity
  have hterm : ∀ (τ : X.Ψ) (i : Fin r), ContinuousOn
      (fun x => ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) X.dom := by
    intro τ i
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn
        fun x hx => dmin_ne_of_dom X hx τ _).norm
    · intro x hx
      exact Or.inl (norm_ne_zero_iff.2 (div_ne_zero (dmin_ne_of_dom X hx τ _) (dmin_ne_of_dom X hx τ _)))
  unfold Data.pnorm
  refine ContinuousOn.mul hP.norm ?_
  first
    | exact continuousOn_finset_prod _ fun τ _ => continuousOn_finset_prod _ fun i _ => hterm τ i
    | fun_prop

end FD

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Gen

section Core

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps CompSplitPfB

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)


variable {j} in
def CompOf (cm : ∀ σ : Tc.Q.c.F →+* ℂ, (Tc.U j σ).Comp → Comp (Tc.Q.Xo j) Tc.Q.c) : Prop :=
  ∀ (σ : Tc.Q.c.F →+* ℂ) (k : (Tc.U j σ).Comp) (x : ((Tc.U j σ).X k).dom) (q : PrimeSpectrum (CAt σ)),
    cspB_lift ((Tc.U j σ).un k x).x ((Tc.U j σ).un k x).x_over q ∈
      ((cm σ k : Comp (Tc.Q.Xo j) Tc.Q.c) : Set ((Tc.Q.Xo j).XF Tc.Q.c))

def ptAt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c) (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ)
    (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c)
    (P : Om Z →+* ℂ) (sg : Tc.Q.c.F →+* ℂ) (hP : sgOf P = sg) : SupPtAt j (goodOf Tc.Q.c sg) :=
  hP ▸ nrmTieDefPt hL j hj hA hB h hb Z P

end Core

end Formalism.L2.Pj
end
end
