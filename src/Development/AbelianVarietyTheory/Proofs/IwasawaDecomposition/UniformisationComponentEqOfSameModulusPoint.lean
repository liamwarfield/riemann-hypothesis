module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitary
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

theorem lie_coord_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x x₁ hx hx₁ e τ T hT
  obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r _ hU
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.HodgeSmooth.exists_diag_riem hσ hU W
  obtain ⟨Hm, -, -, hH⟩ := (W.period k x₁).2.2.2.2
  obtain ⟨hPx, hv⟩ := W.lie k x₁
  have h1 := hd k x₁ hx₁ (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH hPx.symm τ _ ((U.un k x₁).u τ) 1 (hv τ)
    (fun b => by
      convert GlobalTheory.isCombAt_single_of_isTanAt (U.un k x₁).x ((U.un k x₁).u τ) ((U.un k x₁).tan τ) b using 1
      show (fun b' => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) b' b) = Pi.single b 1
      funext b'
      rw [Matrix.one_apply, Pi.single_apply])
  have h2 := hd k x hx (W.ik k) (W.Pm k x₁) (W.period k x₁) Hm hH (hPx.symm.trans e) τ _ ((U.un k x₁).u τ) T
    (hv τ) hT
  have h3 : d k τ • (Tᴴ * T) = d k τ • (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) := by
    rw [← h2, h1, conjTranspose_one, Matrix.mul_one]
  exact smul_right_injective _ (hd0 k τ) h3

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesLieCoordinatesUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  first | exact @GlobalTheory.ShFam.lie_coord_unitary | exact GlobalTheory.ShFam.lie_coord_unitary | (intros; apply GlobalTheory.ShFam.lie_coord_unitary <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram GlobalTheory.TrueCx Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeGenUnf

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_mem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : Formalism.L2.PjFree.relab c σ τ.1 ∈ (U.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ.1).2 τ.2)

theorem comb_unitary {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x x₁ : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k) x₁.1)
    (e : (U.un k x₁).x = (U.un k x).x) (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hT : ∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) ((U.un k x₁).u τ b)) :
    Tᴴ * T = 1 :=
  GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary hσ hU k x x₁ hx hx₁ e τ T hT

theorem uniformisation_component_eq_of_same_modulusPoint {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨g0, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem unitary_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)} (hf : IsHodgeFrame Uf y f) (hg : IsHodgeFrame Uf y g)
    (τ : E →+* ℂ) : (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  have e1 : σ = σ' := by_contra fun h => (hE σ' (Ne.symm h)).false k
  have e2 : σ = σ₁ := by_contra fun h => (hE σ₁ (Ne.symm h)).false k₁
  subst e1 e2
  have hid : ∀ {ψ : ℂ →+* ℂ}, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) → σ = ψ.comp σ → ψ = RingHom.id ℂ := by
    intro ψ h h'
    rcases h with rfl | rfl
    · rfl
    · exact (not_good_conj c (σ := σ) hσ (h' ▸ hσ)).elim
  obtain rfl := hid h1 h2
  obtain rfl := hid g1 g2
  have hx : (cxPt Z ((Uf σ).un k x)).1 ≫ genι Z = spMap (RingHom.id ℂ) ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap (RingHom.id ℂ) h2 hx
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  obtain rfl : k = k₁ := (uniformisation_component_eq_of_same_modulusPoint hσ hU x x₁ e.symm).symm
  have key := comb_unitary hσ hU k x x₁ h4 g4 e τ _ (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  rw [h6.co τ hg' hx] at key
  convert key using 2 <;> ext <;> simp

theorem gram_eq_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ} {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : IsHodgeFrame Uf y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge Uf b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame Uf y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    unitary_of_single hE hσ hU h.choose_spec hf, Matrix.one_mul]

theorem unfFam_empty (U : Formalism.L2.PjFree.Unf Xo c σ r) (σ' : c.F →+* ℂ) (h : σ' ≠ σ) :
    IsEmpty (unfFam U σ').Comp := by
  unfold unfFam
  rw [dite_eq_right (Ne.symm h)]
  exact Empty.instIsEmpty

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := dif_pos rfl

theorem isHodgeFrame_of_eq {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hq : Uf σ = U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) :
    IsHodgeFrame (Z := Z) Uf (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) := by
  subst hq
  exact isHodgeFrame_cxFrame hσ hx


variable (Z) in
theorem hodgeMet_gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  rw [hodgeMet, gram_eq_of_single (unfFam_empty U) hσ ((unfFam_self U).symm ▸ hU)
    (isHodgeFrame_of_eq (unfFam_self U) hσ hx), EigFrame.co_self, conjTranspose_one, Matrix.mul_one]

end GlobalTheory.HodgeGenUnf

namespace GlobalTheory.HodgeGenUnf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

def letter {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : (U.X k).Ψ :=
  ⟨Formalism.L2.PjFree.relab c σ τ.1, relab_mem hσ hU k τ⟩

theorem mult_psi (τ : GlobalTheory.AllWt.Psi H) : Dw.mult τ.1 = Dw.p := if_pos τ.2


variable (Z) in
theorem hodgeMet_gram_frame {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (f : (U.X k).dom) (τ : GlobalTheory.AllWt.Psi H) (τ' : (U.X k).Ψ)
    (hτ : τ'.1 = Formalism.L2.PjFree.relab c σ τ.1) (hj : Dw.p ≤ Dw.p + Dw.q) :
    ((hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1).submatrix
        (Fin.cast (mult_psi τ).symm) (Fin.cast (mult_psi τ).symm) =
      ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) hj f.1 τ')ᴴ * (hP (moeb (frameCo (U.X k) hj f.1 τ') 0))⁻¹ *
        coW (U.X k) hj f.1 τ') := by
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k) f.1 f.2
  let f' : (U.X k).dom := ⟨x1, KU.orth_dom _ h1⟩
  have hz : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f.1 = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f'.1 := by
    show domPt _ _ _ f.1 = domPt _ _ _ x1
    rw [ef, domPt_rmul _ _ _ hb]
  have hmo : ∀ ρ : (U.X k).Ψ, moeb (frameCo (U.X k) hj f.1 ρ) 0 = moeb (frameCo (U.X k) hj f'.1 ρ) 0 :=
    fun ρ => congrFun hz ρ
  have h1' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f.2 f'.2 ρ (hmo ρ)
  have h2' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f'.2 f.2 ρ (hmo ρ).symm
  have hx : (U.un k f).x = (U.un k f').x := PointWell.pt_eq_of_block hU hσ k f f' h1' h2'
  have hg : (hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1 =
      (Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i)ᴴ *
        (hodgeMet Z U).gram (cxPt Z (U.un k f')) (cxFrame Z (U.un k f')) τ.1 *
        Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i :=
    eigGram_of_comb (hodgeMet Z U) _ _ hx τ.1 _ (fun i => lie_comb_of_block hU hσ k f f' h1' h2' τ.1 i)
  rw [hg, hodgeMet_gram_orth Z hσ hU (x := f') h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_submatrix_sq]
  set e := Fin.cast (mult_psi τ).symm
  have he : Function.Bijective e := (finCongr (mult_psi τ).symm).bijective
  rw [Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
  have hKe : (Matrix.of fun b i : Fin (Dw.mult τ.1) =>
      coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i).submatrix e e =
      Matrix.of fun b i : Fin Dw.p => coef (U.X k) f.1 f'.1 τ'.1 b i := by
    ext b i; rw [hτ]; rfl
  obtain ⟨hco1, -⟩ := hodge_co (U.X k) hj hp h1 τ'
  rw [hKe, coef_eq_coW_change (U.X k) hj hp f.2 f'.2 τ' (hmo τ'), hmo τ',
    eq_of_conj_eq_one (isUnit_coW _ _ hp f'.2 _) hco1]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeGenUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseReadingZeroWithoutEvaluationProperty
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.EvZero

open GlobalTheory.Mem.R3.Rw.GeoTies

def NoEvAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (v : M.Vec) {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ}
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (Z : Prop) : Prop :=
  GoodEmb T.Q.c s → ∀ hV : T.V j s = W,
    (¬ ∃ j' : (Fin n → L) →ₛₗ[σ] Hm.H, ∀ f : T.cuspA j (wtA w) w.n,
      Hm.e (j' (c f)) v = phiC T hV (wtA w) (f : T.R j)) → Z

theorem exists_extend {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) :
    ∃ j' : (Fin n → L') →ₛₗ[σ'] A, ∀ x x', CrdOver ι x x' → j' x' = j x := by
  refine ⟨{ toFun := fun x' => ∑ k, σ' (x' k) • j (Pi.single k 1), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  · intro a x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  · intro x x' h
    change ∑ k, σ' (x' k) • j (Pi.single k 1) = j x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, h.2 k k rfl]
    rfl

theorem NoEvAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm) (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v)
    {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hnn : n = n')
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (c' : T'.cuspA j (wtA w') w'.n → Fin n' → L')
    (hc : ∀ f f', HEq f' f → CrdOver ι (c f) (c' f')) {Z Z' : Prop} (hZ : Z → Z') :
    NoEvAtOne T j w s M Hm v (σ'.comp ι) c Z → NoEvAtOne T' j w' s' M' Hm' v' σ' c' Z' := by
  obtain ⟨⟨⟨H, l, cc, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', cc', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, m, _⟩ := w
  obtain ⟨aP', aM', _, _, m', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  subst hnn
  intro h hg hV hno
  refine hZ (h hg hV ?_)
  rintro ⟨j₀, hj₀⟩
  obtain ⟨j', hj'⟩ := exists_extend ι σ' j₀
  exact hno ⟨j', fun f => by rw [hj' _ _ (hc f f HEq.rfl)]; exact hj₀ f⟩

def intEquivOfEq {F F' : IntermediateField ℚ ℂ} (h : F' = F) : 𝓞 F ≃+* 𝓞 F' := by
  subst h
  exact RingEquiv.refl _

theorem coeff_field_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (h1 : HEq H' H) (h2 : HEq l' l) (h3 : HEq c' c) : c'.F = c.F := by
  cases h1
  cases h2
  cases h3
  rfl

theorem enlargedBase_reading_zero_without_evaluationProperty : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
      ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
          HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) →
      ∀ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), Formalism.L2.Pj.GoodEmb core'.Q.c (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) →
        ∀ hV : core'.V ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) = Wc (w'.st Z').toD7 i,
        (¬ ∃ j' : (Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL) →ₛₗ[σ] (R'.HW i σ).H, ∀ f : core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n,
          ((R'.HW i σ).e (j' ((e' i f : (R'.FW i).WK) : Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL))) (v₀' i σ) =
            hV ▸ core'.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) (wtA (κ' i)) (f : core'.R ((i : ℕ) + 1))) →
        (R'.FW i).j σ = 0 := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι κ' hκ v₀' hv e' he i' σ'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb : NoEvAtOne z.core ((i : ℕ) + 1) (z.geo.κ i) (res z.core (σ'.comp ι)) (z.R.MW i (σ'.comp ι)) (z.R.HW i (σ'.comp ι))
      (z.geo.v₀ i (σ'.comp ι)) (σ'.comp ι) (fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) ((z.R.FW i).j (σ'.comp ι) = 0) :=
    z.geo.fw.ev0 i (σ'.comp ι)
  have hnW := hRS.2.2.2.2.2.1
  have hcl := ((hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hMM : ModelSame (z.R.MW i (σ'.comp ι)) (R'.MW i' σ') :=
    ⟨hcl.1.1, hcl.1.2.1, hcl.1.2.2.1, hcl.1.2.2.2.1, hcl.1.2.2.2.2.1, hcl.1.2.2.2.2.2.1, hcl.1.2.2.2.2.2.2.1⟩
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  have hv1 := hv i i' hi σ'
  have he1 := he i i' hi
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host (w'.st Z').toD7.host.E := (by with_unfolding_all exact (z.core.Q.H :))
  let l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁ := (by with_unfolding_all exact (z.core.Q.l :))
  let c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁ := (by with_unfolding_all exact (z.core.Q.c :))
  have hF : core'.Q.c.F = c₁.F := coeff_field_eq (H := H₁) (l := l₁) (c := c₁) ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :)))
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := H₁, l := l₁, c := c₁, Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (intEquivOfEq hF).trans core'.Q.eO }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let u₀ : M₀.Vec := (by with_unfolding_all exact ((z.geo.v₀ i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let c₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL :=
    (by with_unfolding_all exact ((fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) :))
  exact (by with_unfolding_all exact ((NoEvAtOne.congr core₀ core' ((c1)) ((c2)) ((c3)) ((c4)) ((c5)) ((c6)) ((c7)) ((c8)) ((c9)) ((c10))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((hP)) ((hM)) ((hnn)) s₀ (res core' σ') ((hs)) M₀ (R'.MW i' σ') ((hMM))
    H₀ (R'.HW i' σ') ((hH)) u₀ (v₀' i' σ') ((hv1)) ι σ' hn c₀ (fun φ => (e' i' φ : (R'.FW i').WK).1) ((he1)) hZ ((hb))) : _))

end GlobalTheory.Mem.R3.Rw.EvZero

end
end
