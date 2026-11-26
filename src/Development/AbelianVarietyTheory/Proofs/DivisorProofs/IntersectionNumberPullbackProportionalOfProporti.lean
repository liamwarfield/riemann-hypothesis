module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem interNumRed_pull_curve {k : Type} [Field k] {M W : Scheme.{0}} (p : W ⟶ Sp k)
    (f : M ⟶ W) [IsProper p] (C : Closeds M) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom (f ≫ p)
    IsCompleteCurve k C →
    (∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = 0) ∨
    ∃ C' : Closeds W, IsCompleteCurve k C' ∧ ∃ d : ℕ, ∀ L : LB W, L.IsLB →
      interNumRed k C ![L.pull f] = d * interNumRed k C' ![L] := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  have hcomp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
      (f : Y ⟶ X) (g : Z ⟶ Y) :
      cls ((L.pull f).pull g) (LB.isLB_pull (LB.isLB_pull hL f) g) =
        cls (L.pull (g ≫ f)) (LB.isLB_pull hL _) := by
    exact (cls_eq_iff _ _).2 (iso_of_chart (LB.isLB_pull hL _)
      (chartPullLinComb L f (fun _ : PUnit => g) (fun _ => g ≫ f) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm))
  intro hC
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red hC.isIrreducible
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
    algebraΓOfHom (redι C ≫ f ≫ p)
  let g := redι C ≫ f
  have hsM : strHom k M = f ≫ p := strHom_eq (fun _ => rfl)
  have hsW : strHom k W = p := strHom_eq (fun _ => rfl)
  have hsZ : strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme = g ≫ p :=
    (strHom_eq (f := redι C ≫ f ≫ p) (fun _ => rfl)).trans (Category.assoc _ _ _).symm
  have hpZ : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal C).subscheme)) := by
    have := hC.isProper
    rw [hsM] at this
    rw [hsZ, Category.assoc]
    exact this
  have : IsProper (g ≫ p) := hsZ ▸ hpZ
  have : IsProper g := .of_comp g p
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = 1 :=
    (topologicalKrullDim_red C).trans hC.dim_eq
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (strHom k _)
  have := isNoetherian_of_locallyOfFiniteType_field
    (strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
  have hdeg : ∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = topSelfIntersection k (L.pull g) 1 := by
    intro L hL
    have hL' := LB.isLB_pull hL f
    refine (interNumOn_eq_interNum_pull (appTop_algebraΓOfHom (redι C) (f ≫ p) rfl)
      (isLB_vecOne hL')).trans ?_
    refine interNum_congr_cls k _ (fun i => by fin_cases i; exact LB.isLB_pull hL' _)
      (fun _ => LB.isLB_pull hL g) fun i => ?_
    fin_cases i
    exact hcomp hL f (redι C)
  by_cases hc : ∀ z, g z = g (genericPoint _)
  · left
    intro L hL
    rw [hdeg L hL]
    exact ArInt.topSelf_pull_eq_zero_of_const k hL g _ hc
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  right
  let φ := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint _) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint _) = genericPoint g.image := by
    have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal C).subscheme).image
      φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 :=
    le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (ArInt.one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  letI : Algebra k Γ(g.image, ⊤) := algebraΓOfHom (g.imageι ≫ p)
  have hf : ∀ r : k, φ.appTop (algebraMap k Γ(g.image, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r :=
    appTop_algebraΓOfHom φ (g.imageι ≫ p) (by rw [reassoc_of% e]; exact Category.assoc _ _ _)
  have hsI : strHom k g.image = g.imageι ≫ p := strHom_eq (fun _ => rfl)
  have : IsProper (strHom k (X := g.image)) := by rw [hsI]; infer_instance
  have hproj : IsProjOver (strHom k (X := g.image)) := ProperCurve.isProjOver_of_isProper _ hdZ
  have : IsProper (g.imageι ≫ strHom k W) := by rw [hsW]; infer_instance
  refine ⟨⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩,
    isCompleteCurve_range g.imageι hdZ, φ.residueDegree (genericPoint _), fun L hL => ?_⟩
  have hN := LB.isLB_pull hL g.imageι
  have h₁ := ProjFin.interNumOn_eq_residueDegree_mul k g.image _ φ hproj hdZ hgen
    (L.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := k) (L := ![L.pull g.imageι]) hf (isLB_vecOne hN)
  have h₃ : topSelfIntersection k (L.pull g) 1 = interNum k (structureModule _)
      fun i => (![L.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => LB.isLB_pull hL g)
      (fun i => by fin_cases i; exact LB.isLB_pull hN φ) fun i => ?_
    fin_cases i
    change cls (L.pull g) _ = cls ((L.pull g.imageι).pull φ) _
    simpa only [e] using (hcomp hL g.imageι φ).symm
  have h₄ : interNumRed k ⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩ ![L] =
      interNum k (structureModule g.image) ![L.pull g.imageι] :=
    (InterModel.interNumRed_eq_interNumOn k g.imageι _ rfl _).trans
      ((interNumOn_eq_interNum_pull (appTop_algebraΓOfHom g.imageι p rfl) (isLB_vecOne hL)).trans
        (congrArg _ (funext fun j => by fin_cases j; rfl)))
  rw [hdeg L hL, h₃, ← h₂, h₁, h₄]

end GlobalTheory.NumPull

namespace GlobalTheory.NumPull

theorem interNumRed_pull_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  intro M W _ _ p f hp _
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro L L' hL hL' a b H C hC
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  rcases interNumRed_pull_curve p f C hC with h | ⟨C', hC', d, hd⟩
  · rw [h L hL, h L' hL', mul_zero, mul_zero]
  · rw [hd L hL, hd L' hL']
    linear_combination (d : ℤ) * H C' hC'

end GlobalTheory.NumPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProportiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  first | exact @GlobalTheory.NumPull.interNumRed_pull_proportional | exact GlobalTheory.NumPull.interNumRed_pull_proportional | (intros; apply GlobalTheory.NumPull.interNumRed_pull_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
noncomputable section

namespace GlobalTheory.CovTop.VolUp

open NumberField MeasureTheory Matrix Formalism.BasicNotions GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

def dg {ι : Type} [DecidableEq ι] (a₀ : ι) (z : ℂ) : Matrix ι ι ℂ := Matrix.diagonal (Function.update 1 a₀ z)

def sMat {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  UpqT.mat u * dg a₀ (UpqT.mat u).det⁻¹

def permM {ι : Type} {r : ℕ} (e : ι ≃ Fin r) : Matrix ι (Fin r) ℂ := Matrix.of fun i j => if e i = j then 1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def frBall (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (ε : ℝ) : Set (realSU Ψ G) :=
  {s | ∀ τ a b, ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}

def IsIdent {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ = -(G.map (σ ρ).1)ᵀ ∧ A ρ * mat x (σ ρ) = permM (e ρ)

def IsProj {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ))
    (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) : Prop :=
  ∀ b ρ, A ρ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = sMat (a₀ ρ) (b ρ) * A ρ

section Adelic

open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsRealPart {D : D7} (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V → ∀ ρ, Upq V ρ) : Prop :=
  ∀ h ρ, UpqT.mat (rp h ρ) * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h

end Adelic

theorem permM_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) : permM e * (permM e)ᵀ = 1 := by
  ext i j
  simp [permM, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem transpose_mul_permM {ι : Type} [Fintype ι] (e : ι ≃ Fin r) : (permM e)ᵀ * permM e = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.one_apply, eq_comm]

theorem det_dg {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (z : ℂ) : (dg a₀ z).det = z := by
  rw [dg, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end GlobalTheory.CovTop.VolUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameDenseZ


open _root_.Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT in
theorem exists_poly_div_det_secZ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    (e : Ix Dw → ℤ) (F : Rul Xo c) (hF : F ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S)
      (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)),
      (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := GlobalTheory.LamT.RatFn.exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.FrameDenseZ

namespace GlobalTheory.FrameDenseZ


open _root_.Formalism.L2.LamCM in
theorem exists_frame_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] (m : B → ℕ)
    (P : MvPolynomial (FrVar m) K) (hP : P ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr P Y ≠ 0 := by
  classical
  have hD : ∀ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 := by
    intro b h
    have := GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly (K := K) m b (fun _ => 1)
    rw [h] at this
    simp [evalFr] at this
  have hQ : P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 :=
    mul_ne_zero hP (Finset.prod_ne_zero_iff.2 fun b _ => hD b)
  obtain ⟨v, hv⟩ : ∃ v : FrVar m → K,
      MvPolynomial.eval v (P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ (MvPolynomial.funext fun x => by simp only [h x, map_zero])
  let Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => v ⟨b, (j, i)⟩
  have hY : ∀ R : MvPolynomial (FrVar m) K, evalFr R Y = MvPolynomial.eval v R := fun R => rfl
  rw [map_mul, map_prod] at hv
  refine ⟨Y, fun b => ?_, ?_⟩
  · rw [← GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly m b Y, hY]
    exact (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hv)) b (Finset.mem_univ b)
  · rw [hY]
    exact left_ne_zero_of_mul hv

theorem exists_frame_evR_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y e F hF σ σ₁ w hw hne
  classical
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_secZ E H Dw l Xo c K y e F hF
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hP0 : P ≠ 0 := by
    intro hP0
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ :=
      (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e' : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e'
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
      ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
    have hv := hP _ σ₁ z z1 (fun b => (g b).transpose)
      (fun b => by rw [Matrix.det_transpose]; exact hg b) hz
      (by simpa only [Matrix.transpose_transpose] using h1)
    rw [hP0, map_zero] at hv
    have hz1 : evR Xo c F z1 = 0 := by
      have hdet : (∏ b, ((g b).transpose).det) ^ N ≠ 0 :=
        pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun b _ => by
          rw [Matrix.det_transpose]; exact (hg b).ne_zero)
      have h00 : Formalism.L2.LamCM.evalFr (0 : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) (CAt σ))
          (fun b => (g b).transpose) = 0 := by simp [Formalism.L2.LamCM.evalFr]
      rw [h00] at hv
      exact (mul_eq_zero.1 hv).resolve_left hdet
    apply hne
    rw [GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF (CAt σ) t z1 z2 hb, hz1, mul_zero]
  obtain ⟨Y, hYd, hYv⟩ := exists_frame_evalFr_ne_zero Dw.mult P hP0
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hYd b).isUnit)
  refine ⟨y', hy'.1, fun h0 => hYv ?_⟩
  have hv := hP K (AlgHom.id c.F K) y y' Y (fun b => (hYd b).isUnit)
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y).2.1 hy'
  rw [h0, mul_zero, show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at hv
  exact hv.symm

end GlobalTheory.FrameDenseZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberFieldFrame_value_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  first | exact @GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex | exact GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex | (intros; apply GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)

def pc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)

variable (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_pow_left {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP (x ^ k) y = k • pc hP x y := by
  have one : pc hP (1 : T ⟶ A) y = 0 := by
    have := hB T 1 1 y
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]

include hB' in
theorem pc_pow_right {T : Over S} (x y : T ⟶ A) (k : ℕ) : pc hP x (y ^ k) = k • pc hP x y := by
  have one : pc hP x (1 : T ⟶ A) = 0 := by
    have := hB' T x 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  induction k with
  | zero => rw [pow_zero, one, zero_smul]
  | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]


include hB hB' in
theorem exists_theta_diag {k : ℕ} {T : Over S} (x : T ⟶ A) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl
  have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : k • pc hP (fst T A ≫ x) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (fst T A ≫ x)
    rwa [_root_.mul_one, left_eq_add] at this
  have h2 : k • pc hP (fst T A ≫ x) (snd T A) = 0 := by
    rw [← pc_pow_left hP hB, ha]
    have := hB (T ⊗ A) 1 1 (snd T A)
    rwa [_root_.mul_one, left_eq_add] at this
  have h3 : k • pc hP (snd T A) (fst T A ≫ x) = 0 := by
    rw [← pc_pow_right hP hB', ha]
    have := hB' (T ⊗ A) (snd T A) 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
    abel
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Classes

section Mul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]


open WeilMul in
theorem weilIs_mul_left (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ}
    {T : Over S} {x x' y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c)
    (h' : Out.WeilIs A L k x' y c') : Out.WeilIs A L k (x * x') y (c * c') := by
  intro p
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le hL (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le hL (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul hL (hc'.congr hG hA hL rfl (py.trans py'.symm))
  have q : θ.pt = Out.overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff hL _ _ _ _).2 (hθ.congr hG hA hL (p₁.trans q.symm) (p₂.trans py.symm))

end Mul

end GlobalTheory.DiagPairing

namespace GlobalTheory.DiagPairing

open GlobalTheory.CechPic

theorem exists_weilIs_diag_root : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N →
    IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := by
  intro h n B _ ζ S s c N T x y hamp hN _ hx hy
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ c.A), pc c.isLB (x * x') y = pc c.isLB x y + pc c.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ c.A), pc c.isLB x (y * y') = pc c.isLB x y + pc c.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab hD hamp c.P c.isLB c.rig₁ c.rig₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ c.A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp c.A c.diag N (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag c.isLB hB hB' (k := N) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG c.ab hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := weilIs_mul_left hG c.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG c.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs c.A c.diag N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact weilIs_mul_left hG c.ab hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG c.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.DiagPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory

theorem exists_rdU_ne_zero_of_mem_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, F ≠ 0 → ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U hU e F hF hF0
  by_contra hcon
  push_neg at hcon
  apply hF0
  funext p y
  show F p y = 0
  refine Formalism.L2.Pj.eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨k, x, u, hk⟩ :=
    GlobalTheory.test_value_eq_const_mul_reading_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange U hU e p y ψ
  have h := hk F hF
  rw [hcon k x.1 x.2, mul_zero] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationFrame_reading_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, F ≠ 0 → ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
  first | exact @GlobalTheory.exists_rdU_ne_zero_of_mem_secZ | exact GlobalTheory.exists_rdU_ne_zero_of_mem_secZ | (intros; apply GlobalTheory.exists_rdU_ne_zero_of_mem_secZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.PetDef

open MeasureTheory _root_.Formalism.L2.Theta Formalism.BasicNotions.TH ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Topology TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adelAut_of_gamma {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, γ ∈ (X k).Γ → (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr)
    (hm : MuUnit V dict mu) (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (eqv_holSub X la (holCusp_mem_holSub X la hP)).2 (dict g).1 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (X k).IsSec (la k) (P k) := (hP k).1.1
    have hPc : ContinuousOn (P k) (X k).dom := hsec.1.continuousOn
    have hc : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hmc.continuousOn.mul (hPc.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd', γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd', hχ _ _ _ hγ, one_mul]
    exact (hc.continuousAt hN).congr heq

end Gen

section Cover

variable {D : D7} {T : Core D} {j : ℕ}

theorem dictLoc_of_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ)
    (hσ : GoodEmb Y.d.c₂ σ) : ∃ th hr, DictIsUnif (D.sp.W j) (Y.dict σ) Y.Kf th hr ∧ DictLoc (D.sp.W j) (Y.dict σ) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  refine ⟨th, hr, hd, ?_⟩
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hK : Y.Kf ≤ GfC (D.sp.W j) := fun k hk => ((h.levelK k).1 hk).1
  exact GlobalTheory.DictLocTest.locClause_of_unif_places hd hK (GlobalTheory.T.principalLevel_mul_archimedean_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)

theorem muUnit_one (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
  ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, h.unit σ hσ⟩

theorem adelAut_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelAut (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, hL⟩ := dictLoc_of_good Y h σ hσ
  exact adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd (muUnit_one Y h σ hσ) hL
    continuous_const

theorem aeDom_good (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AeDom Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hd, -⟩ := dictLoc_of_good Y h σ hσ
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)
  exact aeDom_of_aut Y.d.Xo₂ Y.d.c₂ (adelAut_good Y h σ hσ) (quotSupp_of _ hV hP) (muUnit_one Y h σ hσ) hd

end Cover

end GlobalTheory.PetDef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLower

theorem weilIs_lower_field {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {n d : ℕ} (hd : d ≠ 0) {T : Over (Sp K)} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * d) = 1) (hy : y ^ (n * d) = 1)
    (h : Out.WeilIs A L ((n * d : ℕ) : ℤ) x y c) : Out.WeilIs A L n (x ^ d) (y ^ d) (c ^ d) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := K) (L.pull (eSec A)) (pull_isLB hL _)
  let M : RigLB A := ⟨L, r, hL, hr⟩
  obtain ⟨t, ht⟩ := AbLaw.CubeProj.exists_gen_theta_abelianVariety globalFns_holds K A hA
    (AbelianProjective.isProjBy_of_isAbelianScheme K A hA) L hL
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hL t ht
  let cub : CubicalStr A M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hA M t' ht' hn
  have hx' : (x ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hx]
  have hy' : (y ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hy]
  obtain ⟨w, hw⟩ := exists_weil cub hx' hy'
  have h₁ : Out.WeilIs A L n (x ^ d) (y ^ d) w := (weilIs_iff cub globalFns_holds hA hx' hy' hw w).2 rfl
  have h' := CommPairing.weilIs_symm hL h
  have hp : ∀ j : ℕ, Out.WeilIs A L ((n * d : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact SiegelTypings.weilIs_mul hA hL ih h'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h₂ := CommPairing.weilIs_symm hL (hp j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  rw [PairingLevels.weilIs_value_eq globalFns_holds hA hL ht h₂ h₁]
  exact h₁

variable {h N : ℕ} {B' : Type} [CommRing B'] {ζ' : B'} {S : Scheme.{0}} {s' : S ⟶ Sp B'}

theorem weilIs_lower (C : SiegPre h N ζ' s') {K : Type} [Field K] [IsAlgClosed K] (p : Sp K ⟶ S) {n d : ℕ} (hd : d ≠ 0) :
    ∀ (x y : Over.mk p ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
  obtain ⟨c, φ, φ₂, pb, sq, iso, -⟩ := (siegPre_pullback h N B' ζ' S _ s' _ p C rfl).1
  have key : ∀ q : Sp K ⟶ S, q = 𝟙 _ ≫ p → ∀ (x y : Over.mk q ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
    rintro q rfl x y u hx hy H
    let e := ObjPull.pushEquiv pb (Over.mk (𝟙 (Sp K)))
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    have tr := fun (k : ℤ) (a b : Over.mk (𝟙 (Sp K)) ⟶ c.A) (v : Γ(Sp K, ⊤)ˣ) =>
      weilIs_grpPullback_of_comm S _ C.A c.A p φ C.diag c.diag (pull_isLB C.isLB _) (pull_isLB c.isLB _) pb
        (SiegelPull.diag_iso sq iso) (Over.mk (𝟙 _)) k a b (e a) (e b) v rfl rfl
    have hx' : x ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hx.trans (map_one e).symm))
    have hy' : y ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hy.trans (map_one e).symm))
    have H' := (tr _ _ _ _).1 (weilIs_lower_field c.ab (pull_isLB c.isLB _) hd hx' hy' ((tr _ _ _ _).2 H))
    rw [map_pow, map_pow] at H'
    have e' : unitOn (u ^ d) = unitOn u ^ d := map_pow _ _ _
    rw [e']
    exact H'
  exact key p (Category.id_comp p).symm

def lower (C : SiegPre h N ζ' s') {n d : ℕ} (hN : N = n * d) (h0 : N ≠ 0) {B : Type} [CommRing B] {ζ : B} (j : B →+* B')
    (hj : j ζ = ζ' ^ d) : SiegPre h n ζ (s' ≫ spMap j) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add a b := by rw [C.lev_add, mul_pow]
  lev_tors a := by rw [← pow_mul, mul_comm, ← hN, C.lev_tors]
  geom k _ _ x β z hx hz := by
    have hn : n ≠ 0 := fun e => h0 (by rw [hN, e, zero_mul])
    have hd : d ≠ 0 := fun e => h0 (by rw [hN, e, mul_zero])
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, x ≫ s' = spMap β' :=
      ⟨(Spec.preimage (x ≫ s')).hom, (Spec.map_preimage _).symm⟩
    have hβ : β = β'.comp j := by
      have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom (β'.comp j)) := by
        refine hx.symm.trans ?_
        rw [← Category.assoc, hβ']
        exact (Spec.map_comp _ _).symm
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    have hz' : (z : k) = β' ζ' ^ d := by rw [hz, hβ, RingHom.comp_apply, hj, map_pow]
    have hu : β' ζ' ≠ 0 := fun e => z.ne_zero (by rw [hz', e, zero_pow hd])
    have ez : z = Units.mk0 _ hu ^ d := Units.ext (by rw [hz', Units.val_pow_eq_pow_val, Units.val_mk0])
    obtain ⟨g₁, g₂, g₃⟩ := C.geom k x β' (Units.mk0 _ hu) hβ' rfl
    refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
    · rw [← SiegelTypings.lev_nsmul, g₁]
      refine exists_congr fun b => ?_
      rw [hN, mul_comm, mul_smul]
      exact (smul_right_injective _ hd).eq_iff
    · obtain ⟨a, rfl⟩ := g₂ g ((congrArg (g ^ ·) hN).trans (by rw [pow_mul, hg, one_pow]))
      rw [← MonObj.comp_pow, ← SiegelTypings.lev_nsmul, g₁] at hg
      obtain ⟨b, hb⟩ := hg
      rw [hN, mul_smul] at hb
      exact ⟨b, by rw [smul_right_injective _ hn hb, SiegelTypings.lev_nsmul]⟩
    · have t : ∀ a, (toUnit (Over.mk x) ≫ C.lev a) ^ (n * d) = 1 := fun a => by
        rw [← MonObj.comp_pow, ← hN, C.lev_tors, MonObj.comp_one]
      have H := weilIs_lower C x hd _ _ _ (t a) (t b) (by rw [← hN]; exact g₃ a b)
      have e : (Units.mk0 _ hu ^ d) ^ (2 * omegaStd a b) = (Units.mk0 _ hu ^ (2 * omegaStd a b)) ^ d := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      show Out.WeilIs C.A C.diag n (toUnit (Over.mk x) ≫ C.lev a ^ d) (toUnit (Over.mk x) ≫ C.lev b ^ d)
        (unitOn (z ^ (2 * omegaStd a b)))
      rw [ez, e, MonObj.comp_pow, MonObj.comp_pow]
      exact H

theorem isGrpPullback_id (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 G.left) G.hom G.hom (𝟙 S)),
    fun T x y x₀ y₀ hx hy => ?_⟩
  refine Eq.trans ?_ (Category.comp_id _).symm
  exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))

theorem lbIso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  (LBIso.chartPull (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl) (chartPullId L) (lbIso_refl hL)).symm

theorem exists_lower : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B')
    (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) →
    ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  intro h n N B B' _ _ ζ ζ' j S s' C h0 _ hn hj
  have sq : IsSquare (G' := C.A) (G := C.A) (𝟙 _) (𝟙 _) := ⟨by simp, by simp⟩
  refine ⟨lower C (Nat.mul_div_cancel' hn).symm h0 j hj,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩⟩
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.SiegLower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_lowered_level : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) → ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  first | exact @GlobalTheory.SiegLower.exists_lower | exact GlobalTheory.SiegLower.exists_lower | (intros; apply GlobalTheory.SiegLower.exists_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.CovTop.MeasFin

theorem measure_ne_top_of_isMeasFD {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (μ : MeasureTheory.Measure (GA D V)) (𝓕 : Set (GA D V)) (hF : IsMeasFD V K μ 𝓕) : μ 𝓕 ≠ ⊤ :=
  (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hF.1.1 hF.2).ne

end GlobalTheory.CovTop.MeasFin
end
