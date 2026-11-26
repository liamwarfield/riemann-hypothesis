module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralAndArchimedeanBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubmatrixMulVec
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
open scoped Matrix

namespace GlobalTheory.FlatChange

theorem exists_blockMat {J : Type} [Fintype J] {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ, Fin (m τ))
    (K : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ) :
    ∃ V : Matrix (Fin g) (Fin g) ℂ, ∀ (z : Fin g → ℂ) τ i,
      (V *ᵥ z) (e.symm ⟨τ, i⟩) = (K τ *ᵥ fun j => z (e.symm ⟨τ, j⟩)) i := by
  classical
  refine ⟨(Matrix.blockDiagonal' K).submatrix e e, fun z τ i => ?_⟩
  rw [Matrix.mulVec, dotProduct, ← e.symm.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct]
  · intro τ' _ h
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ h.symm]
  · simp

theorem det_mul_eq_one {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ C i = Pi.single i 1) : B.det * C.det = 1 := by
  subst h
  have : B * Cᵀ = 1 := by
    ext a i
    have := congrFun (hC i) a
    rw [Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  rw [← Matrix.det_transpose C, ← Matrix.det_mul, this, Matrix.det_one]

theorem submatrix_mulVec {n r : ℕ} (h : n = r) (B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) (i : Fin n) :
    (B.submatrix (Fin.cast h) (Fin.cast h) *ᵥ fun j => v (Fin.cast h j)) i = (B *ᵥ v) (Fin.cast h i) := by
  subst h
  rfl

theorem perFr_of_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} (h : n = r) (X : Data E r)
    (h0 : X.p0 = 0) (x : Frame X.Ψ r) (v : Fin r → E) {ρ : E →+* ℂ} (hρ : ρ ∈ X.Ψ) (i : Fin n) :
    perFr X x v ρ i = ((mat x ⟨ρ, hρ⟩)⁻¹ *ᵥ Data.emb ρ v) (Fin.cast h i) := by
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
  unfold perFr
  rw [dif_pos hρ, dif_pos hi]
  congr 1
  ext
  simp [h0]


set_option maxHeartbeats 1000000 in
theorem det_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Dw.q = 0 → GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x x' : (U.X k).dom) (τ : Psi H) (hτ : relab c σ τ.1 ∈ (U.X k).Ψ) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) (CAt σ))) (a : CAt σ), FrChg g a (U.un k x) (U.un k x') → (mat x'.1 ⟨_, hτ⟩).det = toC (g τ.1).det * (mat x.1 ⟨_, hτ⟩).det := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hq hσ hU k x x' τ hτ cf a hchg
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨-, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hΨ⟩ := hty k
  obtain ⟨P, hPe, p, hx, hd, -⟩ := hpt k x
  obtain ⟨P', hPe', p', -, hd', -⟩ := hpt k x'
  have hm : ∀ ρ, relab c σ ρ ∈ (U.X k).Ψ → Dw.mult ρ = r := fun ρ h => by
    unfold Datum.mult
    rw [if_pos ((hrt ρ).1 ((hΨ _).1 h))]; omega
  have hm' : ∀ ρ, Fin (Dw.mult ρ) → relab c σ ρ ∈ (U.X k).Ψ := fun ρ i => by
    by_contra h
    have h1 : Dw.mult ρ = 0 := by
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hΨ _).2 ((hrt ρ).2 h'))), hq]
    have := i.2
    omega
  let B : (U.X k).Ψ → Matrix (Fin r) (Fin r) ℂ := fun ρ => (mat x'.1 ρ)⁻¹ * mat x.1 ρ
  let K : ∀ ρ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ := fun ρ =>
    if h : relab c σ ρ ∈ (U.X k).Ψ then (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) else 0
  have hK : ∀ ρ (h : relab c σ ρ ∈ (U.X k).Ψ),
      K ρ = (B ⟨_, h⟩).submatrix (Fin.cast (hm ρ h)) (Fin.cast (hm ρ h)) := fun ρ h => dif_pos h
  obtain ⟨V, hV⟩ := exists_blockMat e K
  have hPV : ∀ b, P' b = V *ᵥ P b := by
    intro b
    funext j
    obtain ⟨⟨ρ, i⟩, rfl⟩ := e.symm.surjective j
    have h := hm' ρ i
    have h1 : ∀ (y : Frame (U.X k).Ψ r) (i : Fin (Dw.mult ρ)),
        perFr (U.X k) y (φ k b : Fin r → E) (relab c σ (e (e.symm ⟨ρ, i⟩)).1) (e (e.symm ⟨ρ, i⟩)).2 =
          ((mat y ⟨_, h⟩)⁻¹ *ᵥ Data.emb (relab c σ ρ) (φ k b : Fin r → E)) (Fin.cast (hm ρ h) i) := fun y i => by
      rw [Equiv.apply_symm_apply]
      exact perFr_of_zero (hm ρ h) _ (hp0.trans hq) y _ h i
    rw [hV, hPe', h1, hK ρ h]
    simp only [hPe, h1]
    rw [submatrix_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (x.2 _).1)]
  obtain ⟨-, -, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F (ik k) P P'
    (LinearEquiv.refl _ _) V p p' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hPV
  have hcol : ∀ i, V *ᵥ (∑ j, (show ℂ from cf τ.1 i j) • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) =
      Pi.single (e.symm ⟨τ.1, i⟩) 1 := by
    intro i
    have hc : IsCombAt (F.u (ik k) P) ((U.un k x).u τ.1) (show Fin (Dw.mult τ.1) → ℂ from cf τ.1 i)
        ((U.un k x').u τ.1 i) := by
      rw [← hx]; exact hchg.2.1 τ.1 i
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F (ik k) P p _ ((U.un k x).u τ.1) _
      (hd τ.1) (cf τ.1 i) _).1 hc
    have d2 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F (ik k) P p (ik k) P' (Matrix.mulVecLin V) p'
      hex _ _).1 d1
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F (ik k) P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 (hd' τ.1 i)
  have hs : ∀ (i j : Fin (Dw.mult τ.1)),
      (Pi.single (e.symm ⟨τ.1, i⟩) 1 : Fin g → ℂ) (e.symm ⟨τ.1, j⟩) = (Pi.single i 1 : _ → ℂ) j := by
    intro i j
    simp [Pi.single_apply]
  have hdet := det_mul_eq_one (hm _ hτ) (B ⟨_, hτ⟩) (show Matrix _ _ ℂ from cf τ.1) fun i => by
    funext j
    rw [← hs, ← hcol, hV, hK _ hτ]
    congr 2
    funext j'
    refine (?_ : ∀ w : Fin (Dw.mult τ.1) → ℂ,
      w j' = (∑ j, w j • (Pi.single (e.symm ⟨τ.1, j⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ.1, j'⟩)) (cf τ.1 i)
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, hs, smul_eq_mul]
    simp [Pi.single_apply]
  have hx' := (x'.2 ⟨_, hτ⟩).1
  simp only [B, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdet
  change _ = Matrix.det (show Matrix _ _ ℂ from cf τ.1) * _
  field_simp at hdet
  linear_combination -hdet

end GlobalTheory.FlatChange
end

noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem comp_eq {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k k' : U.Comp}
    (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor (Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x (U.un k' x') h
  obtain ⟨γ, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem nonempty_flatSec {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hq : Dw.q = 0) (hp : 1 ≤ Dw.p)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (Z : Comp Xo c) (τ : Psi H) : Nonempty (FlatSec U x Z τ) := by
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hP := hasPts U hpq hg hU Z
  obtain ⟨y₀, h₀, hy₀⟩ := GlobalTheory.FlatLine.DefinitePoint.main E H Dw l Xo c hq hF Z
  obtain ⟨f, f', m₁, m₂, i₁, i₂, hm, hv⟩ := exists_flatRule E H Dw l Xo c hq Z τ y₀ h₀ hy₀
  have chg : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S), LiesOn Z y →
      FrMap (Algebra.ofId c.F S) y₀ z → ∃ (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : Sˣ), (∀ ρ, IsUnit (g ρ).det) ∧ FrChg g (a : S) y z :=
    fun S _ _ y z hy hz => (frChg_exists_unique E H Dw l Xo c S y z).1 (hz.1.trans (hy₀ S y hy).symm)

  have hinf : ∀ σ : c.F →+* ℂ, ∃ b : ℝ, 0 < b ∧ homN (U (goodOf c σ)) x (wtOf Dw (flatWt Dw τ) 0) f ''
      framesOn (U (goodOf c σ)) Z = {b} := by
    intro σ₀
    obtain ⟨⟨⟨k, x₀⟩, hx₀⟩, ht⟩ := hP.1 σ₀
    have hσ := goodEmb_goodOf c σ₀
    generalize goodOf c σ₀ = σ at *
    have hV := hU σ hσ
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
    have hτ : ∀ k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun k => ((hV.2.1 k).2 _).2 (by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)
    have rd : ∀ k y (hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z) g a,
        FrChg g a ((U σ).un k ⟨y, hy.1⟩) z → rdU (U σ) f k y = toC (g τ.1).det := fun k y hy g a hc => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy.1, dif_pos]
      exact congrArg toC (hv _ _ z g a (ht _ hy hy.1) hz hc)
    have hh : IsHorizontal (U σ) Z τ f := fun k => by
      by_cases hne : ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨y₁, h₁⟩ := hne
        refine ⟨hτ k, rdU (U σ) f k y₁ * (mat y₁ ⟨_, hτ k⟩).det, fun y hy => ?_⟩
        obtain ⟨g₁, a₁, -, c₁⟩ := chg _ _ z h₁.2 hz
        obtain ⟨g, a, -, c₂⟩ := (frChg_exists_unique E H Dw l Xo c _ ((U σ).un k ⟨y, hy.1⟩)
          ((U σ).un k ⟨y₁, h₁.1⟩)).1 ((hy₀ _ _ h₁.2).trans (hy₀ _ _ hy.2).symm)
        have c₃ := (frChg_refl_and_comp E H Dw l Xo c _ _ _ _).2 _ _ _ _ c₂ c₁
        have e := GlobalTheory.FlatChange.det_frChg E H Dw l Xo c σ r (U σ) hq hσ hV k ⟨y, hy.1⟩ ⟨y₁, h₁.1⟩ τ (hτ k) g a c₂
        rw [rd k y hy _ _ c₃, rd k y₁ h₁ _ _ c₁, e, horizGen, Matrix.det_mul, mul_assoc, mul_assoc,
          mul_inv_cancel₀ (hy.1 _).1, mul_one]
        rfl
      · exact ⟨hτ k, 0, fun y hy => absurd ⟨y, hy⟩ hne⟩
    obtain ⟨b, hb⟩ := hh.homN_const hσ hV x k
    refine ⟨b, ?_, image_eq_singleton_iff.2 ⟨⟨_, hx₀⟩, ?_⟩⟩
    · have h1 := homN_mul (U σ) x (even_wtOf (-flatWt Dw τ) 0) (even_wtOf (flatWt Dw τ) 0) f' f ⟨k, x₀⟩ hx₀.1
      rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm f', hm, homN_idem _ x hx₀.1 hx₀.2 (ht _ hx₀ _),
        hb x₀ hx₀] at h1
      refine lt_of_le_of_ne (hb x₀ hx₀ ▸ homN_nonneg _ _ _ _ _) fun h0 => ?_
      rw [← h0, mul_zero] at h1
      exact one_ne_zero h1
    · rintro ⟨k', y⟩ hy
      obtain rfl : k' = k := comp_eq hσ hV ⟨x₀, hx₀.1⟩ ⟨y, hy.1⟩ ((hy₀ _ _ hx₀.2).trans (hy₀ _ _ hy.2).symm)
      exact hb y hy
  choose cI hI₁ hI₂ using hinf

  choose ρ hρ using GlobalTheory.FlatLine.PlaceConst.nval_det_frChg_const E H Dw l Xo c hpq hg y₀ τ.1
  obtain ⟨S, hS0, hS⟩ := GlobalTheory.FlatLine.exists_finset_integral_of_definite E H Dw l Xo c hq hp hg y₀
  refine ⟨⟨f, f', m₁, m₂, i₁, i₂, hm, cI, hI₁, hI₂, ρ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, ?_⟩, ?_⟩⟩
  · rintro _ ⟨⟨_, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    obtain ⟨g, a, -, hc⟩ := chg _ y.1 z hy.2 hz
    show nval T.V e (evR Xo c f y.1) = _
    rw [hv _ _ z g a y.2.1 hz hc, hρ w T io e ho y.1 z g a y.2.2 hz hc]
    simp [flDefect_vw, hq]
  · refine (S.finite_toSet.biUnion fun s hs => finite_vAdd (hS0 s hs)).subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not, Int.cast_eq_zero] at hn
    obtain ⟨_, ⟨_, T, io, e, ho, -⟩, -⟩ := hP.2 w
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    have hi := hS T io (fun s hs => by rw [ho.2 s]; exact mul_eq_zero_of_right _ (hn s hs)) z hz
    have h1 := hρ w T io e ho z z _ _ hi hz (frChg_refl_and_comp E H Dw l Xo c _ z z z).1
    rw [Matrix.det_one, nval_of_ne one_ne_zero, EReal.coe_eq_coe_iff] at h1
    exact hw (h1.symm.trans (by simp [vV]))

end GlobalTheory.FlatLine.Definite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RamifiedPlacesSplitEigen
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G]

def IsEigTan (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsCombAt {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigBasis (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigTan act x χ (v i)) ∧ ∀ w, IsEigTan act x χ w → ∃! c : Fin n → R, IsCombAt c v w

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def charIn (c : Coeff l) {R : Type} [CommRing R] (φ : c.F →+* R) (τ : E →+* ℂ) : 𝓞 E →+* R :=
  φ.comp ((τ.codRestrict c.F (c.conj τ)).comp (algebraMap (𝓞 E) E))

def IsFrame (Y : Model Xo c β) (τ : E →+* ℂ) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Y.X)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  x ≫ Y.s = spMap (φ.comp β) ∧ IsEigBasis Y.t.act x (charIn c φ τ) v ∧
    IsEigBasis Y.t.act x (charIn c φ (conjEmb τ)) w

end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {A : Over (Sp R)} [GrpObj A]
  {φ : A.left ⟶ G.left} {m : ℕ}

theorem exists_lift (h : IsGrpPullback A G x φ) (u : FramedFlatCoordinates.epsAt x ⟶ G) :
    ∃ v : epsR R ⟶ A, v.left ≫ φ = u.left :=
  let ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  ⟨e.symm u, by rw [← he, e.apply_symm_apply]⟩

theorem fibre_iff (h : IsGrpPullback A G x φ) {v : Fin m → (epsR R ⟶ A)} {u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hu : ∀ i, (v i).left ≫ φ = (u i).left) :
    (∀ (c : Fin m → R) (w : epsR R ⟶ A) (w' : FramedFlatCoordinates.epsAt x ⟶ G), w.left ≫ φ = w'.left →
      (IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (u i).left) w')) ∧
    ∀ {O : Type} [CommRing O] {a : OAct O A} {b : OAct O G}, (∀ c, (a.act c).left ≫ φ = φ ≫ (b.act c).left) →
      ∀ χ : O →+* R, EigenvectorLieDegree.IsEigBasis a χ v ↔ FramedFlatCoordinates.IsEigenBasis b x χ u := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  obtain rfl : u = fun i => e (v i) := funext fun i => Over.OverMorphism.ext ((hu i).symm.trans (he _).symm)
  have one : (1 : Over.mk x ⟶ G).left = η[A].left ≫ φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ A), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have pr : ∀ u : Fin m → (epsR R ⟶ A), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin m → R) (w : epsR R ⟶ A),
      IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine ⟨fun c w w' hw => ?_, fun {O} _ a b hab χ => ?_⟩
  · obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
    exact hC c w
  have hP : ∀ v : epsR R ⟶ A, EigenvectorLieDegree.IsEigVec a χ v ↔ FramedFlatCoordinates.IsEigenTangent b x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[A]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ a.act c) = e v ≫ b.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hab, Category.assoc])
      rw [hR, E]
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def EigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ) (m : ℕ)
    (v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)) (v' : Fin m → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ T.G)),
    FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v →
    (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) →
    FramedFlatCoordinates.IsEigenBasis T.act (spMap g ≫ x) (FramedFlatCoordinates.chr c τ (g.comp j)) v'

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

end GlobalTheory.FlatRow
end
end
