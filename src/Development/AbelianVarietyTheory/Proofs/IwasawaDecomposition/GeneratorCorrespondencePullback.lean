module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam
noncomputable section
namespace GlobalTheory.IntFam.TermLift

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev gB : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _)

abbrev trB (mu : D.X) : D.P.A ⟶ D.P.A := padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)

omit [IsDomain R] in
theorem comp_padd {T T' : Over (Spec (CommRingCat.of R))} (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
    (x : T' ⟶ T) (a b : T ⟶ A) : x ≫ padd A a b = padd A (x ≫ a) (x ≫ b) := by
  rw [padd, padd, ← Category.assoc, comp_lift]

omit [IsDomain R] in
theorem comp_toUnit {Y T W : Over (Spec (CommRingCat.of R))} (f : 𝟙_ _ ⟶ W) (x : T ⟶ Y) :
    x ≫ toUnit Y ≫ f = toUnit T ≫ f := by
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit Y) (toUnit T)]

theorem gB_famφT (β : D.X) (i : Fin 4) : (gB D).left ≫ famφT D (𝟙_ _) β i = D.famφB β i := by
  fin_cases i
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
  · refine congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (?_ : gB D ≫ padd D.P.A (snd _ _) (toUnit _ ≫ D.c β) = _)
    rw [comp_padd, lift_snd, comp_toUnit]
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (D.c β) (gB D))
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (MonObj.one : 𝟙_ _ ⟶ D.P.A) (gB D))

theorem gB_trT (mu : D.X) : gB D ≫ trT D (toUnit (𝟙_ _) ≫ D.c mu) = trB D mu ≫ gB D := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, trT, lift_fst, lift_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, Category.assoc, trT, lift_snd, lift_snd, Category.comp_id, comp_padd, lift_snd,
      ← Category.assoc, lift_fst, comp_toUnit]

theorem gB_trT_famφT (mu α : D.X) (i : Fin 4) :
    (gB D).left ≫ (trT D (toUnit (𝟙_ _) ≫ D.c mu)).left ≫ famφT D (𝟙_ _) α i = (trB D mu).left ≫ D.famφB α i := by
  rw [← Category.assoc, ← Over.comp_left, gB_trT, Over.comp_left, Category.assoc, gB_famφT]

theorem formEq (k : ℕ) (α mu : D.X) :
    FormEq (Sum.elim (fun i => (trB D mu).left ≫ D.famφB α i)
        (fun i => (gB D).left ≫ deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu) i))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, deltaφT, DegPre.deltaε, gB_famφT, gB_trT_famφT,
    zpow_neg, Finset.prod_inv_distrib]
  rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem prB_gB : DegPre.prB D F ≫ gB D = toUnit (TF (R := R) F) ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, whiskerRight_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, lift_snd, whiskerRight_snd, Category.comp_id]

theorem trF_prB (mu : D.X) : DegPre.trF D F mu ≫ DegPre.prB D F = DegPre.prB D F ≫ trB D mu := by
  rw [DegPre.trF, lift_snd, comp_padd, Category.comp_id, comp_toUnit]

end GlobalTheory.IntFam.TermLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LocSplice

theorem adAt_eq_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = Formalism.UG.prV (E := E) (P.under (𝓞 F)) z') :
    adAt F P z = adAt F P z' := by
  set v := P.under (𝓞 F)
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 :=
    GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P (Formalism.UG.P.afsplit_prV_eps v)
  have e : ∀ w : AfE F E, adAt F P w =
      adAt F P (Formalism.UG.P.afsplitIE v (Formalism.UG.prV (E := E) v w)) := fun w => by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, h3, one_mul]
  rw [e z, e z', h]

theorem map_conj_inv_mul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (w w' A C : GL (Fin n) R)
    (h : ∀ r s, φ (w.1 r s) = φ (w'.1 r s)) (r s : Fin n) :
    φ ((((A⁻¹ * w * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) =
      φ ((((A⁻¹ * w' * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) := by
  have hΦ : Matrix.GeneralLinearGroup.map (n := Fin n) φ w = Matrix.GeneralLinearGroup.map φ w' := by
    apply Units.ext
    exact Matrix.ext h
  have h2 : Matrix.GeneralLinearGroup.map (n := Fin n) φ ((A⁻¹ * w * A)⁻¹ * C) =
      Matrix.GeneralLinearGroup.map φ ((A⁻¹ * w' * A)⁻¹ * C) := by
    simp only [map_mul, map_inv, hΦ]
  exact congrArg (fun z : GL (Fin n) S => (z : Matrix (Fin n) (Fin n) S) r s) h2

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  intro B X I hOk l Z a T i hi bad S P v hv κ hκ hloc
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1, ?_, ?_⟩
  · rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ hκ) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_right1]
      exact hloc
    · have h1 : bc (prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
        simp
      rw [h1]
      exact one_mem _
  · intro fb dep g hx
    have hseam := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1).1
    have hdict := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) (dep P) P z).2.2
    have hvP : P.1.under (𝓞 B.host.F) = v := by
      apply HeightOneSpectrum.ext
      rw [hseam] at hv
      exact hv.symm
    unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hx ⊢
    have h1 := (hdict _).1 hx
    refine (hdict _).2 (fun r s => ?_)
    have h2 := h1 r s
    convert h2 using 3
    refine (map_conj_inv_mul _ _ _ _ _ (fun r s => ?_) r s).symm
    · apply adAt_eq_of_prV
      rw [hvP]
      exact congrFun (congrFun (Formalism.UG.P.afsplitC_prV (E := (I.rec7 l Z).host.E) v _ _) r) s

end GlobalTheory.Mem.Col2.AdT.LocSplice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_group_element_eq_level_component_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LocSplice.main | exact GlobalTheory.Mem.Col2.AdT.LocSplice.main | (intros; apply GlobalTheory.Mem.Col2.AdT.LocSplice.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.SecFrame

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

def frameAt (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) : mat (frameAt X hj κ z) τ =
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) := rfl

theorem frameCo_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (frameAt X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  rw [frameCo, mat_frameAt, nonsing_inv_mul_cancel_left _ _ (det_x0F X _).isUnit, Equiv.apply_symm_apply]

theorem lminor_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin (m + 1)) : lminor Mᵀ i = lminor M i := by
  unfold lminor
  rw [← transpose_submatrix, det_transpose]

theorem frameAt_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    frameAt X hj κ z ∈ X.dom := by
  intro τ
  set Z := z (κ.symm τ) with hZ
  set B : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 Z 0 1 with hB
  set M := (reindex (idx hj) (idx hj)).symm B with hM
  have hRM : reindex (idx hj) (idx hj) M = B := Equiv.apply_symm_apply _ _
  have hdM : M.det = 1 := by
    rw [hM, reindex_symm, det_reindex_self, hB, det_fromBlocks_zero₂₁]; simp
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_frameAt, det_mul, ← hM, hdM, mul_one]; exact det_x0F X τ
  · set Dg : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) with hDg
    have h0 := congrArg transpose (isOrth_x0F X τ)
    rw [gram_eq_mul, diagonal_transpose, hp] at h0
    have hT : (gram τ.1 X.Gm (mat (frameAt X hj κ z) τ))ᵀ = Mᴴ * Dg * M := by
      rw [gram_eq_mul, mat_frameAt, ← hM, hDg, ← h0]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have hR : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
      have : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) =
          (reindex (idx hj) (idx hj) M)ᴴ * reindex (idx hj) (idx hj) Dg * reindex (idx hj) (idx hj) M := by
        simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
      rw [this, hRM, hDg, reindex_sgn hj, Formalism.UG.Jpq, hB, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
        fromBlocks_multiply]
      simp [hQ, sub_eq_neg_add]
    have hZd : (hQ Z).PosDef := hz (κ.symm τ)
    have h2 : (reindex (idx hj) (idx hj) (Mᴴ * Dg * M)).toBlocks₂₂.PosDef := by
      rw [hR, toBlocks_fromBlocks₂₂]; exact hZd
    have hs : (-schur (reindex (idx hj) (idx hj) (Mᴴ * Dg * M))).PosDef := by
      rw [hR, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      have e : -(-1 - -Z * (hQ Z)⁻¹ * -Zᴴ) = (1 : Matrix (Fin j) (Fin j) ℂ) + Z * (hQ Z)⁻¹ * Zᴴ := by
        simp [Matrix.neg_mul, Matrix.mul_neg]; exact add_comm _ _
      rw [e]
      exact PosDef.add_posSemidef PosDef.one (hZd.inv.posSemidef.mul_mul_conjTranspose_same Z)
    have key := signs_of_blocks (isBlockOrderedSumEquiv_trueIndex hj) (Mᴴ * Dg * M) h2 hs i
    rw [dmin, hp, ← lminor_transpose, hT]
    exact key

theorem domPt_frameAt (z : Pt Tau j (r - j)) : domPt X hj κ (frameAt X hj κ z) = z := by
  funext t
  simp only [domPt, frameCo_frameAt, Equiv.symm_apply_apply, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    inv_one, Matrix.mul_one]

theorem co_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    coW X hj (frameAt X hj κ z) τ = 1 ∧ coOm X hj (frameAt X hj κ z) τ = 1 := by
  simp [coW, coOm, frameCo_frameAt, toBlocks_fromBlocks₂₁]

theorem differentiable_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) := by
  have hM : ∀ c, Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact differentiable_const _ | exact differentiable_apply _
  simp only [mat_frameAt, Matrix.mul_apply]
  exact Differentiable.fun_sum (u := Finset.univ) (A := fun c (v : Tau × Fin j × Fin (r - j) → ℂ) =>
    mat (x0F X) τ a c * ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b)
    fun c _ => (hM c).const_mul _

end GlobalTheory.ShFam.SecFrame

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FieldPtGlue

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X}

theorem valF_ne_zero_iff {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem valF_restrict {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_sub {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF, dif_pos h, map_sub]

theorem le_preimage_iff (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint F) ∈ U := by
  constructor
  · intro h
    exact h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro h y _
    have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    subst this
    exact h

end Val

noncomputable def resPt (X : Scheme.{0}) (z : X) : Sp (X.residueField z : Type) ⟶ X := X.fromSpecResidueField z

theorem resPt_le_iff (X : Scheme.{0}) (z : X) (U : X.Opens) : ⊤ ≤ resPt X z ⁻¹ᵁ U ↔ z ∈ U := by
  rw [le_preimage_iff]
  have : resPt X z (IsLocalRing.closedPoint (X.residueField z : Type)) = z :=
    Scheme.fromSpecResidueField_apply z _
  rw [this]

theorem section_ext {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 (X.basicOpen_le _ hz)
  have h1 := (valF_ne_zero_iff hU (a - b)).2 ((resPt_le_iff X z _).2 hz)
  rw [valF_sub hU, h _ _ hU, sub_self] at h1
  exact absurd rfl h1

theorem exists_unit_of_locally : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  intro X _ U P huniq hne hloc
  choose V s hzV hVU hP using hloc
  let V' : U → X.Opens := fun z => V z.1 z.2
  let s' : ∀ z : U, Γ(X, V' z) := fun z => s z.1 z.2
  have hcov : U ≤ iSup V' := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V' s' := by
    intro i j
    refine section_ext (X := X) (U := V' i ⊓ V' j) _ _ fun k _ w hw => ?_
    have hi : ⊤ ≤ w ⁻¹ᵁ V' i := fun q hq => (hw hq).1
    have hj : ⊤ ≤ w ⁻¹ᵁ V' j := fun q hq => (hw hq).2
    refine (valF_restrict inf_le_left hw (s' i)).trans
      (Eq.trans ?_ (valF_restrict inf_le_right hw (s' j)).symm)
    exact huniq k w _ _ (fun q hq => hVU i.1 i.2 (hi hq)) (hP i.1 i.2 k w hi) (hP j.1 j.2 k w hj)
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V' U (fun i => homOfLE (hVU i.1 i.2)) hcov s' hcomp
  have key : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U t) := by
    intro k _ w hw
    have hz := (le_preimage_iff U).1 hw
    have hV : ⊤ ≤ w ⁻¹ᵁ V _ hz := (le_preimage_iff _).2 (hzV _ hz)
    have e : valF w U t = valF w (V _ hz) (s _ hz) :=
      (valF_restrict (hVU _ hz) hV t).symm.trans (congrArg (valF w (V _ hz)) (ht ⟨_, hz⟩))
    rw [e]
    exact hP _ hz k w hV
  have hu : IsUnit (M := Γ(X, U)) t := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 hz
    have h0 : valF (resPt X z) U t ≠ 0 := fun h0 => hne _ _ hU (h0 ▸ key _ _ hU)
    have h1 := (resPt_le_iff X z _).1 ((valF_ne_zero_iff hU t).1 h0)
    exact (X.mem_basicOpen t z hz).1 h1
  exact ⟨hu.unit, key⟩

end GlobalTheory.FieldPtGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundary
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}

section Directions

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1)
  (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ))


include hP hu hy hW in
theorem dirs_exists_comb (τ : E →+* ℂ) (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • W ⟨τ, k⟩ := by
  choose v₀ h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 w
  have ht := t1 w v hv
  have he := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP w v τ hv).2 hw
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [ht.1, ← hu, Category.assoc])
  obtain ⟨cf, hcf, -⟩ := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hu k1).1 ht))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1 (he b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hcf
  have hc := (comb_iff Z.m0.toSABMap hu (fun k => h1 ⟨τ, k⟩) cf k1).2 ((comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf k1).1 hcf)
  exact ⟨cf, (t3 _ ht).unique hv ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _
    (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).1 hc)⟩


include hP hu hy hW in
theorem dirs_span : ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨cf, h⟩ := dirs_exists_comb hP hu hy hW (e j).1 (Pi.basisFun ℂ (Fin g) j) fun k hk => by
    by_contra hne
    exact hk (by rw [Pi.basisFun_apply]; exact Pi.single_eq_of_ne (fun h => hne (by rw [h])) _)
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


include hP hu hy hW in
theorem dirs_basis : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W :=
  ⟨basisOfTopLeSpanOfCardEqFinrank W (dirs_span hP hu hy hW) (by
    rw [Module.finrank_fin_fun, ← Fintype.card_congr e, Fintype.card_fin]), coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩

end Directions

theorem Inner.exists_lift {x : CxPts (genStr Z) σ} (h : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  have hr : Set.range x.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact not_not.1 h
  exact ⟨IsOpenImmersion.lift Z.jQ _ hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_dirs (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) :
    ∃ W : Letter Dw → Fin g → ℂ, ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hy]
  choose v₀ h1 h2 using fun z : Letter Dw => exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) (a.2.v z.1 z.2)
    (by rw [(a.2.tan z.1 z.2).1, ← hx, Category.assoc])
  choose W hW using fun z : Letter Dw => ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hu (h1 z)).2 ((tan_iff Z.m hx (h1 z)).1 (h2 z ▸ a.2.tan z.1 z.2)))).exists
  exact ⟨W, fun z => ⟨v₀ z, h1 z, h2 z, hW z⟩⟩

theorem exists_per_of_isPeriod (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : y ≫ pullback.fst _ _ = Fu.u i P) (hy : y ≫ Z.jQ = a.1.1) : ∃ Q, Per Fu a i Q := by
  obtain ⟨W, hW⟩ := exists_dirs hP hu hy
  obtain ⟨b, rfl⟩ := dirs_basis hP hu hy hW
  exact ⟨b.equivFun.toLinearMap.toAddMonoidHom.comp P, P, b, y, hP, hu, hy, hW, fun v => (b.sum_equivFun (P v)).symm⟩

theorem exists_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a ha
  obtain ⟨y, hy⟩ := ha.exists_lift
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact a.1.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  exact ⟨i, exists_per_of_isPeriod hP hu.symm hy⟩

end GlobalTheory.ShFam.Hor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_in_frame_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), Inner a.1 → ∃ i Q, Per Fu a i Q := by
  first | exact @GlobalTheory.ShFam.Hor.exists_per | exact GlobalTheory.ShFam.Hor.exists_per | (intros; apply GlobalTheory.ShFam.Hor.exists_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open scoped CommRingCat.HomTopology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc.Leave

theorem block_of_span_le {N p : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (h : Submodule.span ℂ (col M' '' {a | (a : ℕ) < p}) ≤ Submodule.span ℂ (col M '' {a | (a : ℕ) < p}))
    (a b : Fin N) (ha : p ≤ a) (hb : (b : ℕ) < p) : (M⁻¹ * M') a b = 0 := by
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (Matrix.mulVecLin M⁻¹)
  have hL : ∀ (P : Matrix (Fin N) (Fin N) ℂ) (d : Fin N), L (col P d) = (M⁻¹ * P) a d := fun _ _ => rfl
  have h1 : Submodule.span ℂ (col M '' {a | (a : ℕ) < p}) ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    show L (col M d) = 0
    rw [hL, Matrix.nonsing_inv_mul _ hM.isUnit]
    exact Matrix.one_apply_ne fun e => absurd (show (d : ℕ) < p from hd) (by rw [← e]; omega)
  exact (hL M' b).symm.trans (h1 (h (Submodule.subset_span ⟨b, hb, rfl⟩)))

theorem imTop_neBot : imTop.NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem ht
    exact ⟨a * Complex.I, by simpa using ha⟩

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun w : ℂ => Real.exp (-(2 * Real.pi * w.im))) imTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) tendsto_comap)
  refine h.congr fun w => ?_
  simp [eTwoPi, Complex.norm_exp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N}

theorem x_eq_of_samePos (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x x' : (U.X k).dom)
    (h : SamePos (U.X k) x.1 x'.1) : (U.un k x).x = (U.un k x').x :=
  GlobalTheory.TrueCx.PointWell.pt_eq_of_block (U := Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x x'
    (fun τ => block_of_span_le (x.2 τ).1 (h τ).ge) fun τ => block_of_span_le (x'.2 τ).1 (h τ).le

theorem isHolTo_ptC (hU : IsUnf U) (k : U.Comp) (s : Frame (U.X k).Ψ N → (U.X k).dom)
    (hs : ∀ x ∈ (U.X k).dom, (s x).1 = x) : IsHolTo (U.X k).dom fun x => GlobalTheory.TrueCx.ptC (U.un k (s x)) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  let L : Frame (U.X k).Ψ N ≃L[ℂ] (Fin (Module.finrank ℂ (Frame (U.X k).Ψ N)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
  have ho : IsOpen (U.X k).dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _
  have hB := ho.preimage L.symm.continuous
  have h1 := (F.hol (ik k) _ _ (fun b => P (s (L.symm b))) hB ⟨fun b _ => hP' _, fun a =>
    differentiableOn_pi.2 fun i => by
      simp only [hP]
      refine GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (s _).2) (fun τ a d => ?_) _ _ _
      refine (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a)
        d).differentiableOn.congr fun b hb => ?_
      rw [hs _ hb]
      rfl⟩).1
  have h2 : IsHolTo (L.symm ⁻¹' (U.X k).dom) fun b => GlobalTheory.TrueCx.ptC (U.un k (s (L.symm b))) := by
    refine GlobalTheory.TrueCx.TorHolo.isHolTo_of_fst _ _ hB _ (fun b => GlobalTheory.TrueCx.ptC_snd _) ?_
    simp only [GlobalTheory.TrueCx.ptC_fst]
    exact LocLift.isHolTo_congr h1 fun b _ => hx _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h2 ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]

theorem lift_not_converges : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T xx hσ hU ⟨⟨⟨hr, hψ⟩, hxs, hφ⟩, hb0, _⟩ hm hl x₀ hx₀ x' ht hev
  have := isProper_genStr Z
  have := imTop_neBot
  let s : Frame (U.X k).Ψ N → (U.X k).dom := fun v => if h : v ∈ (U.X k).dom then ⟨v, h⟩ else ⟨x₀, hx₀⟩
  have hs : ∀ v (h : v ∈ (U.X k).dom), s v = ⟨v, h⟩ := fun v h => dif_pos h
  let pt : Frame (U.X k).Ψ N → CxPts (genStr Z) σ := fun v =>
    ⟨GlobalTheory.TrueCx.ptC (U.un k (s v)) ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over, GlobalTheory.TrueCx.ptC_snd]⟩
  have hc : ContinuousOn pt (U.X k).dom := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo
    (LocLift.isHolTo_comp_hom (isHolTo_ptC hU k s fun v h => by rw [hs v h]) Z.jQ)
  have h1 : Tendsto (fun w => pt (x' w)) imTop (𝓝 (pt x₀)) :=
    (hc.continuousAt ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _).mem_nhds hx₀)).tendsto.comp ht
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  let q : CxPts (genStr Z) σ := ⟨spMap (ψ 0) ≫ x, by
    rw [Category.assoc, hxs, ← hφ 0 h0, ← Spec.map_comp]; rfl⟩
  have ha : ContinuousAt (fun u => spMap (ψ u) ≫ x) 0 := by
    refine ((GlobalTheory.Points.continuous_comp x).comp
      (GlobalTheory.Points.continuous_specMap (C := ℂ) (CommRingCat.of A))).continuousAt.comp
      (f := fun u => CommRingCat.ofHom (ψ u)) ?_
    refine (CommRingCat.HomTopology.isEmbedding_hom _ _).isInducing.continuousAt_iff.2 (continuousAt_pi.2 fun a => ?_)
    exact ((hψ a).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have h2 : Tendsto (fun w => pt (x' w)) imTop (𝓝 q) := by
    refine tendsto_subtype_rng.2 ((ha.tendsto.comp tendsto_eTwoPi).congr' ?_)
    filter_upwards [hev, tendsto_eTwoPi.eventually (Metric.isOpen_ball.mem_nhds h0),
      (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop T)] with w hw hb hT
    obtain ⟨hd, he, -⟩ := hl w hT
    have e1 := (hm _ hb (Complex.exp_ne_zero _)).1
    have e2 : GlobalTheory.TrueCx.ptC (U.un k (s (x' w))) = GlobalTheory.TrueCx.ptC (y (eTwoPi w)) := by
      refine pullback.hom_ext ?_ ((GlobalTheory.TrueCx.ptC_snd _).trans (GlobalTheory.TrueCx.ptC_snd _).symm)
      rw [GlobalTheory.TrueCx.ptC_fst, GlobalTheory.TrueCx.ptC_fst, hs _ hw.1]
      exact (x_eq_of_samePos hσ hU k ⟨_, hd⟩ ⟨_, hw.1⟩ hw.2).symm.trans he
    exact e1.symm.trans (congrArg (· ≫ Z.jQ) e2.symm)
  have h3 : (pt x₀).1 = q.1 := congrArg Subtype.val (tendsto_nhds_unique h1 h2)
  refine mem_genBd.1 (hb0 (IsLocalRing.closedPoint ℂ)) ⟨GlobalTheory.TrueCx.ptC (U.un k (s x₀)) (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Sp ℂ ⟶ gen Z => f (IsLocalRing.closedPoint ℂ)) h3)

end GlobalTheory.ShFam.BdArc.Leave
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomainStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  first | exact @GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | exact GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | (intros; apply GlobalTheory.ShFam.BdArc.Leave.lift_not_converges <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieBase

theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_affine_factor {Y : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : x (IsLocalRing.closedPoint R) ∈ U) :
    ∃ ψ : Γ(Y, U) →+* R, spMap ψ ≫ hU.fromSpec = x := by
  obtain ⟨ψ, hψ⟩ := EigLoc.exists_stalk_factor x _ (specializes_refl _)
  refine ⟨ψ.comp (Y.presheaf.germ U _ h).hom, ?_⟩
  have hg : spMap (Y.presheaf.germ U _ h).hom ≫ hU.fromSpec = Y.fromSpecStalk _ := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [spMap_trans, Category.assoc, hg, hψ]

theorem par_zero_iff {ι : Type} {m : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) (O : Subring K) (hO : ∀ x, x ∈ O ↔ ∃ r, a r = x) (P : Mat m K) :
    Par 0 O P ↔ ∃ G : Mat m R, (∀ τ, IsUnit (G τ).det) ∧ P = G.map a := by
  constructor
  · intro hP
    have hent : ∀ τ i j, ∃ r, a r = P τ i j := fun τ i j => (hO _).1 ((hP τ).1 i j)
    choose G₀ hG using hent
    let G : Mat m R := fun τ => Matrix.of (G₀ τ)
    have hGP : P = G.map a := by
      funext τ i j
      exact (hG τ i j).symm
    refine ⟨G, fun τ => ?_, hGP⟩
    obtain ⟨s, hs⟩ := (hO _).1 (hP τ).2.2.1
    have hdet : a (G τ).det = (P τ).det := by
      rw [hGP]
      exact RingHom.map_det a (G τ)
    refine isUnit_iff_exists_inv.2 ⟨s, ha ?_⟩
    rw [map_mul, hdet, hs, map_one, mul_inv_cancel₀ (hP τ).2.1]
  · rintro ⟨G, hG, rfl⟩ τ
    have hdet : (G.map a τ).det = a (G τ).det := (RingHom.map_det a (G τ)).symm
    obtain ⟨u, hu⟩ := hG τ
    refine ⟨fun i j => (hO _).2 ⟨G τ i j, rfl⟩, ?_, ?_, fun i j hi _ => absurd hi (Nat.not_lt_zero _)⟩
    · rw [hdet, ← hu]
      exact (u.isUnit.map a).ne_zero
    · rw [hdet, ← hu]
      exact (hO _).2 ⟨((u⁻¹ : Rˣ) : R), by rw [map_units_inv]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem frames_iff {R R₁ K : Type} [CommRing R] [CommRing R₁] [IsLocalRing R₁] [Field K] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (hf : f.Stable) (ψ : R →+* R₁) (a : R₁ →+* K) (ha : Function.Injective a)
    {x₁ : Sp R₁ ⟶ Z.X} (hx : x₁ = spMap ψ ≫ x) {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (f₀ : EigFrame Z φ₀ x₀)
    {T : Mat Dw.mult K} (hT : f.Coord (a.comp ψ) f₀ T) (A : Mat Dw.mult K) :
    ((∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ₁ : c.F →+* R₁) (g : EigFrame Z φ₁ x₁), g.Coord a f₀ A⁻¹) ↔
      ∃ G : Mat Dw.mult R₁, (∀ τ, IsUnit (G τ).det) ∧ A * T = G.map a := by
  have hU := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f K φ₀ x₀ (a.comp ψ) inferInstance hf hT.1 hT.2.1).1 f₀
  have huniq : ∀ B, f.Coord (a.comp ψ) f₀ B → B = T := fun B hB => hU.1.unique hB hT
  constructor
  · rintro ⟨hA, φ₁, g, hg⟩
    have hφ₁ : φ₁ = ψ.comp φ := by
      apply RingHom.ext
      intro r
      apply ha
      have h := RingHom.congr_fun (hg.2.1.symm.trans hT.2.1) r
      simpa using h
    subst hφ₁
    obtain ⟨hE, hunits⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).1 g
    obtain ⟨G, hG, -⟩ := hE
    refine ⟨G, hunits G hG, ?_⟩
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G A⁻¹ inferInstance hG hg
    rw [← huniq _ hc, ← mul_assoc, Mat.mul_inv hA, one_mul]
  · rintro ⟨G, hG, hAT⟩
    obtain ⟨g, hfg⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).2 G hG
    have hgs : g.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g inferInstance
    have hx₀ : x₀ = spMap a ≫ x₁ := by rw [hT.1, hx, spMap_trans, Category.assoc]
    have hφ₀ : φ₀ = a.comp (ψ.comp φ) := hT.2.1.trans (RingHom.comp_assoc _ _ _)
    obtain ⟨⟨B, hB, -⟩, -⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g K φ₀ x₀ a inferInstance hgs hx₀ hφ₀).1 f₀
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G B inferInstance hfg hB
    have hTB : B * G.map a = T := huniq _ hc
    have hGd : ∀ τ, (G.map a τ).det ≠ 0 := fun τ => by
      have h := ((hG τ).map a).ne_zero
      rw [RingHom.map_det] at h
      exact h
    have hAB : A * B = 1 := by
      calc A * B = A * B * (G.map a * (G.map a)⁻¹) := by rw [Mat.mul_inv hGd, mul_one]
      _ = A * (B * G.map a) * (G.map a)⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hTB, hAT, Mat.mul_inv hGd]
    have hAτ : ∀ τ, A τ * B τ = 1 := fun τ => congrFun hAB τ
    have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ hd => by
      have h := congrArg Matrix.det (hAτ τ)
      rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hAi : A⁻¹ = B := funext fun τ => Matrix.inv_eq_right_inv (hAτ τ)
    refine ⟨hAd, ψ.comp φ, g, ?_⟩
    rw [hAi]
    exact hB

variable {F : Type} [Field F]

theorem genericPt_eq (B : GlobalTheory.ProjVar.Var F) (y : B.X) :
    genericPt B = spMap (algebraMap (B.X.presheaf.stalk y) B.X.functionField) ≫ stalkPt B y := by
  unfold genericPt stalkPt
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
  rfl

theorem genericPt_str (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) : (genericPt B ≫ j) ≫ genStr Z = spMap (constF e B) := by
  have hs : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := by
    apply ext_of_isAffine
    unfold genericPt spMap
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_mono (Scheme.ΓSpecIso _).hom,
      Scheme.ΓSpecIso_naturality]
    ext a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [IsScalarTower.algebraMap_apply F Γ(B.X, ⊤) B.Fn, GlobalTheory.ProjVar.Var.algebraMap_Γ,
      GlobalTheory.Cartier.CartierDiv.algebraMap_top, CommRingCat.inv_hom_apply]
    have hmap : (Spec (B.X.presheaf.stalk (genericPoint B.X))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)) = 𝟙 _ from rfl]
      exact CategoryTheory.Functor.map_id _ _
    rw [hmap, CommRingCat.hom_id, RingHom.id_apply]
    exact CommRingCat.hom_inv_apply _ _
  have hid : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← spMap_trans, RingEquiv.toRingHom_comp_symm_toRingHom]
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  unfold constF
  rw [spMap_trans, ← hs, ← hj]
  simp only [Category.assoc, hid, Category.comp_id]

def fam (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) :
    Fr (ratOf B) Dw.mult 0 where
  S (y : B.X) := {A | (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
    f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹}
  loc (z : B.X) := by
    obtain ⟨U, hU, φ, f, hz, hφ, hf⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H Dw l Xo c O β Z (j z)
    have key : ∀ y : B.X, j y ∈ U → ∃ ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y,
        spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j := fun y hy =>
      exists_affine_factor _ hU (by
        show j (B.X.fromSpecStalk y (IsLocalRing.closedPoint _)) ∈ U
        rw [Scheme.fromSpecStalk_closedPoint]; exact hy)
    have key' : ∀ (y : B.X) (ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y), spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j →
        spMap ((algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ) ≫ hU.fromSpec = genericPt B ≫ j :=
      fun y ψ h => by rw [spMap_trans, Category.assoc, h, genericPt_eq B y, Category.assoc]
    obtain ⟨ψ₀, hψ₀⟩ := key z hz
    have h₀ := key' z ψ₀ hψ₀
    obtain ⟨⟨T, hT, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φ _ f B.Fn (constF e B) (genericPt B ≫ j ≫ genι Z)
      ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀) inferInstance hf
      (by rw [← Category.assoc, ← h₀, Category.assoc])
      (EigLoc.spMap_inj (by rw [← genericPt_str e B j hj, ← h₀, Category.assoc, hφ, ← spMap_trans]))).1 f₀
    have hTd : ∀ τ, (T τ).det ≠ 0 := fun τ => (hu T hT τ).ne_zero
    refine ⟨j ⁻¹ᵁ U, T⁻¹, hz, fun τ => ?_, fun (y : B.X) hy A => ?_⟩
    · exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hTd) τ)).ne_zero
    · obtain ⟨ψ, hψ⟩ := key y hy
      have e1 : (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀ =
          (algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ :=
        EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (h₀.trans (key' y ψ hψ).symm))
      rw [e1] at hT
      have ha : Function.Injective (algebraMap (B.X.presheaf.stalk y) B.X.functionField) :=
        IsFractionRing.injective _ _
      rw [Mat.inv_inv hTd]
      refine (frames_iff f hf ψ _ ha (by rw [← Category.assoc, ← hψ, Category.assoc]) f₀ hT A).trans
        (par_zero_iff _ ha _ (fun x => mem_O_ratOf (Y := B) (y := y) (g := x)) _).symm

end GlobalTheory.ShFam.TieBase


open GlobalTheory.ShFam.TieBase in
theorem GlobalTheory.ShFam.TieBase.exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B j hj
  have hx : (genericPt B ≫ j) ≫ genι Z = genericPt B ≫ j ≫ genι Z := Category.assoc _ _ _
  obtain ⟨f₀⟩ : Nonempty (EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) := by
    rw [← hx]
    exact EigLoc.exists_eigFrame E H Dw l Xo c O β Z B.Fn (constF e B) (genericPt B ≫ j) (genericPt_str e B j hj)
  refine ⟨f₀, fam e B j hj f₀, 1, ?_⟩
  unfold GlobalTheory.ShFam.Tied
  refine ⟨?_, ?_⟩
  · have hst : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ inferInstance
    have hsp : spMap (RingHom.id B.Fn) = 𝟙 _ := by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    obtain ⟨⟨A₁, hA₁, huq⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _
      (RingHom.id B.Fn) inferInstance hst (by rw [hsp, Category.id_comp]) (RingHom.id_comp _).symm).1 f₀
    have h2 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀
      (RingHom.id B.Fn) (RingHom.id B.Fn) A₁ A₁ inferInstance hA₁ hA₁
    have hm : A₁.map (RingHom.id B.Fn) = A₁ := by
      funext τ i j
      rfl
    rw [RingHom.id_comp, hm] at h2
    have hsq : A₁ * A₁ = A₁ := huq _ h2
    have hdet : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => (hu A₁ hA₁ τ).ne_zero
    have h1 : A₁ = 1 := by
      calc A₁ = A₁⁻¹ * (A₁ * A₁) := by rw [← mul_assoc, Mat.inv_mul hdet, one_mul]
      _ = 1 := by rw [hsq, Mat.inv_mul hdet]
    have hinv : (1 : Mat Dw.mult B.Fn)⁻¹ = 1 := funext fun τ => by simp
    have halg : @algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X)) = RingHom.id _ := by
      ext r
      show (B.X.presheaf.stalkSpecializes _).hom r = r
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    show (∀ τ, ((1 : Mat Dw.mult B.Fn) τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk (genericPoint B.X))
      (f : EigFrame Z φ (stalkPt B (genericPoint B.X) ≫ j ≫ genι Z)),
      f.Coord (@algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X))) f₀ (1 : Mat Dw.mult B.Fn)⁻¹
    refine ⟨fun τ => by simp, constF e B, f₀, ?_⟩
    rw [halg, hinv, ← h1]
    exact hA₁
  · intro y A hA
    have hA' : (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
        (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
        f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹ := hA
    obtain ⟨-, φ, f, hf⟩ := hA'
    exact ⟨φ, f, by rw [one_mul]; exact hf⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVarietyStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  first | exact @GlobalTheory.ShFam.TieBase.exists_tied | exact GlobalTheory.ShFam.TieBase.exists_tied | (intros; apply GlobalTheory.ShFam.TieBase.exists_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChange
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_eigFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z R R' _ hR _ _ φ x f ψ
  exact GlobalTheory.ShFam.EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z R φ x f hR R' ψ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChangeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  first | exact @GlobalTheory.CuspFrom.exists_eigFrame_baseChange | exact GlobalTheory.CuspFrom.exists_eigFrame_baseChange | (intros; apply GlobalTheory.CuspFrom.exists_eigFrame_baseChange <;> assumption)
end
end
