module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

section Generic2

variable {S : Type*} [Ring S]

theorem triv_change (σ : S →+* Sᵐᵒᵖ) (x u : Sˣ) (b : S) :
    ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop =
      x * b * (σ x).unop := by
  have h1 : (σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop
      = x * ((((u⁻¹ : Sˣ) : S) * u) * b * ((σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop)) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Generic2

namespace Pair

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

theorem triv_conj (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ) (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]; rfl
  rw [e, triv_change, hx]

end Pair

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnFibFrEqOfExLeftEq
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FrameEquiv.anFib_fr_eq_of_ex_left_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL he j z hj
  have hch : ∀ z, ∃ i, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U i := fun z => by
    have h : (A.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hc using hch
  have hyx : y'.x = y.x := by
    have h1 : (A.ex 0).left ≫ Xo.univ.t.G.hom = y.x := Over.w (A.ex 0)
    have h2 : (A'.ex 0).left ≫ Xo.univ.t.G.hom = y'.x := Over.w (A'.ex 0)
    rw [← h1, ← h2, he]
  have ne' : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z ≠ 0 :=
    fun j z h => A'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => A.fr (ch z) z / A'.fr (ch z) z
  have key : ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → q z = A.fr j z / A'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (A.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U (ch z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := A.fr_g j (ch z) z hz
    have h2 := A'.fr_g j (ch z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ A.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa using (A.hol (Xo.univ.t.PP.L.U (ch z0)) 0).1
    have h' : DifferentiableOn ℂ (A'.fr (ch z0)) {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} := by
      simpa only [he] using A'.fr_hol (ch z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z0)} :=
      ((A.fr_hol (ch z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  let pvh : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) GlobalTheory.Dict.FrameSign.pv_add
  let P : L →+ (Fin g → ℂ) := pvh.comp L.subtype.toAddMonoidHom
  have hP : Submodule.span ℝ (Set.range P) = ⊤ := by
    rw [← span_image_pv idx hs hx L (TensLat.span_of_selfD X hL)]
    congr 1
    ext w
    exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩, fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩⟩
  have hper : ∀ z (a : L), ‖q (z + P a)‖ = ‖q z‖ := fun z a => by
    have h : ⊤ ≤ (A.ex (z + pv X idx x a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U (ch z) := by
      rw [GlobalTheory.Dict.FrameSign.ex_add_pv A z a.2]; exact hc z
    have h1 := A.fr_per a a.2 (ch z) z (hc z)
    have h2 := A'.fr_per a a.2 (ch z) z (by rw [he]; exact hc z)
    change ‖q (z + pv X idx x a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      A.χ_norm _ a.2, A'.χ_norm _ a.2,
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range P hP q hq hper z 0
  have h0 : q 0 = 1 := by
    have := A'.fr_0 (ch 0) (by rw [he]; exact hc 0)
    rw [hyx, ← A.fr_0 (ch 0) (hc 0)] at this
    change A.fr (ch 0) 0 / A'.fr (ch 0) 0 = 1
    rw [this, div_self (A.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact ((div_eq_one_iff_eq (ne' j z hj)).1 hc0).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
open Filter Topology

namespace GlobalTheory.InvolutionNorm

theorem exists_compact_mod_kernel : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  intro Z _ _ _ _ _ _ hc τ hτ hinv hW D hD
  obtain ⟨W, hW1, hWs⟩ := hW
  let N : Z →* Z :=
    { toFun := fun z => τ z * z
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (τ b) a b, hc (τ b) a, mul_assoc] }
  have hN : Continuous N := hτ.mul continuous_id
  have hNval : ∀ z, N z = τ z * z := fun _ => rfl
  let I : Subgroup Z := N.range
  have hIH : ∀ y ∈ I, τ y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hNval, map_mul, hinv, hc]
  have hHcl : IsClosed {y : Z | τ y = y} := isClosed_eq hτ continuous_id
  have hIcl : IsClosed (I : Set Z) := by
    refine closure_subset_iff_isClosed.1 fun x hx => ?_
    have hxH : τ x = x := closure_minimal (fun y hy => hIH y hy) hHcl hx
    have hnb : (fun y => x⁻¹ * y) ⁻¹' W ∈ 𝓝 x := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW1
    obtain ⟨i, hiW, hiI⟩ := mem_closure_iff_nhds.1 hx _ hnb
    have hiH : τ i = i := hIH i hiI
    obtain ⟨r, hr, hrr⟩ := hWs _ hiW (by rw [map_mul, map_inv, hxH, hiH])
    have hNr : N r = x⁻¹ * i := by rw [hNval, hr, hrr]
    have : x = i * (N r)⁻¹ := by rw [hNr]; group
    rw [this]
    exact I.mul_mem hiI (I.inv_mem ⟨r, rfl⟩)
  let f : Z →* I := N.rangeRestrict
  have hfc : Continuous f := hN.subtype_mk _
  have hfs : Function.Surjective f := N.rangeRestrict_surjective
  have : LocallyCompactSpace I := hIcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hopen : IsOpenMap f := f.isOpenMap_of_sigmaCompact hfs hfc
  have hK' : IsCompact (Subtype.val ⁻¹' D : Set I) :=
    hIcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have key : ∃ C : Set Z, IsCompact C ∧ (Subtype.val ⁻¹' D : Set I) ⊆ f '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set Z, IsCompact C ∧ s ⊆ f '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · intro y _
      obtain ⟨g, rfl⟩ := hfs y
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, hCD⟩ := key
  refine ⟨C, hC, fun z hz => ?_⟩
  obtain ⟨c, hcC, e⟩ := hCD (a := f z) hz
  have e' : N c = N z := congrArg Subtype.val e
  refine ⟨z * c⁻¹, ?_, c, hcC, by group⟩
  rw [← hNval, map_mul, map_inv, e', mul_inv_cancel]

end GlobalTheory.InvolutionNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolutionStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_mod_normOneKernel_involution : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  first | exact @GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | exact GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | (intros; apply GlobalTheory.InvolutionNorm.exists_compact_mod_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem similitude_eigvec_orthogonal : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  intro n h g c Z lam hh hdet hc hg hinj hnorm hgZ
  set M : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  set H : Matrix (Fin n) (Fin n) ℂ := Mᴴ * h * M with hH
  have hHherm : H.IsHermitian := by
    simp only [hH, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]
  have key : (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam = (c : ℂ) • H := by
    have e1 : (M * Matrix.diagonal lam)ᴴ * h * (M * Matrix.diagonal lam) = (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam := by
      simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← e1, ← hgZ]
    simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * h), hg]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hc' : ∀ i, (starRingEnd ℂ) (lam i) * lam i = (c : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hnorm i
    rw [h0, norm_zero] at this
    exact hc (by simpa using this.symm)
  have hoff : ∀ i j, i ≠ j → H i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun key i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul] at e
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h).symm)
    have hstar : (starRingEnd ℂ) (lam i) ≠ 0 := by simpa using hlam0 i
    have e2 : (starRingEnd ℂ) (lam i) * (lam j - lam i) * H i j = 0 := by
      rw [← hc' i] at e
      simp only [Pi.star_apply] at e
      have : star (lam i) = (starRingEnd ℂ) (lam i) := rfl
      rw [this] at e
      linear_combination e
    rcases mul_eq_zero.mp e2 with h1 | h1
    · exact absurd h1 (mul_ne_zero hstar hne)
    · exact h1
  have hdiag : H = Matrix.diagonal (fun i => (((H i i).re : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact (hHherm.coe_re_apply_self i).symm
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun i => (H i i).re, ?_, hdiag⟩
  have hdetH : H.det ≠ 0 := by
    have hMdet : M.det ≠ 0 := by
      rw [hM]; exact (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit |>.ne_zero
    simp only [hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (by simpa using hMdet) hdet) hMdet
  intro i hi
  rw [hdiag, Matrix.det_diagonal] at hdetH
  apply hdetH
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvaluStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  first | (exact @GlobalTheory.similitude_eigvec_orthogonal) | (exact GlobalTheory.similitude_eigvec_orthogonal) | (intros; apply GlobalTheory.similitude_eigvec_orthogonal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAway
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p → ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.ratDen_pow_of_intAfP) | (exact GlobalTheory.ratDen_pow_of_intAfP) | (intros; apply GlobalTheory.ratDen_pow_of_intAfP  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.IndepBaseChange

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_contract {k E : Type} [Field k] [Field E] [Algebra k E] {A B : CommRingCat.{0}}
    {f : CommRingCat.of k ⟶ A} {p : A ⟶ B} {q : CommRingCat.of E ⟶ B}
    (po : IsPushout f (CommRingCat.ofHom (algebraMap k E)) p q) (l : E →ₗ[k] k) :
    ∃ Λ : B →+ A, ∀ (e : E) (a : A), Λ (q.hom e * p.hom a) = f.hom (l e) * a := by
  letI : Algebra k A := f.hom.toAlgebra
  have w := (CommRingCat.isPushout_tensorProduct k A E).w
  let d := po.desc _ _ w
  let m : A ⊗[k] E →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ l.lTensor A
  refine ⟨m.toAddMonoidHom.comp d.hom.toAddMonoidHom, fun e a => ?_⟩
  have h₁ : d.hom (p.hom a) = a ⊗ₜ[k] (1 : E) := congrArg (fun g => g.hom a) (po.inl_desc _ _ w)
  have h₂ : d.hom (q.hom e) = (1 : A) ⊗ₜ[k] e := congrArg (fun g => g.hom e) (po.inr_desc _ _ w)
  change m (d.hom (q.hom e * p.hom a)) = _
  rw [map_mul, h₁, h₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [m, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  rfl

theorem comb_f {k : Type} [Field k] (S : LinSys k) (u : Fin S.N → k) (i : S.L.ι) {W : S.Y.Opens}
    (h : W ≤ S.L.U i) : resG S.Y h ((S.comb u).f i) =
      ∑ j, ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top).hom (u j) *
        resG S.Y h ((S.b j).f i) := by
  let e : S.L.Sec →+ Γ(S.Y, W) :=
    { toFun := fun s => resG S.Y h (s.f i), map_zero' := map_zero _, map_add' := fun _ _ => map_add _ _ _ }
  refine (map_sum e _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (map_mul (resG S.Y h) _ _).trans (congrArg (· * _) ?_)
  refine (LB.resG_resG _ _ _).trans ?_
  rfl

theorem indep_baseChange (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k) (hS : S.Indep) :
    (S.baseChange E).Indep := by
  intro u hu
  have key : ∀ l : E →ₗ[k] k, (fun j => l (u j)) = (0 : Fin S.N → k) := fun l => by
    refine hS _ (LB.f_injective (funext fun i => ?_))
    refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
      (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
    · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
      exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
    obtain ⟨⟨W, hW⟩, hle⟩ := W
    have H := S.isPullback_baseChange E
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
      (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
    have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
        (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
      refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
        (by simp) ?_ (by simp) (by simp)
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    obtain ⟨Λ, hΛ⟩ := exists_contract po' l
    have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
      fun y hy => Set.mem_iInter.2 fun _ => hle hy
    have e := comb_f (S.baseChange E) u (fun _ => i) hle'
    rw [hu] at e
    have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
        ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
      have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
        (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
      have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
      exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
    have e₂ := congrArg Λ e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e', map_sum, hΛ] at e₂
    refine (comb_f S _ i hle).trans (e₂.symm.trans ?_)
    exact ((congrArg Λ (map_zero _)).trans (map_zero Λ)).trans (map_zero _).symm
  funext j
  exact (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l => congrFun (key l) j

end GlobalTheory.Adelic.IndepBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSq
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem cm_conj_extends_of_adjoin :
    ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M]
      (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) →
      ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧
        σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  intro F M _ _ _ _ _ _ π c hadj hc hπ

  have gen : ∀ S : Subring M, (∀ x : F, algebraMap F M x ∈ S) → π ∈ S → ∀ y : M, y ∈ S := by
    intro S hS hpS y
    let A : Subalgebra F M := { S with algebraMap_mem' := hS }
    have hle : Algebra.adjoin F {π} ≤ A := Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show π ∈ A from hpS))
    rw [hadj] at hle
    exact hle (Algebra.mem_top (x := y))

  have hconj : ∀ φ : M →+* ℂ, φ π ≠ 0 ∧ (starRingEnd ℂ) (φ π) = φ ((c : M) / π) := by
    intro φ
    have hn : Complex.normSq (φ π) = (c : ℝ) := by rw [← Complex.sq_norm]; exact hπ φ
    have hne : φ π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hn
      exact hc (by exact_mod_cast hn.symm)
    refine ⟨hne, ?_⟩
    rw [map_div₀, map_ratCast, eq_div_iff hne, mul_comm, Complex.mul_conj, hn]
    norm_cast
  obtain ⟨φ₀⟩ : Nonempty (M →+* ℂ) := inferInstance
  let ψ : M →+* ℂ := (starRingEnd ℂ).comp φ₀
  have hrange : ∀ y : M, ψ y ∈ φ₀.range := by
    refine gen (Subring.comap ψ φ₀.range) ?_ ?_
    · intro x
      show ψ (algebraMap F M x) ∈ φ₀.range
      refine ⟨algebraMap F M (IsCMField.complexConj F x), ?_⟩
      exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x)
    · show ψ π ∈ φ₀.range
      exact ⟨(c : M) / π, ((hconj φ₀).2).symm⟩
  let e : M ≃+* φ₀.range := RingEquiv.ofBijective φ₀.rangeRestrict
    ⟨fun a b h => φ₀.injective (congrArg Subtype.val h), φ₀.rangeRestrict_surjective⟩
  let σ : M →+* M := e.symm.toRingHom.comp (ψ.codRestrict φ₀.range hrange)
  have hσ0 : ∀ x : M, φ₀ (σ x) = (starRingEnd ℂ) (φ₀ x) := by
    intro x
    have h1 : e (σ x) = ψ.codRestrict φ₀.range hrange x := by simp [σ]
    have h2 : ((e (σ x) : φ₀.range) : ℂ) = ((ψ.codRestrict φ₀.range hrange x : φ₀.range) : ℂ) := congrArg Subtype.val h1
    exact h2
  have hσF : ∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x) := by
    intro x
    apply φ₀.injective
    rw [hσ0]
    exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x).symm
  have hσπ : σ π = (c : M) / π := by
    apply φ₀.injective
    rw [hσ0]; exact (hconj φ₀).2
  have hπ0 : π ≠ 0 := fun h => (hconj φ₀).1 (by rw [h, map_zero])
  refine ⟨σ, hσF, ?_, ?_⟩
  · rw [hσπ, div_mul_cancel₀ _ hπ0]
  · intro φ
    have := gen (RingHom.eqLocus (φ.comp σ) ((starRingEnd ℂ).comp φ)) ?_ ?_
    · intro x; exact this x
    · intro x
      show φ (σ (algebraMap F M x)) = (starRingEnd ℂ) (φ (algebraMap F M x))
      rw [hσF]
      exact IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F M)) x
    · show φ (σ π) = (starRingEnd ℂ) (φ π)
      rw [hσπ]; exact ((hconj φ).2).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSqStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_conj_extends_of_adjoin_absSq : ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M] (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) → ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧ σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  first | (exact @GlobalTheory.cm_conj_extends_of_adjoin) | (exact GlobalTheory.cm_conj_extends_of_adjoin) | (intros; apply GlobalTheory.cm_conj_extends_of_adjoin  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxTranslateExponent
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

open GlobalTheory.FinTranslate

theorem hx_translate_exponent {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (hs : IsSympl X bas)
    (hd : x ∈ X.dom) (z a : Fin g → ℂ) :
    (Real.pi : ℂ) * I * (((hx X bas idx x (z + a) (-a)).im : ℝ) : ℂ) +
        -(Real.pi / 2 : ℂ) * hx X bas idx x (z + a) (z + a) =
      -(Real.pi / 2 : ℂ) * hx X bas idx x z z + -(Real.pi * hx X bas idx x (z + (1 / 2 : ℂ) • a) a) := by
  have h1 := fock_hx_conj X bas idx x hs hd z a
  have h2 := fock_hx_conj X bas idx x hs hd a a
  have h3 : hx X bas idx x (z + a) (-a) = -hx X bas idx x (z + a) a := by
    rw [← neg_one_smul ℂ a, fock_hx_smul_right]; simp
  rw [h3]
  simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left]
  rw [h1]
  have h4 : (hx X bas idx x a a).im = 0 := conj_eq_iff_im.1 h2.symm
  generalize hx X bas idx x z a = s
  generalize hx X bas idx x z z = t
  generalize hx X bas idx x a a = q at h4
  have h5 : ((s.im : ℝ) : ℂ) = (s - conj s) / (2 * I) := im_eq_sub_conj s
  simp only [neg_im, add_im, h4, add_zero, ofReal_neg, h5]
  field_simp
  ring

theorem reads_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ γ u, IsFinOf V W γ u → Reads θ V W hr X bas idx (heisO ψ V W u f) (heisG X bas (-(colsR hr γ)) φ) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0 f φ hf hR γ u hu
  have hd : x ∈ X.dom := mem_dom_of_isOrtho hx0
  obtain ⟨hsb, hth⟩ := (thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hs he x hd φ hR.1).1
    (-(colsR hr γ))
    |> fun h => (⟨(h 0).1, fun z => (h z).2⟩ : _ ∧ ∀ z, _)
  refine ⟨hsb, fun w hw => ?_⟩
  obtain ⟨hrat, hadd, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x
  have hsy : ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I *
      ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
    first
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hd
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0
  obtain ⟨v, hv⟩ : ∃ v : WO V W, ratW W V γ = v + u := ⟨ratW W V γ - u, (sub_add_cancel _ _).symm⟩
  have hfadd (a b : WO V W) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
    ext i j
    exact (finPart D).map_add _ _
  have hiadd (a b : WO V W) : (a + b).map (infPart D) = a.map (infPart D) + b.map (infPart D) := by
    ext i j
    exact (infPart D).map_add _ _
  have hvf : v.map (finPart D) = 0 := by
    have h := hu.2
    rw [hv, hfadd] at h
    exact left_eq_add.1 (h.trans (add_comm _ _))
  have hvi : v.map (infPart D) = (ratW W V γ).map (infPart D) := by
    rw [hv, hiadd, hu.1, add_zero]
  obtain ⟨w', hw'⟩ : ∃ w' : WO V W, w = w' + v := ⟨w - v, (sub_add_cancel _ _).symm⟩
  have hw'f : w'.map (finPart D) = 0 := by
    have h := hw
    rwa [hw', hfadd, hvf, add_zero] at h
  have hzv := hrat γ v hvi
  have hneg : ∀ b, pv X idx x ((-(colsR hr γ)) b) = -pv X idx x (colsR hr γ b) := by
    intro b
    have h0 : per X x 0 = 0 := by simpa using per_add X x 0 0
    have h1 := per_add X x (colsR hr γ b) (-(colsR hr γ b))
    rw [add_neg_cancel, h0] at h1
    funext j
    have h2 := congrFun h1 (idx j)
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hz' : zOf θ V W hr X idx x w' =
      fun b => zOf θ V W hr X idx x w b + pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hw', hadd, hzv]
    simp
  have hzv' : zOf θ V W hr X idx x v = fun b => -pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hzv, neg_neg]
  have e1 : w + u = ratW W V γ + w' := by rw [hw', hv]; abel
  have e2 : -symplOH V W (ratW W V γ) w' = symplOH V W w' v := by
    rw [hv, symplOH_add_left, symplOH_fin_real hu.1 hw'f, add_zero, symplOH_skew V W v w']
  rw [heisO, symplOH_real_fin hu.1 hw, AddChar.map_zero_eq_one, _root_.one_mul, e1, hf.quasi, e2, hsy w' v hw'f,
    hR.2 w' hw'f, hth, hz', hzv', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [ofReal_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => hx_translate_exponent X bas idx x hs hd _ _

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothForm
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology

namespace GlobalTheory.ConstTermZalg

open GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem good_add {φ ψ : Sm E a} (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1, hψ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      (Filter.inter_mem (hφ.2.mem_nhds (by simp)) (hψ.2.mem_nhds (by simp))) fun k hk => ?_)
    obtain ⟨h1, h2⟩ := hk
    have h1' : finRep E a k φ = φ := h1
    have h2' : finRep E a k ψ = ψ := h2
    show finRep E a k (φ + ψ) = φ + ψ
    rw [map_add (f := _), h1', h2']

theorem good_smul {φ : Sm E a} (hφ : Good φ) (s : ℂ) : Good (s • φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · simp [hφ.1]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hφ.2.mem_nhds (by simp)) fun k hk => ?_)
    have h1' : finRep E a k φ = φ := hk
    show finRep E a k (s • φ) = s • φ
    rw [map_smul, h1']

theorem good_integrable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν] {φ : Sm E a} (h : Good φ) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) ν := by
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h.2
  exact integrable_unip ν (Ψ := fun g (_ : Lie E a) => φ.1 g) (hc.comp continuous_fst).continuousOn
    (fun γ g => funext fun _ => h.1 γ g) g (y := oneL E a) isUnit_one

theorem constTerm_zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
      (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hH hF h1 φ hl ho z hz c hc
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  let CT : Sm E a → GA E a → ℂ := fun ψ g => ∫ x, ψ.1 (unip x * g) ∂(μ.restrict 𝓕)
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ ψ, Good ψ → Good (z ψ) ∧ ∀ c : Sm E a, c.1 = CT ψ → (z c).1 = CT (z ψ)}
      mul_mem' := by
        intro z w hz hw ψ h
        exact ⟨(hz _ (hw ψ h).1).1, fun c hc => (hz _ (hw ψ h).1).2 _ ((hw ψ h).2 c hc)⟩
      add_mem' := by
        intro z w hz hw ψ h
        refine ⟨good_add (hz ψ h).1 (hw ψ h).1, fun c hc => ?_⟩
        have e1 := (hz ψ h).2 c hc
        have e2 := (hw ψ h).2 c hc
        funext g
        simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, e1, e2, CT]
        rw [integral_add (good_integrable _ (hz ψ h).1 g) (good_integrable _ (hw ψ h).1 g)]
      algebraMap_mem' := by
        intro s ψ h
        simp only [Module.algebraMap_end_apply]
        refine ⟨good_smul h s, fun c hc => ?_⟩
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, hc, CT, smul_eq_mul]
        rw [integral_const_mul] }
  have hlie : ∀ X, lie E a X ∈ S := fun X ψ h => ⟨h.lie X, fun c hc => funext fun g => by
    rw [lie_apply, hc]
    exact (constTerm_mem_Sm E a r μ 𝓕 hH hF h1 ψ h.1 h.2).2 X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hlie _) (S.smul_mem (hlie _) _)) _
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, ho⟩).2 c hc

end GlobalTheory.ConstTermZalg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothFormStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_center_action_smooth_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermZalg.constTerm_zalg | exact GlobalTheory.ConstTermZalg.constTerm_zalg | (intros; apply GlobalTheory.ConstTermZalg.constTerm_zalg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.CentSep

theorem apply_basis_eq_smul {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g) (k : κ) :
    ∃ c : L, g (b k) = c • b k := by
  refine ⟨b.repr (g (b k)) k, ?_⟩
  set x := g (b k) with hx
  have hfx : f x = μ k • x := by
    have := congrArg (fun φ : Module.End L V => φ (b k)) hg
    simp only [LinearMap.comp_apply, hf] at this
    rw [hx, ← this, map_smul]
  have hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j := by
    intro y j
    have key : (b.coord j).comp f = μ j • b.coord j := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    exact congrArg (fun φ : V →ₗ[L] L => φ y) key
  apply b.ext_elem
  intro j
  by_cases hj : j = k
  · subst hj; simp
  · have h1 := hrep x j
    rw [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h0 : b.repr x j = 0 := by
      have h2 : (μ j - μ k) * b.repr x j = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (hμ (sub_eq_zero.mp h)) hj
      · exact h
    rw [h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj),
      smul_zero]

theorem comm_of_eigenbasis {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g h : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g)
    (hh : h ∘ₗ f = f ∘ₗ h) : g ∘ₗ h = h ∘ₗ g := by
  refine b.ext fun k => ?_
  obtain ⟨c, hc⟩ := apply_basis_eq_smul b μ hμ f g hf hg k
  obtain ⟨d, hd⟩ := apply_basis_eq_smul b μ hμ f h hf hh k
  simp only [LinearMap.comp_apply]
  rw [hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]

theorem comm_of_separable_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι] [DecidableEq ι]
    (A G H : Matrix ι ι L) (hs : A.charpoly.Separable) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set f := Matrix.toLin' A with hfdef
  set s : Finset L := A.charpoly.roots.toFinset with hsdef
  have hcard : s.card = Fintype.card ι := by
    rw [hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  have hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ := by
    intro μ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']
    have hμ := μ.2
    simp only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ
    exact Polynomial.isRoot_of_mem_roots hμ
  choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent f (s : Set L) v hv
  have hc : Fintype.card (s : Set L) = Module.finrank L (ι → L) := by
    simp [hcard]
  haveI : Nonempty (s : Set L) := by
    rw [← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]; exact Fintype.card_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ∀ k, f (b k) = (k : L) • b k := fun k => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hv k).apply_eq_smul
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb
    (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul])
    (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])

theorem centraliser_comm_of_separable : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  intro K _ ι _ _ γ g h hs hg hh
  apply Units.ext
  have hg' := congrArg Units.val hg
  have hh' := congrArg Units.val hh
  simp only [Units.val_mul] at hg' hh' ⊢
  let φ := algebraMap K (AlgebraicClosure K)
  apply Matrix.map_injective φ.injective
  simp only [Matrix.map_mul]
  apply comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [← Matrix.map_mul, hg', Matrix.map_mul]
  · rw [← Matrix.map_mul, hh', Matrix.map_mul]

end GlobalTheory.CentSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqOfOrth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker GlobalTheory.IndefiniteRowSideFullHecke Filter Topology
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.VacuumFrameCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem af_ext {α β : Af D.host.F} (h : ∀ w, evalV D.host.F w α = evalV D.host.F w β) : α = β :=
  FiniteAdeleRing.ext _ h

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from af_ext fun w => ?_)
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

end GlobalTheory.VacuumFrameCompare

end
end
