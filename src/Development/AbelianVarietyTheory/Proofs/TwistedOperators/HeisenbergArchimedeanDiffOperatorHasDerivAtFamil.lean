module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

noncomputable section

namespace GlobalTheory.HeisOrbit.DOpDeriv

theorem hasDerivAt_fderiv_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ℂ) (hH : ContDiff ℝ 2 H) (g : E → ℂ)
    (hg : ∀ y, HasDerivAt (fun t => H (t, y)) (g y) 0) (P : ℝ → E) (P' : E) (hP : HasDerivAt P P' 0) (y : E) :
    HasDerivAt (fun t => fderiv ℝ (fun z => H (t, z)) y (P t))
      (fderiv ℝ g y (P 0) + fderiv ℝ (fun z => H (0, z)) y P') 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ (t : ℝ) (v : E), fderiv ℝ (fun z => H (t, z)) y v = fderiv ℝ H (t, y) (0, v) := by
    intro t v
    have := ((hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv
    have e : (fun z => H (t, z)) = H ∘ (fun z => (t, z)) := rfl
    rw [e, this]
    simp
  have h2 : g = fun z => fderiv ℝ H (0, z) (1, 0) := by
    funext z
    have hc : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    have := (hd (0, z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact (hg z).unique this
  have h3 : ∀ v : E, fderiv ℝ g y v = fderiv ℝ (fderiv ℝ H) (0, y) (0, v) (1, 0) := by
    intro v
    have a := (hd1 (0, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have b := (a.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)).fderiv
    have e : g = fun z => ((fderiv ℝ H) ∘ (fun z => ((0 : ℝ), z))) z (1, 0) := h2
    rw [e, b]
    simp
  have hs : IsSymmSndFDerivAt ℝ H (0, y) :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp)
  have hc : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
  have a := (hd1 (0, y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hQ : HasDerivAt (fun t : ℝ => ((0 : ℝ), P t)) ((0 : ℝ), P') 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hP
  have b := a.clm_apply hQ
  simp only [h1, h3]
  rw [hs.eq (0, P 0) (1, 0)]
  exact b

theorem dOp_hasDerivAt : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  intro F _ _ κ _ G P Q g' P' Q' hG hg hP hQ y
  have h1 := hasDerivAt_fderiv_family (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2)
    (hG.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) g' hg P P' hP y
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    { toFun := fun q => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * q i)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, RingHom.id_apply] }
  have h2 : HasDerivAt (fun t => L (Q t)) (L Q') 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ
  have h3 := ((h2.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).mul (hg y))
  have h4 := h1.sub h3
  refine HasDerivAt.congr_deriv (f := fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) h4 ?_
  symm
  simp only [GlobalTheory.HeisOrbit.dOp]
  change _ = fderiv ℝ g' y (P 0) + fderiv ℝ (G 0) y P' - (2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q' i) : ℝ) : ℂ) * G 0 y + 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q 0 i) : ℝ) : ℂ) * g' y)
  ring

end GlobalTheory.HeisOrbit.DOpDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamilStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergArchimedeanDiffOperator_hasDerivAt_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  first | exact @GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | exact GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | (intros; apply GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∉ P.asIdeal := by
  classical
  choose! x hx hxP using hP
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ v ∈ S, x v) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hv := hS Q hJ
    have hxv : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hv
    rw [map_prod, ← Finset.prod_erase_mul _ _ hv]
    exact Ideal.mul_mem_left J _ hxv
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ v ∈ S, x v) ^ K, by rwa [map_pow], fun h => ?_⟩
  rw [map_pow] at h
  have h1 := P.isPrime.mem_of_pow_mem K h
  rw [map_prod] at h1
  obtain ⟨v, hv, h2⟩ := (P.isPrime.prod_mem_iff).1 h1
  exact hxP v hv _ rfl h2

theorem oToS_smul_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    oToS F E a • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Subring.smul_def, oToS_coe]
    simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx

end GlobalTheory.CongMember

namespace GlobalTheory.CongMember

open Matrix
open scoped TensorProduct

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_sub_one {R : Type} [CommRing R] (u : R) (hu : u * u = u) (A B K : Matrix (Fin n) (Fin n) R)
    (hA : u • (A - 1) = A - 1) (hB : (1 - u) • (B - 1) = B - 1) (hK : K = A * B ∨ K = B * A) : A - 1 = u • (K - 1) := by
  have e1 : u • B = u • 1 := by
    rw [← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]
  have e2 : u • K = u • A := by
    rcases hK with rfl | rfl
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
  rw [smul_sub, e2, ← smul_sub, hA]

theorem cong_of_eq (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ 𝔪)
    (u : Formalism.L2.Herm.intAf F E) (A K : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (e : A - 1 = ((u * oToS F E a : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • (K - 1))
    (hK : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, K *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, A *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  intro y hy
  have e1 : A *ᵥ y - y = (A - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e2 : K *ᵥ y - y = (K - 1) *ᵥ y := by rw [sub_mulVec, one_mulVec]
  have e' : A *ᵥ y - y = (u * oToS F E a) • (K *ᵥ y - y) := by
    rw [e1, e2, e, Matrix.smul_mulVec, Subring.smul_def]
  rw [e', mul_smul]
  exact Submodule.smul_mem _ u (oToS_smul_mem_hatL Λ ha (Submodule.sub_mem _ (hK y hy) hy))

theorem hatL_smul_le (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) :
    Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) ≤ Formalism.L2.Herm.hatL (F := F) Λ :=
  Submodule.span_mono (Set.image_mono Submodule.smul_le_right)

theorem mem_congLev_of [StarRing E] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hU : x ∈ UA hc J)
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ))
    (h2 : ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    x ∈ congLev hc J Λ 𝔪 := by
  refine ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, h1⟩
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h1 y hy)) hy
    rwa [sub_add_cancel] at this
  · have := Submodule.add_mem _ (hatL_smul_le Λ 𝔪 (h2 _ hy)) hy
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec, sub_add_cancel] at this

theorem stab_of_mem_congLev [StarRing E] {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {𝔪 : Ideal (𝓞 E)} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ congLev hc J Λ 𝔪) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  ⟨fun y hy => (hx.2.1 y).1 hy, fun y hy => ((Subgroup.inv_mem _ hx).2.1 y).1 hy⟩

end General

variable {D : D7}

theorem exists_idem_eq {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {e f : Formalism.L2.Theta.AE D} (hi : IsPrimeIdem P e f) :
    ∃ a ∈ 𝔪, ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      ((u * oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f := by
  obtain ⟨X, hX𝔪, hXP⟩ := exists_F_mem h𝔪 hS hP
  obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int hi _ _ ((D.sp.cm.fixed _).2 ⟨(X : D.host.F), rfl⟩).symm hXP hXP
  exact ⟨_, hX𝔪, u, hu⟩

end GlobalTheory.CongMember
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulMemLattice
namespace GlobalTheory.NatMultipleInLattice

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨F, hF, hz⟩ := hz
    refine ⟨D * F, mul_ne_zero hD hF, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy F
    · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hz D
  | smul a y _ hy =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨m, hm, hi⟩ := exists_nat_mul_integral a
    refine ⟨m * D, mul_ne_zero hm hD, ?_⟩
    have key := L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy
    have : (m * D) • a • y =
        (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y := by
      have h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y
          = ((m : E) * a) • D • y := rfl
      rw [h3]
      ext i
      simp only [Pi.smul_apply]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]; exact key

end GlobalTheory.NatMultipleInLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.AdelicLatticeIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nsmul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice L hL x

theorem exists_nsmul_map_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (N : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ D : ℕ, D ≠ 0 ∧ ∀ y ∈ L, D • N y ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)
  refine ⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem D hg
      rw [hk, mul_comm, mul_smul]; exact nsmul_mem (hDm g) k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact L.add_mem hx hy
  | smul r x _ hx =>
      have : N (r • x) = r • N x := N.map_smul_of_tower r x
      rw [this, smul_comm]; exact L.smul_mem r hx

end GlobalTheory.AdelicLatticeIntegral

namespace GlobalTheory.AdelicLatticeIntegral

theorem exists_finset_smul_mulVec_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  classical
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Fin n × Fin n × Fin (Module.finrank F E) → AF F := fun j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := fun y i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)
  have key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · intro p _ hp
      simp [Nm, incV, Pi.single_apply, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)
  let c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))
  refine ⟨(Set.finite_iUnion hfin).toFinset, ?_⟩
  intro w hw a ha hai y hy
  have hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F := by
    intro j
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y) := by
    intro j
    have h1 : incV (D j • Nm j y) = D j • incV (Nm j y) := by
      funext i; simp [incV]
    rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
    congr 1
    have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
    simp only [c', mul_assoc]
    rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
  change a • (M *ᵥ incV y) ∈ _
  rw [key, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [hterm j]
  refine AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
  · rw [map_mul]; exact mul_mem hai (hc' j)

end GlobalTheory.AdelicLatticeIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  exact @_root_.GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquations
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_realAd_mul (t : ℝ) (c : AF F) : evI F (realAd F t * c) = t • evI F c := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, Algebra.smul_def]
  congr 1
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem realAd_mul_snd (t : ℝ) (c : AF F) : (realAd F t * c).2 = 0 := by
  show (realAd F t).2 * c.2 = 0
  simp [realAd]

theorem at_realAd_mul (t : ℝ) (c : AF F) : At (evI F) (realAd F t * c) := by
  intro b hb
  have h1 : b.1 = 0 := by
    have : InfiniteAdeleRing.ringEquiv_mixedSpace F b.1 = 0 := hb
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  rw [smul_eq_mul, ← mul_assoc]
  have : b * realAd F t = 0 := Prod.ext (by show b.1 * _ = 0; rw [h1, zero_mul]) (by show _ * (realAd F t).2 = 0; simp [realAd])
  rw [this, zero_mul]

def gam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (t : ℝ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ _ (y ⬝ᵥ fun i => evI F (w.2 i)) + t ^ 2 * Algebra.trace ℝ _ (evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : ℝ) : ℂ)) *
    f (y + t • fun i => evI F (w.1 i))

theorem gam_differentiableAt (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun t => gam w f t y) 0 := by
  unfold gam
  fun_prop

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ) (f : SInf F κ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x = gam w f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  have hK : x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2) =
      realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hev : evI F (realAd F t * (x ⬝ᵥ w.2 + realAd F t * (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))) =
      t • ((fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (w.2 i)) + t • evI F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) := by
    rw [evI_realAd_mul]
    congr 1
    rw [← evIHom_apply, map_add (f := _), evIHom_apply, evIHom_apply, evI_realAd_mul, ← evIHom_apply (x ⬝ᵥ w.2),
      RingHom.map_dotProduct]
    rfl
  unfold schr pureA gam
  rw [hK, hψ.2.2 _ (at_realAd_mul _ _), hev]
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • w).1) i).1) =
      (fun i => evI F (x i)) + t • fun i => evI F (w.1 i) := by
    funext i
    show evIHom (x i + realAd F t * w.1 i) = evI F (x i) + t • evI F (w.1 i)
    rw [map_add (f := _), evIHom_apply, evIHom_apply, evI_realAd_mul]
  have hg : (fun i => ((x + (realAd F t • w).1) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (realAd F t * w.1 i).2 = (x i).2
    rw [realAd_mul_snd, add_zero]
  rw [hf, hg]
  simp only [map_smul, map_add (f := _), smul_eq_mul]
  ring_nf

end GlobalTheory.VacFactor

noncomputable section

namespace GlobalTheory.VacFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dgam (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  deriv (fun t => gam w f t y) 0

theorem exists_indep {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ k, g k ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ LinearIndependent ℂ g ∧ Φ = ∑ k, pureA F (f k) (g k) := by
  obtain ⟨m₀, c, p, hp⟩ := Submodule.mem_span_set'.mp hΦ
  choose f₀ g₀ hg₀ hp₀ using fun i => (p i).2
  set f₁ : Fin m₀ → SInf F κ := fun i => c i • f₀ i
  have hΦ' : Φ = ∑ i, pureA F (f₁ i) (g₀ i) := by
    rw [← hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hp₀ i]
    funext x
    simp [f₁, pureA, mul_assoc]
  set V := Submodule.span ℂ (Set.range g₀)
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g₀)
  let b := Module.finBasis ℂ V
  have hmem : ∀ i, g₀ i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  let a : Fin m₀ → Fin (Module.finrank ℂ V) → ℂ := fun i j => b.repr ⟨g₀ i, hmem i⟩ j
  have hg : ∀ i z, g₀ i z = ∑ j, a i j * (b j : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z := by
    intro i z
    have := congrArg (fun v : V => (v : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) z) (b.sum_repr ⟨g₀ i, hmem i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨Module.finrank ℂ V, fun j => ∑ i, a i j • f₁ i, fun j => (b j : _), fun j => ?_, ?_, ?_⟩
  · exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hg₀ i)) (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · rw [hΦ']
    funext x
    simp only [Finset.sum_apply, pureA, hg, Finset.mul_sum, Finset.sum_mul, SchwartzMap.sum_apply,
      SchwartzMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (t : ℝ) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    M.heisLine ψ u t (pureA F f g) x = gam (M.co.e u) f t (fun i => evI F (x i)) * g (fun i => (x i).2) := by
  unfold Model.heisLine Darboux.rho
  rw [map_smul, schr_pureA ψ hψ]

theorem hasDerivAt_heisLine_pureA (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (pureA F f g) x)
      (dgam (M.co.e u) f (fun i => evI F (x i)) * g (fun i => (x i).2)) 0 := by
  simp only [heisLine_pureA M ψ hψ]
  exact (gam_differentiableAt _ _ _).hasDerivAt.mul_const _

theorem hasDerivAt_heisLine_sum (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (g : Fin m → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : Fin n × Fin d → AF F) :
    HasDerivAt (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x)
      (∑ k, dgam (M.co.e u) (f k) (fun i => evI F (x i)) * g k (fun i => (x i).2)) 0 := by
  have e : (fun t : ℝ => M.heisLine ψ u t (∑ k, pureA F (f k) (g k)) x) =
      fun t => ∑ k, M.heisLine ψ u t (pureA F (f k) (g k)) x := by
    funext t
    simp only [Model.heisLine, Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [e]
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_heisLine_pureA M ψ hψ u (f k) (g k) x

end GlobalTheory.VacFactor


open GlobalTheory.VacFactor in
theorem GlobalTheory.VacFactor.mem_span_of_isGaussEq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hψ Φ hΦ hG
  obtain ⟨m, f, g, hg, hgi, rfl⟩ := exists_indep hΦ
  obtain ⟨ε, hε⟩ := hG
  let mk : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) →
      (Fin n × Fin d → AF F) :=
    fun y z i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), z i)
  have hmk1 : ∀ y z, (fun i => evI F (mk y z i)) = y := fun y z => by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have hmk2 : ∀ y z, (fun i => (mk y z i).2) = z := fun y z => rfl
  have key : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
      ∀ k y, dgam (M.co.e u') (f k) y = Complex.I * dgam (M.co.e u) (f k) y := by
    intro u u' hu hu' hr k y
    have h0 : ∑ k, (dgam (M.co.e u') (f k) y - Complex.I * dgam (M.co.e u) (f k) y) • g k = 0 := by
      funext z
      have e := hε u u' hu hu' hr (mk y z)
      rw [(hasDerivAt_heisLine_sum M ψ hψ u' f g (mk y z)).deriv,
        (hasDerivAt_heisLine_sum M ψ hψ u f g (mk y z)).deriv, hmk1, hmk2] at e
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
      rw [e, Finset.mul_sum]
      simp only [mul_assoc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hgi _ h0 k)
  have hgne : ∀ k, ∃ z, g k z ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hgi.ne_zero k (funext h)
  have gauss : ∀ k, M.IsGauss ψ τ (f k) := by
    intro k
    obtain ⟨z₀, hz₀⟩ := hgne k
    refine ⟨ε, fun u u' hu hu' hr f₁ f₁' h1 h1' => ?_⟩
    have hR : Rest (evI F) (⇑(f k)) (fun x : Fin n × Fin d → AF F => g k (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f k, g k, hg k, rfl⟩⟩
      have hz2 : ∀ i, (z i).2 = 0 := by
        intro i
        have h0 : evI F (show AF F from ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))) = 0 := by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _
        have := congrArg (fun v : Fin n × Fin d → AF F => (v i).2) (hz _ h0)
        change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at this
        simpa using this
      have hxz : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [hz2, add_zero]
      exact congrArg (g k) hxz
    have hD : ∀ (v : Matrix (Fin n) (Fin d) (AE F E)) (f₂ : SInf F (Fin n × Fin d)),
        ActsD (evI F) (M.heisLine ψ v) (⇑(f k)) (⇑f₂) → ∀ y, f₂ y = dgam (M.co.e v) (f k) y := by
      intro v f₂ h y
      have a := h _ hR (mk y z₀)
      have b := hasDerivAt_heisLine_pureA M ψ hψ v (f k) (g k) (mk y z₀)
      have := a.unique b
      simp only [tens, hmk1, hmk2] at this
      exact mul_right_cancel₀ hz₀ this
    refine DFunLike.ext _ _ fun y => ?_
    rw [hD u' f₁' h1' y, key u u' hu hu' hr k y, ← hD u f₁ h1 y]
    simp
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, g k, ?_, hg k, rfl⟩
  exact Submodule.mem_sInf.mpr fun N hN => hN.1 _ (gauss k)

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGaussianVacuaSpanOfVacuumEquationsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gaussianVacuaSpan_of_vacuumEquations : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), GlobalTheory.VacDatum.IsGaussEq M ψ τ Φ →
      Φ ∈ Submodule.span ℂ {Φ' | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ),
        f ∈ M.Pol ψ τ ∧ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ Φ' = GlobalTheory.WeilM.pureA F f g} := by
  exact @GlobalTheory.VacFactor.mem_span_of_isGaussEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockLatVac

theorem infPart_latO_any {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem theta_isLatVac_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  intro D ψ θ S T hψ hθ LS LT P g hg hvac sS BS sT BT φ
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) := fun φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT hg φ
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth (2 • u)
      (infPart_latO_any (AddSubgroup.nsmul_mem _ hu 2)) (hvac.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT g hth u
      (infPart_latO_any hu) (hvac.2 e he u hu hh) φ

end GlobalTheory.FockLatVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaIsLatticeVacuumFockPureTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T LS LT P) g → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT g φ) ∧ IsLatVac (heisO ψ S T) (latO S T LS LT P) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | exact GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO | (intros; apply GlobalTheory.FockLatVac.theta_isLatVac_pureTensorO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem places_over_g : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL
  have hPg := hL.Pg
  refine ⟨fun PP hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact PP.asIdeal.mul_mem_right _ h1
    · exact PP.asIdeal.mul_mem_left _ h1
  · rw [Nat.cast_mul] at hQ
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      rcases Q.isPrime.mem_or_mem hQ with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hc : GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv Q (GlobalTheory.IdemSupport.cP Q) := by
      refine (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y hxy => ?_
      have h1 : y = GlobalTheory.IdemSupport.cO D x := by
        apply RingOfIntegers.ext
        rw [hxy, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      rw [GlobalTheory.IdemSupport.mem_cP, h1, GlobalTheory.IdemSupport.cO_cO]
    have hsp := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) Q hk).2.2.2
      (R.C.P.pb k) (R.C.P.pb_over k) _ hc
    by_cases hu : Q.under (𝓞 D.host.K) = R.C.P.pb k
    · exact ⟨Q, (hPg Q).2 ⟨k, hu⟩, Or.inl rfl⟩
    · have hu' : (GlobalTheory.IdemSupport.cP Q).under (𝓞 D.host.K) = R.C.P.pb k := by
        by_contra hn
        exact hu (hsp.2.2 hn)
      exact ⟨GlobalTheory.IdemSupport.cP Q, (hPg _).2 ⟨k, hu'⟩, Or.inr (GlobalTheory.StdFrames.cP_cP Q).symm⟩

end GlobalTheory.SeeConjRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_over_norm_and_cover_with_conjugates : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  first | exact @GlobalTheory.SeeConjRead.places_over_g | exact GlobalTheory.SeeConjRead.places_over_g | (intros; apply GlobalTheory.SeeConjRead.places_over_g <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefCont

theorem continuous_coefR : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  intro D θ hθ V S M v a
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  unfold coefR
  refine continuous_finsetProd _ fun τ _ => ?_

  have hc : Continuous fun g : GA D V => cmp θ τ g := GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)
  have hu : ∀ g : GA D V, (cmp θ τ g)ᴴ * gramAt D V τ * cmp θ τ g = gramAt D V τ := by
    intro g
    have h0 := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram (tauE D τ)
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x) (θ τ) (hθ τ) g
    have he : (cmp θ τ g)ᴴ = ((cmp θ τ g).map (starRingEnd ℂ)).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he]
    exact h0
  have hB : M.fr τ * (M.fr τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hmem : ∀ g : GA D V, Formalism.REAL.inUJ (M.ε τ) (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) := by
    intro g
    unfold Formalism.REAL.inUJ
    calc (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)
        = ((M.fr τ)⁻¹)ᴴ * ((cmp θ τ g)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * cmp θ τ g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
          rw [M.fr_gram τ, hu g]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) := by
          rw [hB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hconj : Continuous fun g : GA D V => M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have hσ := (M.ds τ).2.2.1.2.2 (a τ)
  have hrep : Continuous fun g : GA D V => M.rep τ (cmp θ τ g) (a τ) :=
    hσ.comp_continuous hconj hmem
  exact continuous_const.inner hrep

end GlobalTheory.SepPer.CoefCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_realPlacesMatrixCoefficientProduct : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  first | exact @GlobalTheory.SepPer.CoefCont.continuous_coefR | exact GlobalTheory.SepPer.CoefCont.continuous_coefR | (intros; apply GlobalTheory.SepPer.CoefCont.continuous_coefR <;> assumption)
end
end
