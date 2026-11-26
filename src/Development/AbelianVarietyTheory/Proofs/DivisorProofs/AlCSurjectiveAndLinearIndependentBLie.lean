module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem alC_surjective_and_linearIndependent_bLie :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → Function.Surjective P.alC ∧ ∀ (n : ℕ) (x : Fin n → LieG P.Gt), LinearIndependent C (fun j => evLie P (x j)) → LinearIndependent C (fun j => P.bLie (x j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hHT
  have hp : p.Prime := Fact.out
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : Function.Surjective P.alC := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro w -
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul c f =>
      have h1 : v (algebraMap O C (p : O)) ^ (p - 1) ≤ v (p : C) := by
        have hle := P.integers.map_le_one (p : O)
        rw [map_natCast] at hle ⊢
        exact pow_le_of_le_one zero_le hle (by have := hp.two_le; omega)
      have h2 := hHT (p : O) h1 f.1 f.2
      rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
      have h3 : P.al t = (p : O) • f := Subtype.ext ht
      refine ⟨(c * (p : C)⁻¹) • P.inclT t, ?_⟩
      rw [map_smul, P.alC_inclT, h3, map_smul, ← algebraMap_smul C (p : O), map_natCast, smul_smul,
        inv_mul_cancel_right₀ h0, Point.inclOm, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
  refine ⟨hs, fun n x hx => LinearIndependent.of_comp P.pairV ?_⟩
  have e : (⇑P.pairV ∘ fun j => P.bLie (x j)) = ⇑P.alC.dualMap ∘ fun j => evLie P (x j) :=
    funext fun j => LinearMap.ext fun w => pairV_bLie_eq_evLie (x j) w
  rw [e]
  exact hx.map' _ (LinearMap.ker_eq_bot.2 (LinearMap.dualMap_injective_of_surjective hs))

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

end GlobalTheory.CurveClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem isCoprime_of_natCast_mem {D : D7} {I : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : Nat.Coprime N (D.host.QS * D.host.q))
    (hI : (N : 𝓞 D.host.E) ∈ I) : IsCoprime I D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  exact GlobalTheory.HalfCompare.not_mem_of_coprime P hN (GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb))
    (hle (Ideal.mem_sup_left hI))

theorem coprime_of_mod {a b m : ℕ} (h : a % m = 1) (hb : b ∣ m) : Nat.Coprime a b := by
  have : Nat.Coprime a m := by rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact this.coprime_dvd_right hb

theorem exists_nat_mem_place_coprime {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ∃ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hg : ∀ k, Nat.Coprime (D.host.g k) (D.host.QS * D.host.q) := fun k =>
    coprime_of_mod (D.ntypes.g_cond k) (dvd_mul_right _ _)
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
  · exact ⟨q0 D, coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      (Dvd.dvd.mul_left ⟨D.host.d, rfl⟩ _), P.basePlace_over_qZero⟩
  · rcases (S1_mem_OmF D).1 h1 with h' | h' | h' | h'
    · exact ⟨_, hg 0, h'⟩
    · exact ⟨_, hg 1, h'⟩
    · exact ⟨_, h.1, h'⟩
    · exact ⟨_, h.2, h'⟩

theorem exists_nat_mem_condE {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ N : ℕ, Nat.Coprime N (D.host.QS * D.host.q) ∧ (N : 𝓞 D.host.E) ∈ SqNum.condE P := by
  classical
  choose! p hp hm using fun v (hv : v ∈ P.S0) => exists_nat_mem_place_coprime P h hv
  refine ⟨∏ v ∈ P.S0, p v ^ condExp P v, Nat.Coprime.prod_left fun v hv => (hp v hv).pow_left _, ?_⟩
  unfold SqNum.condE
  push_cast
  refine Ideal.prod_mem_prod fun v hv => Ideal.pow_mem_pow ?_ _
  have h1 : ((p v : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by
    rw [P.under_w hv]; exact hm v hv
  simpa using Ideal.mem_comap.1 h1

theorem condE_isCoprime_halfDifferent {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    IsCoprime (SqNum.condE P) D.host.𝔟 ∧ IsCoprime (D.host.conj • SqNum.condE P) D.host.𝔟 := by
  obtain ⟨N, hN, hm⟩ := exists_nat_mem_condE P h
  refine ⟨isCoprime_of_natCast_mem hN hm, isCoprime_of_natCast_mem hN ?_⟩
  have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  have h2 : D.host.conj • (N : 𝓞 D.host.E) = N := map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) N
  rwa [h2] at h1

end GlobalTheory.FunObj.StdDatum.HalfDiff

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLatti
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

theorem word_succ {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    {t : ℕ} (u : Fin (t + 1) → Fin N → K) : word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem word_zero {K B : Type} [Field K] [AddCommGroup B] [Module K B] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K B)
    (u : Fin 0 → Fin N → K) : word mul u = 1 := by
  simp [word]

theorem mul_mem_V_succ (S : Sys F A) (hS : S.Hyp) {j : ℕ} (hj : j < S.T) (u : Fin S.N → F) {x : A} (hx : x ∈ S.V j) :
    S.mul u x ∈ S.V (j + 1) := by
  have key : ∀ m ∈ S.M j, ∀ u : Fin S.N → F, S.mul u (m : A) ∈ S.V (j + 1) := by
    intro m hm u
    have hu : u ∈ Submodule.span F (Set.range S.w.col) := hS.lat.spans ▸ Submodule.mem_top
    let L : (Fin S.N → F) →ₗ[F] A := (LinearMap.applyₗ (m : A)) ∘ₗ S.mul
    have hle : Submodule.span F (Set.range S.w.col) ≤ (S.V (j + 1)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, -, hg⟩ := hS.stable j hj k m hm
      show L (S.w.col k) ∈ S.V (j + 1)
      simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.applyₗ_apply_apply]
      rw [← hg]
      exact g.2
    exact hle hu
  let P : Submodule F (S.V j) := (S.V (j + 1)).comap (S.mul u ∘ₗ (S.V j).subtype)
  have hP : Submodule.span F (S.M j : Set (S.V j)) ≤ P := by
    rw [Submodule.span_le]
    intro m hm
    exact key m hm u
  have hx' : (⟨x, hx⟩ : S.V j) ∈ Submodule.span F (S.M j : Set (S.V j)) :=
    (hS.full j hj.le).span ▸ Submodule.mem_top
  exact hP hx'

theorem word_mem (S : Sys F A) (hS : S.Hyp) (j t : ℕ) (hjt : j + t ≤ S.T) :
    (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧
      ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  induction t with
  | zero =>
    refine ⟨fun u x hx => ?_, fun e x hx => ⟨x, hx, ?_⟩⟩
    · simpa [word_zero] using hx
    · simp [word_zero]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : j + t < S.T := by omega
    refine ⟨fun u x hx => ?_, fun e x hx => ?_⟩
    · rw [word_succ, Module.End.mul_apply]
      exact mul_mem_V_succ S hS hlt (u 0) (ih1 (fun i => u i.succ) x hx)
    · obtain ⟨g', hg', hg'e⟩ := ih2 (fun i => e i.succ) x hx
      obtain ⟨g, hg, hge⟩ := hS.stable (j + t) hlt (e 0) g' hg'
      refine ⟨g, hg, ?_⟩
      rw [word_succ, Module.End.mul_apply, hge, hg'e]

end GlobalTheory.HSShort.Sys

namespace GlobalTheory.HSShort

theorem wordMem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x :=
  fun _ _ _ _ _ _ _ _ S hS j t hjt => S.word_mem hS j t hjt

end GlobalTheory.HSShort
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLattiStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (j t : ℕ), j + t ≤ S.T → (∀ (u : Fin t → Fin S.N → F), ∀ x ∈ S.V j, word S.mul u x ∈ S.V (j + t)) ∧ ∀ (e : Fin t → Fin S.n), ∀ x ∈ S.M j, ∃ g ∈ S.M (j + t), (g : A) = word S.mul (fun i => S.w.col (e i)) x := by
  first | exact @GlobalTheory.HSShort.wordMem | exact GlobalTheory.HSShort.wordMem | (intros; apply GlobalTheory.HSShort.wordMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem hasSignature_of_hasSig_conj {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (M.map (starRingEnd ℂ)) r s) : Formalism.UG.HasSignature M r s := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  let P : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := A.submatrix e.symm id
  have h2 := congrArg (fun X => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.fromBlocks_map] at h2
  have hc : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => Complex.conj_conj z
  have hc' : (starRingEnd ℂ) ∘ (star : ℂ → ℂ) = id := funext fun z => Complex.conj_conj z
  simp only [hc, hc', Matrix.map_id] at h2
  have key : (A.map (starRingEnd ℂ))ᵀ * M * A = Formalism.UG.Jpq r s := by
    rw [Formalism.UG.Jpq, h2]
    congr 1
    · ext a b; simp [Matrix.one_apply]
    · ext a b; simp
    · ext a b; simp
    · ext a b; simp [Matrix.one_apply]
  have key2 : Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M * P = Formalism.UG.Jpq r s := by
    rw [← key, Formalism.UG.cT, Matrix.reindex_apply]
    have hm : (A.submatrix e.symm id).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ)).submatrix e.symm id := rfl
    simp only [P, hm, Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hinv : (Formalism.UG.Jpq r s * (Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M)) * P = 1 := by
    rw [Matrix.mul_assoc, key2, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    simp
  exact ⟨e, ⟨P, _, mul_eq_one_comm.mp hinv, hinv⟩, key2⟩

theorem squareTriple_sig_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, -⟩ := hT.of_forall hM
  refine ⟨Γ.p, ?_, ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ, hτ, -⟩ := h.cart w
    refine ⟨τ, hasSignature_of_hasSig_conj ?_⟩
    have hs := hTr.geo.hV.sig w
    rw [h.JW, one_smul] at hs
    have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ).map (starRingEnd ℂ) := by
      ext a b; simp [gramAt, hτ]
    rw [hmap] at hs
    exact hs
  · have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hb := hTr.geo.eBig
    have hl := hTr.geo.lt
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁] at hc hb hl
    show (G.V (.grid (↑i) (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank < _
    omega

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank | exact GlobalTheory.FunObj.squareTriple_sig_rank | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.RegSmooth

theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top,
    ← Module.finrank_eq_spanFinrank_of_free]
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R))
    (Submodule.topEquiv (R := R) (M := M))).finrank_eq

theorem spanFinrank_top_tensor_eq {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    (⊤ : Submodule B (B ⊗[A] N)).spanFinrank = (⊤ : Submodule A N).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B)
    (ResidueField B) N
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
    (ResidueField B) N
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

theorem spanFinrank_map_eq_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).spanFinrank = (⊤ : Submodule B (B ⊗[A] I)).spanFinrank := by
  let g : B ⊗[A] I →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  have hg : Function.Injective g := by
    have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    exact (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1
  have hr : Submodule.map g ⊤ = I.map (algebraMap A B) := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      induction x with
      | tmul b i =>
        have : g (b ⊗ₜ i) = b * algebraMap A B i := by
          simp [g, Algebra.smul_def, mul_comm]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩
      simp [g, Algebra.smul_def]
  rw [← hr, Submodule.spanFinrank_map_eq_of_injective g hg]

theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at e
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal h
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩
  have e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    rw [← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]
  rw [e, hd]
  exact ((isRegularLocalRing_iff B).mp inferInstance).le

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal' {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hf : φ.Flat)
    (h : (maximalIdeal A).map φ = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  algebraize [φ]
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have : algebraMap A B a ∈ maximalIdeal B := h ▸ Ideal.mem_map_of_mem _ hm
    exact (mem_maximalIdeal _).1 this ha
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal h

theorem isRegularLocalRing_of_isEtaleCompletion {A B : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (h : GlobalTheory.Toroidal.IsEtaleCompletion φ) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1

theorem smoothOfRelativeDimension_of_isRegularLocalRing {F : Type} [Field F] [PerfectField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] (n : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    X.affineOpenCover.openCover fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of F ⟶ R := Spec.preimage (x ≫ f)
  letI : Algebra F R := φ.hom.toAlgebra
  have hφ : x ≫ f = spMap (algebraMap F R) := (Spec.map_preimage (x ≫ f)).symm
  change SmoothOfRelativeDimension n (x ≫ f)
  rw [hφ]
  have hft : LocallyOfFiniteType (spMap (algebraMap F R)) := by rw [← hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType F R := RingHom.finiteType_algebraMap.mp hft
  refine GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_
  let y : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  have hcl : IsClosed ({x y} : Set X) := by
    have h1 : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
    have he := x.isOpenEmbedding
    have hlc := IsLocallyClosed.image h1.isLocallyClosed he.isInducing
      he.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  obtain ⟨h1, h2⟩ := h (x y) hcl
  let e := (asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

end GlobalTheory.RegSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.TieFrame

theorem one_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushPt h.1.w (1 : T ⟶ G') = 1 := mul_eq_left.1 (Over.OverMorphism.ext e)
  refine (congrArg Over.Hom.left e').trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  exact Category.assoc _ _ _

theorem exists_hom {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {A : Over (Sp K)} [GrpObj A]
    {φ : A.left ⟶ G.left} {φ' : A.left ⟶ G'.left} (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback A G (spMap (algebraMap V K)) φ) (hφ' : IsGrpPullback A G' (spMap (algebraMap V K)) φ') :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, h₁⟩ := grpPullback_iso hφ (isGrpPullback_pullback G _)
  obtain ⟨e', he', h₂⟩ := grpPullback_iso hφ' (isGrpPullback_pullback G' _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := HomExtExamples.homExtSt_holds V K G G' hG hG' (e.inv ≫ e'.hom) inferInstance
  have a : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G'.hom _ =
      pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
  refine ⟨F, hF, ?_⟩
  rw [← h₁, Category.assoc, ← a, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, h₂]

theorem dual_w {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pull {V O : Type} [CommRing V] [CommRing O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
    {f : V →+* O} {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) π) {u : epsOver V V ⟶ G} (hu : IsTan u) :
    ∃ x : LieG G', x.1.left ≫ π = spMap (dualMap f) ≫ u.left := by
  have w : (spMap (dualMap f) ≫ u.left) ≫ G.hom = spMap (algebraMap O (DualNumber O)) ≫ spMap f := by
    rw [Category.assoc, Over.w u, ← dual_w]
    rfl
  refine ⟨⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_⟩, h.1.lift_fst _ _ w⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine Eq.trans ?_ (one_comp h (specO O O)).symm
  change (spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ h.1.lift _ _ w) ≫ π = spMap (algebraMap O O) ≫ _
  have e : spMap (TrivSqZeroExt.fstHom O O O).toRingHom ≫ spMap (dualMap f) =
      spMap f ≫ spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
    rw [spMap_spMap, spMap_spMap]
    congr 1
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, h.1.lift_fst, ← Category.assoc, e, Category.assoc, hu, Hom.one_def, Over.comp_left,
    Over.toUnit_left]
  change spMap f ≫ spMap (algebraMap V V) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]

theorem exists_lieTie_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∃ x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt, ∀ τ j, LieTie P ψ (x τ j) (z.u τ j) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz
  letI := io.toAlgebra
  obtain ⟨hk, G, t', m₁, m₂, π, φ, hπ, -, hφ, h4, rfl, -⟩ := hP
  obtain ⟨G₀, t₀, n₁, n₂, ⟨ub, ht, -, -, hub⟩, -⟩ := y₀.2.2
  obtain ⟨e, he, h₁⟩ := grpPullback_iso n₁.cart m₁.cart
  have h₂ : IsGrpPullback t₀.G G.G (spMap (algebraMap T.V T.Fr)) (e.hom.left ≫ m₂.φ) :=
    ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl
  obtain ⟨F, hF, h₃⟩ := exists_hom G₀.semi G.semi n₂.cart h₂
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  suffices h : ∀ τ j, ∃ x : LieG P.Gt, LieTie P (φ ≫ m₁.φ) x (z.u τ j) by
    choose x hx using h
    exact ⟨x, hx⟩
  intro τ j
  obtain ⟨u', h5, h6⟩ := hub τ j
  have ht' : IsTan (ub τ j ≫ F) := by
    unfold IsTan
    rw [Over.comp_left, ← Category.assoc, ht τ j, ← Over.comp_left, MonObj.one_comp]
  obtain ⟨xG, hx⟩ := exists_pull hπ ht'
  have mem_pow {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd (n : ℕ) (x : DualNumber O) :
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hadic : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h : IsAdicComplete (Ideal.span {(p : O)}) O := inferInstance
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  obtain ⟨x, hc, -⟩ := existsUnique_left (P := P) hp hadic xG.1
  have h7 := hc.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h7
  have hu : (u' ≫ e.hom.left) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    haveI : Mono (spMap (algebraMap T.V T.Fr)) :=
      haveI : IsPreimmersion (spMap (algebraMap T.V T.Fr)) := IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
      inferInstance
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, Category.assoc, ← m₂.cart.1.w,
      ← Category.assoc e.hom.left, ← h₃, Category.assoc, Over.w F, ← Category.assoc, h6, Category.assoc,
      Over.w (ub τ j), ← dual_w]
    rfl
  have w : (spMap (dualMap k.toRingHom) ≫ u' ≫ e.hom.left) ≫ t'.G.hom =
      spMap (algebraMap C (DualNumber C)) ≫ spMap k.toRingHom := by
    rw [Category.assoc, hu, dual_w]
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique h7 Corr.one⟩, xG,
    Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w), hc, ?_, hπ.1.hom_ext ?_ ?_⟩
  · change hφ.1.lift _ _ w ≫ _ = _
    rw [hφ.1.lift_fst_assoc, hz.2.1, ← h5, Category.assoc, Category.assoc, h₁]
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, ← h4, hφ.1.lift_fst_assoc, Category.assoc, Category.assoc, ← h₃, ← Category.assoc u', h6,
      Category.assoc, Category.assoc, hx, ← Category.assoc, ← Category.assoc (spMap _) (spMap _), spMap_spMap,
      spMap_spMap, Over.comp_left]
    congr 2
    refine RingHom.ext fun s => TrivSqZeroExt.ext ?_ ?_
    · simpa [dualMap] using (hk s.fst).symm
    · simpa [dualMap, Algebra.algebraMap_eq_smul_one] using (hk s.snd).symm
  · change (hφ.1.lift _ _ w ≫ _) ≫ _ = _
    rw [Category.assoc, P.gen_pull.1.w, hφ.1.lift_snd_assoc, Category.assoc, Over.w xG.1]
    exact (dual_w _).symm

end GlobalTheory.CompHt.TieFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRep
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

noncomputable section

namespace GlobalTheory.DetInv

open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta (epsTate epsEquiv epsPairing toO pairingO bQuot Realizes)

section Group

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)

theorem pairing_dual_bidual (t : G.Tate) (u : G.dual.Tate) :
    pairing G.dual O u (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t u :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing]
    have h1 : charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
        WithConv.toConv (t.pt n).toLinearMap :=
      (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)
    rw [h1]
    exact (apply_charElem u n _).symm

end Group

end GlobalTheory.DetInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.RelDimOfDim

theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq :
    ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ),
      Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  intro F _ X _ q n hq hn
  have x₀ : X := Classical.arbitrary X
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected q x₀
  have h := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q d hd
  rw [hn] at h
  have hdn : d = n := by exact_mod_cast h.symm
  exact hdn ▸ hd

end GlobalTheory.RelDimOfDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ), Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  first | exact @GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | exact GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq | (intros; apply GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDegEqPowMulCard
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

end GlobalTheory.SemiAbelianTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := GlobalTheory.T.matrix_rank_normal_form k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGeStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_rank_ge : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  first | exact @GlobalTheory.isOpen_setOf_le_rank_localField | exact GlobalTheory.isOpen_setOf_le_rank_localField | (intros; apply GlobalTheory.isOpen_setOf_le_rank_localField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
open NumberField

noncomputable section

namespace GlobalTheory.TraceDual

def traceFormMap (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun Y X => -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i))
    (fun Y₁ Y₂ X => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])
    (fun Y X₁ X₂ => by simp [add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])

theorem traceFormMap_apply (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Y X : κ → mixedEmbedding.mixedSpace F) :
    traceFormMap F κ Y X = -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := rfl

theorem traceFormMap_injective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Injective (traceFormMap F κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h0 := LinearMap.congr_fun hY (fun i => GlobalTheory.VacLn.TrNondeg.conjM (Y i))
  rw [traceFormMap_apply, LinearMap.zero_apply] at h0
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (neg_eq_zero.1 h) hpi
    · exact h
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) := by
    intro i
    rw [GlobalTheory.VacLn.TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
  funext i
  exact GlobalTheory.VacLn.TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

theorem traceFormMap_surjective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Surjective (traceFormMap F κ) := by
  have h := Subspace.dual_finrank_eq (K := ℝ) (V := κ → mixedEmbedding.mixedSpace F)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).1
    (traceFormMap_injective F κ)

theorem exists_trace_rep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∃ Y : κ → mixedEmbedding.mixedSpace F,
      ∀ X, L X = -(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := by
  intro F _ _ κ _ L
  obtain ⟨Y, hY⟩ := traceFormMap_surjective F κ L.toLinearMap
  exact ⟨Y, fun X => by rw [← traceFormMap_apply, hY]; rfl⟩

end GlobalTheory.TraceDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruence
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hasPrinc_laws : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (U σ)) l.M := by
  intro D j H Dw l Xo c U dict h σ hσ k γ hγ hc
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hM : 3 ≤ l.M := l.three_le
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.levA hr k γ hγ hc
  obtain ⟨Kf, th, hrk, hK, hth, hD, hunit⟩ := h.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hunit⟩
  have h1 := GlobalTheory.PrincCore.root_eq_one (D.sp.W j) hrk hr (U σ).X (dict σ) (fun _ => (1 : ℂ)) Kf th hth hD
    hmu _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.LevGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruenceStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_arithmeticGroups_contain_congruence : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (U σ)) l.M := by
  first | exact @GlobalTheory.LevGeo.hasPrinc_laws | exact GlobalTheory.LevGeo.hasPrinc_laws | (intros; apply GlobalTheory.LevGeo.hasPrinc_laws <;> assumption)
end
end
