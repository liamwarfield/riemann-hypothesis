module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelForms
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finU_mul_infU_comm (k y : UA E n) (hk : k ∈ finU (E := E) (n := n)) (hy : y ∈ infU E n) : k * y = y * k := by
  have hk' : Matrix.GeneralLinearGroup.map (pInf E) (k : GA E n) = 1 := MonoidHom.mem_ker.1 hk
  have hy' : Matrix.GeneralLinearGroup.map (pFin E) (y : GA E n) = 1 := MonoidHom.mem_ker.1 hy
  apply Subtype.ext
  apply ga_ext
  · simp only [Subgroup.coe_mul, map_mul, hk', one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, hy', one_mul, mul_one]

def levelForms (L : Subgroup (finU (E := E) (n := n))) (C : Submodule ℂ (infU E n → ℂ)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
    ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, a1 γ hγ g, b1 γ hγ g]
    · simp only [Pi.add_apply, a2 k hk g, b2 k hk g]
    · exact C.add_mem (a3 g) (b3 g)
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => C.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨a1, a2, a3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, a1 γ hγ g]
    · simp only [Pi.smul_apply, a2 k hk g]
    · exact C.smul_mem c (a3 g)

end GlobalTheory.UnitaryBC

theorem GlobalTheory.UnitaryBC.finiteDimensional_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  intro E _ _ _ n hS L hL C _
  obtain ⟨S, hS⟩ := hS L hL
  let M := levelForms L C
  have hle : Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} ≤ M :=
    Submodule.span_le.2 fun ψ h => h

  have key : ∀ ψ ∈ M, ∀ g, ∃ s ∈ S, ∃ y ∈ infU E n, ψ g = ψ (s * y) := by
    rintro ψ ⟨h1, h2, -⟩ g
    obtain ⟨γ, hγ, s, hs, k, hk, y, hy, rfl⟩ := hS g
    refine ⟨s, hs, y, hy, ?_⟩
    rw [mul_assoc, mul_assoc, h1 γ hγ, finU_mul_infU_comm _ _ k.2 hy, ← mul_assoc, h2 k hk]
  let f : M →ₗ[ℂ] (S → C) :=
    { toFun := fun ψ s => ⟨fun y : infU E n => ψ.1 ((s : UA E n) * (y : UA E n)), ψ.2.2.2 s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext g
    obtain ⟨s, hs, y, hy, e⟩ := key (a.1 - b.1) (M.sub_mem a.2 b.2) g
    have := congrArg (fun F : S → C => ((F ⟨s, hs⟩ : C) : infU E n → ℂ) ⟨y, hy⟩) hab
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
    have e' : a.1 g - b.1 g = a.1 (s * y) - b.1 (s * y) := e
    rw [this, sub_self, sub_eq_zero] at e'
    exact e'
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective f hf
  exact Submodule.finiteDimensional_of_le hle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDefiniteUnitaryLevelFormsStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_definiteUnitary_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  first | exact @GlobalTheory.UnitaryBC.finiteDimensional_levelForms | exact GlobalTheory.UnitaryBC.finiteDimensional_levelForms | (intros; apply GlobalTheory.UnitaryBC.finiteDimensional_levelForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Small

theorem exists_under (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
      exact bot_le)
  refine ⟨⟨Q, hQ, fun h => v.ne_bot ?_⟩, HeightOneSpectrum.ext hQv⟩
  rw [← hQv, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem under_eq_of_conj {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

end GlobalTheory.RawLift.Small

namespace GlobalTheory.RawLift.Small

theorem norm_eq_rpow {z : ℂ} {L n : ℕ} (h : ‖z‖ ^ 2 * (L : ℝ) ^ n = 1) : ‖z‖ = (L : ℝ) ^ (-(n : ℝ) / 2) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hLn : (L : ℝ) ^ n ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  have h1 : ((L : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((L : ℝ) ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
      Real.rpow_neg hL, Real.rpow_natCast]
  have h2 : ‖z‖ ^ 2 = ((L : ℝ) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hL _) two_ne_zero).1 (h2.trans h1.symm)

theorem locSmall : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t → GoodMod R i t → IndexSum (Wc D i) (Vc D i).rank → LocSmall R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hB hG hI μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hsC⟩ := hI
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · exact Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => max_le (le_abs_self _) (abs_nonneg _)) hs.abs
  intro v f hf C hC hCd
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e f', IsPrimeIdem P e f' ∧ f' = f
  · obtain ⟨P, hP, e, f', hPI, rfl⟩ := hbad
    rw [Finset.sum_eq_zero fun g hg => by rw [hB μ 𝓕 hμ P hP e f' hPI g (hC g hg).1 (hC g hg).2, norm_zero]]
    exact le_max_right _ _
  push_neg at hbad
  obtain ⟨ε, hε, hfε⟩ := hf
  have hI0 := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)
  obtain ⟨P, hPv⟩ := exists_under D v
  obtain ⟨e, fP, hPI⟩ := hI0.2.1 P
  have hfP : fP = f := by
    rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv, hfε, GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε]
  subst hfP
  obtain ⟨c, hβ⟩ := hL.lev.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    obtain ⟨e', f', h'⟩ := hI0.2.1 PP
    have hne := hbad PP (Or.inl hPP') e' f' h'
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · subst h
      exact ((hI0.2.2.1 PP e fP hPI).2.2.2.1 e' f' h').2
    · rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem h' ((under_eq_of_conj h).trans hPv),
        GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv]
  obtain ⟨hJ, -, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ c) (R.datWp i R.triv) hβ).2 P e fP hPI hN hoff
  have hPI' := hI0.2.2.1 P e fP hPI
  obtain ⟨L, hL'⟩ := (hI0.1 fP hPI'.1 hPI'.2.1).1
  have hsupp : ∀ g ∈ C, ∀ g' ∈ C, SuppF (Wc D i) fP (g⁻¹ * g') := fun g hg g' hg' =>
    (hL' _).1 (L.mul_mem (L.inv_mem ((hL' g).2 (hC g hg).1)) ((hL' g').2 (hC g' hg').1))
  calc ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ = ∑ g ∈ C, (latIndex (Wc D i) g : ℝ) ^ (-((Vc D i).rank : ℝ) / 2) :=
        Finset.sum_congr rfl fun g hg => norm_eq_rpow (hG μ 𝓕 hμ v fP ⟨ε, hε, hfε⟩ hbad g (hC g hg).1)
    _ ≤ s v := hsC v fP ⟨ε, hε, hfε⟩ C (fun g hg => ⟨(hC g hg).1, fun hk => (hC g hg).2 ((hJ g (hC g hg).1).2 hk)⟩)
        fun g hg g' hg' hk => hCd g hg g' hg' ((hJ _ (hsupp g hg g' hg')).2 hk)
    _ ≤ max (s v) 0 := le_max_left _ _

end GlobalTheory.RawLift.Small

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7} (W : HSp D)

theorem exists_gqMat (γ : GQ W) : ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat c = mt W γ :=
  mem_ratMx.1 ((mem_GQ_iff W γ).1 γ.2)

def gqMat (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_gqMat W γ)

theorem rat_gqMat (γ : GQ W) : rat (gqMat W γ) = mt W γ := Classical.choose_spec (exists_gqMat W γ)

theorem gqMat_map (γ : GQ W) : (gqMat W γ).map (incA D) = mt W γ := rat_gqMat W γ

theorem gqMat_mul (γ δ : GQ W) : gqMat W (γ * δ) = gqMat W γ * gqMat W δ :=
  rat_injective (by rw [rat_mul, rat_gqMat, rat_gqMat, rat_gqMat]; rfl)

theorem gqMat_one : gqMat W 1 = 1 := rat_injective (by rw [rat_gqMat, rat_one]; rfl)

theorem gqMat_inv_mul (γ : GQ W) : gqMat W γ⁻¹ * gqMat W γ = 1 := by
  rw [← gqMat_mul, inv_mul_cancel, gqMat_one]

theorem gqMat_mul_inv (γ : GQ W) : gqMat W γ * gqMat W γ⁻¹ = 1 := by
  rw [← gqMat_mul, mul_inv_cancel, gqMat_one]

theorem gqMat_unitary (γ : GQ W) : (gqMat W γ)ᴴ * W.gram * gqMat W γ = W.gram := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_gqMat]
  exact mt_rel W γ

def actEquiv (γ : GQ W) :
    ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E] ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearEquiv.prodCongr
    (LinearEquiv.ofLinear (Matrix.toLin' (gqMat W γ)) (Matrix.toLin' (gqMat W γ⁻¹))
      (by rw [← Matrix.toLin'_mul, gqMat_mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, gqMat_inv_mul, Matrix.toLin'_one]))
    (LinearEquiv.refl _ _)

theorem actEquiv_apply (γ : GQ W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    actEquiv W γ y = (gqMat W γ *ᵥ y.1, y.2) := rfl

theorem isotropic_mulVec (γ : GQ W) (x x' : Fin W.rank → D.host.E) :
    star (gqMat W γ *ᵥ x) ⬝ᵥ W.gram *ᵥ (gqMat W γ *ᵥ x') = star x ⬝ᵥ W.gram *ᵥ x' := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, gqMat_unitary]

def lagAct (γ : GQ W) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _), by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [LinearEquiv.coe_coe, actEquiv_apply]
    rw [isotropic_mulVec]
    exact Y.2.2 y hy y' hy'⟩

theorem mem_lagAct (γ : GQ W) (Y : Lag W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    y ∈ (lagAct W γ Y).1 ↔ (gqMat W γ⁻¹ *ᵥ y.1, y.2) ∈ Y.1 := by
  show y ∈ Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem lagAct_one (Y : Lag W) : lagAct W 1 Y = Y := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, inv_one, gqMat_one, Matrix.one_mulVec]

theorem lagAct_mul (γ δ : GQ W) (Y : Lag W) : lagAct W (γ * δ) Y = lagAct W γ (lagAct W δ Y) := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, mem_lagAct, mem_lagAct, _root_.mul_inv_rev, gqMat_mul]
  simp only [Matrix.mulVec_mulVec]

theorem isLagFrame_lagAct (γ : GQ W) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    IsLagFrame W (lagAct W γ Y) (gqMat W γ * C.1, C.2) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (actEquiv W γ).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

abbrev NGLag (W : HSp D) : Type := {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}

theorem lagAct_ne_bot (γ : GQ W) (Y : Lag W) (h : Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥) :
    (lagAct W γ Y).1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 h
  refine (Submodule.ne_bot_iff _).2 ⟨gqMat W γ *ᵥ x, ?_, ?_⟩
  · rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lagAct, Matrix.mulVec_mulVec, gqMat_inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h0
    apply hx0
    have := congrArg (fun v => gqMat W γ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, gqMat_inv_mul] using this

def ngAct (γ : GQ W) (Y : NGLag W) : NGLag W := ⟨lagAct W γ Y.1, lagAct_ne_bot W γ Y.1 Y.2⟩

theorem ngAct_one (Y : NGLag W) : ngAct W 1 Y = Y := Subtype.ext (lagAct_one W Y.1)

theorem ngAct_mul (γ δ : GQ W) (Y : NGLag W) : ngAct W (γ * δ) Y = ngAct W γ (ngAct W δ Y) :=
  Subtype.ext (lagAct_mul W γ δ Y.1)

end GlobalTheory.RallisCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.CompIndep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_mem_map_of_prod {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* R) (A I : Ideal R) (m p : R) (hm : m ≠ 0)
    (h : A * A.map f = Ideal.span {m}) (h1 : A * I * (A * I).map f = Ideal.span {m * p}) :
    ∀ b ∈ A.map f, p * b ∈ (A * I).map f := by
  intro b hb
  have h0 : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  rw [Ideal.map_mul, ← Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm, h] at h1
  have h2 := mul_left_cancel₀ h0 h1
  have h3 : p ∈ I.map f := by
    have h4 := Ideal.mem_span_singleton_self p
    rw [← h2] at h4
    exact (Ideal.mul_le_inf h4).2
  rw [Ideal.map_mul, mul_comm p]
  exact Ideal.mul_mem_mul hb h3

theorem smul_pull {R : Type} [CommRing R] {n : ℕ} (κ : Matrix (Fin n) (Fin n) R) (M p : ℕ) (v y : Fin n → R)
    (e : κ *ᵥ (p • v) - p • v = (M * p) • y) : p • (κ *ᵥ v - v) = p • M • y := by
  rw [smul_sub, ← Matrix.mulVec_smul, e, mul_comm M p, mul_smul]

theorem ratio_mul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p) (hI : l₂.Mb = l.Mb * I) :
    ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), (p : 𝓞 E) * b ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 := l₂.prod
  rw [hI, hM, Nat.cast_mul] at h1
  rw [hI]
  refine mul_mem_map_of_prod _ _ _ _ _ (Nat.cast_ne_zero.2 ?_) l.prod h1
  have := l.three_le
  omega

theorem congr_of_marked {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (M p : ℕ) (hp : p ≠ 0)
    (J J₂ : Ideal (𝓞 D.host.E)) (hJ : ∀ b ∈ J, (p : 𝓞 D.host.E) * b ∈ J₂) (g g' k : GA D V)
    (hk : finHom V k = finHom V (g⁻¹ * g')) (hL : latG V g = latG V g')
    (x : La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hm : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g,
      x a - (finHom V g).1.mulVec (finVec V (ι a)) = (M * p) • w)
    (hm' : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g',
      x a - (finHom V g').1.mulVec (finVec V (ι a)) = (M * p) • w) :
    ∀ b ∈ J, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M J).2 fun v hv => ?_
  have hH : latGHat V g' = latGHat V g := by
    rw [GlobalTheory.RecDict.coset_latGHat, GlobalTheory.RecDict.coset_latGHat, hL]
  have hv' : v ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := by
    rw [Submodule.map_smul'', Submodule.map_top, hι.2]
    exact hv
  obtain ⟨a, ha, rfl⟩ := hv'
  have hpa : p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La) := by
    refine Submodule.smul_induction_on (p := fun a => p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La)) ha
      (fun b hb c _ => ?_) (fun s t hs ht => ?_)
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul]
      exact Submodule.smul_mem_smul (hJ b hb) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hs ht
  obtain ⟨w, hw, e⟩ := hm _ hpa
  obtain ⟨w', hw', e'⟩ := hm' _ hpa
  rw [hH] at hw'
  obtain ⟨y, hy, ey⟩ := GlobalTheory.RecDict.coset_fin (latGHat V 1) (latGHat V g) (finHom V g) (finHom V g') 1 (M * p)
    (fun u hu => ((GlobalTheory.MarkCoset.latG_spec D V g).2 u).1 hu) (fun u hu => by simpa using hu)
    (fun u hu => by simpa using hu) _ _ w w' 0 hw hw' (zero_mem _) e e' (by simp)
  refine ⟨y, hy, ?_⟩
  have hf : finVec V (ι (p • a)) = p • finVec V (ι a) := by
    rw [map_nsmul]
    exact AdLat.cap_fv_nsmul D.host.F p _
  rw [hf, one_mul, ← map_inv, ← map_mul, ← hk] at ey
  funext i
  exact GlobalTheory.MarkCoset.nsmul_cancel D.host.F p (Nat.cast_ne_zero.2 hp) (congrFun (smul_pull _ M p _ y ey) i)

theorem comp_eq_of_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  intro D T hT j hj σ hσ C hC h h' hh
  obtain ⟨⟨-, hM, -, hI, -⟩, -, -, -, -, hr, g, e, F, ik, φ, th, -, -, -, hd⟩ := hC
  obtain ⟨hr', -, -, -, -, -, -, hι, -⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr'', -, hQ, hK, ⟨x0, -, hR⟩, -⟩ := hT.dictU j hj σ hσ
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hd h
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hd h'
  rw [← hh] at hΛ' hm'
  have hinj : Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hL : latG (T.V j σ) (γ * h) = latG (T.V j σ) (γ' * h') :=
    SetLike.coe_injective (hinj.image_injective (hΛ.symm.trans hΛ'))
  obtain ⟨a, ha, k, hk, eak⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ * h)⁻¹ * (γ' * h'))
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hM, h0] at this
    omega
  have hk' : k ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k).2 ⟨hk, ?_⟩
    have hm₁ := hm
    have hm₂ := hm'
    rw [hM] at hm₁ hm₂
    exact congr_of_marked (T.V j σ) _ hι _ _ hp _ _ (ratio_mul_mem T.Q.l C.d.l₂ _ _ hM hI) (γ * h) (γ' * h') k
      (by rw [eak, map_mul, show finHom (T.V j σ) a = 1 from ha, one_mul]) hL _ hm₁ hm₂
  have q : ∀ δ ∈ GQ (T.V j σ), ∀ u, (T.dict j σ (δ * u)).1 = (T.dict j σ u).1 := fun δ hδ u => by
    obtain ⟨_, -, e⟩ := hQ δ hδ u
    rw [e]
  have q₁ : (T.dict j σ (γ * h * a * k)).1 = (T.dict j σ (γ * h * a)).1 := by
    obtain ⟨_, -, e⟩ := hK k hk' (γ * h * a)
    rw [e]
  have q₂ : (T.dict j σ (γ * h * a)).1 = (T.dict j σ (γ * h)).1 := by
    obtain ⟨_, -, e⟩ := hR (γ * h) a ha
    rw [e]
  rw [← q γ hγ h, ← q γ' hγ' h', ← q₂, ← q₁, mul_assoc (γ * h), ← eak, mul_inv_cancel_left]

end GlobalTheory.CoverRead.CompIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverComponentEqImpliesBaseComponentEqStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_component_eq_implies_base_component_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  first | exact @GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | exact GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover | (intros; apply GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmGL.EvalInj

private theorem eq_zero_of_sum_intertwining_apply_eq_zero {H X Y : Type} [Group H] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X)
    (ρ : Representation ℂ H Y) (hρ : ρ.IsIrreducible)
    (hschur : ∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) :
    ∀ (m : ℕ) (φ : Fin m → (Y →ₗ[ℂ] X)), LinearIndependent ℂ φ →
      (∀ i g v, φ i (ρ g v) = τ g (φ i v)) → ∀ y : Fin m → Y, ∑ i, φ i (y i) = 0 → y = 0 := by
  intro m
  induction m with
  | zero => intro φ _ _ y _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hli hφ y hy
    let Φ : (Fin (m + 1) → Y) →ₗ[ℂ] X := ∑ i, (φ i).comp (LinearMap.proj i)
    have hΦ : ∀ w, Φ w = ∑ i, φ i (w i) := fun w => by simp [Φ]
    let S := LinearMap.ker Φ
    have hSinv : ∀ g, ∀ w ∈ S, (fun i => ρ g (w i)) ∈ S := by
      intro g w hw
      rw [LinearMap.mem_ker, hΦ] at hw ⊢
      simp_rw [hφ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hw, map_zero]
    let p : S →ₗ[ℂ] Y := (LinearMap.proj (Fin.last m)).comp S.subtype
    have hp : Function.Injective p := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hw0 : (w : Fin (m + 1) → Y) (Fin.last m) = 0 := hw
      have hsum : ∑ i : Fin m, φ (Fin.castSucc i) ((w : Fin (m + 1) → Y) (Fin.castSucc i)) = 0 := by
        have hw' := w.2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc, hw0, map_zero, add_zero] at hw'
        exact hw'
      have hzero := ih (fun i => φ (Fin.castSucc i)) (hli.comp _ (Fin.castSucc_injective m))
        (fun i => hφ _) _ hsum
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hw0
      · exact congrFun hzero j
    let R : Subrepresentation ρ := ⟨LinearMap.range p, by
      rintro g _ ⟨w, rfl⟩
      exact ⟨⟨fun i => ρ g ((w : Fin (m + 1) → Y) i), hSinv g w w.2⟩, rfl⟩⟩
    have hyS : y ∈ S := by rw [LinearMap.mem_ker, hΦ]; exact hy
    haveI := hρ
    rcases IsSimpleOrder.eq_bot_or_eq_top R with hR | hR
    · have hrange : LinearMap.range p = ⊥ := congrArg Subrepresentation.toSubmodule hR
      have hpy : p ⟨y, hyS⟩ = 0 := by
        rw [LinearMap.range_eq_bot] at hrange
        rw [hrange]
        rfl
      exact congrArg Subtype.val (hp (hpy.trans (map_zero p).symm))
    · exfalso
      have hrange : LinearMap.range p = ⊤ := congrArg Subrepresentation.toSubmodule hR
      let e := LinearEquiv.ofBijective p ⟨hp, LinearMap.range_eq_top.mp hrange⟩
      have hlast : ∀ v, (e.symm v : Fin (m + 1) → Y) (Fin.last m) = v := fun v =>
        e.apply_symm_apply v
      have he : ∀ g v, e.symm (ρ g v) =
          ⟨fun i => ρ g ((e.symm v : Fin (m + 1) → Y) i), hSinv g _ (e.symm v).2⟩ := by
        intro g v
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        show ρ g v = ρ g ((e.symm v : Fin (m + 1) → Y) (Fin.last m))
        rw [hlast]
      let T : Fin m → ρ.IntertwiningMap ρ := fun j =>
        ⟨(LinearMap.proj (Fin.castSucc j)).comp (S.subtype.comp e.symm.toLinearMap), by
          intro g
          ext v
          simp [he]⟩
      choose c hc using fun j => hschur (T j)
      have hT : ∀ j v, (e.symm v : Fin (m + 1) → Y) (Fin.castSucc j) = c j • v := fun j v => hc j v
      have hzero : ∑ i, (Fin.snoc (α := fun _ => ℂ) c 1 i) • φ i = 0 := by
        ext v
        have hv := (e.symm v).2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc] at hv
        simp only [hT, hlast, map_smul] at hv
        simpa [Fin.sum_univ_castSucc] using hv
      have h1 := (Fintype.linearIndependent_iff.mp hli) _ hzero (Fin.last m)
      simp at h1

theorem _root_.GlobalTheory.SmGL.EvalInj.lift_subtype_injective :
    ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible →
      (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) →
      ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) →
      Function.Injective (TensorProduct.lift M.subtype) := by
  intro H X Y _ _ _ _ _ τ ρ hρ hschur M hM
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨M', hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {t} (Set.finite_singleton t)
  obtain ⟨t₀, rfl⟩ := hsub (Set.mem_singleton t)
  haveI := hfin
  let b := Module.finBasis ℂ M'
  set y : Fin (Module.finrank ℂ M') → Y := fun i => TensorProduct.equivFinsuppOfBasisLeft b t₀ i
    with hy
  have ht₀ : t₀ = ∑ i, b i ⊗ₜ[ℂ] y i := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t₀]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
    intro i
    exact TensorProduct.tmul_zero _ _
  let φ : Fin (Module.finrank ℂ M') → (Y →ₗ[ℂ] X) := fun i => ((b i : M) : Y →ₗ[ℂ] X)
  have hli : LinearIndependent ℂ φ :=
    (b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)).map' M.subtype
      (Submodule.ker_subtype _)
  have hsum : ∑ i, φ i (y i) = 0 := by
    rw [ht₀] at ht
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, φ] using ht
  have hy0 := eq_zero_of_sum_intertwining_apply_eq_zero τ ρ hρ hschur _ φ hli
    (fun i g v => hM _ (b i : M).2 g v) y hsum
  rw [ht₀, hy0]
  simp

end GlobalTheory.SmGL.EvalInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible : ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible → (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) → ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) → Function.Injective (TensorProduct.lift M.subtype) := by
  first | exact @GlobalTheory.SmGL.EvalInj.lift_subtype_injective | exact GlobalTheory.SmGL.EvalInj.lift_subtype_injective | (intros; apply GlobalTheory.SmGL.EvalInj.lift_subtype_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNe
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem nontrivial_of_simpleRep {Γ : Type} [Group Γ] [Fintype Γ] (V : FDRep ℂ Γ) (h : Simple V) :
    Nontrivial V := by
  rw [FDRep.simple_iff_char_is_norm_one] at h
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h0 : ∀ g, V.character g = 0 := fun g => by
    rw [FDRep.character, Subsingleton.elim (V.ρ g) 0, map_zero]
  simp only [h0, mul_zero, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card Γ : ℂ) ≠ 0) h.symm

theorem invariant_eq_bot_or_top_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ)
    [Simple τ] (U : Submodule ℂ τ) (hU : ∀ g, ∀ x ∈ U, τ.ρ g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let A : Subrepresentation τ.ρ := ⟨U, fun g v hv => hU g v hv⟩
  let X : FDRep ℂ Γ := FDRep.of A.toRepresentation
  let i : X ⟶ τ := ⟨InducedCategory.homMk (ModuleCat.ofHom U.subtype), fun g => by
    ext1; ext x; rfl⟩
  have hinj : Function.Injective ⇑(ConcreteCategory.hom i) := by
    intro x y h; exact Subtype.ext h
  have : Mono i := ConcreteCategory.mono_of_injective i hinj
  by_cases h0 : i = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := congrArg (fun f : X ⟶ τ => ConcreteCategory.hom f ⟨x, hx⟩) h0
    have h1 : ConcreteCategory.hom i ⟨x, hx⟩ = x := rfl
    have h2 : ConcreteCategory.hom (0 : X ⟶ τ) ⟨x, hx⟩ = 0 := rfl
    simp only [h1, h2] at this
    exact this
  · right
    have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 h0
    apply Submodule.eq_top_of_finrank_eq
    exact (FDRep.isoToLinearEquiv (asIso i)).finrank_eq

theorem zIdem_eq_of_linearEquiv {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) : zIdem τ = zIdem τ' := by
  apply MonoidAlgebra.ext
  ext γ
  rw [zIdem_coeff, zIdem_coeff, φ.finrank_eq]
  have h : τ'.ρ γ⁻¹ = φ.conj (τ.ρ γ⁻¹) := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp [hφ]
  rw [h, LinearMap.trace_conj']

theorem zIdem_eq_centralIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ),
    Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  intro Γ _ _ τ τ' hτ hτ' hne
  haveI := nontrivial_of_simpleRep τ hτ
  haveI := nontrivial_of_simpleRep τ' hτ'
  rw [zIdem_eq_centralIdem, zIdem_eq_centralIdem]
  exact Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_orthogonal Γ τ τ' τ.ρ τ'.ρ
    (invariant_eq_bot_or_top_of_simple τ) (invariant_eq_bot_or_top_of_simple τ')
    (by rintro ⟨φ, hφ⟩; exact hne (zIdem_eq_of_linearEquiv τ τ' φ hφ))

end GlobalTheory.SerOSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentMulEqZeroOfNeStatement
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ ≠ zIdem τ' → zIdem τ * zIdem τ' = 0 := by
  first | exact @GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | exact GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne | (intros; apply GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne <;> assumption)
end
end

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h

theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne

theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntLowMul
namespace GlobalTheory.LowerIntegralMul

theorem intLow_mul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (Mp : Formalism.MainNotions.S.Loc.Model F E) {n : ℕ}
    {l l' : Matrix (Fin n) (Fin n) E} (hl : Formalism.MainNotions.S.TieN.IntLow Mp l) (hl' : Formalism.MainNotions.S.TieN.IntLow Mp l') :
    Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  unfold Formalism.MainNotions.S.TieN.IntLow at *
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [h2' c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge a c with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (h3 a c) (h3' c b)

end GlobalTheory.LowerIntegralMul
end
