module

public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedTheta

variable {l : ℕ} [Fact l.Prime]


open Classical in
def thetaExt (x : Per.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x then Per.θD l h.choose else 0

theorem thetaExt_alg (y : Per.BdRp l) :
    thetaExt (algebraMap (Per.BdRp l) (Per.BdR l) y) = Per.θD l y := by
  have h : ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z =
      algebraMap (Per.BdRp l) (Per.BdR l) y := ⟨y, rfl⟩
  rw [thetaExt, dite_eq_left h, (BdRField.bdR_isField l).2.1 h.choose_spec]

theorem exists_of_mem_FilD_zero {x : Per.BdR l} (hx : x ∈ Per.FilD l 0) :
    ∃ y : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨e, he⟩ := FilLaws.exists_isEps l
  obtain ⟨y, hy⟩ := (mem_FilD_iff_xi_pow l e he 0 x).1 hx
  exact ⟨y, by simpa using hy⟩

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (c : ℂ_[l]) :
    AI.actC g c = Per.σC g c := by
  have h1 : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  have h2 : Continuous (Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction c using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem norm_untilt_sub (x : Per.Fl l) (y : Per.OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    ‖((x.untilt : Per.OC l) : ℂ_[l]) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h
  have h1 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
  rw [pow_one] at h1
  exact h1

theorem nonempty_thetaL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  intro l _ P AI T
  have hex : ∀ x ∈ (P.PD (MainNotions.LocalSituation.botExt l)).Fil 0,
      ∃ y : Per.BdRp l, T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun x hx => exists_of_mem_FilD_zero ((T.fil _ _ _).1 hx)
  have hU := TiedUnif.tied_uniformiser l P AI T
  refine ⟨{
    θ := fun x => thetaExt (T.eD x)
    θ_one := ?_
    θ_add := fun x hx y hy => ?_
    θ_mul := fun x hx y hy => ?_
    θ_onto := fun c => ?_
    θ_ker := fun x hx => ?_
    θ_act := fun g x hx => ?_
    θ_Om := fun x => ?_
    θ_int := fun a => ?_
    θ_teich := fun x y h => ?_
    fil_succ_iff_mul_t := hU.2.2 _
    t_μ := hU.1 _ }⟩
  · rw [map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), thetaExt_alg, map_one]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_add (f := _), hu, hv, ← map_add (f := _), thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add (f := _)]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
  · obtain ⟨y, rfl⟩ := (thetaD_props l).1 c
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y), ?_, ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact TiedUnif.alg_mem_FilD_zero y
    · rw [RingEquiv.apply_symm_apply, thetaExt_alg]
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.fil, hu, thetaExt_alg, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.actD, hu, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, thetaExt_alg, thetaExt_alg,
      (thetaD_props l).2.2.2.2, actC_eq]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    rw [hy, thetaExt_alg, hθ]
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1,
      WittVector.fontaineTheta_teichmuller]
    exact norm_untilt_sub x y h

end GlobalTheory.MemLoc.TiedTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriodStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  first | exact @GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | exact GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | (intros; apply GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdNormEmbeddingsEqAbsNorm
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem prod_norm_embeddings_eq_abs_norm (E : Type) [Field E] [NumberField E] (γ : E) :
    ∏ φ : E →+* ℂ, ‖φ γ‖ = |((Algebra.norm ℚ γ : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ γ
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖)
    (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  simp

theorem norm_typeNorm_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (γ : E) (σ : K →+* ℂ), ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ n := by
  intro E _ _ _ _ r n hr K _ hK γ σ
  let s : (E →+* ℂ) → (E →+* ℂ) := fun τ => σ.comp (τ.codRestrict K (hK τ))
  have hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩ := fun _ _ => rfl
  have hinj : Function.Injective s := by
    intro a b hab
    ext x
    have := DFunLike.congr_fun hab x
    rw [hs, hs] at this
    exact congrArg Subtype.val (σ.injective this)
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  have hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖ := by
    intro τ
    have h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ) := by
      rw [hs, hs]
      congr 2
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have hinv : Function.Involutive
      (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ) := fun τ => star_star τ
  have hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ := by
    rw [map_prod, norm_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, norm_pow, hs]
  have hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ
      = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ) := by
    rw [← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hconj]
  rw [hP, sq]
  nth_rewrite 2 [hQ]
  rw [← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm,
    ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← pow_add, hr]

end GlobalTheory.Mem
end

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory.Mem

theorem span_image_eq_coeSubmodule_map {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, x = f (a : E)} =
      IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f)) := by
  rw [Ideal.map, IsLocalization.coeSubmodule_span, Set.image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

noncomputable def extendIdealHom {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) : Ideal (𝓞 E) →* Submodule (𝓞 K) K where
  toFun 𝔞 := IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f))
  map_one' := by
    rw [Ideal.one_eq_top, Ideal.map_top, IsLocalization.coeSubmodule_top]
  map_mul' a b := by rw [Ideal.map_mul, IsLocalization.coeSubmodule_mul]

theorem extendIdealHom_span {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (a : 𝓞 E) :
    extendIdealHom f (Ideal.span {a}) = Submodule.span (𝓞 K) {f (a : E)} := by
  show IsLocalization.coeSubmodule K ((Ideal.span {a}).map (RingOfIntegers.mapRingHom f)) = _
  rw [Ideal.map_span, IsLocalization.coeSubmodule_span, Set.image_singleton, Set.image_singleton]
  rfl

theorem extendIdealHom_fg {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) : (extendIdealHom f 𝔞).FG :=
  Submodule.FG.map _ (IsNoetherian.noetherian _)

theorem span_singleton_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (x : ι → K) (r : ι → ℕ) :
    ∏ i ∈ s, Submodule.span R {x i} ^ r i = Submodule.span R {∏ i ∈ s, x i ^ r i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.one_eq_span]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Submodule.span_pow, Set.singleton_pow,
      Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem fg_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (I : ι → Submodule R K) (r : ι → ℕ) (h : ∀ i, (I i).FG) :
    (∏ i ∈ s, I i ^ r i).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

theorem exists_rep_pow_classNumber (E : Type) [Field E] [NumberField E] (c : ClassGroup (𝓞 E)) :
    ∃ (𝔠 : (Ideal (𝓞 E))⁰) (γ : 𝓞 E), ClassGroup.mk0 𝔠 = c ∧ γ ≠ 0 ∧
      (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := by
  obtain ⟨𝔠, h𝔠⟩ := ClassGroup.mk0_surjective c
  have h1 : ClassGroup.mk0 (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))).2).1 h1
  obtain ⟨γ, hγ⟩ := h2
  have hγ' : (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := hγ
  refine ⟨𝔠, γ, h𝔠, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ (nonZeroDivisors.ne_zero 𝔠.2) hγ'

theorem exists_finset_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (∀ z ∈ S, z ∈ K) → (∀ (τ : E →+* ℂ) x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : 0 < h := Fintype.card_pos
  choose 𝔠 γ h𝔠 hγ0 hγ using exists_rep_pow_classNumber E
  have hex : ∀ c, ∃ z : ℂ, z ^ h = ∏ τ : E →+* ℂ, τ (γ c : E) ^ r τ := fun c =>
    IsAlgClosed.exists_pow_nat_eq _ hpos
  choose b hb using hex
  refine ⟨Finset.univ.image b, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
    refine IsAlgebraic.of_pow hpos ?_
    rw [hb]
    refine IsIntegral.isAlgebraic (IsIntegral.prod _ fun τ _ => IsIntegral.pow ?_ _)
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (γ c : E)).map τ.toRatAlgHom
  intro K _ hS hK 𝔞 h𝔞
  have : NumberField K := NumberField.mk
  let f : (E →+* ℂ) → (E →+* K) := fun τ => τ.codRestrict K (hK τ)
  let N : 𝓞 E → K := fun a => ∏ τ : E →+* ℂ, f τ (a : E) ^ r τ
  have hN0 : ∀ a, a ≠ 0 → N a ≠ 0 := fun a ha =>
    Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by
      rw [map_ne_zero]; exact_mod_cast ha)
  have hNabs : ∀ (a : 𝓞 E) (σ : K →+* ℂ),
      ‖σ (N a)‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) ^ n := by
    intro a σ
    have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this
  let Φ : Ideal (𝓞 E) → Submodule (𝓞 K) K := fun I => ∏ τ : E →+* ℂ, extendIdealHom (f τ) I ^ r τ
  have hΦmul : ∀ I J, Φ (I * J) = Φ I * Φ J := by
    intro I J
    simp only [Φ, map_mul, mul_pow, Finset.prod_mul_distrib]
  have hΦpow : ∀ I, Φ (I ^ h) = Φ I ^ h := by
    intro I
    simp only [Φ, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]
  have hΦspan : ∀ a, Φ (Ideal.span {a}) = Submodule.span (𝓞 K) {N a} := by
    intro a
    simp only [Φ, N, extendIdealHom_span, span_singleton_prod_pow]
  have hgoal : ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ
      = Φ 𝔞 := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (f τ) 𝔞)
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
    rfl
  rw [hgoal]
  let 𝔞' : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  set c := ClassGroup.mk0 𝔞' with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hc.symm.trans (h𝔠 c).symm)
  have hxy' : Ideal.span {x} * 𝔞 = Ideal.span {y} * (𝔠 c : Ideal (𝓞 E)) := hxy
  let βc : K := ⟨b c, hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  have hβc : βc ^ h = N (γ c) := by
    apply Subtype.ext
    simp only [βc, N, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβc0 : βc ≠ 0 := by
    intro h0
    rw [h0, zero_pow hpos.ne'] at hβc
    exact hN0 _ (hγ0 c) hβc.symm
  have hΦc : Φ (𝔠 c) = Submodule.span (𝓞 K) {βc} := by
    refine GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ βc h hpos hβc0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_
    rw [← hΦpow, hγ, hΦspan, hβc]
  have hcabs : ∀ σ : K →+* ℂ, ‖σ βc‖ ^ 2 = (Ideal.absNorm (𝔠 c : Ideal (𝓞 E)) : ℝ) ^ n := by
    intro σ
    have := hNabs (γ c) σ
    rw [← hγ, ← hβc, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 this
  refine ⟨(N x)⁻¹ * (N y * βc), mul_ne_zero (inv_ne_zero (hN0 x hx)) (mul_ne_zero (hN0 y hy) hβc0),
    ?_, ?_⟩
  · have h1 := congrArg Φ hxy'
    rw [hΦmul, hΦmul, hΦspan, hΦspan, hΦc] at h1
    rw [← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span,
      ← Submodule.span_mul_span, ← h1, ← mul_assoc, Submodule.span_mul_span,
      Set.singleton_mul_singleton, inv_mul_cancel₀ (hN0 x hx), ← Submodule.one_eq_span, one_mul]
  · intro σ
    have h1 := congrArg (fun I => (Ideal.absNorm I : ℝ) ^ n) hxy'
    simp only [map_mul, Nat.cast_mul, mul_pow] at h1
    rw [← hNabs x σ, ← hNabs y σ, ← hcabs σ] at h1
    have h2 : ‖σ (N x)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hN0 x hx
    rw [map_mul, map_mul, map_inv₀, norm_mul, norm_mul, norm_inv, mul_pow, mul_pow, ← h1]
    field_simp

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonVEqZeroIffMemRangeCrisIncl
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem monV_eq_zero_iff_mem_range_crisIncl {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (x : V ⊗[ℚ_[l]] Bst P) : monV P LL V x = 0 ↔ ∃ y, crisIncl P LL V y = x := by
  have h : Function.Exact (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap (monSt P) := fun p =>
    (monSt_eq_zero_iff P p).trans ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  exact Module.Flat.lTensor_exact V h x

theorem mem_Dst_and_monV_eq_zero_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V ⊗[ℚ_[l]] Bst P), (x ∈ Dst P ρ ∧ monV P ↥LL.1 V x = 0) ↔ x ∈ (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) := by
  intro l _ P K LL V _ _ _ _ ρ x
  have key : ∀ y, crisIncl P ↥LL.1 V y ∈ Dst P ρ ↔ y ∈ Dcris (P.PD K) ρ := fun y => by
    rw [mem_Dst, Dcris, Submodule.mem_iInf]
    refine forall_congr' fun g => ?_
    rw [stRep_crisIncl, (crisIncl_injective P).eq_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  rw [monV_eq_zero_iff_mem_range_crisIncl, Submodule.mem_map]
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, (key y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(key y).mpr hy, y, rfl⟩

end GlobalTheory.Pst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_kur_of_actQ_fixed (K : FinExt l) (b : P.R.B) (hb : ∀ g ∈ GK K, P.actQ g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = b := by
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by rw [P.PD_actB]; exact hb g g.2
  exact ⟨_, hc⟩

theorem exists_kur_of_actSt_fixed (K : FinExt l)
    (hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (p : Bst P) (hp : ∀ g ∈ GK K, actSt P g p = p) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = p := by
  have hC : ∀ b : P.R.B, (∀ g ∈ GK K, actSt P g (C b) = C b) →
      ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = C b := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_kur_of_actQ_fixed P K b fun g hg =>
      C_injective (by rw [← actSt_C]; exact hb g hg)
    exact ⟨c, by rw [Polynomial.algebraMap_apply, hc]⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0] at hp ⊢
      exact hC _ hp
    · have hN : ∀ g ∈ GK K, actSt P g (monSt P p) = monSt P p := fun g hg => by
        rw [← monSt_actSt, hp g hg]
      obtain ⟨c, hc⟩ := ih (monSt P p).natDegree (by
        rw [monSt_apply, natDegree_neg, ← hn]; exact natDegree_derivative_lt h0) _ hN rfl
      rw [Polynomial.algebraMap_apply] at hc
      set a := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c with ha
      have hfa : ∀ g ∈ GK K, P.actQ g a = a := fun g hg =>
        C_injective (by rw [← actSt_C, hc]; exact hN g hg)
      obtain ⟨b, hb⟩ := (monSt_eq_zero_iff P (p + C a * X)).mp (by
        rw [map_add (f := _), ← hc]; simp)
      have hpb : p = C b - C a * X := by rw [← hb]; ring
      by_cases hc0 : c = 0
      · have : p = C b := by rw [hpb, ha, hc0]; simp
        rw [this] at hp ⊢
        exact hC _ hp
      · exfalso
        set a' := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c⁻¹ with ha'
        have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, inv_mul_cancel₀ hc0, map_one]
        refine hK (a' * b) fun g hg => ?_
        have h1 := hp g hg
        rw [hpb, map_sub, map_mul, actSt_C, actSt_C, actSt_X, hfa g hg] at h1
        have h2 : P.actQ g b - a * ((kummer P g : ℚ_[l]) • P.tB) = b :=
          C_injective (by rw [map_sub, map_mul]; linear_combination h1)
        have h3 : P.actQ g a' * a = 1 := by
          have := congrArg (P.actQ g) haa
          rwa [map_mul, map_one, hfa g hg] at this
        have h4 : P.actQ g a' = a' := by
          linear_combination a' * h3 - P.actQ g a' * haa
        rw [map_mul, h4]
        linear_combination a' * h2 + ((kummer P g : ℚ_[l]) • P.tB) * haa

end GlobalTheory.Pst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureMulVOfFinrankEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem semilinear_coord_fixed {F D ι : Type*} [Field F] [AddCommGroup D] [Module F D] [Fintype ι]
    {b : ι → D} (hb : LinearIndependent F b) (σ : F → F) (T : D →+ D)
    (hT : ∀ c x, T (c • x) = σ c • T x) (hTb : ∀ i, T (b i) = b i) (c : ι → F)
    (h : T (∑ i, c i • b i) = ∑ i, c i • b i) (i : ι) : σ (c i) = c i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [hT, hTb] at h
  exact Fintype.linearIndependent_iffₛ.mp hb _ _ h i

variable {l : ℕ} [Fact l.Prime]

theorem galois_mem_Kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨c, hc⟩ := c
  change g c ∈ MaximalUnramifiedExtension l
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, h0, hm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

theorem mem_of_GK_fixed {K : FinExt l} {x : Om l} (hx : ∀ g : ↥(GK K), (g : GQ l) x = x) : x ∈ K.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact fun g hg => hx ⟨g, hg⟩

theorem mulV_padic_smul (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, Algebra.smul_def q c, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc, ← Algebra.smul_def]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem mem_closure_mulV_of_finrank_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → ∀ S : Submodule ↥LL.1 (V ⊗[ℚ_[l]] Bst P), S ≤ Dst P ρ → (∀ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 → ∀ x ∈ S, mulV P ↥LL.1 V c x ∈ S) → finrank ↥LL.1 ↥S = finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V → ∀ x ∈ Dpst P ρ, x ∈ AddSubgroup.closure {y | ∃ (c : ↥(MaximalUnramifiedExtension l)) (s : V ⊗[ℚ_[l]] Bst P), s ∈ S ∧ y = mulV P ↥LL.1 V c s} := by
  intro l _ P K LL V _ _ _ _ _ ρ hV S hS _ hrk x hx
  haveI := LL.2
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  obtain ⟨hfin, hd⟩ := (isPst_iff P ρ).mp hV
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : S ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp (hS hs) g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ S}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ↥LL.1 V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : S.restrictScalars ℚ_[l] ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hS (hbS j.2)) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp (hS hs) g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    change finrank ℚ_[l] ↥S = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥S, hrk, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V]
    ring
  have h3 : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Fintype.card ↥b := by
    rw [hd]
    exact Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  have htop := hli.span_eq_top_of_card_eq_finrank' (le_antisymm hli.fintype_card_le_finrank h3)
  rw [Subtype.range_coe] at htop
  obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨x, hx⟩) (htop ▸ Submodule.mem_top)
  have h4 := congrArg val hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h4
  rw [← show _ = x from h4]
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, val i, hbS i.2, rfl⟩

end GlobalTheory.Pst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.LabConv

theorem isCuspOf_of_hasCuspLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  intro g _ L t ht hζ htL d V P hd hcusp hlab
  subst htL
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := hlab
  rw [Fintype.card_fin] at hdeg
  have hPl : GlobalTheory.GLq.IsPrimeLab d P := ⟨hm, hi, Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX, hdeg⟩
  refine ⟨hPl, hcusp, ?_⟩
  intro x hx y hy z hz
  have hd0 : 0 < d := hd
  have hcpl : GlobalTheory.GLq.IsPrimeLab d (y : GlobalTheory.GLq.Mt g d).charpoly := by
    refine ⟨Matrix.charpoly_monic _, hy, ?_, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩
    intro h0
    have hdet := Matrix.det_eq_sign_charpoly_coeff (y : GlobalTheory.GLq.Mt g d)
    rw [h0, mul_zero] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit y) |>.ne_zero hdet
  have hz1 : z ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hcpl hz
  have hx1 : x ^ (g ^ d - 1) = 1 := GlobalTheory.GLq.LabelUnique.pow_sub_one_eq_one hPl hx
  have hprim : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := by
    rw [← L.gen_order d hd0]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (g ^ d - 1) := ⟨by
    have := Nat.one_lt_pow hd0.ne' (Fact.out : g.Prime).one_lt
    omega⟩
  obtain ⟨m, -, hmz⟩ := hprim.eq_pow_of_pow_eq_one hz1
  have hax : aeval x P = 0 := GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem hm.ne_zero hx
  have haz : aeval z (y : GlobalTheory.GLq.Mt g d).charpoly = 0 :=
    GlobalTheory.GLq.LabelUnique.aeval_eq_zero_of_mem (Matrix.charpoly_monic _).ne_zero hz
  have hmz' : (Formalism.L2.NT.convC L.teich ht L.gen hζ).gen (Fintype.card (Fin d)) ^ m = z := by
    rw [Fintype.card_fin]; exact hmz
  have e := hval x hax y hy z haz m hmz'
  simp only [Fintype.card_fin, ZMod.card] at e
  have htx : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  show LinearMap.trace ℂ V (V.ρ y) = _
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hmz, ← pow_mul, GlobalTheory.GLq.LabelUnique.thetaOf_gen_pow L d hd0 x htx]
  rfl

end GlobalTheory.SerCmp.LabConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabelStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  first | exact @GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | exact GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | (intros; apply GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem exists_root_congr_unit : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal →
      ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ _ A P hA u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  set q := normV P with hq
  have hqc : q = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [hq, normV, Nat.card_eq_fintype_card]
  have hq1 : 1 < q := by rw [hqc]; exact Fintype.one_lt_card
  set n := q - 1 with hn
  have hn0 : 0 < n := by omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have h0 : (Ideal.Quotient.mk P.asIdeal u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ h0
    rwa [← hqc] at this
  have hlt : A.valuation (algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E)) < 1 := (hA _).mpr hmem
  set a : Ω := algebraMap E Ω (u : E) with ha
  have hcast : algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E) = a ^ n - 1 := by
    simp [ha]
  rw [hcast] at hlt

  set p : Polynomial Ω := Polynomial.X ^ n - Polynomial.C 1 with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn0.ne'
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmon
  have heval : a ^ n - 1 = (p.roots.map (fun ζ => a - ζ)).prod := by
    have := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Function.comp_def] at this
    rw [this]
  by_contra hcon
  push_neg at hcon
  have hall : ∀ ζ ∈ p.roots, 1 ≤ A.valuation (a - ζ) := by
    intro ζ hζ
    have hroot : ζ ^ n = 1 := by
      have := (Polynomial.mem_roots hmon.ne_zero).mp hζ
      simpa [hp, sub_eq_zero] using this
    rw [Valuation.map_sub_swap]
    exact hcon ζ hroot
  have : 1 ≤ A.valuation (a ^ n - 1) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    have key : ∀ s : Multiset Ω, (∀ ζ ∈ s, 1 ≤ A.valuation (a - ζ)) →
        1 ≤ (s.map (A.valuation ∘ fun ζ => a - ζ)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simp
      | cons b s ih =>
        intro h
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact one_le_mul (h b (Multiset.mem_cons_self b s))
          (ih fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ))
    exact key _ hall
  exact absurd hlt (not_lt.mpr this)

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlaceStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  first | exact @GlobalTheory.TameTau.exists_root_congr_unit | exact GlobalTheory.TameTau.exists_root_congr_unit | (intros; apply GlobalTheory.TameTau.exists_root_congr_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameRepConjugateInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
open scoped Pointwise

namespace GlobalTheory.TameTauConj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem conj_mem_Ine_of_mem_Ine_smul [IsAlgClosure E Ω] {A : ValuationSubring Ω} {g σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) (g • A)) : g⁻¹ * σ * g ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        AlgEquiv.smul_def]
      have : (g⁻¹ : G E Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (smul_valuation_lt_one_iff g A _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G E Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ : G E Ω) (g x) = x
      show (g⁻¹ * g) x = x
      simp
    rw [e] at h
    exact h

end GlobalTheory.TameTauConj


open GlobalTheory.TameTauConj in
theorem GlobalTheory.TameTauConj.tameRep_conj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A₀ : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A₀ P → ∀ (e : ℤ) (σ : G E Ω) (u : 𝓞 E), NX.TameRep P e σ u → ∃ ρ : G E Ω, ρ⁻¹ * σ * ρ ∈ Ine (F := E) A₀ ∧ ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ π ^ (normV P - 1) = algebraMap E Ω (ϖ : E) ∧ A₀.valuation ((ρ⁻¹ * σ * ρ) π / π - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ A₀ P hA₀ e σ u hT
  obtain ⟨A, hA, hσ, ϖ, π, h1, h2, h3, h4⟩ := hT
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  subst hρ
  refine ⟨ρ, conj_mem_Ine_of_mem_Ine_smul hσ, ϖ, (ρ⁻¹ : G E Ω) π, h1, h2, ?_, ?_⟩
  · rw [← map_pow, h3, AlgEquiv.commutes]
  · have e1 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) = (ρ⁻¹ : G E Ω) (σ π) := by
      show (ρ⁻¹ * σ * ρ * ρ⁻¹) π = (ρ⁻¹ * σ) π
      rw [show ρ⁻¹ * σ * ρ * ρ⁻¹ = ρ⁻¹ * σ by group]
    have e2 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) / (ρ⁻¹ : G E Ω) π - (algebraMap E Ω (u : E)) ^ e
        = (ρ⁻¹ : G E Ω) (σ π / π - (algebraMap E Ω (u : E)) ^ e) := by
      rw [e1, map_sub, map_div₀, map_zpow₀, AlgEquiv.commutes]
    rw [e2]
    exact (smul_valuation_lt_one_iff ρ A₀ _).1 h4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharacterIndependentUniformizer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem valuation_algebraMap_int_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) : A.valuation (algebraMap E Ω (x : E)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)

theorem valuation_uniformiser_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hP : IsPlaceOver A P) {ϖ ϖ' : 𝓞 E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal) :
    A.valuation (algebraMap E Ω (ϖ' : E)) ≤ A.valuation (algebraMap E Ω (ϖ : E)) := by
  have hdvd : P.asIdeal ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal := by
    intro hle
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  have hmem : ϖ' * s ∈ Ideal.span {ϖ} := by
    rw [hJ]; exact Ideal.mul_mem_mul h1' hsJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hs1 : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))
  have e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact_mod_cast ha
  have hv := congrArg A.valuation e
  rw [map_mul, map_mul, hs1, mul_one] at hv
  rw [← hv]
  calc A.valuation (algebraMap E Ω (a : E)) * A.valuation (algebraMap E Ω (ϖ : E))
      ≤ 1 * A.valuation (algebraMap E Ω (ϖ : E)) := by
        gcongr; exact valuation_algebraMap_int_le_one A a
    _ = A.valuation (algebraMap E Ω (ϖ : E)) := one_mul _

theorem tame_quot_indep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ ϖ' : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ (π π' : Ω), π ^ m = algebraMap E Ω (ϖ : E) → π' ^ m = algebraMap E Ω (ϖ' : E) → ∀ σ ∈ Ine (F := E) A, σ π / π = σ π' / π' := by
  intro E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ
  have hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0 := by
    intro x hx h0
    apply hx
    have hx0 : (x : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0
    have : x = 0 := by exact_mod_cast hx0
    rw [this]; exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])
  have hπ0' : π' ≠ 0 := by
    rintro rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])
  have hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E)) :=
    le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')
  set ρ := π' / π with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hπ0' hπ0
  have hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E)) := by
    rw [hρ, div_pow, hπ, hπ', map_div₀]
  have hvρm : A.valuation ρ ^ m = 1 := by
    rw [← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]
    simpa using hne ϖ' h2'
  have hvρ : A.valuation ρ = 1 := by
    rcases lt_trichotomy (A.valuation ρ) 1 with h | h | h
    · exact absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne
    · exact h
    · exact absurd hvρm (one_lt_pow₀ h hm0.ne').ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    apply (hP _).1
    simpa using h
  have hσρm : (σ ρ / ρ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]
    exact div_self (pow_ne_zero _ hρ0)
  have hclose : A.valuation (σ ρ / ρ - 1) < 1 := by
    have e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ := by field_simp
    rw [e, map_div₀, hvρ, div_one]
    exact hσ.2 ρ hvρ.le
  have hfix : σ ρ / ρ = 1 := root_eq_of_close A m hσρm (one_pow m) hmv hclose
  have hfix' : σ ρ = ρ := (div_eq_one_iff_eq hρ0).1 hfix
  have eπ' : π' = ρ * π := by rw [hρ]; field_simp
  rw [eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]

end GlobalTheory.TameTau
end
