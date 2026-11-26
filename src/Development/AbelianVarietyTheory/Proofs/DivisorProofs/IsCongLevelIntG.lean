module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)
open GlobalTheory.NormDict

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsScale (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Prop :=
  r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)

def coordY (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ) (r : D.host.E) (w : WO S T) :
    VC D a d :=
  fun τ i j => δ * embT D τ r * compAt θ τ w (Fin.cast hT.symm i) (Fin.cast hS.symm j)

def Reads (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) (G : VC D a d → ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
    f w = Complex.exp (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) (coordY θ hS hT δ r w) (coordY θ hS hT δ r w)) *
      G (coordY θ hS hT δ r w)

structure Setup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) :
    Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ
  scale : IsScale D cc r

def finPt {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z : Matrix (Fin d) (Fin a) D.host.E) :
    WO S T :=
  GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j)))

def IsFinIdl (x : (AE D)ˣ) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) = GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)

def HasFinPart (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) : Prop :=
  ∀ x y, IsFinIdl x y → ((χ x : Circle) : ℂ) = ((c.f y ^ e : ℂˣ) : ℂ)

def IsCongLevel {N : ℕ} (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D N)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ k ∈ intG D N, (∀ i j, ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    (((k : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j =
      (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s) → k ∈ J

def period (D : D7) (δ : ℂ) (r : D.host.E) (τ : D.what₂.Tau) : ℂ :=
  δ * embT D τ r / (Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℂ)

def normConst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (Real.pi / area (lamOf D cc δ)) ^ (a * n τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure IsStdFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  frame : IsFrame P Y
  ptA : ∀ x, GlobalTheory.BotFormula.IsFinPt Y.A (Y.ιA x) x
  ptB : ∀ h, GlobalTheory.BotFormula.IsFinPt Y.B (Y.ιB h) h

structure IsMaxLevel {P : Pair D cc δ t0 Q} (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D)))
    (μ₀ : Measure (GA D Y.B)) : Prop where
  lev : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B K₀
  mem_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ K₀ ↔ h ∈ intG D P.d
  meas : ∃ 𝓕, Links.IsMeasDef Y.B K₀ μ₀ 𝓕

structure IsExact (P : Pair D cc δ t0 Q) (X : Data P) (r : D.host.E) : Prop where
  std : IsStdFrame P X.toFrame
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  chA : HasFinPart X.χA P.W.chV P.W.ep
  chB : HasFinPart X.χB P.W.chV' (-P.W.ep')
  scale : IsScale D cc r
  read : Reads X.ψ X.θ X.rkA X.rkB cc δ r P.F X.vac
  const : X.c₁ = ∏ τ, period D δ r τ ^ (P.a * P.n τ)

theorem IsExact.setup {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E} (h : IsExact P X r) :
    Setup X.ψ X.θ X.A X.B cc δ r :=
  ⟨h.weil.std, h.inf, h.std.frame.gramA, h.std.frame.gramB, P.crv, h.scale⟩

theorem isCongLevel_intG (N : ℕ) : IsCongLevel (intG D N) := ⟨1, one_pos, fun _ hk _ => hk⟩

theorem isScale_one (D : D7) : IsScale D D.host.ccK 1 := by simp [IsScale]

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.ArchFourier

open scoped FourierTransform SchwartzMap

theorem exists_schwartz_fourier_form {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ ei : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ), Function.Bijective ei ∧ ∀ (f : 𝓢(V, ℂ)) (y : V),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) * (B x y : ℂ)) ∂μ := by
  let T := toEuclidean (E := V)
  obtain ⟨R, hR⟩ := GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, haI, -⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let CR := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R
  let CT := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm
  let CRi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R.symm
  let CTi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  let Fo := SchwartzMap.fourierTransformCLM ℂ (V := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) (E := ℂ)
  have h1 : ∀ g, CRi (CR g) = g := fun g => by ext x; simp [CRi, CR]
  have h2 : ∀ g, CR (CRi g) = g := fun g => by ext x; simp [CRi, CR]
  have h3 : ∀ g, CTi (CT g) = g := fun g => by ext x; simp [CTi, CT]
  have h4 : ∀ g, CT (CTi g) = g := fun g => by ext x; simp [CTi, CT]
  have h5 : ∀ g, 𝓕⁻ (Fo g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourierInv_fourier_eq g
  have h6 : ∀ g, Fo (𝓕⁻ g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourier_fourierInv_eq g
  refine ⟨(a : ℂ) • (CR.comp (Fo.comp CT)), ?_, fun f y => ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => (a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g)), fun f => ?_, fun g => ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, h1, h5, h3,
        FourierTransform.fourierInv_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
    · change (a : ℂ) • CR (Fo (CT ((a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g))))) = g
      rw [map_smul, map_smul, map_smul, h4, h6, h2, smul_smul, mul_inv_cancel₀ ha', one_smul]
  · have e1 : ((a : ℂ) • (CR.comp (Fo.comp CT))) f y = (a : ℂ) * 𝓕 (fun w => f (T.symm w)) (R y) := rfl
    rw [e1, Real.fourier_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring

end GlobalTheory.ArchFourier

namespace GlobalTheory.ArchFourier

noncomputable def traceDot (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y))
    (fun x x' y => by simp only [add_dotProduct, map_add (f := _)])
    (fun c x y => by simp only [smul_dotProduct, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [dotProduct_add, map_add (f := _)])
    (fun c x y => by simp only [dotProduct_smul, map_smul, smul_eq_mul])

theorem traceDot_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    traceDot F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) := rfl

theorem traceDot_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : traceDot F κ x y = traceDot F κ y x := by
  rw [traceDot_apply, traceDot_apply, dotProduct_comm]

theorem traceDot_nondeg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, traceDot F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [traceDot_apply, dotProduct_single] at this

theorem exists_fourier_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Bijective ei ∧ ∀ (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ := by
  intro F _ _ κ _ _ _ μ _
  classical
  exact exists_schwartz_fourier_form (traceDot F κ) traceDot_comm traceDot_nondeg μ

end GlobalTheory.ArchFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijectiveStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Bijective ei ∧ ∀ (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ := by
  first | exact @GlobalTheory.ArchFourier.exists_fourier_sInf | exact GlobalTheory.ArchFourier.exists_fourier_sInf | (intros; apply GlobalTheory.ArchFourier.exists_fourier_sInf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFraction
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem injective_ringHom_genericStalk_integralScheme (C : Scheme.{0}) [IsIntegral C] (q : C) (hq : q = genericPoint C)
    {A : Type} [CommRing A] [Nontrivial A] (φ : C.presheaf.stalk q →+* A) : Function.Injective φ := by
  subst hq
  exact RingHom.injective (φ : C.functionField →+* A)

theorem exists_fraction_genericStalk_germ_affineOpen (C : Scheme.{0}) [IsIntegral C] (V : C.Opens) (hV : IsAffineOpen V)
    (q : C) (hq : q = genericPoint C) (hqV : q ∈ V) (s : C.presheaf.stalk q) :
    ∃ a b : Γ(C, V), b ≠ 0 ∧ s * C.presheaf.germ V q hqV b = C.presheaf.germ V q hqV a := by
  subst hq
  haveI : Nonempty V := ⟨⟨_, hqV⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen (X := C) V hV
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (S := C.functionField) (nonZeroDivisors Γ(C, V)) s
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  have := IsLocalization.mk'_spec (S := C.functionField) a b
  rw [← hab]
  exact this

theorem germ_appLE_eq_stalkMap_germ_specField {K : Type} [Field K] (C : Scheme.{0}) (x : Sp K ⟶ C) (V : C.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (p : Sp K) (hp : x p ∈ V) (c : Γ(C, V)) :
    (Sp K).presheaf.germ ⊤ p (by simp) (x.appLE V ⊤ h c) = x.stalkMap p (C.presheaf.germ V (x p) hp c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
  simp

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isGen_evAt_frac : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x →
    ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧
      (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  intro K _ C _ x hx V hV
  haveI : IsDominant x := hx.1
  haveI : IsPreimmersion x := hx.2
  have hsub : ∀ p q : Sp K, p = q := fun p q => Subsingleton.elim (α := PrimeSpectrum K) p q
  have hgen : ∀ p : Sp K, x p = genericPoint C := by
    intro p
    apply ((genericPoint_spec C).eq _).symm
    rw [isGenericPoint_def]
    have hr : Set.range x = {x p} := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        rw [hsub q p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← hr]
    exact x.denseRange.closure_range
  have hmem : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have h : ⊤ ≤ x ⁻¹ᵁ V := by
    intro p _
    show x p ∈ V
    rw [hgen p]
    exact hmem
  obtain ⟨p⟩ : Nonempty (Sp K) := ⟨(⊥ : PrimeSpectrum K)⟩
  have hp : x p ∈ V := by rw [hgen p]; exact hmem
  refine ⟨h, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : x.appLE V ⊤ h c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of K)).inv.hom hc
      simpa [evAt] using this
    have h2 := germ_appLE_eq_stalkMap_germ_specField C x V h p hp c
    rw [h1, map_zero] at h2
    have h3 : C.presheaf.germ V (x p) hp c = 0 :=
      injective_ringHom_genericStalk_integralScheme C (x p) (hgen p) (x.stalkMap p).hom (by rw [← h2, map_zero])
    exact germ_injective_of_isIntegral (X := C) (x p) hp (by rw [h3, map_zero])
  · intro hA z
    obtain ⟨s, hs⟩ := x.stalkMap_surjective p
      ((Sp K).presheaf.germ ⊤ p (by simp) ((Scheme.ΓSpecIso (.of K)).inv.hom z))
    obtain ⟨a, b, hb, hab⟩ := exists_fraction_genericStalk_germ_affineOpen C V hA (x p) (hgen p) hp s
    refine ⟨a, b, hb, ?_⟩
    have e := congrArg (x.stalkMap p).hom hab
    rw [map_mul, hs, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← map_mul] at e
    have e2 := germ_injective_of_isIntegral (X := Sp K) p (by simp) e
    have e3 := congrArg (Scheme.ΓSpecIso (.of K)).hom.hom e2
    simpa [evAt] using e3

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFractionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x → ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧ (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  first | exact @GlobalTheory.Nef.isGen_evAt_frac | exact GlobalTheory.Nef.isGen_evAt_frac | (intros; apply GlobalTheory.Nef.isGen_evAt_frac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchTraceNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro hM
  apply h2
  simp [Matrix.det_mul, hM]

theorem det_J_ne_zero {σ : E →ₐ[F] E} (B : Base F E) {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_surjective (σ : E →ₐ[F] E) : Function.Surjective σ := by
  have hinj : Function.Injective ((σ : E →+* E).toRatAlgHom.toLinearMap) := (σ : E →+* E).injective
  exact LinearMap.injective_iff_surjective.1 hinj

def cAinv (σ : E →ₐ[F] E) : AE F E →ₐ[AF F] AE F E :=
  Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F))
    (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩).symm.toAlgHom

theorem cA_cAinv (σ : E →ₐ[F] E) (x : AE F E) : cA σ (cAinv σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [cAinv, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact AlgEquiv.apply_symm_apply (AlgEquiv.ofBijective σ ⟨(σ : E →+* E).injective, sigma_surjective σ⟩) y
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem at_cAinv (σ : E →ₐ[F] E) {t : AE F E} (ht : At (evI F) t) : At (evI F) (cAinv σ t) := by
  intro u hu
  rw [← map_smul, ht u hu, map_zero]

theorem at_single {n : ℕ} (k : Fin n) {t : AE F E} (ht : At (evI F) t) :
    At (evI F) (Pi.single k t : Fin n → AE F E) := by
  intro u hu
  funext j
  by_cases hj : j = k
  · subst hj; simp [ht u hu]
  · simp [Pi.single_apply, hj]

theorem at_vecMul {n : ℕ} {b : Fin n → AE F E} (hb : At (evI F) b) (A : Matrix (Fin n) (Fin n) (AE F E)) (k : Fin n) :
    At (evI F) ((b ᵥ* A) k) := by
  intro u hu
  have h := hb u hu
  simp only [Matrix.vecMul, dotProduct, Finset.smul_sum, smul_mul_assoc]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← smul_mul_assoc]
  have : u • b i = 0 := by simpa using congrFun h i
  rw [this, zero_mul]

theorem eq_zero_of_trace_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n : ℕ} (X : Spc F E n) (r s : ℕ),
    (∀ β : AE F E, At (evI F) β → (∀ t : AE F E, At (evI F) t →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) (β * t))) = 0) → β = 0) →
    X.IsHerm σ B r s → ∀ b : Fin n → AE F E, At (evI F) b →
    (∀ c : Fin n → AE F E, At (evI F) c → Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F X.J *ᵥ fun k => cA σ (c k))))) = 0) → b = 0 := by
  intro F E _ _ _ _ _ σ B n X r s hβ hX b hb hc
  have hdet : IsUnit (incM F X.J).det := by
    have h : (incM F X.J).det = inclR (F := F) (AF F) X.J.det := by
      rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 (det_J_ne_zero B hX)).map _
  have hv : b ᵥ* incM F X.J = 0 := by
    funext k
    apply hβ _ (at_vecMul hb _ k)
    intro t ht
    have h := hc (Pi.single k (cAinv σ t)) (at_single k (at_cAinv σ ht))
    rw [Matrix.dotProduct_mulVec] at h
    have hw : (fun j => cA σ ((Pi.single k (cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [cA_cAinv]
      · simp [Pi.single_apply, hj]
    rw [hw, dotProduct_single] at h
    exact h
  calc b = b ᵥ* (incM F X.J * (incM F X.J)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = (b ᵥ* incM F X.J) ᵥ* (incM F X.J)⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [hv, Matrix.zero_vecMul]

end GlobalTheory.ArchTraceNondeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzHadamardLemma
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.SchOp

theorem iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_ech : Function.HasTemperateGrowth ech := by
  set a : ℂ := -(2 * Real.pi * Complex.I) with ha
  have e : ech = fun y : ℝ => Complex.exp (a * y) := rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (a * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨by rw [e]; exact hc, fun n => ⟨0, ‖a‖ ^ n, fun x => ?_⟩⟩
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (a * x)‖ = 1 := by
    have : a * (x : ℂ) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by rw [ha]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_ech_affine {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] ℝ) (c : ℝ) : Function.HasTemperateGrowth (fun x : Y => ech (L x + c)) :=
  hasTemperateGrowth_ech.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const c))

theorem sch_schwartz {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (β : LinearMap.BilinForm ℝ Y) (a b : Y) (f : SchwartzMap Y ℂ) : ∃ g : SchwartzMap Y ℂ, ⇑g = sch β a b ⇑f := by
  let L : Y →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (β.flip b)
  have hL : ∀ x, L x = β x b := fun x => rfl
  have hm : Function.HasTemperateGrowth (fun x : Y => ech (β x b + β a b / 2)) := by
    simpa only [hL] using hasTemperateGrowth_ech_affine L (β a b / 2)
  have ht : Function.HasTemperateGrowth (fun x : Y => x + a) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a)
  have hu : ∃ (k : ℕ) (C : ℝ), ∀ x : Y, ‖x‖ ≤ C * (1 + ‖x + a‖) ^ k := by
    refine ⟨1, 1 + ‖a‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
      calc ‖x‖ = ‖(x + a) - a‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
    have h2 := norm_nonneg (x + a)
    have h3 := norm_nonneg a
    rw [pow_one]
    nlinarith
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : Y => ech (β x b + β a b / 2)) (SchwartzMap.compCLM ℂ ht hu f), ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.compCLM_apply]
  simp [sch, smul_eq_mul]

end GlobalTheory.SchOp
end

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

noncomputable section

namespace GlobalTheory.ArchUniqStd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def bil {P : V → V → ℝ} (h : IsPairing P) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
    (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)

theorem bil_apply {P : V → V → ℝ} (h : IsPairing P) (x y : V) : bil h x y = P x y := rfl

theorem exists_right [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : IsPairing P) (L : V →L[ℝ] ℝ) :
    ∃ b, ∀ y, P y b = L y := by
  have hinj : Function.Injective (bil h).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact h.nondegR b fun x => by simpa [bil_apply] using LinearMap.congr_fun hb x
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨b, hb⟩ := hsurj (L : V →ₗ[ℝ] ℝ)
  exact ⟨b, fun y => by simpa [bil_apply] using LinearMap.congr_fun hb y⟩

theorem exists_one [FiniteDimensional ℝ V] : ∃ Φ : 𝓢(V, ℂ), Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem eq_sum_pureA_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ U K hUo hUc hK
  classical
  have hcov : K ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ K, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  have hSB : ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    intro r
    have hcl : IsClopen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      ⟨(AddSubgroup.isClosed_of_isOpen U hUo).preimage (continuous_id.sub continuous_const),
        hUo.preimage (continuous_id.sub continuous_const)⟩
    have hco : IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      (Homeomorph.subRight r).isCompact_preimage.2 hUc
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U}
      · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} from hy),
          Set.indicator_of_mem hx]
      · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
  refine ⟨R, fun r _ => hSB r, fun Φ hinv hsupp => ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, (fun i => (x i).2) - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : (fun i => (x i).2) ∈ {y | y - r0 ∈ U} := hxr0
      simp only [GlobalTheory.WeilM.pureA, GlobalTheory.WeilAdm.slice, RingEquiv.symm_apply_apply, Set.indicator_of_mem hm, mul_one]
      obtain ⟨x', hx'⟩ : ∃ x' : κ → AdeleRing (𝓞 F) F, x' = fun i => ((x i).1, r0 i) := ⟨_, rfl⟩
      have e : x = x' + GlobalTheory.WeilAdm.finE F ((fun i => (x i).2) - r0) := by
        subst hx'
        funext i
        refine Prod.ext ?_ ?_
        · show (x i).1 = (x i).1 + 0
          rw [add_zero]
        · show (x i).2 = r0 i + ((x i).2 - r0 i)
          rw [add_sub_cancel]
      conv_lhs => rw [e]
      rw [hinv x' _ hxr0, hx']
    · intro r hr hne
      simp only [GlobalTheory.WeilM.pureA]
      have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : (fun i => (x i).2) ∉ K := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [hsupp x hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    simp only [GlobalTheory.WeilM.pureA]
    have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.WeilAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_finset_sum_pureTensor_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | exact GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator | (intros; apply GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
noncomputable section

namespace GlobalTheory.KBridge

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def infT : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
def finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


variable (F E) in
def ofInfT : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inl F (Ainf F) (Af F)).rTensor E


variable (F E) in
def ofFinT : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inr F (Ainf F) (Af F)).rTensor E

theorem decomp (z : AF F ⊗[F] E) : z = ofInfT F E (infT F E z) + ofFinT F E (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hx, hy]
    abel
  | tmul a e =>
    change a ⊗ₜ[F] e = ((a.1, 0) : AF F) ⊗ₜ[F] e + ((0, a.2) : AF F) ⊗ₜ[F] e
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem tmul_eq_smul_incV {n : ℕ} (a : AF F) (x : Fin n → E) : (fun i => a ⊗ₜ[F] x i) = a • incV F x := by
  funext i
  change a ⊗ₜ[F] x i = a • ((1 : AF F) ⊗ₜ[F] x i)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infT_tmul (a : AF F) (e : E) : infT F E (a ⊗ₜ[F] e) = a.1 ⊗ₜ[F] e := rfl

theorem mem_latHat_iff {n : ℕ} (X : Spc F E n) (z : Fin n → AE F E) :
    z ∈ latHat X ↔ (∀ i, infT F E (z i) = 0) ∧
      (fun i => finT F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hv, x, hx, rfl⟩ := hz
      have h0 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
      rw [← tmul_eq_smul_incV]
      refine ⟨fun i => ?_, ?_⟩
      · rw [infT_tmul, h0, TensorProduct.zero_tmul]
      · exact AddSubgroup.subset_closure ⟨a.2, fun v => hv v, x, hx, rfl⟩
    | zero =>
      refine ⟨fun i => map_zero _, ?_⟩
      have e : (fun i => finT F E ((0 : Fin n → AE F E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.add_apply, map_add (f := _), hy.1 i, hz.1 i, add_zero]
      · have e : (fun i => finT F E ((y + z) i)) = (fun i => finT F E (y i)) + fun i => finT F E (z i) :=
          funext fun i => map_add _ _ _
        rw [e]; exact add_mem hy.2 hz.2
    | neg y _ hy =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.neg_apply, map_neg, hy.1 i, neg_zero]
      · have e : (fun i => finT F E ((-y) i)) = -fun i => finT F E (y i) := funext fun i => map_neg _ _
        rw [e]; exact neg_mem hy.2
  · rintro ⟨hi, hf⟩
    have e : z = fun i => ofFinT F E (finT F E (z i)) := funext fun i => by
      conv_lhs => rw [decomp (z i)]
      rw [hi i, map_zero, zero_add]
    rw [e]
    suffices H : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (fun i => ofFinT F E (y i)) ∈ latHat X from H _ hf
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨show AF F from (0, a), map_zero _, fun v => ha v, x, hx, tmul_eq_smul_incV (show AF F from (0, a)) x⟩
    | zero =>
      have e : (fun i => ofFinT F E ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y y' _ _ hy hy' =>
      have e : (fun i => ofFinT F E ((y + y') i)) = (fun i => ofFinT F E (y i)) + fun i => ofFinT F E (y' i) :=
        funext fun i => map_add _ _ _
      rw [e]; exact add_mem hy hy'
    | neg y _ hy =>
      have e : (fun i => ofFinT F E ((-y) i)) = -fun i => ofFinT F E (y i) := funext fun i => map_neg _ _
      rw [e]; exact neg_mem hy

theorem mulVec_mem_latHat {n : ℕ} (σ : E →ₐ[F] E) (X : Spc F E n) (hfg : X.L.FG) {k : GAd σ X.Jᵀ}
    (hk : k ∈ levelOpen σ X.Jᵀ X.L) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (matHom (AF F) σ X.Jᵀ k).1 *ᵥ z ∈ latHat X := by
  rw [mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ k).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => finT F E (((matHom (AF F) σ X.Jᵀ k).1 *ᵥ z) i)) =
        Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ k *ᵥ fun i => finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
    rw [e]
    exact ((mem_levelOpen_iff_latHat σ X.Jᵀ hfg k).1 hk _).1 hf

theorem ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), X.L.IsLattice E → ∀ g : GAd σ X.Jᵀ,
    (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) →
    (∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v) → GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
  intro F E _ _ _ _ _ σ B n X hL g h1 h2
  have hfg : X.L.FG := hL.fg
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := mem_levelOpen.2 h2
  refine ⟨fun w => h1 w, fun z hz => ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg hg hz
  · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg (inv_mem hg) hz

end GlobalTheory.KBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

open Matrix GlobalTheory.Doubling

theorem dblGram_xi : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  intro D S JB ξ h
  have hinv : (dblSp S).gram⁻¹ = blkMat finSumFinEquiv S.gram⁻¹ (-S.gram⁻¹) :=
    Matrix.inv_eq_left_inv (by
      rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram S).2.isUnit, blkMat_one])
  rw [hinv, incM_JBd]
  ext i j
  have hij : ∀ a b, ξ * incM D.host.F JB a b = incM D.host.F (D.host.xi0 • S.gram⁻¹) a b := fun a b => by
    rw [← h]; rfl
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [blkMat, GlobalTheory.WeilM.dbl, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, Matrix.submatrix_apply, h1, h2,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, map_zero, smul_neg, map_neg, smul_eq_mul, mul_zero, mul_neg] at hij ⊢
  · exact hij i' j'
  · exact congrArg Neg.neg (hij i' j')

end GlobalTheory.DblSchr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledGram_satisfies_xi_relation : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  first | exact @GlobalTheory.DblSchr.dblGram_xi | exact GlobalTheory.DblSchr.dblGram_xi | (intros; apply GlobalTheory.DblSchr.dblGram_xi <;> assumption)
end
end
