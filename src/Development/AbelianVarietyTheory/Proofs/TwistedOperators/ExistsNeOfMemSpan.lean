module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensors
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.IoLift
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.PointAtPlaceHom
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.KFinOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'}

theorem span_eq_top
    {aS aT : D.what₂.Tau → ℚ} {a : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)}
    {a' : ∀ τ, Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)} (ha : ∀ τ, IsKAct M τ (a τ))
    (hirr : ∀ τ, AbsIrr fun X : lieAt V τ => a τ X) (hker : ∀ τ, LocKer M M' τ (aS τ) (aT τ) (a' τ))
    (I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M)
    (h0 : I ≠ 0) (hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y, I (srcOp M M' τ (aT τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y))
    (hIt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y, I (tgtOp M M' τ (aS τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0) :
    Submodule.span ℂ {x | ∃ φ y, I φ y = x} = ⊤ := by
  classical

  have hne : ∃ p y, multi I p y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (span_multi I fun p y => by rw [← multi_apply]; exact hc p y)

  have hsrc : ∀ τ (X : lieAt V τ) (q : D.what₂.Tau → LPol W.rank V.rank) (w : KVec M'),
      multi I (Function.update q τ (sOp M M' τ (aT τ) X (q τ))) w = intersection_update_fsHerm_neg_one τ (a τ X) (multi I q w) := by
    intro τ X q w
    rw [multi_apply, multi_apply, ← srcOp_glue]
    exact hIs τ X X.2 (glue q) (PiTensorProduct.tprod ℂ w)

  have hpair : ∀ τ (L : KT M →ₗ[ℂ] kFin M τ), IsContr τ L → ∀ (p : D.what₂.Tau → LPol W.rank V.rank) (y : KVec M'),
      IsLocPair M M' τ (aS τ) (aT τ) (a' τ) ((slice (multi I) τ p y).compr₂ L) := by
    intro τ L hL p y
    have hmove : ∀ X (hX : X ∈ lieAt V τ) (P : LPol W.rank V.rank) (z : kFin M' τ),
        (slice (multi I) τ p y).compr₂ L (sOp M M' τ (aT τ) X P) z =
          a τ X ((slice (multi I) τ p y).compr₂ L P z) := by
      intro X hX P z
      simp only [LinearMap.compr₂_apply, slice_apply]
      have hq : Function.update p τ (sOp M M' τ (aT τ) X P) =
          Function.update (Function.update p τ P) τ
            (sOp M M' τ (aT τ) X ((Function.update p τ P) τ)) := by simp
      rw [hq, hsrc τ ⟨X, hX⟩]
      exact LinearMap.congr_fun (hL (a τ X)) _
    refine ⟨fun X hX P P' z z' => ?_, fun Y hY P z => ?_⟩
    · rw [hmove X hX, hmove X hX]
      exact (ha τ).skew X hX _ _
    · simp only [LinearMap.compr₂_apply, slice_apply]
      have hq : Function.update p τ (tOp M M' τ (aS τ) Y P) =
          Function.update (Function.update p τ P) τ
            (tOp M M' τ (aS τ) Y ((Function.update p τ P) τ)) := by simp
      have hz : PiTensorProduct.tprod ℂ (Function.update y τ (a' τ Y z)) =
          intersection_update_fsHerm_neg_one τ (a' τ Y) (PiTensorProduct.tprod ℂ (Function.update y τ z)) := by
        rw [position_tprod]; simp
      rw [hq, multi_apply, multi_apply, ← tgtOp_glue, hz, ← map_add (f := _), hIt τ Y hY, map_zero]
  have key := (exists_factor (P := fun _ : D.what₂.Tau => LPol W.rank V.rank) (Y := fun τ => kFin M' τ)
    (K := fun τ => kFin M τ) (Z := ℂ) (G := fun τ => lieAt V τ)
    (fun τ X => sOp M M' τ (aT τ) X) (fun τ X => a τ X) hirr (multi I) 0 hne
    (fun τ X p y => hsrc τ X p y)
    (fun τ L hL p y hL0 => ⟨fun L' hL' p' y' => hker τ _ _ _ _ (hpair τ L hL p y) (hpair τ L' hL' p' y') hL0,
      fun p' y' n x z _ => by simp [slice_apply]⟩)).2
  rw [eq_top_iff, ← key]
  apply Submodule.span_mono
  rintro x ⟨p, y, rfl⟩
  exact ⟨glue p, PiTensorProduct.tprod ℂ y, (multi_apply I p y).symm⟩

end GlobalTheory.Chain.KFinOnto

namespace GlobalTheory.Chain.KFinOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem itW_onto_kFin : ∀ (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7)
    (k : Fin D.R.m) (a b : ℕ),
    a = k → b = (k : ℕ) + 1 → ∀ (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ (h : KSm M) (h' : KSm M'), LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, It φ (inclK h' y) = x} := by
  intro hD hH D k a b hab hb V W M M' θ ψ hθ hC ω f hω hf It hIt
  subst hab hb
  obtain ⟨X, hX, -, -, -, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hD hH
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hD hH D

  have hloc : ∀ τ, (kFin M τ ≤ M.sm τ ∧ kFin M' τ ≤ M'.sm τ) ∧ ∃ a a', IsKAct M τ a ∧ IsKAct M' τ a' ∧
      AbsIrr (fun X : lieAt V τ => a X) ∧ LocKer M M' τ (expS D k τ) (expT D k τ) a' := by
    intro τ
    obtain ⟨al, be, ga, de, hd, -, hA, hA'⟩ := hC τ
    refine exists_local hX h3 hH hB M M' τ hd ?_ ?_
    · show dualPar (parA (Ptw D) k τ) = _
      rw [hA]
    · show dualPar (parA (Ptw D) (k + 1) τ) = _
      rw [hA']
  choose hsm a a' ha ha' hirr hker using hloc
  have h : KSm M := fun τ => (hsm τ).1
  have h' : KSm M' := fun τ => (hsm τ).2
  refine ⟨h, h', ?_⟩

  obtain ⟨χS, χT, hW, hexp⟩ := hω
  have hvc : ∀ τ, _ := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D V W _ _ M M' θ ψ χS χT ω f τ (expS D k τ) (expT D k τ) hθ hW
    (hexp τ).1 (hexp τ).2 hf
  have hinj : Function.Injective (ptOf ψ θ M M' f) :=
    (GlobalTheory.VacuumFockLaws.vacuumFock_onObjects D V W _ _ M M' ψ θ hW.std hθ f hf).2.2.2.2

  have h0K : ∃ φ y, It φ (inclK h' y) ≠ 0 := by
    have hs : ∀ τ φ (v : M'.Vec), ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (u : Fin n → M'.sm τ),
        (∀ i, (u i : M'.H τ) ∈ kFin M' τ) ∧
          It φ (PiTensorProduct.tprod ℂ v) = ∑ i, It (φs i) (PiTensorProduct.tprod ℂ (Function.update v τ (u i))) := by
      intro τ φ v
      obtain ⟨n, φs, c, hc, hωc⟩ := FockOrbit.fock_orbit_coefFam D V W _ _ M M' θ ψ ω f τ (expS D k τ) (expT D k τ)
        hθ hinj (hvc τ).2.1 φ
      refine ⟨n, φs, fun i => ⟨kMean M' τ (c i) (v τ),
        (GlobalTheory.SmoothAverage.kMean_smooth D W _ M' τ (c i) (hc.1 i) (v τ) (v τ).2).1⟩,
        fun i => kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (v τ) i, ?_⟩
      exact it_eq_sum_kMean D V W _ _ M M' θ ω (ptOf ψ θ M M' f) It hIt τ n c φ φs v _ hc.1 hωc fun i => rfl
    by_contra hc
    push_neg at hc
    have hspan : Submodule.span ℂ {z | ∃ φ y, It φ (inclK h' y) = z} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨φ, y, rfl⟩
      exact hc φ y
    refine hIt.ne (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have hx := mem_span_of_average It h' hs φ x
    rw [hspan, Submodule.mem_bot] at hx
    simpa using hx

  have hK : ∀ φ y, It φ (inclK h' y) ∈ LinearMap.range (inclK h) := by
    intro φ y
    apply mem_range_inclK h
    intro τ
    refine ⟨Submodule.map ((inclT M) ∘ₗ It.flip (inclK h' y))
      (MvPolynomial.restrictTotalDegree (FVar D W.rank V.rank) ℂ φ.totalDegree), inferInstance, fun g hg => ?_⟩
    have hκ : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := hg
    have hFu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
    have hg' : g = (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFu, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFu, Matrix.one_mul]

    have hUH : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      obtain ⟨hu, hJ⟩ := hκ
      have e3 : (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
        have := (Matrix.mem_unitaryGroup_iff').mp hu
        rwa [Matrix.star_eq_conjTranspose] at this
      have e1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
        rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hFu, Matrix.conjTranspose_one,
          Matrix.one_mul]
      have e2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hFu, Matrix.one_mul]
      show gᴴ * gramAt D V τ * g = gramAt D V τ
      generalize hk : M.fr τ * g * (M.fr τ)⁻¹ = κ at e3 hJ hg'
      rw [← M.fr_gram τ, hg']
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, e2]
      rw [← Matrix.mul_assoc (Formalism.REAL.Jm (M.ε τ)) κ, ← hJ, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ κ, e3,
        Matrix.one_mul]
    have helt : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt]
      rw [← hg']
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) :=
      ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
    obtain ⟨xx, yy, -, -, hcf⟩ := (hvc τ).2.1
    have hcf1 := hcf _ hκ 1 h1 φ
    rw [elt_one hθ, helt] at hcf1
    obtain ⟨c, Q, hQ, hcQ⟩ : ∃ (c : ℂ) (Q : PolF D W.rank V.rank), Q.totalDegree ≤ φ.totalDegree ∧
        ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) = c • ptOf ψ θ M M' f Q :=
      ⟨_, _, GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ φ, hcf1⟩
    have hpt : ptOf ψ θ M M' f (c • Q) = ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) := by
      rw [hcQ]
      simp only [ptOf, map_smul]
    rw [← hIt.eqK τ g hUH φ (c • Q) hpt (inclK h' y)]
    exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.totalDegree_smul_le _ _).trans hQ))

  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    let e := LinearEquiv.ofInjective (inclK h) (inclK_injective h)
    have he : ∀ z : LinearMap.range (inclK h), inclK h (e.symm z) = z := fun z => by
      have := congrArg Subtype.val (e.apply_symm_apply z)
      rw [LinearEquiv.ofInjective_apply] at this
      exact this
    refine ⟨LinearMap.mk₂ ℂ (fun φ y => e.symm ⟨It φ (inclK h' y), hK φ y⟩) ?_ ?_ ?_ ?_, fun φ y => he _⟩
    · intro φ₁ φ₂ y
      apply inclK_injective h
      simp only [map_add (f := _), he, LinearMap.add_apply]
    · intro c φ y
      apply inclK_injective h
      simp only [map_smul, he, LinearMap.smul_apply]
    · intro φ y₁ y₂
      apply inclK_injective h
      simp only [map_add (f := _), he]
    · intro c φ y
      apply inclK_injective h
      simp only [map_smul, he]
  have hI0 : I ≠ 0 := by
    obtain ⟨φ, y, hne⟩ := h0K
    intro h0
    apply hne
    rw [← hI, h0]
    simp
  have hIs : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ y,
      I (srcOp M M' τ (expT D k τ) X φ) y = intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) := by
    intro τ X hX φ y
    apply inclK_injective h
    have e1 : ptOf ψ θ M M' f (srcOp M M' τ (expT D k τ) X φ) =
        ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) φ -
          ((expT D k τ : ℂ) * X.trace) • φ) := by
      congr 1
      simp only [srcOp, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul,
        sub_eq_add_neg]
    have d1 := hIt.eqg τ X hX φ (srcOp M M' τ (expT D k τ) X φ)
      (fun z => by rw [e1]; exact (hvc τ).2.2.1 X hX φ z) (inclK h' y)
    have d2 := FinTensor.derT_mapFactor h τ (a τ) (ha τ) X hX (I φ y)
    rw [hI] at d2
    rw [hI]
    exact derT_unique d1 d2
  have hIt' : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ y,
      I (tgtOp M M' τ (expS D k τ) Y φ) y + I φ (intersection_update_fsHerm_neg_one τ (a' τ Y) y) = 0 := by
    intro τ Y hY φ y
    apply inclK_injective h
    have e1 : ptOf ψ θ M M' f (tgtOp M M' τ (expS D k τ) Y φ) =
        ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ +
          ((expS D k τ : ℂ) * Y.trace) • φ) := by
      rfl
    have hd : ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f φ) z)
        (ptOf ψ θ M M' f (tgtOp M M' τ (expS D k τ) Y φ) z) 0 := fun z => by
      rw [e1]
      exact (hvc τ).2.2.2 Y hY φ z
    have hd2 := FinTensor.derT_mapFactor h' τ (a' τ) (ha' τ) Y hY y
    have hsum := hIt.invg τ Y hY φ _ _ _ hd hd2
    rw [LinearMap.map_add (inclK h), hI, hI, LinearMap.map_zero]
    exact hsum
  have hspanI := span_eq_top (aS := fun τ => expS D k τ) (aT := fun τ => expT D k τ) ha hirr hker I hI0 hIs hIt'
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ Submodule.span ℂ {x | ∃ φ y, I φ y = x} := by rw [hspanI]; exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := inclK h) ht
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨φ, y, rfl⟩, rfl⟩
  exact ⟨φ, y, (hI φ y).symm⟩

end GlobalTheory.Chain.KFinOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Chain GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors : ∀ (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (k : Fin D.R.m) (a b : ℕ),
    a = k → b = (k : ℕ) + 1 → ∀ (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ (h : KSm M) (h' : KSm M'), LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, It φ (inclK h' y) = x} := by
  first | exact @GlobalTheory.Chain.KFinOnto.itW_onto_kFin | exact GlobalTheory.Chain.KFinOnto.itW_onto_kFin | (intros; apply GlobalTheory.Chain.KFinOnto.itW_onto_kFin <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.L2.DIV Formalism.L2.Indef NumberField GlobalTheory.Chain GlobalTheory.Chain.IoLift
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowTest.WVec

variable {D : D7}

theorem tprod_ne_zero {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_inclK_ne {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h : KSm M) :
    ∃ y : KT M, inclK h y ≠ 0 := by
  have hu : ∀ τ, ∃ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, u ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun e => hx0 (congrArg Subtype.val e)⟩
  choose u hu using hu
  refine ⟨PiTensorProduct.tprod ℂ u, fun e => tprod_ne_zero hu ?_⟩
  exact GlobalTheory.Chain.IoLift.FinTensor.inclK_injective h (e.trans (map_zero _).symm)

theorem exists_ne_of_mem_span {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) {s : Set E} {x : E} (hx : x ∈ Submodule.span ℂ s) (h : L x ≠ 0) : ∃ z ∈ s, L z ≠ 0 := by
  by_contra hn
  push_neg at hn
  exact h ((Submodule.span_le (p := LinearMap.ker L)).2 (fun z hz => hn z hz) hx)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnVec_congr (d d' : ChainVec R) : ∀ n, (∀ k < n, d.polY k = d'.polY k) → d.dnVec n = d'.dnVec n
  | 0, _ => rfl
  | n + 1, h => by
    show d.dnVec n ∘ₗ R.ItY n (d.polY n) = d'.dnVec n ∘ₗ R.ItY n (d'.polY n)
    rw [dnVec_congr d d' n fun k hk => h k (by omega), h n (by omega)]

def ofPol (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) : ChainVec R := ⟨p, 0, 0⟩

theorem exists_w_ne (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : ∀ k, ChainPar D k) (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hθ : R.models_inf) :
    ∃ cv : ChainVec R, cv.w ≠ 0 := by
  have hm := D.R.two_le_m
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hch.ωY hch.ωX hch.vY hch.vX
  have stepY : ∀ k, k + 1 < D.R.m → ∃ (h : KSm (R.MY k)) (h' : KSm (R.MY (k + 1))),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItY k φ (inclK h' y) = x} := fun k hk => by
    obtain ⟨hW, hV⟩ := hS.1 A.μ0 ⟨k, by omega⟩ hk
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨k, by omega⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left (by omega))
      (min_eq_left (by omega)) _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY A.μ0 k) (R.vY A.μ0 k) hW hV (R.ItY k)
      (hch.ItY A.μ0 k hk)
  have stepX : ∃ (h : KSm (R.MY (D.R.m - 1))) (h' : KSm R.MX),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItX φ (inclK h' y) = x} := by
    obtain ⟨hW, hV⟩ := hS.2 A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨D.R.m - 1, by omega⟩ (min (D.R.m - 1) D.R.m) D.R.m (min_eq_left (Nat.sub_le _ _))
      (by show D.R.m = D.R.m - 1 + 1; omega) _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ hθ (hC _) (R.ωX A.μ0) (R.vX A.μ0) hW hV
      R.ItX (hch.ItX A.μ0)
  have key : ∀ n, n + 1 ≤ D.R.m → ∃ (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (h : KSm (R.MY n))
      (y : KT (R.MY n)), (ofPol (R := R) p).dnVec n (inclK h y) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨h, -, -⟩ := stepY 0 (by omega)
      obtain ⟨y, hy⟩ := exists_inclK_ne h
      exact ⟨fun _ => 0, h, y, hy⟩
    | succ n ih =>
      intro hn
      obtain ⟨p, h, y, hy⟩ := ih (by omega)
      obtain ⟨h1, h2, hsp⟩ := stepY n (by omega)
      obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
      refine ⟨Function.update p n φ, h2, y', ?_⟩
      show (ofPol (R := R) (Function.update p n φ)).dnVec n
        (R.ItY n ((Function.update p n φ) n) (inclK h2 y')) ≠ 0
      rw [Function.update_self, dnVec_congr (ofPol (Function.update p n φ)) (ofPol p) n
        fun k hk => Function.update_of_ne (by omega) _ _]
      exact hz
  obtain ⟨p, h, y, hy⟩ := key (D.R.m - 1) (by omega)
  obtain ⟨h1, h2, hsp⟩ := stepX
  obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
  refine ⟨⟨p, φ, inclK h2 y'⟩, ?_⟩
  show ChainVec.dnVec ⟨p, φ, inclK h2 y'⟩ (D.R.m - 1) (R.ItX φ (inclK h2 y')) ≠ 0
  rwa [dnVec_congr ⟨p, φ, inclK h2 y'⟩ (ofPol p) (D.R.m - 1) fun k _ => rfl]

end GlobalTheory.RowTest.WVec

end
