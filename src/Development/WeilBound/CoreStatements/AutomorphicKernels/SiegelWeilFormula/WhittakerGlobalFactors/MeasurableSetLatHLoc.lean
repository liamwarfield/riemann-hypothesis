module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MapRestrictIntH
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SigmaFiniteOfMp
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac.HS

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH hermMap)
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hermVec_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d) :
    hermVec R' σ b n (hermMap f σ S) i = f (hermVec R σ b n S i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  cases i with
  | inl i =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inl, hermMap, Matrix.map_apply]
    rw [GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f b, map_mul, AlgHom.commutes]
    congr 1
    have h := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) b ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)
    rw [Algebra.TensorProduct.map_id, AlgHom.id_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes]
    rfl
  | inr q =>
    simp only [hermVec, toVec, GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord, Sum.elim_inr, hermMap, Matrix.map_apply]
    exact GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.repr_map f b _ q.2

def hInfR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermInf σ S

def hFinR (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermFin σ S

theorem sigmaFinite_of_mp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) {μ : Measure X}
    {ν : Measure Y} [SigmaFinite ν] (h : MeasurePreserving e μ ν) : SigmaFinite μ := by
  have h2 : μ = ν.map e.symm := by
    rw [← h.map_eq, MeasurableEquiv.map_symm_map]
  rw [h2]
  exact e.symm.measurableEmbedding.sigmaFinite_map


omit [NumberField E] in
theorem coordHerm_congr {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    {m₁ m₂ : MeasurableSpace R} (h : m₁ = m₂) (l₁ : @Measure R m₁) (l₂ : @Measure R m₂) (hl : ∀ s, l₁ s = l₂ s)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    @coordHerm F E _ _ _ R _ _ _ m₁ σ d b l₁ n = @coordHerm F E _ _ _ R _ _ _ m₂ σ d b l₂ n := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

section Meas
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

theorem db_split' (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (l : Measure (InfiniteAdeleRing F)) (hH : l.IsAddHaarMeasure)
    (D : Set (Ainf F)) (hD : IsAddFundamentalDomain (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.intInf F) D l) (hD1 : l D = 1)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n)) := by
  obtain ⟨⟨hALC, hASC, hAT2⟩, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp

  let e : HermR (AF F) σ n ≃ₜ (Idx n d → AF F) := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  have hpair : ∀ S T : HermR (AF F) σ n, chiG (ξ • formB σ b n) (e S) (e T) = ψ (pairHerm (AF F) σ n S T) := by
    intro S T
    rw [he, he, pair_eq (AF F) hinv hCM.2.2.1 hδ hσδ b n S T, hξ, chiG]
    congr 2
    have h2 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
        algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
      ext p q
      exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
    rw [h2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hsd : db.map e = adeleMeasurePi F :=
    selfDual_eq _ hs hdet _ (selfDual_transport e (fun S T => by rw [he, he, he, hermVec_add]) _ _ hpair db hdb)
  have hEq := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hH D hD hD1 lf hlf h1
  haveI : SigmaFinite l := Measure.IsAddHaarMeasure.sigmaFinite l
  haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
  have hΘ := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    (Idx n d) (fun _ => l) (fun _ => lf)
  have hA' : MeasurePreserving e.toMeasurableEquiv db (Measure.pi fun _ : Idx n d => l.prod lf) := by
    refine ⟨e.toMeasurableEquiv.measurable, ?_⟩
    change db.map e = _
    rw [hsd, adeleMeasurePi, hEq]
  let eI := ((hermVec_isHomeomorph hCM (Ainf F) b n).homeomorph _).toMeasurableEquiv
  let eF := ((hermVec_isHomeomorph hCM (Af F) b n).homeomorph _).toMeasurableEquiv
  have hI : MeasurePreserving eI (coordHerm (Ainf F) σ b l n) (Measure.pi fun _ : Idx n d => l) :=
    mp_hermVec hCM (Ainf F) b n l
  have hF : MeasurePreserving eF (coordHerm (Af F) σ b lf n) (Measure.pi fun _ : Idx n d => lf) :=
    mp_hermVec hCM (Af F) b n lf
  haveI : SigmaFinite (coordHerm (Ainf F) σ b l n) := sigmaFinite_of_mp eI hI
  haveI : SigmaFinite (coordHerm (Af F) σ b lf n) := sigmaFinite_of_mp eF hF
  let eP := eI.prodCongr eF
  have hP : MeasurePreserving eP ((coordHerm (Ainf F) σ b l n).prod (coordHerm (Af F) σ b lf n))
      ((Measure.pi fun _ : Idx n d => l).prod (Measure.pi fun _ : Idx n d => lf)) :=
    hI.prod hF
  refine (hP.comp_left_iff).1 ?_
  have hc := hΘ.comp hA'
  convert hc using 1
  funext S
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show hermVec (Ainf F) σ b n (hermMap (fstA F) σ S) i = (hermVec (AF F) σ b n S i).1
    rw [hermVec_map]
    rfl
  · show hermVec (Af F) σ b n (hermMap (sndA F) σ S) i = (hermVec (AF F) σ b n S i).2
    rw [hermVec_map]
    rfl

end Meas

theorem db_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n : ℕ)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (hinf : IsStdInf laminf)
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1) :
    MeasurePreserving (fun S : HermR (AF F) σ n => (hInfR σ S, hFinR σ S)) db
      ((coordHerm (Ainf F) σ b laminf n).prod (coordHerm (Af F) σ b lf n)) := by
  have hm : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨l, hl, hH, D, hD, hD1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hm
  have h := db_split' σ hCM ψ hψ n db hdb b l hH D hD hD1 lf hlf h1
  rw [coordHerm_congr hm l laminf hl σ b n] at h
  exact h

end PositivityTheory.SiegelWeilFormula.GFac.HS

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac.HS

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH hermMap)
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hermVec_hermV (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (y : HermR (Af F) σ n) (i : Idx n d) :
    hermVec (Fv F v) σ b n (hermV σ v y) i = evalV F v (hermVec (Af F) σ b n y i) :=
  hermVec_map (evalV F v) σ b n y i


omit [NumberField E] in
theorem mem_latH_iff_vec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (S : HermR (Fv F v) σ n) :
    S ∈ latH σ b v n ↔ ∀ i, hermVec (Fv F v) σ b n S i ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩ i
    cases i with
    | inl i => exact h1 i
    | inr q => exact h2 q.1.1.1 q.1.1.2 q.1.2 q.2
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i j hij k => h (Sum.inr (⟨(i, j), hij⟩, k))⟩

theorem continuous_hermV (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (hermV σ v : HermR (Af F) σ n → HermR (Fv F v) σ n) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  letI : MeasurableSpace (Af F) := borel _
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨d, b⟩ : ∃ d, Nonempty (Module.Basis (Fin d) F E) := by
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
    exact ⟨_, ⟨Module.finBasis F E⟩⟩
  obtain ⟨b⟩ := b
  let ef := (hermVec_isHomeomorph hCM (Af F) b n).homeomorph _
  let ev := (hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _
  have h : (hermV σ v : HermR (Af F) σ n → HermR (Fv F v) σ n) =
      ev.symm ∘ (fun x i => evalV F v (x i)) ∘ ef := by
    funext y
    apply ev.injective
    rw [show (ev.symm ∘ (fun x i => evalV F v (x i)) ∘ ef) y = ev.symm (fun i => evalV F v (ef y i)) from rfl,
      ev.apply_symm_apply]
    funext i
    exact hermVec_hermV σ b n v y i
  rw [h]
  refine ev.symm.continuous.comp (Continuous.comp ?_ ef.continuous)
  exact continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem coordHerm_box (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (hA : ∀ v, MeasurableSet (A v)) :
    coordHerm (Af F) σ b lf n {y | (∀ v ∈ S, hermV σ v y ∈ A v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} =
      ∏ v ∈ S, coordHerm (Fv F v) σ b (lam v) n (A v) := by
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  let ef := ((hermVec_isHomeomorph hCM (Af F) b n).homeomorph _).toMeasurableEquiv
  let ev := fun v => ((hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _).toMeasurableEquiv
  have hef : ∀ y, ef y = hermVec (Af F) σ b n y := fun _ => rfl
  have hev : ∀ v y, ev v y = hermVec (Fv F v) σ b n y := fun _ _ => rfl
  have hF : MeasurePreserving ef (coordHerm (Af F) σ b lf n) (Measure.pi fun _ : Idx n d => lf) :=
    mp_hermVec hCM (Af F) b n lf
  have hV : ∀ v, MeasurePreserving (ev v) (coordHerm (Fv F v) σ b (lam v) n) (Measure.pi fun _ : Idx n d => lam v) :=
    fun v => mp_hermVec hCM (Fv F v) b n (lam v)
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Idx n d → Fv F v) := fun v => (ev v).symm ⁻¹' A v
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => (ev v).symm.measurable (hA v)
  have hset : ({y | (∀ v ∈ S, hermV σ v y ∈ A v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} :
        Set (HermR (Af F) σ n)) = ef ⁻¹' {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A' v) ∧
        ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} := by
    ext y
    have hc : ∀ v, (fun i => evalV F v (ef y i)) = ev v (hermV σ v y) := fun v => by
      funext i
      exact (hermVec_hermV σ b n v y i).symm
    have hsy : ∀ v, (ev v).symm (fun i => evalV F v (ef y i)) = hermV σ v y := fun v =>
      (congrArg (ev v).symm (hc v)).trans ((ev v).symm_apply_apply _)
    have hl : ∀ v, (hermV σ v y ∈ latH σ b v n ↔ ∀ i, evalV F v (ef y i) ∈ v.adicCompletionIntegers F) := fun v =>
      (mem_latH_iff_vec σ b n v (hermV σ v y)).trans (forall_congr' fun i => Iff.of_eq
        (congrArg (fun t => t ∈ v.adicCompletionIntegers F) (hermVec_hermV σ b n v y i)))
    simp only [Set.mem_setOf_eq, Set.mem_preimage, A', hsy]
    exact and_congr Iff.rfl (forall_congr' fun v => imp_congr_right fun _ => hl v)
  rw [hset, hF.measure_preimage_equiv, GlobalTheory.CompanionTheory.SW.AfBox.pi_box F lam hlam lf hlf h1 (Idx n d) S A' hA']
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← (hV v).measure_preimage_equiv]
  congr 1
  ext x
  simp [A']

def hV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermV σ v y

def intHR (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))}

theorem map_restrict_intH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hlam : ∀ v, IsStdV v (lam v))
    (lf : Measure (Af F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1)
    (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ((coordHerm (Af F) σ b lf n).restrict (intHR σ b n S)).map (fun y (v : S) => hV σ v.1 y) =
      Measure.pi fun v : S => coordHerm (Fv F v.1) σ b (lam v.1) n := by
  classical
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  have hSF : ∀ v, SigmaFinite (coordHerm (Fv F v) σ b (lam v) n) := fun v =>
    haveI : SigmaFinite (lam v) := Measure.IsAddHaarMeasure.sigmaFinite (lam v)
    sigmaFinite_of_mp ((hermVec_isHomeomorph hCM (Fv F v) b n).homeomorph _).toMeasurableEquiv
      (mp_hermVec hCM (Fv F v) b n (lam v))
  haveI : ∀ v : S, SigmaFinite (coordHerm (Fv F v.1) σ b (lam v.1) n) := fun v => hSF v.1
  have hρ : Measurable (fun y (v : S) => hV σ v.1 y) :=
    Measurable.of_eval fun v => (continuous_hermV σ hCM n v.1).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
  let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n) :=
    fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
  have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
    by_cases h : v ∈ S
    · simp only [A', dif_pos h]; exact hs _
    · simp only [A', dif_neg h]; exact MeasurableSet.univ
  have key := coordHerm_box σ hCM b lam hlam lf hlf h1 n S A' hA'
  have hset : (fun y (v : S) => hV σ v.1 y) ⁻¹' Set.univ.pi s ∩ intHR σ b n S =
      ({y | (∀ v ∈ S, hermV σ v y ∈ A' v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n} : Set (HermR (Af F) σ n)) := by
    ext y
    change (∀ v : S, v ∈ Set.univ → hV σ v.1 y ∈ s v) ∧ (∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))) ↔
      (∀ v ∈ S, hV σ v y ∈ A' v) ∧ ∀ v, v ∉ S → hV σ v y ∈ (latH σ b v n : Set (HermR (Fv F v) σ n))
    refine and_congr ⟨fun h v hv => ?_, fun h v _ => ?_⟩ Iff.rfl
    · simpa only [A', dif_pos hv] using h ⟨v, hv⟩ (Set.mem_univ _)
    · have := h v.1 v.2
      simpa only [A', dif_pos v.2] using this
  rw [hset, key, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', dif_pos v.2]

end PositivityTheory.SiegelWeilFormula.GFac.HS

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurableSet_latH_loc (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc := (GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) b n).continuous
  have : (latH σ b v n : Set (HermR (Fv F v) σ n)) =
      (GlobalTheory.CompanionTheory.SW.HermSd.hermVec (Fv F v) σ b n) ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    Set.ext fun S => (HS.mem_latH_iff_vec σ b n v S).trans ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [this]
  exact hc.measurable (MeasurableSet.univ_pi fun _ => hO.measurableSet)

theorem measurableSet_intHR (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (HS.intHR σ b n S) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  have : HS.intHR σ b n S =
      ⋂ v, ⋂ (_ : v ∉ S), (HS.hV σ v) ⁻¹' (latH σ b v n : Set (HermR (Fv F v) σ n)) := by
    ext y
    simp only [HS.intHR, Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  exact (HS.continuous_hermV σ hCM n v).measurable (measurableSet_latH_loc σ hCM b n v)

theorem herm_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (n d : ℕ)
    (bs : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (hν : SdHerm F E σ (AF F) ψ n ν)
    (νi : Measure (HermR (Ainf F) σ n)) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∀ (gi : HermR (Ainf F) σ n → ℂ) (g : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
        (∀ v ∈ S, AEStronglyMeasurable (g v) (νv v)) →
        ∫ b in UH σ bs n S, gi (hermInf σ b) * ∏ v ∈ S, g v (hermV σ v (hermFin σ b)) ∂ν =
          (∫ x, gi x ∂νi) * ∏ v ∈ S, ∫ x, g v x ∂(νv v) := by
  classical
  obtain ⟨⟨laminf, hinf⟩, hlamE⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamE
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  obtain ⟨cinf, c, hU, hci, hcv⟩ := GlobalTheory.CompanionTheory.SW.sdHerm_eq_coord F E σ hCM d bs laminf lam hinf hlam ψ hψ n
  have eνi : νi = cinf • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n := (hci νi).1 hνi
  have eνv : ∀ v, νv v = c v • GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := fun v => (hcv v (νv v)).1 (hνv v)
  have hfin : {v | ¬ c v = 1}.Finite := Filter.eventually_cofinite.1 hU.1
  refine ⟨hfin.toFinset, fun S hS gi g hg => ?_⟩
  have hprod : cinf * ∏ v ∈ S, c v = 1 := by
    have h2 := hU.2
    rwa [finprod_eq_prod_of_mulSupport_subset c (s := S) fun v hv => hS (hfin.mem_toFinset.2 hv)] at h2
  have hcS : ∀ v ∈ S, c v ≠ 0 := fun v hv h0 => by
    rw [Finset.prod_eq_zero hv h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (HermR (Af F) σ n) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  have hSF : ∀ v, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n) := fun v =>
    haveI : SigmaFinite (lam v) := Measure.IsAddHaarMeasure.sigmaFinite (lam v)
    HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Fv F v) bs n).homeomorph _).toMeasurableEquiv
      (GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Fv F v) bs n (lam v))
  haveI : ∀ v : S, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := fun v => hSF v.1
  have hmp := HS.db_split σ hCM ψ hψ n ν hν bs laminf hinf lf hlf h1
  obtain ⟨-, -, -, -, -, -, -, -, hme0, -⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n ν hν.1
  have hme : MeasurableEmbedding (fun S : HermR (AF F) σ n => (HS.hInfR σ S, HS.hFinR σ S)) := hme0
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) := by
    obtain ⟨hH, -⟩ := hinf
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
    have hmpI := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Ainf F) bs n laminf
    haveI : SigmaFinite laminf := Measure.IsAddHaarMeasure.sigmaFinite laminf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Ainf F) bs n).homeomorph _).toMeasurableEquiv hmpI
    infer_instance
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n) := by
    obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    haveI : BorelSpace (Af F) := ⟨rfl⟩
    have hmpF := GlobalTheory.CompanionTheory.SW.HermSd.mp_hermVec hCM (Af F) bs n lf
    haveI : SigmaFinite lf := Measure.IsAddHaarMeasure.sigmaFinite lf
    haveI := HS.sigmaFinite_of_mp ((GlobalTheory.CompanionTheory.SW.HermSd.hermVec_isHomeomorph hCM (Af F) bs n).homeomorph _).toMeasurableEquiv hmpF
    infer_instance

  set fS : HermR (Af F) σ n → ℂ := fun y => ∏ v ∈ S, g v (HS.hV σ v y) with hfS
  set Φ : HermR (Ainf F) σ n × HermR (Af F) σ n → ℂ :=
    fun p => gi p.1 * (HS.intHR σ bs n S).indicator fS p.2 with hΦ
  have e1 : ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν =
      ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν := by
    rw [← integral_indicator (measurableSet_UH σ hCM bs n S)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    by_cases hb : b ∈ UH σ bs n S
    · have hb' : HS.hFinR σ b ∈ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_mem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_mem hb']
    · have hb' : HS.hFinR σ b ∉ HS.intHR σ bs n S := hb
      rw [Set.indicator_of_notMem hb]
      change _ = gi (HS.hInfR σ b) * (HS.intHR σ bs n S).indicator fS (HS.hFinR σ b)
      rw [Set.indicator_of_notMem hb', mul_zero]
  have e2 : ∫ b, Φ (HS.hInfR σ b, HS.hFinR σ b) ∂ν =
      (∫ x, gi x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ bs laminf n) *
        ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n := by
    rw [hmp.integral_comp hme Φ]
    exact integral_prod_mul gi _
  have hAE : AEStronglyMeasurable (fun x : ∀ v : S, HermR (Fv F v.1) σ n => ∏ v : S, g v.1 (x v))
      (Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
    have := Finset.aestronglyMeasurable_prod (μ := Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n)
      (f := fun (v : S) (x : ∀ v : S, HermR (Fv F v.1) σ n) => g v.1 (x v)) Finset.univ (fun v _ => by
        have hgv : AEStronglyMeasurable (g v.1) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v.1) σ bs (lam v.1) n) := by
          have h0 := hg v.1 v.2
          rw [eνv v.1] at h0
          refine h0.mono_ac (fun s hs => ?_)
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hs
          exact hs.resolve_left (by exact_mod_cast hcS v.1 v.2)
        exact hgv.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ v))
    convert this using 1
    funext x
    simp [Finset.prod_apply]
  have e3 : ∫ y, (HS.intHR σ bs n S).indicator fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
      ∏ v ∈ S, ∫ x, g v x ∂GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ bs (lam v) n := by
    rw [integral_indicator (measurableSet_intHR σ hCM bs n S)]
    have hρ : Measurable (fun y (v : S) => HS.hV σ v.1 y) :=
      Measurable.of_eval fun v => (HS.continuous_hermV σ hCM n v.1).measurable
    have hmap := HS.map_restrict_intH σ hCM bs lam hlam lf hlf h1 n S
    have e4 : ∫ y in HS.intHR σ bs n S, fS y ∂GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n =
        ∫ x, ∏ v : S, g v.1 (x v) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Af F) σ bs lf n).restrict (HS.intHR σ bs n S)).map
          (fun y (v : S) => HS.hV σ v.1 y) := by
      rw [integral_map hρ.aemeasurable (by rw [hmap]; exact hAE)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hfS]
      rw [← Finset.prod_coe_sort S]
    rw [e4, hmap, integral_fintype_prod_eq_prod (fun (v : S) => g v.1), ← Finset.prod_coe_sort S]
  show ∫ b in UH σ bs n S, gi (HS.hInfR σ b) * ∏ v ∈ S, g v (HS.hV σ v (HS.hFinR σ b)) ∂ν = _
  rw [e1, e2, e3, eνi, integral_smul_nnreal_measure]
  simp only [eνv, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [Finset.prod_mul_distrib]
  have hprodC : ((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ) = 1 := by
    have := congrArg (fun x : NNReal => ((x : ℝ) : ℂ)) hprod
    push_cast at this
    exact this
  have key : ∀ (a k q p : ℂ), k * q = 1 → a * p = (k * a) * (q * p) := fun a k q p h => by
    linear_combination (-(a * p)) * h
  exact key _ _ _ _ hprodC

end PositivityTheory.SiegelWeilFormula.GFac

end
