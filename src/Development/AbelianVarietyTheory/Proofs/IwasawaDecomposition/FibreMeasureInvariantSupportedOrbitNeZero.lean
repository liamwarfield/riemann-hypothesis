module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibProp

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem form_eq (x y : Fin n → A) :
    Formalism.UG.hform s J x y = dotProduct (fun i => s (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT s g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform s J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform s J x y := by
  have e : (fun i => s (g.mulVec x i)) = Matrix.vecMul (fun i => s (x i)) (Formalism.UG.cT s g) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [form_eq, form_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem form_smul (a : A) (x : Fin n → A) :
    Formalism.UG.hform s J (a • x) (a • x) = s a * a * Formalism.UG.hform s J x x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem det_norm {g : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) (hg : Formalism.UG.cT s g * J * g = J) :
    g.det * s g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem lrAct_one (g : Matrix (Fin n) (Fin n) A) {k : ℕ} (X : Fin k → Fin n → A) :
    lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

end Alg

section Q

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sig_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_incl (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem q_scale (r : R) (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  unfold qR hR
  rw [form_smul, sig_alg, ← map_mul, ← Algebra.smul_def (r * r), map_smul, smul_eq_mul]
  ring

theorem q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin M → E) (β : F)
    (hx : hE σ J x x = algebraMap F E β) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R β := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have e : hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (x i)) = inclR R (hE σ J x x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, hE, Formalism.UG.hform, JR, Matrix.map_apply, sig_incl, map_sum, map_mul]
    rfl
  have e2 : inclR R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  unfold qR
  rw [e, hx, e2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (algebraMap F R), ← map_mul]
  norm_num

theorem q_cont [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R] :
    Continuous (qR R σ J) := by
  have hs : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  have ht : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  unfold qR hR Formalism.UG.hform
  fun_prop

end Q

theorem fibre_invariant_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hN M J x β lam ν m hJ hβ hx hlam hν hm
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 β hβ).map _
  have hq : qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := q_rat R σ J hCM.2.2.1 (x 0) β hx
  obtain ⟨hsupp, -, huniq⟩ := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ m hν hu hm
  have h1 : modu R 1 = 1 := (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  refine ⟨fun g => ?_, ?_, ?_⟩
  · set G : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (HA.mat R σ J g).val with hG
    have hg : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := g.2
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 (HA.mat R σ J g).isUnit
    have hJu : IsUnit (JR (F := F) R J).det := by
      unfold JR
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hm1 : modu (R ⊗[F] E) G.det = 1 := by
      rw [(GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ hCM R G.det 1 hd (by rw [map_one, det_norm _ _ hJu hg])).2, h1]
    have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ 1 m G hlam hν hd isUnit_one
      (fun z => by rw [one_mul]; unfold qR hR; rw [form_mulVec _ _ hg]) hm
    rw [one_mul, hm1, h1, inv_one, mul_one, one_smul] at this
    have e : lrAct G 1 = fun X : Fin 1 → Fin M → R ⊗[F] E => g • X := by
      funext X; rw [lrAct_one]; rfl
    rw [e] at this
    exact huniq _ this
  · refine measure_mono_null (fun y hy => ?_) hsupp
    exact fun h => hy (GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM R hN M J hJ _ _ y hu hq h)
  · rintro rfl
    obtain ⟨-, -, hO, U, hU, h1U, s, -, -, hs⟩ := id hN
    obtain ⟨fib, hfib, -⟩ := id hm
    obtain ⟨w, hw⟩ := hu
    let T : Set R := {b | IsUnit b} ∩ (fun b => b * (↑w⁻¹ : R)) ⁻¹' U
    have hT : IsOpen T := by
      refine IsOpen.inter ?_ (hU.preimage (by fun_prop))
      exact hO.isOpenEmbedding_unitsVal.isOpen_range
    have hz : ∀ b ∈ T, fib b = 0 := by
      rintro b ⟨hb, hbU⟩
      set r := s (b * (↑w⁻¹ : R))
      have hr : r * r = b * (↑w⁻¹ : R) := hs _ hbU
      have hrr : IsUnit (r * r) := hr ▸ IsUnit.mul hb (Units.isUnit _)
      have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
      have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ (r * r) 0
        (algebraMap R (R ⊗[F] E) r • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact (hru.map _).pow _) hrr
        (fun z => by rw [Matrix.smul_mulVec, Matrix.one_mulVec, q_scale]) hm
      rw [Measure.map_zero, smul_zero, hr, ← hw, Units.inv_mul_cancel_right] at this
      exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ 0 hν hb this).2.2 _ ⟨fib, hfib, rfl⟩
    let O : Set (Fin 1 → Fin M → R ⊗[F] E) := (fun X => qR R σ J (X 0)) ⁻¹' T
    have hOo : IsOpen O := hT.preimage ((q_cont R σ J).comp (continuous_apply 0))
    have hne : O.Nonempty := ⟨ratTup (F := F) R x, by
      show qR R σ J (ratTup (F := F) R x 0) ∈ T
      rw [hq, ← hw]
      exact ⟨w.isUnit, by simpa using h1U⟩⟩
    have key := hfib.2.1 (O.indicator 1) (measurable_one.indicator hOo.measurableSet)
    have hz' : ∀ b, fib b O = 0 := by
      intro b
      by_cases hb : b ∈ T
      · rw [hz b hb]; rfl
      · refine measure_mono_null (fun y hy => ?_) (hfib.1 b)
        intro h
        apply hb
        have : qR R σ J (y 0) = b := h.1
        rw [← this]; exact hy
    simp only [Measure.restrict_univ, lintegral_indicator_one hOo.measurableSet, hz',
      lintegral_zero] at key
    haveI : (tupMeas lam 1 M).IsOpenPosMeasure := by
      unfold tupMeas
      haveI : (Measure.pi fun _ : Fin M => lam).IsOpenPosMeasure :=
        Measure.pi.isOpenPosMeasure (fun _ : Fin M => lam)
      exact Measure.pi.isOpenPosMeasure (fun _ : Fin 1 => Measure.pi fun _ : Fin M => lam)
    exact (hOo.measure_pos _ hne).ne' key

end GlobalTheory.GaugeEx.FibProp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZeroStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  first | exact @GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | exact GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | (intros; apply GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnSwap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilSwap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck

variable {D : D7}

def trEquiv (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) : ThS ψ V W ≃ₗ[ℂ] ThS ψ W V where
  toFun Φ := ⟨fun y => Φ.1 y.transpose, mem_ThS.2 (isThetaFun_transpose ψ V W hne _ (mem_ThS.1 Φ.2))⟩
  invFun Φ := ⟨fun x => Φ.1 x.transpose, mem_ThS.2 (isThetaFun_transpose ψ W V hne.symm _ (mem_ThS.1 Φ.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem heis_transpose (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W)
    (f : WA W V → ℂ) :
    (fun x : WA V W => Heisenberg₂ ψ W V u.transpose f x.transpose) = Heisenberg₂ ψ V W u (fun x => f x.transpose) := by
  funext x
  simp only [Heisenberg₂, symplH_transpose V W hne, Matrix.transpose_add]

def swapRep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : GA D W × GA D V →* Module.End ℂ (ThS ψ W V) :=
  ((trEquiv ψ hne).conjRingEquiv.toMonoidHom.comp om).comp (MulEquiv.prodComm (M := GA D W) (N := GA D V)).toMonoidHom

theorem swapRep_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) (h : GA D W) (g : GA D V) (Φ : ThS ψ W V) :
    swapRep hne om (h, g) Φ = trEquiv ψ hne (om (g, h) ((trEquiv ψ hne).symm Φ)) := rfl

theorem exists_isWeilOn_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), V.rank ≠ W.rank → IsWeilOn ψ V W χ χ' om → ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧ ∀ (g : GA D V) (h : GA D W) (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) → ∀ x : WA V W, (om' (h, g) Φ').1 x.transpose = (om (g, h) Φ).1 x := by
  intro D ψ _ V W χ χ' om hne H
  refine ⟨swapRep hne om, ⟨fun h g w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_,
    fun μ 𝓕 hμ h𝓕 p Φ => ?_, fun e he h g hh hg y x hy hx => ?_⟩, fun g h Φ Φ' e x => ?_⟩
  · have k := H.Heisenberg₂ g h w₀.transpose ((trEquiv ψ hne).symm Φ) ((trEquiv ψ hne).symm Φ') (by
      show (fun x : WA V W => Φ'.1 x.transpose) = _
      rw [e]
      exact heis_transpose ψ hne w₀.transpose Φ.1)
    rw [swapRep_apply, swapRep_apply]
    show (fun y : WA W V => (om (g, h) _).1 y.transpose) = _
    rw [k, actHom_swap W V hne.symm]
    exact heis_transpose ψ hne.symm _ _
  · exact H.aut γ' hγ' γ hγ ((trEquiv ψ hne).symm Φ)
  · exact (H.cont ((trEquiv ψ hne).symm Φ) w.transpose).comp continuous_swap
  · haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA W V) := Pi.topologicalAddGroup
    haveI : BorelSpace (WA V W) := ⟨rfl⟩
    haveI : BorelSpace (WA W V) := ⟨rfl⟩
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WA W V)
      (Matrix.transposeAddEquiv _ _ _) continuous_id.matrix_transpose continuous_id.matrix_transpose
      (ratL V W) (ratL W V) (fun x => ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩,
        fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩) μ 𝓕 hμ h𝓕
    rw [← h3 fun w => ‖(swapRep hne om p Φ).1 w‖ ^ 2, ← h3 fun w => ‖Φ.1 w‖ ^ 2]
    exact H.unit ν _ h1 h2 (p.2, p.1) ((trEquiv ψ hne).symm Φ)
  · obtain ⟨r, hr, k⟩ := H.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ Φ => ?_⟩
    rw [splitFac_swap V W hne]
    exact k (ℓ.comp (trEquiv ψ hne).toLinearMap) (fun u hu Ψ Ψ' e' =>
      hℓ u.transpose (fun i j => hu j i) (trEquiv ψ hne Ψ) (trEquiv ψ hne Ψ') (by
        show (fun y : WA W V => Ψ'.1 y.transpose) = _
        rw [e']
        exact heis_transpose ψ hne.symm u.transpose Ψ.1)) ((trEquiv ψ hne).symm Φ)
  · have : (trEquiv ψ hne).symm Φ' = Φ := Subtype.ext (funext e)
    rw [swapRep_apply, this]
    rfl

end GlobalTheory.Mem.WeilSwap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamond
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamond
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpDia

section Local
variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem inc_dil {res : R →+* k} (hs : Function.Surjective res) {t : R} {p q : Pr R V k} (hp : p.Ok res)
    (h : Pr.Inc res t p q) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  obtain ⟨b, hb⟩ := hs a⁻¹
  have he : e ∈ q.L := by
    by_contra hn
    rw [h1.off _ hn] at h3
    exact zero_ne_one h3
  have hte : t • e ∈ p.L := by
    by_contra hn
    rw [hp.off _ hn] at h4
    exact zero_ne_one h4
  refine ⟨h1.dil ha, fun y => ?_, b • e, ?_, ?_⟩
  · show y ∈ p.L ↔ y ∈ q.L ∧ a * q.f y = 0
    rw [h2 y, mul_eq_zero, or_iff_right ha]
  · show a * q.f _ = 1
    rw [h1.smul _ _ he, h3, hb, mul_one, mul_inv_cancel₀ ha]
  · show a * p.f _ = 1
    rw [smul_comm, hp.smul _ _ hte, h4, hb, mul_one, mul_inv_cancel₀ ha]

def dilEquiv {a : k} (ha : a ≠ 0) : Pr R V k ≃ Pr R V k where
  toFun q := q.dil a
  invFun q := q.dil a⁻¹
  left_inv q := by
    show (q.dil a).dil a⁻¹ = q
    rw [Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one]
  right_inv q := by
    show (q.dil a⁻¹).dil a = q
    rw [Pr.dil_dil, mul_inv_cancel₀ ha, Pr.dil_one]

end Local

theorem atV_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J}
    (h : AtV v η) (δ : GA σ J) : AtV v (δ⁻¹ * η * δ) := by
  intro v' hv'
  have h1 := h v' hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, mul_one, inv_mul_cancel]

theorem upAd_dia : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hP res t hs hok g hg v' hv' a δ hb' ha hδ x
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.adelicForm_values_near_point_spec F E σ n J T f bad ι S emb v hv k p hb hP g hg
  by_cases hvv : v' = v
  · subst hvv
    have ha' := ha rfl
    unfold upAd
    rw [hP.2.2 x δ a hδ, h2 x δ hδ.1]
    refine finsum_mem_eq_of_bijOn (fun q => q.dil (a : k)) ?_ (fun q _ => (h3 a δ x q ha' hδ).symm)
    refine (dilEquiv ha').bijOn' ?_ ?_
    · intro q hq
      exact inc_dil hs (hok x) hq ha'
    · intro q hq
      have := inc_dil hs ((hok x).dil ha') hq (inv_ne_zero ha')
      rw [Pr.dil_dil, inv_mul_cancel₀ ha', Pr.dil_one] at this
      exact this
  · have hp : ∀ y, p (y * δ) = p y := fun y => (hP.2.1 y δ).2 (by
      rw [hδ.1 v (Ne.symm hvv)]; exact one_mem _)
    have key : valAt v p (fun y => g (y * δ)) x = valAt v p g (x * δ) := by
      funext q
      by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
      · have hc := h.choose_spec
        have e : x * δ * (δ⁻¹ * h.choose * δ) = x * h.choose * δ := by group
        have := h1 (x * δ) _ (atV_conj hc.1 δ)
        rw [e, hp, hc.2] at this
        rw [this]
        unfold valAt
        rw [dite_eq_left h]
      · have h' : ¬ ∃ η, AtV v η ∧ p (x * δ * η) = q := by
          rintro ⟨η, hη, hq⟩
          refine h ⟨δ⁻¹⁻¹ * η * δ⁻¹, atV_conj hη _, ?_⟩
          rw [← hp, ← hq]
          congr 1
          group
        unfold valAt
        rw [dite_eq_right h, dite_eq_right h']
    unfold upAd
    rw [hp, key]

end GlobalTheory.LevelHecke.UpDia
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamondStatement
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardHeckeOperator_commute_diamond : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  first | exact @GlobalTheory.LevelHecke.UpDia.upAd_dia | exact GlobalTheory.LevelHecke.UpDia.upAd_dia | (intros; apply GlobalTheory.LevelHecke.UpDia.upAd_dia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussian
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscPairDer

open MvPolynomial

variable {P Q : ℕ}

def derForm (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ) (T : MvPolynomial (Ix P Q) ℂ → ℂ)
    (f : MvPolynomial (Ix P Q) ℂ) : ℂ :=
  ∑ i, ∑ j, A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)) + ∑ l, x' l * T (pderiv l f)

theorem derForm_comb {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T U : MvPolynomial (Ix P Q) ℂ → ℂ) (a : ℂ) (b : κ → ℂ) (e : κ → Ix P Q)
    (hU : ∀ g, U g = a * T g + ∑ k, b k * T (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' U f = a * derForm A' x' T f + ∑ k, b k * derForm A' x' T (pderiv (e k) f) := by
  simp only [derForm, hU, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ i, ∑ j, ∑ k, A' i j * (b k * T (pderiv (e k) (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)))) =
      ∑ k, ∑ i, ∑ j, b k * (A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) (pderiv (e k) f)))) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset κ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  have h2 : ∑ l, ∑ k, x' l * (b k * T (pderiv (e k) (pderiv l f))) =
      ∑ k, ∑ l, b k * (x' l * T (pderiv l (pderiv (e k) f))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  rw [h1, h2]
  simp only [mul_left_comm a]
  ring

theorem pderiv_X_mul (m l : Ix P Q) (f : MvPolynomial (Ix P Q) ℂ) :
    pderiv m (X l * f) = X l * pderiv m f + if m = l then f else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  by_cases h : m = l
  · simp [h]
  · simp [h, Ne.symm h]

theorem derForm_X_inl (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inl i) * f) = derForm A' x' (fun g => T (X (Sum.inl i) * g)) f +
      (x' (Sum.inl i) * T f + ∑ j, A' i j * T (pderiv (Sum.inr j) f)) := by
  simp only [derForm, pderiv_X_mul, map_add (f := _), apply_ite T, map_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inl.injEq]
  rw [Finset.sum_comm (f := fun i' j => if i' = i then A' i' j * T (pderiv (Sum.inr j) f) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem derForm_X_inr (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inr j) * f) = derForm A' x' (fun g => T (X (Sum.inr j) * g)) f +
      (x' (Sum.inr j) * T f + ∑ i, A' i j * T (pderiv (Sum.inl i) f)) := by
  simp only [derForm, pderiv_X_mul, map_add (f := _), apply_ite T, apply_ite (pderiv _), map_zero, mul_add,
    Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inr.injEq]
  ring

def pair (F : Fock (Ix P Q)) (v : F.H) : MvPolynomial (Ix P Q) ℂ →+ ℂ where
  toFun f := inner ℂ (F.ι f) v
  map_zero' := by simp
  map_add' f g := by simp [inner_add_left]

theorem step {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : ℝ → MvPolynomial (Ix P Q) ℂ → ℂ) (l : Ix P Q) (a : ℝ → ℂ) (b : ℝ → κ → ℂ) (a' : ℂ) (b' : κ → ℂ)
    (e : κ → Ix P Q) (ha : HasDerivAt a a' 0) (hb : ∀ k, HasDerivAt (fun t => b t k) (b' k) 0)
    (hU : ∀ t g, T t (X l * g) = a t * T t g + ∑ k, b t k * T t (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ)
    (h0 : HasDerivAt (fun t => T t f) (derForm A' x' (T 0) f) 0)
    (h1 : ∀ m, HasDerivAt (fun t => T t (pderiv m f)) (derForm A' x' (T 0) (pderiv m f)) 0) :
    HasDerivAt (fun t => T t (X l * f)) (derForm A' x' (fun g => T 0 (X l * g)) f +
      (a' * T 0 f + ∑ k, b' k * T 0 (pderiv (e k) f))) 0 := by
  rw [derForm_comb A' x' (T 0) _ (a 0) (b 0) e (hU 0)]
  simp only [hU]
  refine ((ha.fun_mul h0).fun_add (HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => (hb k).fun_mul (h1 (e k)))).congr_deriv ?_
  rw [Finset.sum_add_distrib]
  ring

theorem hasDerivAt_inner_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  intro P Q F A x v A' x' hv hA hx f
  change HasDerivAt (fun t => pair F (v t) f) (derForm A' x' (pair F (v 0)) f) 0
  have key : ∀ (N : ℕ) (α : Ix P Q →₀ ℕ), α.degree ≤ N → ∀ c : ℂ,
      HasDerivAt (fun t => pair F (v t) (monomial α c)) (derForm A' x' (pair F (v 0)) (monomial α c)) 0 := by
    have h0 : ∀ c : ℂ, HasDerivAt (fun t => pair F (v t) (monomial 0 c))
        (derForm A' x' (pair F (v 0)) (monomial 0 c)) 0 := fun c => by
      have e : ∀ t, pair F (v t) (monomial 0 c) = (starRingEnd ℂ) c := fun t => by
        have e1 : (monomial 0 c : MvPolynomial (Ix P Q) ℂ) = c • monomial 0 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        change inner ℂ (F.ι (monomial 0 c)) (v t) = _
        rw [e1, map_smul, inner_smul_left, hv t 0]
        simp [expPS, MvPowerSeries.coeff_apply]
      simp only [e]
      refine (hasDerivAt_const _ _).congr_deriv ?_
      simp [derForm]
    intro N
    induction N with
    | zero =>
      intro α hα c
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
      exact h0 c
    | succ N ih =>
      intro α hα c
      by_cases hz : α = 0
      · subst hz; exact h0 c
      obtain ⟨l, hl⟩ : ∃ l, α l ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hz (Finsupp.ext hh)
      obtain ⟨β, rfl⟩ : ∃ β, α = Finsupp.single l 1 + β :=
        exists_add_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero hl))
      have hβ : β.degree ≤ N := by
        rw [map_add (f := _), Finsupp.degree_single] at hα
        omega
      have e : (monomial (Finsupp.single l 1 + β) c : MvPolynomial (Ix P Q) ℂ) = X l * monomial β c := by
        rw [X, monomial_mul, one_mul]
      have h1 : ∀ m, HasDerivAt (fun t => pair F (v t) (pderiv m (monomial β c)))
          (derForm A' x' (pair F (v 0)) (pderiv m (monomial β c))) 0 := fun m => by
        rw [pderiv_monomial]
        exact ih _ ((Finsupp.degree_mono tsub_le_self).trans hβ) _
      rw [e]
      rcases l with i | j
      · rw [derForm_X_inl]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inl i)) (fun t j => A t i j) _ _ Sum.inr
          (hx _) (hA i) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).1 i) _ (ih _ hβ c) h1
      · rw [derForm_X_inr]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inr j)) (fun t i => A t i j) _ _ Sum.inl
          (hx _) (fun i => hA i j) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).2 j) _ (ih _ hβ c) h1
  induction f using MvPolynomial.induction_on' with
  | monomial α c => exact key _ α le_rfl c
  | add f g hf hg =>
    simp only [map_add (f := _)]
    refine (hf.fun_add hg).congr_deriv ?_
    simp only [derForm, map_add (f := _), mul_add, Finset.sum_add_distrib]
    ring

end GlobalTheory.OscPairDer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  first | exact @GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | exact GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | (intros; apply GlobalTheory.OscPairDer.hasDerivAt_inner_gauss <;> assumption)
end
end
