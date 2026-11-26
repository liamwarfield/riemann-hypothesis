module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem finiteAdeleRingAway_eq_of_forall_eval_eq {p : ℕ} {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  RestrictedProduct.ext (R := fun v : AwayP p => v.1.adicCompletion ℚ) _ h

theorem basV_repr_map {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (x : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) x) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem ext_of_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf),
    (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  intro p _ G g g' h
  have h1 : ∀ v : AwayP p, Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) =
      Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C))) (h v)
  have h2 : ∀ v : AwayP p, AfP.eval v (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) =
      AfP.eval v (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v))) (h v)
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).ext_elem
    intro i
    apply finiteAdeleRingAway_eq_of_forall_eval_eq
    intro v
    rw [← basV_repr_map, ← basV_repr_map, h1 v]
  · apply Units.ext
    exact finiteAdeleRingAway_eq_of_forall_eval_eq h2

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_ext_of_components : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf), (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  first | (exact @GlobalTheory.OrbFinAf.ext_of_piV) | (exact GlobalTheory.OrbFinAf.ext_of_piV) | (intros; apply GlobalTheory.OrbFinAf.ext_of_piV  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem continuous_gAf_fst (G : HTGroup p) :
    @Continuous G.GAf (AfP p ⊗[ℚ] G.C) _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C))
      (fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_gAf_snd_inv (G : HTGroup p) :
    Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

theorem exists_compact_of_isTest (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (h₁ : G.GAf) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f (h₁⁻¹ * g * h₁) ≠ 0 → g ∈ Q := by
  obtain ⟨S, hS⟩ := hf.2.2.2
  have hK : IsCompact (L.K : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => h₁ * (q.1 * s * q.2) * h₁⁻¹) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hg
  refine Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, ?_⟩
  show h₁ * (k₁ * s * k₂) * h₁⁻¹ = g
  rw [← he]; group

theorem exists_compact_toAfF : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (h₁ : G.GAf), ∃ (Ω : Set (AfP p ⊗[ℚ] G.C)) (Ω' : Set (AfP p)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) Ω ∧ IsCompact Ω' ∧ ∀ y : grp G β,
    f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ Ω ∧
    algebraMap ℚ (AfP p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹) ∈ Ω' := by
  intro p _ G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  obtain ⟨Q, hQ, hmem⟩ := exists_compact_of_isTest G L f hf h₁
  refine ⟨(fun g : G.GAf => ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * x) '' Q,
    (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) '' Q,
    hQ.image ((continuous_const.mul (continuous_gAf_fst G)).mul continuous_const),
    hQ.image (continuous_gAf_snd_inv G), fun y hy => ⟨⟨_, hmem _ hy, ?_⟩, ⟨_, hmem _ hy, ?_⟩⟩⟩
  · show ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      ((x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
        AfP p ⊗[ℚ] G.C) * x = _
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · show (((Units.map (algebraMap ℚ (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).2))⁻¹ : (AfP p)ˣ) : AfP p) = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl

end GlobalTheory.LKCx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicit
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem continuous_tensorMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [Algebra ℚ R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
    letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
    Continuous (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsModuleTopology R' (R' ⊗[ℚ] C) := ⟨rfl⟩
  haveI : ContinuousAdd (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousAdd R' _
  haveI : ContinuousSMul R' (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousSMul R' _
  let b := Module.finBasis ℚ C
  let bA := Algebra.TensorProduct.basis R b
  let bB := Algebra.TensorProduct.basis R' b
  have key : ∀ x, Algebra.TensorProduct.map f (AlgHom.id ℚ C) x = ∑ i, f (bA.repr x i) • bB i := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bA, bB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id ℚ C))) = fun x => ∑ i, f (bA.repr x i) • bB i := funext key
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (hf.comp (IsModuleTopology.continuous_of_linearMap (bA.coord i))).smul continuous_const

theorem continuous_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  intro p _ G v
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) _
  have hf : Continuous (AfP.eval v) := RestrictedProduct.continuous_eval v
  have hφ := continuous_tensorMap (C := G.C) (AfP.eval v) hf
  have h1 := Units.continuous_map (f := (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom) hφ
  have h2 := Units.continuous_map (f := (AfP.eval v).toRingHom.toMonoidHom) hf
  refine continuous_induced_rng.2 ?_
  exact (h1.comp (continuous_fst.comp continuous_subtype_val)).prodMk (h2.comp (continuous_snd.comp continuous_subtype_val))

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.continuous_piV) | (exact GlobalTheory.OrbFinAf.continuous_piV) | (intros; apply GlobalTheory.OrbFinAf.continuous_piV  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSuppor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSuppor
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

noncomputable def finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : (Fin N → Af F) →+ VA F N where
  toFun v := (0, fun i => pairA F 0 (v i))
  map_zero' := rfl
  map_add' v w := by
    refine Prod.ext (add_zero _).symm ?_
    funext i
    exact Prod.ext (add_zero _).symm rfl

theorem continuous_finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : Continuous (finEmbSnd F N) :=
  continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))

theorem dotProduct_finEmbSnd {F : Type} [Field F] [NumberField F] {N : ℕ} (x : Fin N → AF F) (v : Fin N → Af F) :
    x ⬝ᵥ (finEmbSnd F N v).2 = pairA F 0 (Bd (Af F) (half F N) (fin x) v) := by
  have h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i := by
    simp [Bd, half]
  rw [h]
  refine Prod.ext ?_ ?_
  · change fstA F (∑ i, x i * pairA F 0 (v i)) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _
  · change sndA F (∑ i, x i * pairA F 0 (v i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl

theorem invV_level_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  intro F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl
  obtain ⟨U, hU, hf⟩ := hl
  have h0 : inf (0 : Fin N → AF F) = 0 := rfl
  refine ⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)),
    hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · intro u hu hi x
    rw [← invV_heisV_fst, hf (u, 0) hu hi h0]
  · refine ⟨_, (GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N))
      (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩
    have h1 := invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x
    rw [show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl,
      dotProduct_finEmbSnd] at h1
    exact mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)

end GlobalTheory.ThetaTransform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSupporStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  first | exact @GlobalTheory.ThetaTransform.invV_level_support | exact GlobalTheory.ThetaTransform.invV_level_support | (intros; apply GlobalTheory.ThetaTransform.invV_level_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormsAndIntegrality
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.IntAwayP

theorem norm_self_padicAlgCl (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at this
  rw [this, Padic.norm_p]

theorem norm_prime_padicAlgCl_of_ne (ℓ p : ℕ) [hℓ : Fact ℓ.Prime] (hp : p.Prime) (h : ℓ ≠ p) :
    ‖(p : PadicAlgCl ℓ)‖ = 1 := by
  have h1 := PadicAlgCl.norm_extends ℓ (p : ℚ_[ℓ])
  rw [map_natCast] at h1
  rw [h1]
  have h2 : ‖(p : ℤ_[ℓ])‖ = 1 := (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.coprime_primes hℓ.out hp).2 h)
  rw [← h2, PadicInt.norm_def]
  simp

theorem isIntegral_of_pow_mul (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (z : K) (N : ℕ) (hN : IsIntegral ℤ ((p : K) ^ N * z))
    (h : ∀ φ : K →+* PadicAlgCl p, ‖φ z‖ ≤ 1) : IsIntegral ℤ z := by
  refine GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one K z fun q _ τ => ?_
  by_cases hq : q = p
  · subst hq; exact h τ
  · have h1 : ‖τ ((p : K) ^ N * z)‖ ≤ 1 :=
      GlobalTheory.norm_le_one_of_isIntegral_int (hN.map τ.toIntAlgHom)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      norm_prime_padicAlgCl_of_ne q p hp.out hq, one_pow, one_mul] at h1
    exact h1

theorem exists_pow_mul_isIntegral : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  intro K _ _ p _ B
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt B hp1
  refine ⟨m₀, fun c D ⟨m, hm⟩ hB => ?_⟩
  apply isIntegral_of_pow_mul K p _ m
  · have e : (p : K) ^ m * ((p : K) ^ m₀ * D * c) = (p : K) ^ m₀ * ((p : K) ^ m * D * c) := by ring
    rw [e]
    have hpi : IsIntegral ℤ ((p : K) ^ m₀) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (p : ℤ))).pow m₀
    exact hpi.mul hm
  · intro φ
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast, norm_mul, norm_mul, norm_pow,
      norm_self_padicAlgCl]
    have hD := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) D
    have h2 : ‖(D : PadicAlgCl p)‖ * ‖φ c‖ ≤ (p : ℝ) ^ m₀ :=
      (mul_le_of_le_one_left (norm_nonneg _) hD).trans ((hB φ).trans hm₀.le)
    rw [mul_assoc, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h2

end GlobalTheory.IntAwayP
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominator_integral_power : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  first | (exact @GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (exact GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (intros; apply GlobalTheory.IntAwayP.exists_pow_mul_isIntegral <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_smul_eq_of_eigvec_of_charpoly_separable {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g.charpoly.Separable) {μ : ℂ} {x y : Fin n → ℂ} (hx0 : x ≠ 0)
    (hx : g *ᵥ x = μ • x) (hy : g *ᵥ y = μ • y) : ∃ c : ℂ, y = c • x := by
  set f := Matrix.toLin' g
  have hc : f.charpoly = g.charpoly := Matrix.charpoly_toLin' g
  have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, hc]
    exact Polynomial.rootMultiplicity_le_one_of_separable hg μ
  have mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ := fun v hv => by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp [f, hv]⟩
  have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
    (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ)
    fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem form_conjTranspose_mul_mul {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ (gᴴ * A * g) *ᵥ v = star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eigvec_pos_unique_of_similitude : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    A.det ≠ 0 → sigPosH hA = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s →
    gᴴ * A * g = (s : ℂ) • A → g.charpoly.Separable → ∀ x y : Fin n → ℂ,
    0 < (star x ⬝ᵥ A *ᵥ x).re → 0 < (star y ⬝ᵥ A *ᵥ y).re →
    (∃ μ : ℂ, g *ᵥ x = μ • x) → (∃ ν : ℂ, g *ᵥ y = ν • y) → ∃ c : ℂ, y = c • x := by
  intro n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxp
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyp
  have Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v) := by
    intro u v
    rw [← form_conjTranspose_mul_mul, hsim]
    have e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v) := by
      exact Matrix.smul_mulVec (s : ℂ) A v
    rw [e, dotProduct_smul, smul_eq_mul]
  have scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v) := by
    intro a b u v
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hxp; simp at hxp
  have hQy : star y ⬝ᵥ A *ᵥ y ≠ 0 := fun h => by rw [h] at hyp; simp at hyp
  have eμ : star μ * μ = (s : ℂ) := by
    have := Q x x; rw [hμ, scal] at this; exact mul_right_cancel₀ hQx this
  have eν : star ν * ν = (s : ℂ) := by
    have := Q y y; rw [hν, scal] at this; exact mul_right_cancel₀ hQy this
  have exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0 := by
    have := Q x y; rw [hμ, hν, scal] at this; rw [sub_mul, this, sub_self]
  by_cases hμν : μ = ν
  · subst hμν
    exact exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν
  · exfalso
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hμ0 : star μ ≠ 0 := fun h => hs0 (by rw [← eμ, h, zero_mul])
    have hne : star μ * ν - s ≠ 0 := by
      intro h
      apply hμν
      have : star μ * ν = star μ * μ := by rw [eμ]; exact sub_eq_zero.1 h
      exact (mul_left_cancel₀ hμ0 this).symm
    have horth : star x ⬝ᵥ A *ᵥ y = 0 := (mul_eq_zero.1 exy).resolve_left hne
    have := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMem
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

section General

variable {C : Type} [Ring C] [Algebra ℚ C] {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ C)
  {R : Type} [CommRing R] [Algebra ℚ R] (S : Subring R)

theorem repr_mul_mem (hc : ∀ i j k, algebraMap ℚ R (b.repr (b i * b j) k) ∈ S)
    {y y' : R ⊗[ℚ] C} (hy : ∀ i, (Algebra.TensorProduct.basis R b).repr y i ∈ S)
    (hy' : ∀ i, (Algebra.TensorProduct.basis R b).repr y' i ∈ S) (k : ι) :
    (Algebra.TensorProduct.basis R b).repr (y * y') k ∈ S := by
  set B := Algebra.TensorProduct.basis R b
  have hB : ∀ i j, B.repr (B i * B j) k = algebraMap ℚ R (b.repr (b i * b j) k) := by
    intro i j
    simp [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  rw [← B.sum_repr y, ← B.sum_repr y', Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [smul_mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, hB]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.mul_mem (S.mul_mem (hy i) (hy' j)) (hc i j k)

end General

theorem eventually_rat_mem (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (show Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] from
    algebraMap ℚ (AfP p) q).2
  filter_upwards [h] with v hv
  have e : (AfP.eval v) (algebraMap ℚ (AfP p) q) = algebraMap ℚ (Qv v) q := (AfP.eval v).commutes q
  rw [← e]
  exact hv

theorem mul_mem_IntV_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  intro p _ G
  have hall : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k,
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem p _
  filter_upwards [hall] with v hv
  intro a ha a' ha'
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨h1', h2', h3', h4'⟩ := ha'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h1 h1' k
    simpa [IsIntV, basV] using this
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h2' h2 k
    simpa [IsIntV, basV, _root_.mul_inv_rev] using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h3 h3'
    simpa using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h4' h4
    simpa [_root_.mul_inv_rev] using this

end GlobalTheory.OrbFinAf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (exact GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (intros; apply GlobalTheory.OrbFinAf.mul_mem_IntV_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarPreservesIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeUnimodular
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem rat_valuation_le_one_eventually (x : ℚ) :
    ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite, w.valuation ℚ x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

variable {p : ℕ} [Fact p.Prime]

theorem rat_mem_integers_eventually (x : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), algebraMap ℚ (Qv v) x ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (Function.Injective.tendsto_cofinite (f := fun v : AwayP p => v.1) Subtype.val_injective).eventually
    (rat_valuation_le_one_eventually x)
  filter_upwards [h] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 x).trans_le hv

def starLin (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] : (R ⊗[ℚ] G.C) →ₗ[R] (R ⊗[ℚ] G.C) where
  toFun a := (starT G.star R a).unop
  map_add' x y := by rw [map_add (f := _), MulOpposite.unop_add]
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      rw [TensorProduct.smul_tmul', starT_tmul, starT_tmul, TensorProduct.smul_tmul', RingHom.id_apply]
    | add x y hx hy =>
      rw [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, map_add (f := _), MulOpposite.unop_add, smul_add]

theorem starLin_apply (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (a : R ⊗[ℚ] G.C) :
    starLin G R a = (starT G.star R a).unop := rfl

theorem isIntV_star_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a →
      IsIntV G v (starT G.star (Qv v) a).unop := by
  intro p _ G
  have hs : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (G.star (Module.finBasis ℚ G.C ij.2)).unop ij.1)
          ∈ v.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun ij => rat_mem_integers_eventually _
  filter_upwards [hs] with v hv a ha i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← starLin_apply, ← (basV G v).sum_repr a, map_sum, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun j _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine mul_mem (ha j) ?_
  have hb : basV G v j = (1 : Qv v) ⊗ₜ Module.finBasis ℚ G.C j := by
    simp [basV, Algebra.TensorProduct.basis_apply]
  rw [hb, starLin_apply, starT_tmul, basV, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]
  exact hv (i, j)

end GlobalTheory.OrbFinAf
end
end

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_preserves_integrality : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v (starT G.star (Qv v) a).unop := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_star_eventually) | (exact GlobalTheory.OrbFinAf.isIntV_star_eventually) | (intros; apply GlobalTheory.OrbFinAf.isIntV_star_eventually  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositive
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem diag_sign_of_pos_eigenvector : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  intro n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos
  have key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ),
      star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u' := by
    intro N B u u'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  have hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ)) := by
    rw [← hZ, hh, hM, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y :=
    ⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hy : ∀ i, i ≠ i₀ → y i = 0 := by
    have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y)
        = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y) := by
      rw [mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]
    have h2 : diagonal lam *ᵥ y = lam i₀ • y := by
      have := congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec] using this
    intro i hi
    have h3 := congrFun h2 i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    have h4 : (lam i - lam i₀) * y i = 0 := by rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (hlam (sub_eq_zero.mp h5)) hi
    · exact h5
  have hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y)
      = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ) := by
    rw [key, hZ]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hform, Complex.ofReal_re] at hxpos
  have hd0 : 0 < d i₀ := by
    by_contra hc
    push_neg at hc
    nlinarith [Complex.normSq_nonneg (y i₀)]
  refine ⟨hd0, fun i hi => ?_⟩
  have hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1 := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul,
      Matrix.one_mul, Units.inv_mul]
  have hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1)
      = if j = k then (d j : ℂ) else 0 := by
    intro j k
    rw [key, hMd]
    by_cases hjk : j = k
    · subst hjk; simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    · simp [dotProduct, mulVec_diagonal, Pi.single_apply, hjk]
      intro hkj; exact absurd hkj.symm hjk
  have hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0
    simp only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this
    have := congrFun this i
    simp at this
  have hneg := re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1)
    (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne
  rw [hval, if_pos rfl, Complex.ofReal_re] at hneg
  exact hneg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositiveStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  first | (exact @GlobalTheory.diag_sign_of_pos_eigenvector) | (exact GlobalTheory.diag_sign_of_pos_eigenvector) | (intros; apply GlobalTheory.diag_sign_of_pos_eigenvector  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q.1) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W : HeightOneSpectrum (𝓞 E)), SplitsFully E (W.under (𝓞 F)) → ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  first | exact @GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | exact GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | (intros; apply GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompact
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem isCompact_setOf_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C);
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K →
      IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  letI tA : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := T2Space.of_injective_continuous (basV G v).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap)
  have hst1 : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sL : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun y => (starT G.star (Qv v) y).unop
      map_add' := fun x y => by simp
      map_smul' := fun r y => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hst1]
        exact (Algebra.commutes r _).symm }
  have hsc : Continuous sL := IsModuleTopology.continuous_of_linearMap sL
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := Qv v) (s := ({()} : Set Unit))
    (v := fun _ : Unit => (1 : Qv v ⊗[ℚ] G.C)) (by
      rw [linearIndepOn_singleton_iff]; exact one_ne_zero)
  have hf1 : f 1 = 1 := hf () rfl
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have key : ∀ d : Gv G v, f (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C) *
      sL ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)) =
      (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    intro d
    have hd : (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := d.2
    show f (_ * (starT G.star (Qv v) _).unop) = _
    rw [hd, Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_eq_mul, mul_one]
  set L1 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ => f ((u : Qv v ⊗[ℚ] G.C) * sL u)) '' K with hL1
  set L2 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ =>
    f (((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sL ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))) '' K with hL2
  have hL1c : IsCompact L1 := hK.image (hfc.comp (Units.continuous_val.mul (hsc.comp Units.continuous_val)))
  have hL2c : IsCompact L2 := hK.image (hfc.comp (Units.continuous_coe_inv.mul (hsc.comp Units.continuous_coe_inv)))
  set T : Set (Qv v)ˣ := Units.embedProduct (Qv v) ⁻¹' (L1 ×ˢ (MulOpposite.op '' L2)) with hT
  have hTc : IsCompact T :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hL1c.prod (hL2c.image MulOpposite.continuous_op))
  set Z : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ) := {x | ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      sL ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((x.2 : (Qv v)ˣ) : Qv v)} with hZ
  have hZc : IsClosed Z := isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul (hsc.comp (Units.continuous_val.comp continuous_fst)))
    ((continuous_algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (Units.continuous_val.comp continuous_snd))
  have himg : Subtype.val '' {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} = (K ×ˢ T) ∩ Z := by
    ext x
    constructor
    · rintro ⟨d, hdK, rfl⟩
      have k2 := key d⁻¹
      simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv] at k2
      refine ⟨⟨hdK, ?_⟩, d.2⟩
      show Units.embedProduct (Qv v) _ ∈ L1 ×ˢ (MulOpposite.op '' L2)
      rw [Units.embedProduct_apply]
      exact ⟨⟨_, hdK, key d⟩, ⟨_, ⟨_, hdK, k2⟩, rfl⟩⟩
    · rintro ⟨⟨hK1, -⟩, hZ1⟩
      exact ⟨⟨x, hZ1⟩, hK1, rfl⟩
  exact Subtype.isCompact_iff.2 (himg ▸ (hK.prod hTc).inter_right hZc)

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryPointsAtPlace_fst_mem_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K → IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (exact GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem) | (intros; apply GlobalTheory.OrbFinAf.isCompact_setOf_fst_mem  <;> assumption)
end
end
