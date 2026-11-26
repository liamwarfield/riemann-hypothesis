module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

theorem schurAll_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), SchurAll R :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ => GlobalTheory.MultFinite.schurMult hP _ _, GlobalTheory.MultFinite.schurMult hP _ _,
      fun _ => GlobalTheory.MultFinite.schurMult hP _ _⟩

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurConstantsExistOnChain_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), SchurAll R := by
  first | exact @GlobalTheory.Hk3.schurAll_of_cuspRapidDecay | exact GlobalTheory.Hk3.schurAll_of_cuspRapidDecay | (intros; apply GlobalTheory.Hk3.schurAll_of_cuspRapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
noncomputable section

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.PolynomialMatching

section Extend

variable {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def padFam (T S : Finset ι) (c : ∀ i, M i) (x : ∀ u : T, M u) : ∀ u : S, M u :=
  fun u => if h : u.1 ∈ T then x ⟨u.1, h⟩ else c u.1

theorem padFam_update (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) [DecidableEq T] [DecidableEq S]
    (x : ∀ u : T, M u) (i : T) (y : M i) :
    padFam T S c (Function.update x i y) = Function.update (padFam T S c x) ⟨i.1, hTS i.2⟩ y := by
  funext u
  by_cases h : u.1 ∈ T
  · by_cases hu : u.1 = i.1
    · obtain ⟨u, hu'⟩ := u
      obtain ⟨i, hi⟩ := i
      simp only at hu
      subst hu
      simp [padFam, h]
    · have h1 : (⟨u.1, h⟩ : T) ≠ i := fun e => hu (by rw [← e])
      have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => hu (by rw [e])
      simp only [padFam, h, dif_pos, Function.update_of_ne h1, Function.update_of_ne h2]
  · have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => h (by rw [e]; exact i.2)
    simp only [padFam, h, dif_neg, not_false_eq_true, Function.update_of_ne h2]

def padMultilinear (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (∀ u : T, M u) →ₘₗ[ℂ] (⨂[ℂ] u : S, M u) where
  toFun x := PiTensorProduct.tprod ℂ (padFam T S c x)
  map_update_add' x i y z := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i r y := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

def padTensor (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (⨂[ℂ] u : T, M u) →ₗ[ℂ] ⨂[ℂ] u : S, M u :=
  PiTensorProduct.lift (padMultilinear T S hTS c)

theorem padTensor_tprod (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) (x : ∀ u : T, M u) :
    padTensor T S hTS c (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (padFam T S c x) := by
  simp [padTensor, padMultilinear]

end Extend

theorem polMatchOn_insert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (v : Pl (F := F)),
    Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v) → ∀ (T : Finset (Pl (F := F))) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' →
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf (insert v T) Φ Φ' := by
  intro F E _ _ _ _ _ σ B a a' G X R Rf v hv T Φ Φ' hM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hM
  refine ⟨m, m', f, φ, f', φ',
    fun i => ⟨(hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(hφ' j).1, (hφ' j).2.1, fun w hw => (hφ' j).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    hΦ, hΦ', ?_⟩
  let c : ∀ u, Rf.Pi u := fun u => Rf.p u (G.M.vac u)
  have key := congrArg (LinearMap.lTensor R.Pi (padTensor T (insert v T) (Finset.subset_insert _ _) c)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, padTensor_tprod] at key
  have e1 : ∀ i, padFam T (insert v T) c (fun u : T => Rf.p u (φ i u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p u (φ i u) := by
    intro i
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · simp [padFam, h, c, (hφ i).2.2 u.1 h]
  have e2 : ∀ j, padFam T (insert v T) c (fun u : T => Rf.p' u (φ' j u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p' u (φ' j u) := by
    intro j
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · obtain ⟨u, hu⟩ := u
      have huv : u = v := by
        rcases Finset.mem_insert.1 hu with h' | h'
        · exact h'
        · exact absurd h' h
      subst huv
      simp [padFam, h, c, (hφ' j).2.2 u h, hv]
  simp only [e1, e2] at key
  exact key

end GlobalTheory.ThK.PolynomialMatching
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilUniq

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem weilDatum_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

end GlobalTheory.WeilUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_unique_on_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  first | exact @GlobalTheory.WeilUniq.weilDatum_unique | exact GlobalTheory.WeilUniq.weilDatum_unique | (intros; apply GlobalTheory.WeilUniq.weilDatum_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwOrbConj

variable {G : Type} [Group G]

theorem mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ GlobalTheory.BCT.rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mem_twCent (θ : G →* G) (δ x : G) : x ∈ GlobalTheory.BCT.twCent θ δ ↔ x * δ = δ * θ x := Iff.rfl

theorem relIndex_map_equiv (φ : G ≃* G) (H L : Subgroup G) :
    (H.map φ.toMonoidHom).relIndex (L.map φ.toMonoidHom) = H.relIndex L := by
  first
  | (rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.relIndex_comap, Subgroup.map_map]; simp)
  | exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
  | simp [Subgroup.relIndex]

theorem avg_left {H : Type} [Group H] (u : H → ℂ) (a : H) :
    GlobalTheory.BCT.avg (fun h => u (a * h)) = GlobalTheory.BCT.avg u := by
  have hR : GlobalTheory.BCT.rStab (fun h => u (a * h)) = GlobalTheory.BCT.rStab u := by
    ext k
    rw [mem_rStab, mem_rStab]
    constructor
    · intro h x
      simpa [mul_assoc] using h (a⁻¹ * x)
    · intro h x
      simpa [mul_assoc] using h (a * x)
  unfold GlobalTheory.BCT.avg
  rw [hR]
  congr 1
  have hc : ∀ q : H ⧸ GlobalTheory.BCT.rStab u, u (a * q.out) = u (a • q).out := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.BCT.rStab u) (a * q.out)
    have hq : (a • q) = (QuotientGroup.mk (a * q.out) : H ⧸ GlobalTheory.BCT.rStab u) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hr]
    exact ((mem_rStab u r).1 r.2 (a * q.out)).symm
  simp_rw [hc]
  exact finsum_comp_equiv (f := fun q : H ⧸ GlobalTheory.BCT.rStab u => u q.out) (MulAction.toPerm a)

theorem map_conj_self (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom = (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twCent_conj (θ : G →* G) (δ g : G) :
    GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) = (GlobalTheory.BCT.twCent θ δ).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have e : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by simp [MulAut.conj_symm_apply]
  rw [e, mem_twCent, mem_twCent, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc g * x * g⁻¹ * δ = g * (x * (g⁻¹ * δ * θ g)) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g * θ x) * (θ g)⁻¹ := by rw [h]
      _ = δ * (θ g * θ x * (θ g)⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * δ * θ g) = g⁻¹ * (g * x * g⁻¹ * δ) * θ g := by group
      _ = g⁻¹ * (δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by rw [h]
      _ = g⁻¹ * δ * θ g * θ x := by group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map (c : G) (T : Subgroup G) :
    GlobalTheory.BCT.cptPart (T.map (MulAut.conj c).toMonoidHom) = (GlobalTheory.BCT.cptPart T).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure]
  congr 1
  let h : G ≃ₜ G := (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)
  have hh : ∀ x, h x = (MulAut.conj c).toMonoidHom x := fun x => by
    simp [h, MulAut.conj_apply]
  have hz : ∀ t, (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) = h '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    ext y
    simp only [Set.mem_image, hh]
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem relIndex_conj (c : G) (T T' L L' : Subgroup G) (hT : T' = T.map (MulAut.conj c).toMonoidHom)
    (hL : L' = L.map (MulAut.conj c).toMonoidHom) :
    (T' ⊓ L').relIndex (GlobalTheory.BCT.cptPart T') = (T ⊓ L).relIndex (GlobalTheory.BCT.cptPart T) := by
  subst hT hL
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, cptPart_map, relIndex_map_equiv]

def summand (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ) *
    GlobalTheory.BCT.avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
      summand θ K δ f (Quotient.out q) := rfl

theorem summand_rep (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) {t k : G}
    (ht : t ∈ GlobalTheory.BCT.twCent θ δ) (hk : k ∈ K) : summand θ K δ f (t * y * k) = summand θ K δ f y := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj t _ _ _ _ (map_conj_self _ ht).symm
      (by rw [map_conj_mul, map_conj_mul, map_conj_self K hk]))
  · have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have hfun : (fun k' : K => f ((t * y * k * k')⁻¹ * δ * θ (t * y * k * k'))) =
        fun k' : K => (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) (⟨k, hk⟩ * k') := by
      funext k'
      congr 1
      simp only [Subgroup.coe_mul]
      calc (t * y * k * ↑k')⁻¹ * δ * θ (t * y * k * ↑k')
          = (y * (k * ↑k'))⁻¹ * (t⁻¹ * δ * θ t) * θ (y * (k * ↑k')) := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = (y * (k * ↑k'))⁻¹ * δ * θ (y * (k * ↑k')) := by rw [hd]
    rw [hfun]
    exact avg_left (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) ⟨k, hk⟩

theorem summand_twist (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) (x : G) :
    summand θ K (g⁻¹ * δ * θ g) f x = summand θ K δ f (g * x) := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj g⁻¹ _ _ _ _ (twCent_conj θ δ g)
      (by rw [← map_conj_mul, inv_mul_cancel_left]))
  · congr 1
    funext k
    congr 1
    simp only [map_mul, _root_.mul_inv_rev]
    group

def dcEquiv (θ : G →* G) (K : Subgroup G) (δ g : G) :
    DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) : Set G) (K : Set G) ≃
      DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) where
  toFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
  invFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
  left_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
    show DoubleCoset.mk _ K (g⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) (K := K) q]
    rw [DoubleCoset.eq]
    refine ⟨g⁻¹ * t⁻¹ * g, ?_, k⁻¹, K.inv_mem hk, by group⟩
    rw [twCent_conj]
    exact ⟨t⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem ht, by simp [MulAut.conj_apply]⟩
  right_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
    show DoubleCoset.mk _ K (g * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K
      (g⁻¹ * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ δ) (K := K) q]
    rw [DoubleCoset.eq]
    rw [twCent_conj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem hs, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.TwOrbConj

namespace GlobalTheory.TwOrbConj

theorem twOrb_twConj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), (∀ x : G, (GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f _
  rw [twOrb_eq, twOrb_eq]
  calc ∑ᶠ q, summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, summand θ K δ f (Quotient.out (dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ :=
          DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
        show _ = summand θ K δ f (Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)))
        rw [he, summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) =>
          summand θ K δ f (Quotient.out q)) (dcEquiv θ K δ g)

end GlobalTheory.TwOrbConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariantStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_twistedConj_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → twOrb θ K (g⁻¹ * δ * θ g) f = twOrb θ K δ f := by
  first | exact @GlobalTheory.TwOrbConj.twOrb_twConj | exact GlobalTheory.TwOrbConj.twOrb_twConj | (intros; apply GlobalTheory.TwOrbConj.twOrb_twConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.CurveDegreesCompare


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI := (g.residueFieldMap (f x)).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((f ≫ g).residueFieldMap x).hom = _
    rw [Scheme.residueFieldMap_comp]
    rfl
  change Module.finrank (Z.residueField (g (f x))) (X.residueField x) =
    Module.finrank (Z.residueField (g (f x))) (Y.residueField (f x)) *
      Module.finrank (Y.residueField (f x)) (X.residueField x)
  exact (Module.finrank_mul_finrank _ _ _).symm


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits in
theorem _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)
  let e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

variable {C}

end Clauses

end GlobalTheory.CurveDegreesCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.FibreProj

variable {ι : Type} [Fintype ι]


open Classical in
def pol (φ : (ι → ℤ) → ℝ) : ℝ := ∑ S : Finset ι, (-1 : ℝ) ^ S.card * φ fun i => if i ∈ S then -1 else 0


set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.FibreProj.pol_sum {J : Type} (T : Finset J)
    (φ : J → (ι → ℤ) → ℝ) :
    _root_.GlobalTheory.FibreProj.pol (fun n => ∑ j ∈ T, φ j n) =
      ∑ j ∈ T, _root_.GlobalTheory.FibreProj.pol (φ j) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
private theorem sum_pow_eq_sum_words_prod {R : Type} [CommRing R] (c : ι → R) (D : ℕ) :
    (∑ i, c i) ^ D = ∑ f : Fin D → ι, ∏ k, c (f k) := by
  rw [← Fin.prod_const, Fintype.prod_sum]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_range_subset_eq_ite_surjective {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (f : Fin D → ι) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  have hr : ∀ t : Finset ι, (∏ i ∈ t, (-1 : R)) *
      ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) =
        (-1) ^ t.card * (if ∀ k, f k ∈ t then 1 else 0) := by
    intro t
    rw [Finset.prod_const, Finset.prod_ite_zero, Finset.prod_const_one]
    have hiff : (∀ i ∈ Finset.univ \ t, i ∉ Set.range f) ↔ ∀ k, f k ∈ t := by
      constructor
      · intro h k
        by_contra hk
        exact h (f k) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hk⟩) ⟨k, rfl⟩
      · rintro h i hi ⟨k, rfl⟩
        exact (Finset.mem_sdiff.1 hi).2 (h k)
    simp only [hiff]
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)
      = ∑ t ∈ (Finset.univ : Finset ι).powerset, (∏ i ∈ t, (-1 : R)) *
          ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun t _ => (hr t).symm
    _ = ∏ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) := (Finset.prod_add _ _ _).symm
    _ = _ := by
        split_ifs with hs
        · have h1 : ∀ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) = -1 := fun i => by
            rw [if_neg (show ¬(i ∉ Set.range f) from not_not.2 (hs i)), add_zero]
          simp only [h1, Finset.prod_const, Finset.card_univ, hD]
        · simp only [Function.Surjective, not_forall] at hs
          obtain ⟨i, hi⟩ := hs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos (show i ∉ Set.range f from fun h => hi h)]; ring)

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_surjective_words_prod_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ f : Fin D → ι, (∏ k, w (f k)) * (if Function.Surjective f then (-1 : R) ^ D else 0) =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  have hbij : ∀ f : Fin D → ι, Function.Surjective f → Function.Bijective f := fun f hf =>
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, by rw [Fintype.card_fin, hD]⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hprod : ∀ f ∈ Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f),
      (∏ k, w (f k)) * (-1 : R) ^ D = (∏ i, w i) * (-1) ^ D := by
    intro f hf
    rw [← Equiv.prod_comp (Equiv.ofBijective f (hbij f (Finset.mem_filter.1 hf).2)) w]
    rfl
  have e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hD).symm
  have hcard : (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card =
      D.factorial := by
    calc (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card
        = (Finset.univ.map ⟨fun σ : Fin D ≃ ι => (σ : Fin D → ι),
            DFunLike.coe_injective⟩).card := by
          congr 1
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          constructor
          · intro hf
            exact ⟨Equiv.ofBijective f (hbij f hf), rfl⟩
          · rintro ⟨σ, rfl⟩
            exact σ.surjective
      _ = Fintype.card (Fin D ≃ ι) := by rw [Finset.card_map, Finset.card_univ]
      _ = D.factorial := by rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D
      = ∑ S : Finset ι, ∑ f : Fin D → ι,
          (∏ k, w (f k)) * ((-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_pow_eq_sum_words_prod, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.prod_ite_zero]
        simp only [Finset.mem_univ, true_implies]
        split_ifs <;> ring
    _ = ∑ f : Fin D → ι, (∏ k, w (f k)) *
          (if Function.Surjective f then (-1 : R) ^ D else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.mul_sum, sum_neg_one_pow_card_range_subset_eq_ite_surjective hD f]
    _ = _ := sum_surjective_words_prod_eq_factorial_prod hD w


set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
theorem _root_.GlobalTheory.FibreProj.pol_pow {R : Type} [CommRing R]
    [Algebra ℝ R] (z : ι → R) (Φ : R →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    _root_.GlobalTheory.FibreProj.pol (fun n => Φ ((∑ i, (n i : ℝ) • z i) ^ D)) =
      D.factorial * Φ (∏ i, z i) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  have hsum : ∀ S : Finset ι, (∑ i, (((if i ∈ S then -1 else 0 : ℤ) : ℝ)) • z i) =
      ∑ i, if i ∈ S then -z i else 0 := by
    intro S
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [hsum]
  have hterm : ∀ (k : ℕ) (x : R), Φ ((-1 : R) ^ k * x) = (-1 : ℝ) ^ k * Φ x := by
    intro k x
    rw [← smul_eq_mul ((-1 : ℝ) ^ k), ← map_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  have h1 : ((-1 : R) ^ D) * (-1) ^ D = 1 := by rw [← mul_pow]; simp
  have hfinal : Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) = D.factorial * Φ (∏ i, z i) := by
    rw [Finset.prod_neg, Finset.card_univ, hD]
    calc Φ ((-1) ^ D * D.factorial * ((-1) ^ D * ∏ i, z i))
        = Φ ((D.factorial : ℝ) • ∏ i, z i) := by
          congr 1
          rw [Algebra.smul_def, map_natCast]
          linear_combination (↑D.factorial * ∏ i, z i) * h1
      _ = _ := by rw [map_smul, smul_eq_mul]
  calc ∑ S : Finset ι, (-1 : ℝ) ^ S.card * Φ ((∑ i, if i ∈ S then -z i else 0) ^ D)
      = Φ (∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then -z i else 0) ^ D) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [hterm]
    _ = Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) :=
        congrArg Φ (sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod hD fun i => -z i)
    _ = _ := hfinal

end GlobalTheory.FibreProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
noncomputable section

open NumberField GlobalTheory.BCT GlobalTheory.CuspRep Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def mulMat (a : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)).map e

def gram (β : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  Matrix.of fun i j => e (B.herm β (b i) (b j))

def dlt (β : B.A) : GLw m w :=
  if h : IsUnit (gram e b β) then invT m _ h.unit * (PhiU m _)⁻¹ else 1

def lat (g : GLw m w) : Submodule K.O B.A :=
  Submodule.span K.O (Set.range fun j => ∑ i, e.symm (g.val i j) • b i)

end GlobalTheory.TwLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Ker GlobalTheory.Ker.HatLat GlobalTheory.ThetaSpace
open scoped TensorProduct

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem parts_eInf_smul (a : AE D) :
    finPart D (FinTranslate.eInf D • a) = 0 ∧ infPart D (a - FinTranslate.eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, sub_zero, map_zero, and_self]
  | add a b ha hb =>
    refine ⟨by rw [smul_add, RingHom.map_add (f := _), ha.1, hb.1, add_zero], ?_⟩
    rw [smul_add, add_sub_add_comm, RingHom.map_add (f := _), ha.2, hb.2, add_zero]
  | tmul a x =>
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    constructor
    · show (sndA D.host.F (FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show sndA D.host.F (FinTranslate.eInf D • a) = 0 from zero_mul _, TensorProduct.zero_tmul]
    · show (fstA D.host.F (a - FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show fstA D.host.F (a - FinTranslate.eInf D • a) = 0 from
        (show a.1 - 1 * a.1 = 0 by rw [one_mul, sub_self]), TensorProduct.zero_tmul]

theorem exists_fin_add_real (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v :=
  ⟨w - FinTranslate.eInf D • w, FinTranslate.eInf D • w, Matrix.ext fun i j => (parts_eInf_smul (w i j)).2,
    Matrix.ext fun i j => (parts_eInf_smul (w i j)).1, (sub_add_cancel _ _).symm⟩

theorem isTheta_heisO (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 (WeilVacMove.isTheta_heisO_real hψ hv hf) hu
  rwa [WeilVacMove.heisO_heisO, (WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h

theorem theta_eq_zero_of_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  have hΛ := stdL_full D.host.E S.rank
  have hL := stdL_full D.host.E T.rank
  have hO : ∀ c : 𝓞 D.host.F, ∀ y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank),
      (c : D.host.F) • y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank) := fun c y hy =>
    smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem_open (F := D.host.F) (tens_fg _ _ hΛ.1 hL.1) U hU
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  obtain ⟨y, hy⟩ := exists_rat (F := D.host.F) (tens_den _ _ hΛ.2 hL.2) hu
  obtain ⟨y', -, u', hu', e⟩ := exists_mod hO hN hy
  have hfin : IsFinPt (S := S) (T := T) (N • u') := isFinPt_nsmul (inf_eq_zero_of_mem (F := D.host.F) hu') N
  have hr0 : IsRealPt (ratW T S (y + y')ᵀ - finW S T (y + y')) := by
    funext a k
    show finPart D (incA D ((y + y') k a) - finW S T (y + y') a k) = 0
    rw [RingHom.map_sub]
    exact sub_eq_zero.2 rfl
  have hr := isRealPt_sub hv hr0
  have e0 : finW S T (y + y') = fT D.host.F 1 y + fT D.host.F 1 y' := (fT D.host.F 1).map_add y y'
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [e0, sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl _ (hNU u' hu') hfin) (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold heisO at e2
  rw [(WeilVacMove.symplOH_fin_real S T _ _ hfin hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

end Theta

section Can

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Can

section Const

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Const

end GlobalTheory.TwistFactorCompare

end
end
