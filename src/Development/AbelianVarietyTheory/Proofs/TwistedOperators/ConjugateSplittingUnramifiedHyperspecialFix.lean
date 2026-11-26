module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacFix

open GlobalTheory.Hk3 GlobalTheory.WeilParts GlobalTheory.IdemSupport

variable {D : D7}

theorem infPart_eq_one {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {x : AE D}
    (hx : f * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
  have h1 := congrArg (infPart D) hx
  rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at h1
  exact h1

theorem exists_nonSplit {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ v ε, NonSplitAt D v ε ∧ ∀ e f, IsPrimeIdem P e f →
      e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨_, ε, ⟨hε, ?_⟩, fun e f h => ?_⟩
  · rintro ⟨e, ⟨e1, e2, -⟩, e3⟩
    have key : ∀ a : AE D, a * a = a → algebraMap (AF D.host.F) (AE D) ε * a = a → Φ a P ≠ 0 → IsDelta Φ P a :=
      fun a a1 a2 a3 => ⟨by rw [← a2, RingHom.map_mul, h0, zero_mul],
        mul_left_cancel₀ a3 (by rw [← ev_mul, a1, mul_one]),
        fun Q hQ => by rw [← a2, ev_mul, hd.2.2 Q hQ, zero_mul]⟩
    have e1' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, e1]
    have hz : Φ e P * Φ (cA D e) P = 0 := by rw [← ev_mul, e2, ev_zero]
    have hs : Φ e P + Φ (cA D e) P = 1 := by rw [← ev_add, e3, hd.2.1]
    by_cases h : Φ e P = 0
    · have a := key (cA D e) e1' (by rw [← e3]; linear_combination e1' + e2)
        (by rw [h, zero_add] at hs; rw [hs]; exact one_ne_zero)
      have b := delta_conj hΦ a
      rw [cA_cA, ← hc] at b
      exact zero_ne_one (h.symm.trans b.2.1)
    · have a := key e e1 (by rw [← e3]; linear_combination e1 + e2) h
      have b := delta_conj hΦ a
      rw [← hc] at b
      rw [a.2.1, b.2.1, one_mul] at hz
      exact one_ne_zero hz
  · obtain ⟨k1, ε', k2, k3⟩ := of_isPrimeIdem hΦ h
    exact ⟨delta_unique hΦ k1 hd, by rw [k3, placeIdem_unique k2 hε]⟩

theorem isHalf_of_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro i j
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => exact mul_zero _
  | add x x' _ _ h h' => rw [Matrix.add_apply, mul_add, h, h']
  | neg x _ h => rw [Matrix.neg_apply, mul_neg, h]

theorem vacFix_of_unrPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E) (hW : IsWeilDatumO ψ S T χS χT om)
    (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  by_cases hP : Formalism.DivisionValues.conjPl P = P
  swap
  · exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace ψ S T χS χT om P hW hP uS uT).1
  obtain ⟨v, ε, hv, hu⟩ := exists_nonSplit hP
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, e', he⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨rfl, rfl⟩ := hu e e' he
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hu a a' ha).2] at sk
  rw [(hu b b' hb).2] at sk'
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
    χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv (uS _ _ he) (uT _ _ he) k k' sk sk'
    (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
      (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) v ε hv.1 k k'
      (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk.2.1) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hk'.2.1))
    f hf.1 fun u hu => hf.2 _ _ he u
      (by
        rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hu
        exact GlobalTheory.PlaceModel.latO_le_top _ hu)
      (Or.inl (isHalf_of_mem hv.1 hu))

theorem unr_and_vacFix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hc i σ μ' η' H ω hW f₀ f B _ P hP
  have h0 := (GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev A.μ0 P hP).2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have h1 : UnrPl P μ' := fun e f h x a b c => by
    refine (H.mu_cond x ⟨infPart_eq_one h a, b, c⟩).2 ?_
    have h2 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := h0 e f h x a b c
    rwa [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hc.lev.xi_base ▸ hc.lev.xi A.μ0) x, mul_one] at h2
  have h2 : UnrPl P (μ' * η'⁻¹) := fun e f h x a b c => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1 e f h x a b c, H.eta_unr x (infPart_eq_one h a) b c, inv_one, mul_one]
  exact ⟨h1, h2, vacFix_of_unrPl _ _ _ _ _ ω P hW h1 h2⟩

end GlobalTheory.ConjVacFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFixStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSplitting_unramified_hyperspecial_fix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → ∀ f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.UnrPl P μ' ∧ GlobalTheory.Hk3.UnrPl P (μ' * η'⁻¹) ∧ GlobalTheory.Hk3.VacFix R.ψ ω P := by
  first | exact @GlobalTheory.ConjVacFix.unr_and_vacFix | exact GlobalTheory.ConjVacFix.unr_and_vacFix | (intros; apply GlobalTheory.ConjVacFix.unr_and_vacFix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoeffici
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoeffici
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.MeasPet

variable {D : D7}


open GlobalTheory.ChainOnto.HaarInf in
theorem meas_petco : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  let K : Subgroup (GA D V) := s.J
  let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
  let A : Subgroup (GA D V) := Lf.comap (GlobalTheory.AutMult.toFin V)
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg => Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hAset : (A : Set (GA D V)) = s.big := by
    ext g
    refine ⟨fun hg => ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩, ?_⟩
    rintro ⟨b, κ, hκ, rfl⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
    have e : GlobalTheory.AutMult.toFin V (κ : GA D V) = ⟨κ, hs.fin hκ⟩ := GlobalTheory.AutMult.toFin_coe (⟨κ, hs.fin hκ⟩ : GfC V)
    rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf, one_mul, e]
    exact hκ
  have hLf : IsOpen (Lf : Set (GfC V)) := by
    obtain ⟨U, hU, hUK⟩ := hs.isOpen
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
    exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hk) k.2)
  have hAopen : IsOpen (A : Set (GA D V)) := hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact hs.stab _ (hfinK g hg) v
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    constructor
    · rintro ⟨hgA, hgf⟩
      have := hfinK g hgA
      rwa [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hgf⟩ : GfC V))] at this
    · intro hg
      refine ⟨?_, hs.fin hg⟩
      refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
      rw [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hs.fin hg⟩ : GfC V))]
      exact hg
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.ChainOnto.isCompact_of_integral_open D V s.Λ hs.selfDual K hs.fin hs.stab hs.isOpen
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    rw [← SetLike.mem_coe, hAset]
    exact ⟨b, 1, one_mem _, by simp⟩
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨⟨hIopen.measurableSet, hAset ▸ hAopen.measurableSet, hAset ▸ hAint, _, hHaar, fun f F hf hF => ?_⟩, ?_⟩
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
      (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
    have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hF _ _ (hfinK g hg)
    have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
      (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
    rw [← hAset]
    refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
    rw [setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]
  · intro ipD ip hM u v b κ hκ
    have hmem := (mem_multT c.θ s.M (s.J : Set (GA D V)) 1 (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ))).1 u.2
    have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (s.J : Set (GA D V)) 1 hc.inf v b
    have hUw := hU _ hmem
    have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ)) x := by
      intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
      funext g
      rw [ev, ev, hUw]
      simp only [rTr]
      rw [← mul_assoc]
      simpa using hmap.lev v κ hκ (g * (b : GA D s.V))
    have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
    rw [key, hsch, hM.pure w v]
    simp only [hw]

end GlobalTheory.EvenOnto.MeasPet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoefficiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.EvenOnto.MeasPet.meas_petco | exact GlobalTheory.EvenOnto.MeasPet.meas_petco | (intros; apply GlobalTheory.EvenOnto.MeasPet.meas_petco <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    coefW p.ω m X (p.pt φ) (b * κ) = coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ]
  unfold coefW
  rw [hv]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ) (hfin : s.J ≤ GfC s.V)
    (hstab : ∀ k ∈ s.J, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := hfin hκ
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  intro D hMet hRZ
  intro c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ c.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨⟨hmOff, _, hAsub, mR, hmR, hint⟩, hpet⟩ := GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient D c hc k hkm s hs
  have hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ :=
    fun κ hκ => hp.pre.law φ κ hκ 1 s'.J.one_mem
  have hsupp := hp.pre.supp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ s.J,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet ipD ip hip u v b κ hκ]
    simp only [map_mul]
    ring

  have hoff : ∀ g ∈ intOff c s \ s.big,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    have h0 : coefW p.ω m X (p.pt φ) g = 0 := hsupp g hg hgA
    rw [h0, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := s.big) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hs.fin hs.stab a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.EvenOnto.ZetaNeProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow : RowModels → RowStep → RowTower := by
  first | exact @GlobalTheory.SepRows.rowTower_of_step | exact GlobalTheory.SepRows.rowTower_of_step | (intros; apply GlobalTheory.SepRows.rowTower_of_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.PhaseReal.psi_trace_single : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  intro D ψ hψ θ hθ τ t hfin hsupp
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ T = psiInf D.host.F ψ (fstA D.host.F T) := by
    unfold psiInf
    congr 1
  have h2 := hψ.2.2 θ hθ (fstA D.host.F T)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) :=
    fun ρ => GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
  have h4 : ∑ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ τ (infPart D t)).re : ℝ) : ℂ) := by
    simp only [h3]
    refine Finset.sum_eq_single τ (fun ρ _ hρ => ?_) (fun h => absurd (Finset.mem_univ τ) h)
    rw [hsupp ρ hρ]
    simp
  rw [h1, h2, h4]
  congr 1
  have h5 : ((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re = -(4 * Real.pi) * (θ τ (infPart D t)).re := by
    have : (-(4 * Real.pi : ℂ)) = ((-(4 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [h5]
  push_cast
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardChar_trace_single_realPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  first | exact @GlobalTheory.PhaseReal.psi_trace_single | exact GlobalTheory.PhaseReal.psi_trace_single | (intros; apply GlobalTheory.PhaseReal.psi_trace_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopLineFromSeparation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows posDef_dual)
open GlobalTheory.SepRows
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopLineProof

theorem bilin_prop {X Y ι κ : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (fx : ι → X) (fy : κ → Y)
    (hx : Submodule.span ℂ (Set.range fx) = ⊤) (hy : Submodule.span ℂ (Set.range fy) = ⊤) (b b₀ : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (f : ι → κ → ℂ) (l l₀ : ℂ) (hb : ∀ i j, b (fx i) (fy j) = f i j * l) (hb₀ : ∀ i j, b₀ (fx i) (fy j) = f i j * l₀)
    (hne : b₀ ≠ 0) : b = (l / l₀) • b₀ := by
  have hl₀ : l₀ ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_)
    simp [hb₀]
  refine LinearMap.ext_on_range hx fun i => LinearMap.ext_on_range hy fun j => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hb, hb₀, smul_eq_mul]
  field_simp

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem coefPlus_is (G : GridData L sc) {θ : InfFam D} (hθ : IsInfFam θ) : (coefPlus G θ).Is := by
  obtain ⟨hc, hs⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V (.top 0))
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.coefOf_is _ _ _ (fun h hh => ?_) (fun h τ => ?_) (fun τ => ?_) (fun g hg => ?_)
  · have : GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h = 1 := funext fun τ => by
      show Formalism.UG.bc (θ τ) (infHom (G.V (.top 0)) h) = 1
      rw [show infHom (G.V (.top 0)) h = 1 from hh, map_one]
    rw [MonoidHom.comp_apply, this, map_one]
  · exact GlobalTheory.CoefModel.invTr_unitary (g := GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h τ)
      (GlobalTheory.RecDictModel.archM_unitary (G.V (.top 0)) (hθ τ) h)
  · refine ((hc τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (G.V (.top 0)) h⁻¹ τ : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = _
    rw [map_inv]
    rfl
  · obtain ⟨h, e⟩ := hs (invTrK g) fun τ => by
      have := GlobalTheory.CoefModel.invTr_unitary (hg τ)
      rwa [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.FunObj.posDef_Xp G (tauE D τ)).isUnit), Matrix.transpose_transpose] at this
    refine ⟨h, ?_⟩
    rw [MonoidHom.comp_apply, e]
    exact funext fun τ => GlobalTheory.CoefModel.invTr_invTr _

end GlobalTheory.TopLineProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparationLineOfBessel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_prod_of_separately {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (b : ∀ i, X i → ℂ) (β : (∀ i, X i) → ℂ)
    (h : ∀ i x, ∃ c : ℂ, ∀ y, β (Function.update x i y) = c * b i y) : ∃ l : ℂ, ∀ x, β x = (∏ i, b i (x i)) * l := by
  by_cases h0 : ∃ i, ∀ y, b i y = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun x => ?_⟩
    obtain ⟨c, hc⟩ := h i x
    have := hc (x i)
    rw [Function.update_eq_self, hi] at this
    simp [this]
  push_neg at h0
  choose x₀ hx₀ using h0
  have key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) →
      β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]
    | insert j s hj ih =>
      intro x hx
      obtain ⟨c, hc⟩ := h j x
      have e1 := hc (x j)
      rw [Function.update_eq_self] at e1
      have e2 := ih (Function.update x j (x₀ j)) fun i hi => by
        by_cases e : i = j
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hx i (by simp [e, hi])
      have e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hc, e3] at e2
      rw [Finset.prod_insert hj, Finset.prod_insert hj, e1]
      linear_combination b j (x j) * e2
  have hn : ∏ i, b i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i
  refine ⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩
  have := key Finset.univ x (by simp)
  field_simp
  linear_combination this

end GlobalTheory.SepRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamily
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

theorem GlobalTheory.HeisOrbit.dOp_contDiff_family {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (Pv Qv : ℝ → (κ → mixedEmbedding.mixedSpace F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pv → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Qv →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (Pv p.1) (Qv p.1) (G p.1) p.2) := by
  intro hG hP hQ
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (ℝ × (κ → mixedEmbedding.mixedSpace F)) × (κ → mixedEmbedding.mixedSpace F) => (G x.1.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) x.2) :=
    hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (κ → mixedEmbedding.mixedSpace F)) (y : (κ → mixedEmbedding.mixedSpace F)) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) hf contDiff_snd
      (le_of_eq (by simp))
  have hD' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2 (Pv p.1)) :=
    hD.clm_apply (hP.comp contDiff_fst)
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ∑ i, p.2 i * Qv p.1 i) := by
    refine ContDiff.sum (fun i _ => ?_)
    exact ((contDiff_apply ℝ _ i).comp contDiff_snd).mul
      ((contDiff_apply ℝ _ i).comp (hQ.comp contDiff_fst))
  have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, p.2 i * Qv p.1 i) : ℝ) : ℂ)) := by
    have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearMap.contDiff
    exact Complex.ofRealCLM.contDiff.comp (hl.comp hS)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) p.2) := hG
  unfold GlobalTheory.HeisOrbit.dOp
  exact hD'.sub ((contDiff_const.mul hT).mul hg)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamilyStatement
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
theorem _root_.GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (P p.1) (Q p.1) (G p.1) p.2) := by
  first | exact @GlobalTheory.HeisOrbit.dOp_contDiff_family | exact GlobalTheory.HeisOrbit.dOp_contDiff_family | (intros; apply GlobalTheory.HeisOrbit.dOp_contDiff_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramified
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertVac

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem placeIdem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := GlobalTheory.SplitIdem.af_ext _ fun w => by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h']
  | neg x _ h => rw [smul_neg, h]

theorem mem_latO_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u :=
  ⟨fun h => ⟨GlobalTheory.PlaceModel.latO_le_top _ h, placeIdem_smul_eq hε h⟩,
    fun h => h.2 ▸ GlobalTheory.PlaceModel.placeIdem_smul_mem hε h.1⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.FinWeilO.mt_mul, inv_mul_cancel,
    GlobalTheory.FinWeilO.mt_one, Matrix.one_mul]

theorem actO_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) :=
  Function.LeftInverse.injective (actO_inv_actO g h)

theorem om_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT v ε hv uS uT g h hg hh hst f₀ hf hvac
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv uS uT g h hg hh
    (fun u => ?_) f₀ hf fun u hu => ?_
  · rw [mem_latO_place_iff hv.1, mem_latO_place_iff hv.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (actO_injective g h).eq_iff]
  · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, placeIdem_smul_eq hv.1 hu]
    have h2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [h1] at h2

end GlobalTheory.InertVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramifiedStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_fixes_latticeVacuum_nonsplit_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ (g : GA D S) (h : GA D T), SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → om (g, h) f₀ = f₀ := by
  first | exact @GlobalTheory.InertVac.om_fixes_latVac | exact GlobalTheory.InertVac.om_fixes_latVac | (intros; apply GlobalTheory.InertVac.om_fixes_latVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SBCount

theorem countable_compact_open (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsCompact U ∧ IsOpen U}.Countable := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  refine ((Set.countable_setOf_finite_subset hbc).image Set.sUnion).mono ?_
  rintro U ⟨hUc, hUo⟩
  obtain ⟨S, hSb, rfl⟩ := hb.open_eq_sUnion hUo
  obtain ⟨t, htS, htf, hcov⟩ := hUc.elim_finite_subcover_image (b := S) (c := id)
    (fun s hs => hb.isOpen (hSb hs)) (by intro x hx; simpa using hx)
  refine ⟨t, ⟨htf, htS.trans hSb⟩, ?_⟩
  refine le_antisymm (Set.sUnion_subset_sUnion htS) ?_
  intro x hx
  simpa using hcov hx

theorem SB_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (fun _ => (1 : ℂ))) '' {U : Set X | IsCompact U ∧ IsOpen U}) := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨s, hs⟩ := hcs.isCompact.elim_finite_subcover (fun a : ℂ => f ⁻¹' {a})
    (fun a => hlc.isOpen_fiber a) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hf_eq : f = ∑ a ∈ s, a • (f ⁻¹' {a}).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator, Set.mem_preimage,
      Set.mem_singleton_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_cases hx : x ∈ tsupport f
      · exact absurd (by simpa using hs hx) h
      · exact image_eq_zero_of_notMem_tsupport hx
  rw [hf_eq]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {a}, ⟨?_, hlc.isOpen_fiber a⟩, rfl⟩)
    refine hcs.isCompact.of_isClosed_subset (hlc.isClosed_fiber a) ?_
    intro x hx
    refine subset_tsupport f ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [Function.mem_support, hx, ha]

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (SB_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compact_open X).image _).to_subtype

end GlobalTheory.SBCount

namespace GlobalTheory.TripleAssembly

theorem rank_SB_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  intro F _ _ κ _ v
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  exact GlobalTheory.SBCount.rank_SB_le _

end GlobalTheory.TripleAssembly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0Statement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_schwartzBruhat_adicCompletion_pi_le_aleph0 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | exact GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | (intros; apply GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

theorem GlobalTheory.PolMul.pol_mul_pairInf_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ _ τ _ _ q f hf
  exact GlobalTheory.PolMul.model_mul M ψ hψ τ q f hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairingStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf_pair | exact GlobalTheory.PolMul.pol_mul_pairInf_pair | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf_pair <;> assumption)
end
end
