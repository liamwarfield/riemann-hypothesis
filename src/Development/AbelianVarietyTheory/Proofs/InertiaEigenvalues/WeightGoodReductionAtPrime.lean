module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfLocallyConstant
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.UnramifiedClasses

theorem eq_zero_of_locallyConstant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [AddCommGroup A] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (c : G → A)
    (hlc : IsLocallyConstant c) (hc : ∀ g h, c (g * h) = c g + c h) (hφ : c φ = 0)
    (hI : ∀ g ∈ I, c g = 0) (g : G) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let H : Subgroup G :=
    { carrier := {g | c g = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hc, ha, hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := hc a a⁻¹
        rw [mul_inv_cancel, h1, ha, zero_add] at this
        exact this.symm }
  have hle : Subgroup.zpowers φ ⊔ I ≤ H :=
    sup_le ((Subgroup.zpowers_le (G := G)).mpr hφ) (fun g hg => hI g hg)
  have hcl : (Subgroup.zpowers φ ⊔ I).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _ hle (hlc.isClosed_fiber 0)
  rw [hgen] at hcl
  exact hcl (Subgroup.mem_top g)

theorem isLocallyConstant_mkQ {X : Type} [TopologicalSpace X] {O V : Type} [CommRing O]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V] (T : Submodule O V)
    (hT : IsOpen (T : Set V)) (f : X → V) (hf : Continuous f) :
    IsLocallyConstant (fun x => T.mkQ (f x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => f y + (-f x)) ⁻¹' (T : Set V),
    hT.preimage (hf.add continuous_const), by simp, fun y hy => ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hy

theorem exists_not_mem_range {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] :
    ∃ y : LL, y ∉ Set.range (algebraMap O LL) := by
  by_contra h
  push Not at h
  apply IsDiscreteValuationRing.not_isField O
  exact (RingEquiv.ofBijective (algebraMap O LL)
    ⟨IsFractionRing.injective O LL, h⟩).toMulEquiv.isField (Field.toIsField LL)

theorem HfD_eq_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [IsTopologicalGroup G] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsTopologicalRing LL], GoodO (Qp := Qp) LL O → ∀ (T : LocLat G Qp LL O), Module.finrank LL T.V = 1 → (∀ g x, T.ρ g x = x) → Module.finrank LL (FiniteCohomology PD T.ρ) = 1 → ∀ (I : Subgroup G) (φ : G), (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤ → ∀ δ : G → LL, δ ∈ finiteCocycles PD (1 : Representation LL G LL) → (∀ g ∈ I, δ g = 0) → δ ≠ 0 → HfD PD T.L ≠ ⊥ ∧ ∀ c : G → T.V ⧸ T.L.T, c ∈ HfD PD T.L ↔ (c ∈ divisibleCocycles T.L ∧ ∃ x, ∀ g ∈ I, c g = actD T.L g x - x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ _ LL _ _ _ O _ _ _ hO T hV hρ
    hH I φ hgen δ hδ hδI hδ0
  have hopen := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L hV
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_range (O := O) (LL := LL)
  obtain ⟨⟨hδc, hδh⟩, x₀, hx₀⟩ := hδ
  have hδadd : ∀ g h, δ (g * h) = δ g + δ h := fun g h => by simpa using hδh g h
  have hact : ∀ g (x : T.V ⧸ T.L.T), actD T.L g x = x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (Submodule.Quotient.mk (p := T.L.T)) (hρ g x)
  have hBD : BD T.L = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [hact]
  have hB1 : B1 T.ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob, hρ]
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hc₀c : Continuous fun g => e (δ g) := by
    have : (fun g => e (δ g)) = fun g => δ g • e 1 := by
      funext g
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hδc.smul continuous_const
  have hc₀ : (fun g => e (δ g)) ∈ finiteCocycles PD T.ρ := by
    let m := AlgebraTensorModule.map (e : LL →ₗ[LL] T.V) (LinearMap.id : B →ₗ[Qp] B)
    have hm : ∀ g y, m (actVB PD (1 : Representation LL G LL) g y) = actVB PD T.ρ g (m y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m, actVB, hρ]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    refine ⟨⟨hc₀c, fun g h => by simp only [hδadd, map_add (f := _), hρ]⟩, m x₀, fun g => ?_⟩
    have := congrArg m (hx₀ g)
    simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
    rw [← hm]
    exact this
  obtain ⟨g₀, hg₀⟩ : ∃ g, δ g ≠ 0 := Function.ne_iff.mp hδ0
  have hdim : Module.finrank LL ↥(finiteCocycles PD T.ρ) = 1 := by
    rw [← hH]
    refine (Submodule.quotEquivOfEqBot _ ?_).finrank_eq.symm
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  have hspan : ∀ z ∈ finiteCocycles PD T.ρ, ∃ a : LL, ∀ g, z g = e (a * δ g) := by
    intro z hz
    have hne : (⟨_, hc₀⟩ : ↥(finiteCocycles PD T.ρ)) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) g₀
      exact hg₀ (by simpa using this)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hz⟩
    refine ⟨a, fun g => ?_⟩
    have := congrFun (congrArg Subtype.val ha) g
    rw [← smul_eq_mul, map_smul]
    exact this.symm

  let r : LL → G → T.V ⧸ T.L.T := fun a g => T.L.T.mkQ (e (a * δ g))
  have hHf : ∀ c, c ∈ HfD PD T.L ↔ ∃ a, c = r a := by
    intro c
    unfold HfD
    rw [hBD, sup_bot_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hspan z hz
      exact ⟨a, funext fun g => by simp [r, ha]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a • fun g => e (δ g), (finiteCocycles PD T.ρ).smul_mem a hc₀, ?_⟩
      funext g
      simp [r, ← map_smul]
  have hrlc : ∀ a, IsLocallyConstant (r a) := fun a => by
    refine isLocallyConstant_mkQ T.L.T hopen (fun g => e (a * δ g)) ?_
    have : (fun g => e (a * δ g)) = fun g => a • e (δ g) := by
      funext g
      rw [← map_smul, smul_eq_mul]
    rw [this]
    exact hc₀c.const_smul a
  have hradd : ∀ a g h, r a (g * h) = r a g + r a h := fun a g h => by
    simp only [r, hδadd, mul_add, map_add (f := _)]
  have hrI : ∀ a, ∀ g ∈ I, r a g = 0 := fun a g hg => by
    simp only [r, hδI g hg, mul_zero, map_zero]
  have hr₀ : r (y₀ / δ g₀) g₀ ≠ 0 := by
    intro h
    simp only [r, div_mul_cancel₀ _ hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hy₀ ((he _).mp h)
  have hφ : δ φ ≠ 0 := by
    intro h
    exact hr₀ (eq_zero_of_locallyConstant I φ hgen _ (hrlc _) (hradd _)
      (by simp only [r, h, mul_zero, map_zero]) (hrI _) g₀)
  refine ⟨fun h => ?_, fun c => ?_⟩
  · have : r (y₀ / δ g₀) ∈ HfD PD T.L := (hHf _).mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hr₀ (congrFun this g₀)
  · rw [hHf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨hrlc a, fun g h => by rw [hact, hradd]⟩, 0, fun g hg => by
        rw [hrI a g hg, hact, sub_zero]⟩
    · rintro ⟨⟨hlc, hcoc⟩, x, hx⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (c φ)
      refine ⟨e.symm v / δ φ, funext fun g => sub_eq_zero.mp ?_⟩
      refine eq_zero_of_locallyConstant I φ hgen (fun g => c g - r (e.symm v / δ φ) g)
        (hlc.sub (hrlc _)) (fun g h => ?_) ?_ (fun g hg => ?_) g
      · simp only [hcoc, hact, hradd]
        abel
      · simp only [r, div_mul_cancel₀ _ hφ, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, hv,
          sub_self]
      · simp only [hx g hg, hact, hrI _ g hg, sub_self]

end GlobalTheory.UnramifiedClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaTmulOneMem
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HfZero

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in
theorem nontrivial_cris : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
theorem tmul_one_inj {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have := nontrivial_cris PD
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qp B)
    (LinearMap.ker_eq_bot.2 (algebraMap Qp B).injective)
  have h1 : r 1 = 1 := by simpa using LinearMap.congr_fun hr 1
  have := congrArg (fun z => TensorProduct.rid Qp V (r.lTensor V z)) h
  simpa [h1] using this

theorem frob_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem iota_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem frob_tmul_one (v : V) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

theorem act_tmul_one (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem tmul_mem_filV (v : V) (a : ℤ) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

theorem iota_tmul_one_mem (v : V) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have : ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : BdR) := by simp [ιV]
  rw [this]
  exact tmul_mem_filV PD v 0 1 PD.one_mem

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) :=
  antitone_int_of_succ_le (filV_succ_le PD)

theorem exists_mem_filV (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem_filV PD v a b ha⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem mem_dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_ddR_iff (x : V ⊗[Qp] BdR) : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem iota_mem_ddR (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by
  rw [mem_ddR_iff]
  intro g
  rw [← iota_act, (mem_dcris_iff PD ρ x).1 hx g]

end

theorem z1f_le_b1 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], TateFilteredInvariants PD → fontCore PD → GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ → DdR PD A.ρ ≤ FilV PD (LL := LL) (V := A.V) 0 → H0V A.ρ = ⊥ → finiteCocycles PD A.ρ ≤ B1 A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ LL _ _ _ O _ _ h5 hfont hO A
    hdR hFil hH0 c hc
  obtain ⟨-, x, hx⟩ := hc
  have : Module.Finite LL ↥(Dcris PD A.ρ) := (hfont LL O hO A).1.1
  let ψ : A.V ⊗[Qp] B →ₗ[LL] A.V ⊗[Qp] B := LinearMap.id - φVB PD (LL := LL) (V := A.V)
  have hψ : ∀ z, ψ z = z - φVB PD (LL := LL) (V := A.V) z := fun z => rfl
  have hstab : ∀ z ∈ Dcris PD A.ρ, ψ z ∈ Dcris PD A.ρ := by
    intro z hz
    rw [mem_dcris_iff] at hz ⊢
    intro g
    rw [hψ, map_sub, ← frob_act, hz g]
  have hinj : Function.Injective (ψ.restrict hstab) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨z, hz⟩ h0
    have h1 : ψ z = 0 := congrArg Subtype.val h0
    rw [hψ, sub_eq_zero] at h1
    obtain ⟨v, rfl⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) z h1.symm
      (hFil (iota_mem_ddR PD A.ρ z hz))
    have hv : v ∈ H0V A.ρ := by
      simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply tmul_one_inj PD
      rw [← act_tmul_one PD A.ρ, (mem_dcris_iff PD A.ρ _).1 hz g]
    rw [hH0, Submodule.mem_bot] at hv
    subst hv
    exact Subtype.ext (TensorProduct.zero_tmul _ _)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hy : ψ x ∈ Dcris PD A.ρ := by
    rw [mem_dcris_iff]
    intro g
    have h1 := frob_tmul_one PD (LL := LL) (c g)
    rw [hx g, map_sub, frob_act] at h1
    rw [hψ, map_sub, sub_eq_sub_iff_sub_eq_sub, h1]
  obtain ⟨⟨x', hx'⟩, hxx⟩ := hsurj ⟨ψ x, hy⟩
  have h2 : ψ x' = ψ x := congrArg Subtype.val hxx
  have hfix : φVB PD (LL := LL) (V := A.V) (x - x') = x - x' := by
    rw [hψ, hψ, sub_eq_sub_iff_sub_eq_sub] at h2
    rw [map_sub, ← neg_sub x' x, h2, neg_sub]
  obtain ⟨a, ha⟩ := exists_mem_filV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)
  obtain ⟨w, ⟨hw, -⟩, hw'⟩ := h5 LL O hO A hdR a 0 _ ha (fun g => by
    rw [← iota_act, ← map_sub, ← hx g]
    exact iota_tmul_one_mem PD (c g))
  have hF : ιV PD (LL := LL) (V := A.V) (x - x') ∈ FilV PD (LL := LL) (V := A.V) 0 := by
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hw' (hFil hw))
      (hFil (iota_mem_ddR PD A.ρ x' hx'))
    rwa [sub_add_cancel, ← map_sub] at h3
  obtain ⟨v, hv⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) _ hfix hF
  refine ⟨v, funext fun g => ?_⟩
  change A.ρ g v - v = c g
  apply tmul_one_inj PD
  rw [hx g, TensorProduct.sub_tmul, ← act_tmul_one PD A.ρ, ← hv, map_sub,
    (mem_dcris_iff PD A.ρ _).1 hx' g]
  abel

end GlobalTheory.HfZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthTorsionByQuotientDivisibleLe
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem length_torsionBy_quotient_divisible_le (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Q : Type) [AddCommGroup Z] [Module O Z] [AddCommGroup Q]
    [Module O Q] (π : Z →ₗ[O] Q) (hs : Function.Surjective π)
    (hdiv : ∀ b : O, b ≠ 0 → ∀ x, π x = 0 → ∃ y, π y = 0 ∧ b • y = x)
    (htor : ∃ x, x ≠ 0 ∧ π x = 0 ∧ ∃ b : O, b ≠ 0 ∧ b • x = 0) (a : O) (ha : a ≠ 0) (k : ℕ)
    (hle : Module.length O ↥(Submodule.torsionBy O Z a) ≤
      ((k + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) :
    Module.length O ↥(Submodule.torsionBy O Q a) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical

  have hLfin : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero ha)

  let φ : Submodule.torsionBy O Z a →ₗ[O] Submodule.torsionBy O Q a :=
    LinearMap.codRestrict (Submodule.torsionBy O Q a) (π ∘ₗ (Submodule.torsionBy O Z a).subtype)
      (fun z => by
        rw [Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.subtype_apply,
          ← map_smul, (Submodule.mem_torsionBy_iff _ _).mp z.2, map_zero])

  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := hs q
    have h1 : π (a • z) = 0 := by
      rw [map_smul]; exact (Submodule.mem_torsionBy_iff _ _).mp hq
    obtain ⟨y, hy0, hy⟩ := hdiv a ha (a • z) h1
    refine ⟨⟨z - y, ?_⟩, ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hy, sub_self]
    · apply Subtype.ext
      simp [φ, hy0]
  have hexact := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ
    (Submodule.subtype_injective _) hφ (LinearMap.exact_subtype_ker_map φ)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd_unit : ∀ c : O, ¬ ϖ ∣ c → IsUnit c := by
    intro c hc
    by_contra hnu
    apply hc
    have hmem := (IsLocalRing.mem_maximalIdeal c).mpr hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at hmem
    exact hmem
  obtain ⟨x, hx0, hxK, b, hb0, hbx⟩ := htor
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hxm : ϖ ^ m • x = 0 := by
    rw [mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hbx
    exact hbx
  have hex : ∃ j, ϖ ^ j • x = 0 := ⟨m, hxm⟩
  have hj : ϖ ^ Nat.find hex • x = 0 := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, one_smul] at hj
    exact hx0 hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have he0 : ϖ ^ i • x ≠ 0 := Nat.find_min hex (by omega)
  have hϖe : ϖ • (ϖ ^ i • x) = 0 := by
    rw [hi] at hj
    rw [smul_smul, ← pow_succ']; exact hj
  have heK : π (ϖ ^ i • x) = 0 := by rw [map_smul, hxK, smul_zero]
  have hunit_e : ∀ w : O, IsUnit w → w • (ϖ ^ i • x) ≠ 0 := by
    intro w hw h
    exact he0 ((hw.smul_eq_zero).mp h)
  obtain ⟨n, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hadvd : ∀ c : O, a ∣ c ↔ ϖ ^ n ∣ c := by
    intro c; rw [hav, Units.mul_left_dvd]
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ : Z, π y₀ = 0 ∧ ∀ c : O, c • y₀ = 0 ↔ a ∣ c := by
    cases n with
    | zero =>
      refine ⟨0, map_zero π, fun c => ?_⟩
      rw [hadvd, pow_zero]
      simp
    | succ n' =>
      obtain ⟨y, hyK, hy⟩ := hdiv (ϖ ^ n') (pow_ne_zero _ hϖ.ne_zero) _ heK
      refine ⟨y, hyK, fun c => ?_⟩
      rw [hadvd]
      constructor
      · intro hc
        by_cases hc0 : c = 0
        · rw [hc0]; exact dvd_zero _
        obtain ⟨r, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
        by_cases hr : n' + 1 ≤ r
        · exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hr) _
        · exfalso
          obtain ⟨d, hd⟩ : ∃ d, n' = r + d := ⟨n' - r, by omega⟩
          apply hunit_e (w : O) w.isUnit
          have hmul : (w : O) * ϖ ^ n' = ϖ ^ d * ((w : O) * ϖ ^ r) := by rw [hd, pow_add]; ring
          rw [← hy, smul_smul, hmul, mul_smul, hc, smul_zero]
      · rintro ⟨d, rfl⟩
        have hmul : ϖ ^ (n' + 1) * d = d * ϖ * ϖ ^ n' := by ring
        rw [hmul, mul_smul, hy, mul_smul, hϖe, smul_zero]
  have hy₀T : y₀ ∈ Submodule.torsionBy O Z a :=
    (Submodule.mem_torsionBy_iff _ _).mpr ((hy₀ a).mpr dvd_rfl)
  have hy₀ker : (⟨y₀, hy₀T⟩ : Submodule.torsionBy O Z a) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [φ, hy₀K]
  let f : O →ₗ[O] LinearMap.ker φ := LinearMap.toSpanSingleton O _ ⟨⟨y₀, hy₀T⟩, hy₀ker⟩
  have hker : Ideal.span {a} = LinearMap.ker f := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton, ← hy₀ c]
    simp [Subtype.ext_iff]
  have hK : Module.length O (O ⧸ Ideal.span {a}) ≤ Module.length O (LinearMap.ker φ) := by
    calc Module.length O (O ⧸ Ideal.span {a})
        = Module.length O (O ⧸ LinearMap.ker f) :=
          (Submodule.quotEquivOfEq _ _ hker).length_eq
      _ = Module.length O (LinearMap.range f) := f.quotKerEquivRange.length_eq
      _ ≤ Module.length O (LinearMap.ker φ) :=
          Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _)
  have h2 : Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (O ⧸ Ideal.span {a}) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {a}) := by
    calc _ ≤ Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (LinearMap.ker φ) := by
            gcongr
      _ = Module.length O ↥(Submodule.torsionBy O Z a) := by rw [hexact, add_comm]
      _ ≤ _ := hle
      _ = _ := by push_cast; ring
  exact (ENat.add_le_add_iff_right hLfin).mp h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemGKChiPowNeOne
namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.TwistTors

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
  [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

omit [TopologicalSpace Qp] in
theorem actD_mk (T : LocLat G Qp LL O) (g : G) (x : T.V) :
    actD T.L g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T.ρ g x) := rfl


omit [TopologicalSpace Qp] in
theorem lc_mk (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) {f : G → T.V}
    (hf : Continuous f) :
    IsLocallyConstant fun g => (Submodule.Quotient.mk (f g) : T.V ⧸ T.L.T) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => f h + (-f g)) ⁻¹' (T.L.T : Set T.V),
    hT.preimage (hf.add continuous_const), by simp, fun h hh => ?_⟩
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hh

omit [TopologicalSpace Qp] in
theorem lc_act (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) (w : T.V ⧸ T.L.T) :
    IsLocallyConstant fun g => actD T.L g w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact lc_mk T hT (T.cont x)

omit [TopologicalSpace Qp] in
theorem actD_one (T : LocLat G Qp LL O) (w : T.V ⧸ T.L.T) : actD T.L 1 w = w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [actD_mk, map_one]; rfl

omit [TopologicalSpace Qp] in
theorem actD_mul (T : LocLat G Qp LL O) (g h : G) (w : T.V ⧸ T.L.T) :
    actD T.L (g * h) w = actD T.L g (actD T.L h w) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [actD_mk, actD_mk, actD_mk, map_mul]; rfl

omit [TopologicalSpace Qp] in
theorem mem_HfD (T : LocLat G Qp LL O) (c : G → T.V ⧸ T.L.T) :
    c ∈ HfD PD T.L ↔ ∃ z ∈ finiteCocycles PD T.ρ, ∃ x : T.V, ∀ g,
      c g = Submodule.Quotient.mk (z g + (T.ρ g x - x)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨z, hz, x, fun g => rfl⟩
  · rintro ⟨z, hz, x, hc⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk x, rfl⟩, ?_⟩
    funext g
    rw [hc g]; rfl

omit [TopologicalSpace Qp] in
theorem HfD_le (T : LocLat G Qp LL O) (hT : IsOpen (T.L.T : Set T.V)) :
    HfD PD T.L ≤ divisibleCocycles T.L := by
  intro c hc
  obtain ⟨z, hz, x, hc⟩ := (mem_HfD PD T c).1 hc
  obtain rfl : c = _ := funext hc
  refine ⟨lc_mk T hT (hz.1.1.add ?_), fun g h => ?_⟩
  · simp only [sub_eq_add_neg]
    exact (T.cont x).add continuous_const
  · beta_reduce
    rw [actD_mk, ← Submodule.Quotient.mk_add, hz.1.2, map_mul, map_add (f := _), map_sub,
      Module.End.mul_apply]
    congr 1
    abel

omit [TopologicalSpace Qp] in
theorem HfD_div [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) {b : O} (hb : b ≠ 0)
    {c : G → T.V ⧸ T.L.T} (hc : c ∈ HfD PD T.L) : ∃ y ∈ HfD PD T.L, b • y = c := by
  obtain ⟨z, hz, x, hc⟩ := (mem_HfD PD T c).1 hc
  have hb' : algebraMap O LL b ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]
  refine ⟨fun g => Submodule.Quotient.mk (((algebraMap O LL b)⁻¹ • z) g +
    (T.ρ g ((algebraMap O LL b)⁻¹ • x) - (algebraMap O LL b)⁻¹ • x)),
    (mem_HfD PD T _).2 ⟨_, Submodule.smul_mem _ _ hz, _, fun g => rfl⟩, ?_⟩
  funext g
  rw [hc g, Pi.smul_apply, ← Submodule.Quotient.mk_smul, Pi.smul_apply, map_smul, ← smul_sub,
    ← smul_add, ← algebraMap_smul LL b, smul_smul, mul_inv_cancel₀ hb', one_smul]

omit [TopologicalSpace Qp] in
theorem quot_torsion [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O)
    (w : T.V ⧸ T.L.T) : ∃ b : O, b ≠ 0 ∧ b • w = 0 := by
  first
  | exact @_root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion
  | exact _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion
  | (apply _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientLatticeTorsion.quotient_lattice_torsion ..)

omit [TopologicalSpace Qp] in
theorem Z1D_torsion [CompactSpace G] [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O)
    {c : G → T.V ⧸ T.L.T} (hc : c ∈ divisibleCocycles T.L) : ∃ b : O, b ≠ 0 ∧ b • c = 0 := by
  classical
  choose b hb hw using quot_torsion T
  have hfin := hc.1.range_finite
  refine ⟨∏ w ∈ hfin.toFinset, b w, Finset.prod_ne_zero_iff.2 fun w _ => hb w, ?_⟩
  funext g
  obtain ⟨k, hk⟩ : b (c g) ∣ ∏ w ∈ hfin.toFinset, b w :=
    Finset.dvd_prod_of_mem _ (by simp)
  rw [Pi.smul_apply, hk, mul_comm, mul_smul, hw, smul_zero]; rfl

theorem length_le_of_card (O : Type) [CommRing O] [IsLocalRing O] (M N : Type) [AddCommGroup M]
    [Module O M] [Finite M] [AddCommGroup N] [Module O N] [Finite N] (k : ℕ)
    (h : Nat.card M ≤ Nat.card N ^ k) : Module.length O M ≤ (k : ℕ∞) * Module.length O N := by
  obtain ⟨m, hm, hM⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O M
  obtain ⟨n, hn, hN⟩ := GlobalTheory.exists_length_eq_and_card_eq_pow O N
  rw [hm, hn]
  norm_cast
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact Nat.zero_le _
  have hq0 : Nat.card (IsLocalRing.ResidueField O) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm0.ne'] at hM
    exact Nat.card_pos.ne' hM
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero hq0
  have hq : 1 < Nat.card (IsLocalRing.ResidueField O) := Finite.one_lt_card
  rw [hM, hN, ← pow_mul, mul_comm] at h
  exact (Nat.pow_le_pow_iff_right hq).1 h


omit [TopologicalSpace Qp] in
def actTors (T : LocLat G Qp LL O) (a : O) (g : G) :
    ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) →+ ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) where
  toFun m := ⟨actD T.L g m.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, (Submodule.mem_torsionBy_iff _ _).1 m.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem lc_sub {X Y : Type} [TopologicalSpace X] {p : Y → Prop} {f : X → Subtype p}
    (hf : IsLocallyConstant fun x => (f x).1) : IsLocallyConstant f :=
  IsLocallyConstant.desc f Subtype.val hf Subtype.val_injective


omit [TopologicalSpace Qp] in
def toCoc (T : LocLat G Qp LL O) (a : O) (c : ↥(Submodule.torsionBy O ↥(divisibleCocycles T.L) a)) :
    ↥{c : G → ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) a) |
      IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actTors T a g (c h)} :=
  ⟨fun g => ⟨c.1.1 g, congrFun (congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).1 c.2)) g⟩,
    lc_sub c.1.2.1, fun g h => Subtype.ext (c.1.2.2 g h)⟩

omit [TopologicalSpace Qp] in
theorem toCoc_inj (T : LocLat G Qp LL O) (a : O) : Function.Injective (toCoc T a) := by
  intro c c' h
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  exact congrArg Subtype.val (congrFun (congrArg Subtype.val h) g)

theorem len_part [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (T : LocLat G Qp LL O)
    (h1 : Module.finrank LL T.V = 1) (p r d : ℕ) (ha : (p : O) ^ r ≠ 0)
    [Finite (O ⧸ Ideal.span {(p : O) ^ r})]
    (heul : ∀ (M : Type) [AddCommGroup M] [Finite M] (a : G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2))
    (hne : HfD PD T.L ≠ ⊥) :
    Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology T.L ⧸ divisibleFiniteCohomology PD T.L) ((p : O) ^ r)) ≤
      ((d + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {(p : O) ^ r}) := by
  have hT := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨-, he⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L h1
  obtain ⟨e⟩ := he _ ha
  haveI : Finite ↥(Submodule.torsionBy O (T.V ⧸ T.L.T) ((p : O) ^ r)) :=
    Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨hfin, hcard⟩ := heul _ (actTors T ((p : O) ^ r))
    (fun m => Subtype.ext (actD_one T m.1)) (fun g h m => Subtype.ext (actD_mul T g h m.1))
    (fun m => Subtype.ext (by
      have := (Submodule.mem_torsionBy_iff _ _).1 m.2
      change p ^ r • m.1 = 0
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact this))
    (fun m => lc_sub (lc_act T hT m.1))
  haveI := hfin.to_subtype
  haveI : Finite ↥(Submodule.torsionBy O ↥(divisibleCocycles T.L) ((p : O) ^ r)) :=
    Finite.of_injective _ (toCoc_inj T _)
  let π : ↥(divisibleCocycles T.L) →ₗ[O] (DivisibleCohomology T.L ⧸ divisibleFiniteCohomology PD T.L) :=
    (divisibleFiniteCohomology PD T.L).mkQ ∘ₗ Submodule.mkQ _
  have hπ : ∀ c, π c = 0 ↔ c.1 ∈ HfD PD T.L := by
    intro c
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨c', hc', h⟩
      have h0 : c' - c ∈ (BD T.L).comap (divisibleCocycles T.L).subtype := (Submodule.Quotient.eq _).1 h
      have h2 : c'.1 - c.1 ∈ BD T.L := h0
      have h3 : c'.1 - c.1 ∈ HfD PD T.L := Submodule.mem_sup_right h2
      have := Submodule.sub_mem _ (show c'.1 ∈ HfD PD T.L from hc') h3
      rwa [sub_sub_cancel] at this
    · intro hc
      exact ⟨c, hc, rfl⟩
  refine GlobalTheory.length_torsionBy_quotient_divisible_le O _ _ π
    ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)) ?_ ?_ _ ha (d + 1) ?_
  · intro b hb x hx
    obtain ⟨y, hy, h⟩ := HfD_div PD T hb ((hπ x).1 hx)
    exact ⟨⟨y, HfD_le PD T hT hy⟩, (hπ _).2 hy, Subtype.ext h⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b, hb, h⟩ := Z1D_torsion T (HfD_le PD T hT hx)
    exact ⟨⟨x, HfD_le PD T hT hx⟩, fun h0 => hx0 (congrArg Subtype.val h0), (hπ _).2 hx, b, hb,
      Subtype.ext h⟩
  · refine length_le_of_card O _ _ _ ?_
    rw [← Nat.card_congr e.toEquiv]
    exact (Nat.card_le_card_of_injective _ (toCoc_inj T _)).trans hcard

def toG (T : LocLat G Qp LL O) : GRep G Qp LL O where
  V := T.V
  ρ := T.ρ
  cont := T.cont


omit [TopologicalSpace Qp] in
theorem fixed_points_trivial_of_scalar_action_ne_one (T : LocLat G Qp LL O) (g : G) (u : LL) (hu : u ≠ 1)
    (hg : ∀ x, T.ρ g x = u • x) : H0V T.ρ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h := (Submodule.mem_iInf _).1 hx g
  rw [LinearMap.mem_ker, LinearMap.sub_apply, hg, LinearMap.id_apply] at h
  have h2 : (u - 1) • x = 0 := by rw [sub_smul, one_smul, h]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hu)

theorem BD_ne_bot (hO : GoodO (Qp := Qp) LL O) (T : LocLat G Qp LL O)
    (h1 : Module.finrank LL T.V = 1) (g : G) (u : LL) (hu : u ≠ 1)
    (hg : ∀ x, T.ρ g x = u • x) : BD T.L ≠ ⊥ := by
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ' : algebraMap O LL ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O LL)]; exact hϖ.ne_zero
  intro hb
  have hm : (LinearMap.pi fun g => actD T.L g - LinearMap.id)
      (Submodule.Quotient.mk (e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹))) ∈ BD T.L := ⟨_, rfl⟩
  rw [hb, Submodule.mem_bot] at hm
  have h2 : (Submodule.Quotient.mk (T.ρ g (e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹)) -
      e ((u - 1)⁻¹ * (algebraMap O LL ϖ)⁻¹)) : T.V ⧸ T.L.T) = 0 := congrFun hm g
  rw [Submodule.Quotient.mk_eq_zero, hg, ← map_smul, ← map_sub, he] at h2
  obtain ⟨a, ha⟩ := h2
  have hu' := sub_ne_zero.2 hu
  have h3 : algebraMap O LL (ϖ * a) = algebraMap O LL 1 := by
    rw [map_mul, ha, map_one, smul_eq_mul]; field_simp
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one a (IsFractionRing.injective O LL h3))

omit [TopologicalSpace Qp] in
theorem HfD_eq_BD (T : LocLat G Qp LL O) (h : finiteCocycles PD T.ρ ≤ B1 T.ρ) : HfD PD T.L = BD T.L := by
  refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨x, rfl⟩ := h hz
  exact ⟨Submodule.Quotient.mk x, rfl⟩

end Abstract

theorem tbe_of (S : Sit) [TopologicalSpace S.Qp] [CompactSpace S.G] [IsTopologicalGroup S.G]
    [IsTopologicalRing S.LL] (hO : GoodO (Qp := S.Qp) S.LL S.O)
    (hfin : ∀ n : ℕ, Finite (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O) ^ n}))
    (hp : ((S.PD.p : ℕ) : S.O) ≠ 0)
    (h5 : TateFilteredInvariants S.PD) (h7 : fontCore S.PD) (hbk : bkADim S.PD)
    (heul : ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : S.G → M →+ M), (∀ m, a 1 m = m) →
      (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, S.PD.p ^ r • m = 0) →
      (∀ m, IsLocallyConstant fun g => a g m) →
      {c : S.G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : S.G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (Module.finrank S.Qp S.K + 2))
    (hchi : ∀ e : ℕ, 0 < e → ∃ g : S.G, (S.PD.χ g : S.Qp) ^ e ≠ 1)
    (φ : S.G) (hφ : (Subgroup.zpowers φ ⊔ S.IK).topologicalClosure = ⊤)
    (δ : S.G → S.LL) (hδ : δ ∈ finiteCocycles S.PD (1 : Representation S.LL S.G S.LL))
    (hδI : ∀ g ∈ S.IK, δ g = 0) (hδ0 : δ ≠ 0) : TBeAt S := by
  intro e Ve h1 hχ
  obtain ⟨hDR, hFil⟩ := GlobalTheory.isDR_and_DdR_le_Fil_zero_of_twist S.PD Ve.ρ e hχ
  have hpos : 0 < e → HfD S.PD Ve.L = BD Ve.L ∧ BD Ve.L ≠ ⊥ := by
    intro he
    obtain ⟨g, hg1⟩ := hchi e he
    have hu : ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one, ← map_pow, map_eq_one_iff _ (algebraMap S.Qp S.LL).injective]
      exact hg1
    exact ⟨HfD_eq_BD S.PD Ve (GlobalTheory.HfZero.z1f_le_b1 S.PD h5 h7 hO (toG Ve) hDR hFil
      (fixed_points_trivial_of_scalar_action_ne_one Ve _ _ hu (hχ _))), BD_ne_bot hO Ve h1 _ _ hu (hχ _)⟩
  have hzero : e = 0 → HfD S.PD Ve.L ≠ ⊥ ∧ ∀ c : S.G → Ve.V ⧸ Ve.L.T, c ∈ HfD S.PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ S.IK, c g = actD Ve.L g x - x) := by
    rintro rfl
    simp only [pow_zero, one_smul] at hχ
    have htop : H0V Ve.ρ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine (Submodule.mem_iInf _).2 fun g => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hχ, LinearMap.id_apply, sub_self]
    have hdim : ((Module.finrank S.LL (FiniteCohomology S.PD Ve.ρ) : ℕ) : ℤ) =
        Module.finrank S.LL ↥(H0V Ve.ρ) + ((Module.finrank S.LL ↥(DdR S.PD Ve.ρ) : ℤ) -
          Module.finrank S.LL ↥(DdR S.PD Ve.ρ ⊓ FilV S.PD (LL := S.LL) (V := Ve.V) 0)) :=
      hbk _ _ hO (toG Ve) hDR
    rw [inf_eq_left.2 hFil, sub_self, add_zero, htop, finrank_top, h1] at hdim
    exact GlobalTheory.UnramifiedClasses.HfD_eq_unramified S.PD hO Ve h1 hχ (by exact_mod_cast hdim) S.IK φ hφ δ hδ hδI hδ0
  refine ⟨fun n => ?_, fun he => (hpos he).1, fun he => (hzero he).2⟩
  have hne : HfD S.PD Ve.L ≠ ⊥ := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exact (hzero he).1
    · rw [(hpos he).1]; exact (hpos he).2
  haveI := hfin n
  haveI : IsDomain S.O := hO.1.1
  have key := len_part S.PD hO Ve h1 S.PD.p n (Module.finrank S.Qp S.K) (pow_ne_zero n hp)
    (heul n) hne
  have hord : Module.length S.O (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O) ^ n}) =
      n • Module.length S.O (S.O ⧸ Ideal.span {((S.PD.p : ℕ) : S.O)}) :=
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hp) n
  unfold lenOl
  rw [Nat.cast_mul, mul_assoc, ← nsmul_eq_mul n, ← hord]
  exact key

theorem exists_unr (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) :
    ∃ δ : ↥(GK K) → ↥LL.1,
    δ ∈ finiteCocycles ((D.loc l).PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) ∧ (∀ g ∈ IK K, δ g = 0) ∧
      δ ≠ 0 := by
  obtain ⟨δ, hδc, hδm, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  have hcont : Continuous (algebraMap ℚ_[l] ↥LL.1) :=
    continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))
  refine ⟨fun g => algebraMap ℚ_[l] ↥LL.1 (δ g), GlobalTheory.UnramifiedCrys.unramified_mem_Z1f D l K LL _ ?_, ?_, ?_⟩
  · refine ⟨⟨hcont.comp hδc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · beta_reduce
      rw [hδm, map_add (f := _)]; rfl
    · beta_reduce
      rw [hδI g hg, map_zero, map_zero, sub_zero]
  · intro g hg
    beta_reduce
    rw [hδI g hg, map_zero]
  · intro h0
    exact hg₀ ((map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective).1 (congrFun h0 g₀))

theorem twist_torsion_facts : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  intro D HW F hA hB l _ K s LL h S E
  obtain ⟨-, hA2, -, hA4, hA5, -, hA7, -, -⟩ := hA
  obtain ⟨hO, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  haveI := K.2
  have hc : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨δ, hδ, hδI, hδ0⟩ := exists_unr D l K LL
  have hp : S.PD.p = l := (D.loc l).PD_p K
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  letI : TopologicalSpace S.Qp := (inferInstance : TopologicalSpace ℚ_[l])
  haveI : CompactSpace S.G := hc
  haveI : IsTopologicalGroup S.G := (inferInstance : IsTopologicalGroup ↥(GK K))
  haveI : IsTopologicalRing S.LL := hO.2.2.2.1
  refine tbe_of S hO ?_ ?_ (hA5 l K) (hA7 l K) (hB l K).2.1 ?_ ?_ φ hφ δ hδ hδI hδ0
  · rw [hp]; exact hfin
  · rw [hp]; exact hl0
  · rw [hp]; exact GlobalTheory.CocycleCount.cocycles_finite_ncard_le hA2 hA4 l K
  · intro e he
    obtain ⟨g, hg, hg1⟩ := GlobalTheory.Cyc.exists_mem_GK_chi_pow_ne_one l (D.loc l).χQ (D.loc l).χQ_cyc K e he
    refine ⟨⟨g, hg⟩, ?_⟩
    have := (D.loc l).PD_χ K ⟨g, hg⟩
    change (((D.loc l).PD K).χ ⟨g, hg⟩ : ℚ_[l]) ^ e ≠ 1
    rw [this]
    exact hg1

end GlobalTheory.TwistTors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrimeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_good_reduction_at_prime : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  first | exact @GlobalTheory.TwistTors.twist_torsion_facts | exact GlobalTheory.TwistTors.twist_torsion_facts | (intros; apply GlobalTheory.TwistTors.twist_torsion_facts <;> assumption)
end
