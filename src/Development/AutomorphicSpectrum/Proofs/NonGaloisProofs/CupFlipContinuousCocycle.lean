module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.CupFlip

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

theorem continuous_act (A : GRep G Qp LL O) : Continuous fun p : G × A.V => A.ρ p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A.V
  let b := Module.finBasis LL A.V
  have e : (fun p : G × A.V => A.ρ p.1 p.2) =
      fun p => ∑ i, (b.repr p.2 i) • A.ρ p.1 (b i) := by
    funext p
    have h := congrArg (A.ρ p.1) (b.sum_repr p.2)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  have h1 : Continuous fun v : A.V => b.coord i v :=
    IsModuleTopology.continuous_of_linearMap (b.coord i)
  exact (h1.comp continuous_snd).smul ((A.cont (b i)).comp continuous_fst)

theorem continuous_pair (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) :
    Continuous fun p : A.V × A'.V => P p.1 p.2 := by
  have := IsModuleTopology.toContinuousSMul LL A'.V
  exact IsModuleTopology.continuous_bilinear_of_finite_left P

theorem continuous_cup (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL) {a : G → A.V}
    {b : G → A'.V} (ha : Continuous a) (hb : Continuous b) : Continuous (cupL A'.ρ P a b) :=
  (continuous_pair A A' P).comp ((ha.comp continuous_fst).prodMk
    ((continuous_act A').comp (continuous_fst.prodMk (hb.comp continuous_snd))))

end Top

section Cup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} {P : V →ₗ[LL] V' →ₗ[LL] LL}


omit [TopologicalSpace G] in
theorem char_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (g : G) (x : V) (y : V') : charRep (cycLL PD LL) g (P x y) = P (ρ g x) (ρ' g y) := by
  rw [hd]
  rfl

theorem d2_cup (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (cupL ρ' P a b) = 0 := by
  funext ⟨g, h, k⟩
  show charRep (cycLL PD LL) g (P (a h) (ρ' h (b k))) - P (a (g * h)) (ρ' (g * h) (b k)) +
    P (a g) (ρ' g (b (h * k))) - P (a g) (ρ' g (b h)) = 0
  rw [char_pair PD hd, ha, hb, map_mul, Module.End.mul_apply]
  simp only [map_add (f := _), LinearMap.add_apply]
  ring

theorem d1_pair (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) (fun g => P (a g) (b g)) =
      -cupL ρ' P a b - cupL ρ P.flip b a := by
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P (a h) (b h)) - P (a (g * h)) (b (g * h)) + P (a g) (b g) =
    -P (a g) (ρ' g (b h)) - P (ρ g (a h)) (b g)
  rw [char_pair PD hd, ha, hb]
  simp only [map_add (f := _), LinearMap.add_apply]
  ring

variable [TopologicalSpace LL]

theorem cob_of_flip [IsTopologicalRing LL]
    (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} (ha : ∀ g h, a (g * h) = a g + ρ g (a h))
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P (a g) (b g))
    (h : CobL PD (cupL ρ P.flip b a)) : CobL PD (cupL ρ' P a b) := by
  obtain ⟨u, hu, e⟩ := h
  refine ⟨-u - fun g => P (a g) (b g), hu.neg.sub hc, ?_⟩
  rw [map_sub, map_neg, e, d1_pair PD hd ha hb]
  abel

theorem cob_of_left (hd : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    {a : G → V} {b : G → V'} {x : V} (ha : ∀ g, a g = ρ g x - x)
    (hb : ∀ g h, b (g * h) = b g + ρ' g (b h)) (hc : Continuous fun g => P x (b g)) :
    CobL PD (cupL ρ' P a b) := by
  refine ⟨fun g => P x (b g), hc, ?_⟩
  funext ⟨g, h⟩
  show charRep (cycLL PD LL) g (P x (b h)) - P x (b (g * h)) + P x (b g) =
    P (a g) (ρ' g (b h))
  rw [char_pair PD hd, ha, hb]
  simp only [map_add (f := _), map_sub, LinearMap.sub_apply]
  ring

end Cup

end GlobalTheory.CompanionTheory.CupFlip
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TopCoh

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

theorem coboundary_of_characters (hT : LocalTateDualityK) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (hK : FiniteDimensional ℚ_[l] K) (n : ℕ) (hn : 0 < n)
    (hχ : Continuous fun g => ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (z : Formalism.GaloisCohomology.GK l K × Formalism.GaloisCohomology.GK l K → M) (hz : Continuous z)
    (hcoc : ∀ g h k, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • z (h, k) - z (g * h, k) +
      z (g, h * k) - z (g, h) = 0)
    (hchar : ∀ ψ : M →+ ZMod (l ^ n), ∃ f : Formalism.GaloisCohomology.GK l K → ZMod (l ^ n), Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) :
    ∃ f : Formalism.GaloisCohomology.GK l K → M, Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M := scalRep M (cycK l K n)
  have hrho : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp
      ((hχ.comp continuous_fst).prodMk continuous_snd)
  have hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _)) := ⟨hz, hcoc⟩
  have hb := (hT l K hK n M rho hn hrho).2.2.2.2
  have hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0 := by
    refine LinearMap.ext fun φ => ?_
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    let φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ.1
    obtain ⟨f, hf, hd⟩ := hchar φ'.toAddMonoidHom
    exact ⟨f, hf, funext fun p => hd p.1 p.2⟩
  have h0 := hb.1 (hzero.trans (map_zero _).symm)
  obtain ⟨c, hc, hd⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact ⟨c, hc, fun g h => congrFun hd (g, h)⟩

end GlobalTheory.CompanionTheory.LocDual.TopCoh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Pair

private theorem exists_injective_zmod_addCircle_torsion (N : ℕ) [NeZero N] :
    ∃ j : ZMod N →+ AddCircle (1 : ℚ), Function.Injective j ∧
      ∀ t : AddCircle (1 : ℚ), N • t = 0 → t ∈ j.range := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hf : zmultiplesHom (AddCircle (1 : ℚ)) (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) (N : ℤ) = 0 := by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨ZMod.lift N ⟨_, hf⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro k hk
    have hk' : ((k.val : ℤ) : ZMod N) = k := by simp
    rw [← hk', ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hk
    obtain ⟨m, hm⟩ := hk
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
    have hlt := ZMod.val_lt k
    have hm' : (m : ℚ) * N = k.val := by rw [hm]; push_cast; field_simp
    have hm'' : m * (N : ℤ) = (k.val : ℤ) := by exact_mod_cast hm'
    have hNpos : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hlt' : (k.val : ℤ) < N := by exact_mod_cast hlt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hm0, zero_mul] at hm''
    have hv : k.val = 0 := by exact_mod_cast hm''.symm
    exact (ZMod.val_eq_zero k).1 hv
  · intro t ht
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    change N • ((r : ℚ) : AddCircle (1 : ℚ)) = 0 at ht
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    have hm' : (m : ℚ) = N * r := by simpa [zsmul_eq_mul, nsmul_eq_mul] using hm
    refine ⟨(m : ZMod N), ?_⟩
    rw [ZMod.lift_coe]
    change m • (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = ((r : ℚ) : AddCircle (1 : ℚ))
    rw [← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one_div, div_eq_iff hN, hm']
    ring

theorem mem_of_cup_flip {N : ℕ} [NeZero N] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (ψ : Γ →* (ZMod N)ˣ) {M : Type} [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod N) Γ M)
    (hrho : ReciprocityTheory.Gal.ContAction (rho.comp (MonoidHom.id Γ)))
    (e : ReciprocityTheory.Gal.H2 ((ReciprocityTheory.Gal.charRep ψ).comp (MonoidHom.id Γ)) ≃ₗ[ZMod N] ZMod N)
    (hs : Function.Surjective (ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho).flip)
    (A : AddSubgroup (ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))))
    (hB : ∀ z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)),
      z.1 ∈ ReciprocityTheory.Gal.B1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) → z ∈ A)
    (z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)))
    (h : ∀ y : ReciprocityTheory.Gal.H1 (rho.comp (MonoidHom.id Γ)),
      (∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0) →
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk z) y = 0) : z ∈ A := by
  classical
  by_contra hz
  let π : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+
      ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) :=
    { toFun := fun s => Submodule.Quotient.mk s
      map_zero' := Submodule.Quotient.mk_zero _
      map_add' := fun s t => Submodule.Quotient.mk_add _ }
  have hzA : π z ∉ A.map π := by
    rintro ⟨s, hs', hsz⟩
    apply hz
    have hq : (Submodule.Quotient.mk s :
        ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))) = Submodule.Quotient.mk z := hsz
    rw [Submodule.Quotient.eq] at hq
    have hq' := Submodule.neg_mem _ hq
    rw [neg_sub] at hq'
    have hmem : z - s ∈ A := hB (z - s) hq'
    have hsum := A.add_mem hmem hs'
    rwa [sub_add_cancel] at hsum
  have hq0 : (QuotientAddGroup.mk (π z) : _ ⧸ A.map π) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hzA
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq0
  let c' : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ AddCircle (1 : ℚ) :=
    c.comp (QuotientAddGroup.mk' (A.map π))
  have htors : ∀ h, N • c' h = 0 := by
    intro h
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨j, hj, hjr⟩ := exists_injective_zmod_addCircle_torsion N
  let φ0 : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ ZMod N :=
    (AddMonoidHom.ofInjective hj).symm.toAddMonoidHom.comp
      (c'.codRestrict j.range (fun h => hjr _ (htors h)))
  have key : ∀ h, j (φ0 h) = c' h := by
    intro h
    have hh := (AddMonoidHom.ofInjective hj).apply_symm_apply
      (c'.codRestrict j.range (fun h => hjr _ (htors h)) h)
    rw [Subtype.ext_iff, AddMonoidHom.ofInjective_apply] at hh
    exact hh
  let Lm := e.symm.toLinearMap ∘ₗ φ0.toZModLinearMap N
  obtain ⟨y, hy⟩ := hs Lm
  have hval : ∀ s, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y =
      e.symm (φ0 (π s)) := by
    intro s
    have hh := LinearMap.congr_fun hy (Submodule.Quotient.mk s)
    rw [LinearMap.flip_apply] at hh
    rw [hh]
    rfl
  have hyA : ∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0 := by
    intro s hs'
    rw [hval]
    have h0 : φ0 (π s) = 0 := by
      apply hj
      rw [key, map_zero]
      show c (QuotientAddGroup.mk (π s)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_map_of_mem π hs'), map_zero]
    rw [h0, map_zero]
  have hfin := h y hyA
  rw [hval, LinearEquiv.map_eq_zero_iff] at hfin
  apply hc
  have hj0 := congrArg j hfin
  rw [key, map_zero] at hj0
  exact hj0

theorem exists_equiv_dual {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ ReciprocityTheory.Gal.TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  classical
  have hfin : ∀ (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Finite (Module.Dual (ZMod n) A) := fun A _ _ _ => (GlobalTheory.CocycleCount.card_linear_le n A).1
  let f : M' →+ Module.Dual (ZMod n) M :=
    { toFun := fun y => (P.flip y).toZModLinearMap n
      map_zero' := LinearMap.ext fun x => by
        show P x 0 = 0
        exact map_zero (P x)
      map_add' := fun y y' => LinearMap.ext fun x => by
        show P x (y + y') = P x y + P x y'
        exact map_add (P x) y y' }
  let g : M → Module.Dual (ZMod n) M' := fun x => (P x).toZModLinearMap n
  have hf : Function.Injective f := by
    intro y y' hyy
    have hyx : ∀ x, P x (y - y') = 0 := by
      intro x
      have hx := LinearMap.congr_fun hyy x
      change P x y = P x y' at hx
      rw [map_sub, hx, sub_self]
    exact sub_eq_zero.1 (h2 _ hyx)
  have hg : Function.Injective g := by
    intro x x' hxx
    have hxy : ∀ y, P (x - x') y = 0 := by
      intro y
      have hy := LinearMap.congr_fun hxx y
      change P x y = P x' y at hy
      rw [map_sub, AddMonoidHom.sub_apply, hy, sub_self]
    exact sub_eq_zero.1 (h1 _ hxy)
  haveI := hfin M
  haveI := hfin M'
  have c1 := Nat.card_le_card_of_injective f hf
  have c2 := Nat.card_le_card_of_injective g hg
  rw [GlobalTheory.ZModDual.card_dual_eq] at c1 c2
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [GlobalTheory.ZModDual.card_dual_eq]; exact c2)
  exact ⟨AddEquiv.ofBijective f hb, fun y x => rfl⟩

end GlobalTheory.CompanionTheory.LocDual.Pair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.GenChar

theorem exists_addHom_zmod_ne_zero {N : ℕ} [NeZero N] {A : Type} [AddCommGroup A]
    (hA : ∀ a : A, N • a = 0) {q : A} (hq : q ≠ 0) : ∃ f : A →+ ZMod N, f q ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq
  let c' : A →+ AddCircle (1 : ℚ) := c
  have hc' : c' q ≠ 0 := hc
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  let g : ℤ →+ AddCircle (1 : ℚ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      ((AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Int.castAddHom ℚ))
  have hg : ∀ z : ℤ, g z = QuotientAddGroup.mk ((z : ℚ) * (N : ℚ)⁻¹) := fun z => rfl
  have hgN : g N = 0 := by
    rw [hg, Int.cast_natCast, mul_inv_cancel₀ hN]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  let ι : ZMod N →+ AddCircle (1 : ℚ) := ZMod.lift N ⟨g, hgN⟩
  have hι : ∀ z : ℤ, ι z = g z := fun z => ZMod.lift_coe N ⟨g, hgN⟩ z
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).2 fun m hm => ?_
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective m
    rw [hι, hg] at hm
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 hm)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have h2 : (z : ℚ) = (N : ℚ) * k := by
      field_simp at hk
      linarith
    exact_mod_cast h2
  have hmem : ∀ a : A, c' a ∈ ι.range := by
    intro a
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (c' a)
    have h1 : N • c' a = 0 := by rw [← map_nsmul, hA, map_zero]
    have h0 : (N • r : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hr]
      exact h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h0
    refine AddMonoidHom.mem_range.2 ⟨(k : ZMod N), ?_⟩
    rw [hι, hg, ← hr]
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    rw [hk]
    field_simp
  refine ⟨(AddMonoidHom.ofInjective hinj).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict c' ι.range hmem), ?_⟩
  intro h0
  apply hc'
  have h1 : AddMonoidHom.codRestrict c' ι.range hmem q = 0 := by
    have h3 := congrArg (AddMonoidHom.ofInjective hinj) h0
    simpa using h3
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem exists_mul_eq_socle {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) {x : O ⧸ Ideal.span {ϖ ^ (s + 1)}} (hx : x ≠ 0) :
    ∃ o, o * x = Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  have hn : n ≤ s := by
    by_contra hlt
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.succ_le_of_lt (not_le.1 hlt))) _
  refine ⟨Ideal.Quotient.mk _ (↑u⁻¹ * ϖ ^ (s - n)), ?_⟩
  rw [← map_mul, hu]
  congr 1
  calc ↑u⁻¹ * ϖ ^ (s - n) * (↑u * ϖ ^ n) = (↑u⁻¹ * ↑u) * (ϖ ^ (s - n) * ϖ ^ n) := by ring
    _ = ϖ ^ s := by rw [Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hn]

theorem socle_ne_zero {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : Irreducible ϖ) (s : ℕ) :
    Ideal.Quotient.mk (Ideal.span {ϖ ^ (s + 1)}) (ϖ ^ s) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  omega

theorem exists_generating_character : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  intro O _ _ _ ϖ hϖ r N hN hfin hNmem
  haveI : NeZero N := ⟨by omega⟩
  have htors : ∀ a : O ⧸ Ideal.span {ϖ ^ r}, N • a = 0 := by
    intro a
    have hN0 : ((N : O ⧸ Ideal.span {ϖ ^ r})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ϖ ^ r}))]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hNmem
    rw [nsmul_eq_mul, hN0, zero_mul]
  have key : ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N,
      ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0 := by
    cases r with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_zero, Ideal.span_singleton_one]
      exact Submodule.mem_top
    | succ s =>
      obtain ⟨ψ₀, hψ₀⟩ := exists_addHom_zmod_ne_zero htors (socle_ne_zero hϖ s)
      refine ⟨ψ₀, fun x hx => ?_⟩
      by_contra hne
      obtain ⟨o, ho⟩ := exists_mul_eq_socle hϖ s hne
      have h5 := hx o
      rw [ho] at h5
      exact hψ₀ h5
  obtain ⟨ψ₀, hψ₀⟩ := key
  refine ⟨ψ₀, hψ₀, ?_⟩
  let Φ : (O ⧸ Ideal.span {ϖ ^ r}) → ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    fun o => ψ₀.comp (AddMonoidHom.mulLeft o)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∀ x, ψ₀ ((a - b) * x) = 0 := by
      intro x
      have h6 : ψ₀ (a * x) = ψ₀ (b * x) := DFunLike.congr_fun hab x
      rw [sub_mul, map_sub, h6, sub_self]
    have h7 : a - b = 0 := hψ₀ (a - b) (fun o => by rw [mul_comm]; exact h0 o)
    exact sub_eq_zero.1 h7
  haveI : Finite ((O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N) :=
    Finite.of_injective (fun f : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N =>
      (f : (O ⧸ Ideal.span {ϖ ^ r}) → ZMod N)) DFunLike.coe_injective
  have hbij := hinj.bijective_of_nat_card_le (GlobalTheory.natCard_addMonoidHom_zmod_le N _)
  intro ψ
  obtain ⟨o, ho⟩ := hbij.2 ψ
  exact ⟨o, fun x => by rw [← ho]; rfl⟩

end GlobalTheory.CompanionTheory.LocDual.GenChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotientStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perfect_character_quotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  first | exact @GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character | exact GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character | (intros; apply GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character <;> assumption)
end
end
