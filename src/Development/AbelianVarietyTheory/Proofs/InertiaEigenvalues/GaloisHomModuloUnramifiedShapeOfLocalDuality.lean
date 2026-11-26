module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditions
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardUnramifiedLevelTrivialAction
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def LCHomLev {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (M : Type)
    [AddCommGroup M] [Module O M] (c : O) (I : Subgroup G) : Type :=
  {f : G → Lev M c // IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧ ∀ g ∈ I, f g = 0}

section Triv

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem mem_coboundaries_of_trivial {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m) (x : G → M) :
    x ∈ Formalism.NG.coB1 ρ ↔ x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    funext g
    show ρ g v - v = 0
    rw [hρ, sub_self]
  · rintro rfl
    exact zero_mem _

theorem mk_eq_zero_of_triv {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m)
    (z : Formalism.NG.coZ1s ρ) : (Submodule.Quotient.mk z : Formalism.NG.H1z ρ) = 0 ↔ (z : G → M) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    mem_coboundaries_of_trivial hρ]

variable [TopologicalSpace G]

theorem card_torsion_eq_locConstHom_trivial_action (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m)
    (I : Subgroup G) (c : O) :
    Nat.card (LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (LCHomLev M c I) := by
  have hres : ∀ (g : I) (m : M), Formalism.NG.resRep ρ I g m = m := fun g m => hρ g m
  let coc : LCHomLev M c I → Formalism.NG.coZ1s ρ := fun f =>
    ⟨fun g => (f.1 g).val, fun a b => by
      show (f.1 (a * b)).val = (f.1 a).val + ρ a (f.1 b).val
      rw [hρ, f.2.2.1, Lev.val_add]⟩
  let F : LCHomLev M c I → LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype)) := fun f =>
    ⟨⟨⟨Submodule.Quotient.mk (coc f),
        Submodule.mem_map.2 ⟨coc f, f.2.1.comp Lev.val, rfl⟩⟩,
      by
        change (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I (coc f)) :
          Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0
        rw [mk_eq_zero_of_triv hres]
        funext g
        show (f.1 g.1).val = 0
        rw [f.2.2.2 g.1 g.2]
        rfl⟩,
      by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        apply Subtype.ext
        show c • (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) = 0
        rw [← Submodule.Quotient.mk_smul, mk_eq_zero_of_triv hρ]
        funext g
        exact Lev.smul_val (f.1 g)⟩
  have hinj : ∀ f f' : LCHomLev M c I, (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) =
      Submodule.Quotient.mk (coc f') → f = f' := by
    intro f f' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_of_triv hρ] at h
    apply Subtype.ext
    funext g
    apply Lev.ext
    have h1 : (f.1 g).val - (f'.1 g).val = 0 := congrFun h g
    exact sub_eq_zero.1 h1
  refine (Nat.card_eq_of_bijective F ⟨fun f f' h => hinj f f' ?_, fun y => ?_⟩).symm
  · exact congrArg (fun y => y.1.1.1) h
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.1.1.2
    have hk : (Submodule.Quotient.mk (c • z) : Formalism.NG.H1z ρ) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      change c • Submodule.mkQ _ z = 0
      rw [hzy]
      exact congrArg (fun w => w.1.1) (LinearMap.mem_ker.1 y.2)
    rw [mk_eq_zero_of_triv hρ] at hk
    have hz0 : ∀ g, c • (z : G → M) g = 0 := fun g => congrFun hk g
    have hu : Formalism.NG.resH1 ρ I (Submodule.mkQ _ z) = 0 := by
      rw [hzy]
      exact y.1.2
    have hu' : (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I z) :
        Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0 := hu
    rw [mk_eq_zero_of_triv hres] at hu'
    have hI0 : ∀ g ∈ I, (z : G → M) g = 0 := fun g hg => congrFun hu' ⟨g, hg⟩
    let f : LCHomLev M c I := ⟨fun g => Lev.mk ((z : G → M) g) (hz0 g),
      IsLocallyConstant.desc _ Lev.val hz (fun a b h => Lev.ext h),
      fun a b => Lev.ext (by rw [Lev.val_add, Lev.val_mk, Lev.val_mk, Lev.val_mk, z.2 a b, hρ]),
      fun g hg => Lev.ext (by rw [Lev.val_mk, hI0 g hg]; rfl)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.Quotient.mk (coc f) = y.1.1.1
    rw [← hzy]
    rfl

end Triv

section H1Triv

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {N : Type}
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

theorem H1_mk_eq_zero_iff_of_trivial {rho : Representation R Γ N} (hrho : ∀ g m, rho g m = m)
    (z : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = 0 ↔ z = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    funext g
    rw [hm g, hrho, sub_self]
    rfl
  · rintro rfl
    exact ⟨0, fun g => by rw [map_zero, sub_zero]; rfl⟩

theorem mk_mem_H1ur_of_vanish (rho : Representation R Γ N) (J : Subgroup Γ) (z : Z1 rho)
    (hz : ∀ g ∈ J, z.1 g = 0) : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J := by
  change (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
    H1 (rho.comp J.subtype)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact (mem_coboundaries1 _ _).2 ⟨0, fun g => by rw [map_zero, sub_zero]; exact hz g.1 g.2⟩

theorem vanish_of_mk_mem_H1ur (rho : Representation R Γ N) (J : Subgroup Γ)
    (hJ : ∀ g ∈ J, ∀ m, rho g m = m) (z : Z1 rho)
    (hz : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J) (g : Γ) (hg : g ∈ J) : z.1 g = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
      H1 (rho.comp J.subtype)) = 0 := hz
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  have h3 : z.1 g = rho g m - m := hm ⟨g, hg⟩
  rw [h3, hJ g hg, sub_self]

end H1Triv

theorem card_LCHomLev_eq_unrK {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m) (I : Subgroup G)
    (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) (r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    letI := levZ (M := M) p r h
    Nat.card (LCHomLev M c I) =
      Nat.card (Formalism.GaloisCohomology.unrK (levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  letI := levZ (M := M) p r h
  let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  let F : LCHomLev M c I → Formalism.GaloisCohomology.unrK ρ' := fun f =>
    ⟨Submodule.Quotient.mk ⟨f.1 ∘ i.symm, (f.2.1.comp_continuous i.symm.continuous).continuous,
        fun a b => by
          show f.1 (i.symm (a * b)) = f.1 (i.symm a) + ρ' a (f.1 (i.symm b))
          rw [hρ', map_mul, f.2.2.1]⟩,
      mk_mem_H1ur_of_vanish ρ' _ _ fun g hg => by
        show f.1 (i.symm g) = 0
        exact f.2.2.2 _ ((hI _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg))⟩
  refine Nat.card_eq_of_bijective F ⟨fun f f' hff => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hff
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, H1_mk_eq_zero_iff_of_trivial hρ', sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    funext g
    have h3 := congrFun h2 (i g)
    simpa only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] using h3
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx : (Submodule.Quotient.mk z : H1 ρ') ∈ H1ur ρ' (Formalism.GaloisCohomology.inertiaK p K) := by
      rw [hz]; exact x.2
    let f : LCHomLev M c I := ⟨fun g => z.1 (i g),
      ((IsLocallyConstant.iff_continuous _).2 z.2.1).comp_continuous i.continuous,
      fun a b => by
        show z.1 (i (a * b)) = z.1 (i a) + z.1 (i b)
        rw [map_mul, z.2.2, hρ'],
      fun g hg => vanish_of_mk_mem_H1ur ρ' _ (fun σ _ m => hρ' σ m) z hx (i g) ((hI g).1 hg)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change Submodule.Quotient.mk _ = x.1
    rw [← hz]
    congr 1
    apply Subtype.ext
    funext g
    show z.1 (i (i.symm g)) = z.1 g
    rw [ContinuousMulEquiv.apply_symm_apply]


open scoped ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem card_unramifiedClasses_eq_card_invariants_localGalois {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    (rho : Representation R (Formalism.GaloisCohomology.GK p K) N) (hrho : ReciprocityTheory.Gal.ContAction rho)
    (hI : ∀ σ ∈ Formalism.GaloisCohomology.inertiaK p K, ∀ m, rho σ m = m) :
    Nat.card (Formalism.GaloisCohomology.unrK rho) = Nat.card (H0 rho) := by
  change Nat.card (Neutral.B1.H1ur rho (Neutral.B1.inertiaK p K)) = Nat.card (Neutral.B1.H0 rho)
  replace hI : ∀ σ ∈ Neutral.B1.inertiaK p K, ∀ m, rho σ m = m := hI
  rw [← ReciprocityTheory.DiscreteGroups.LocalClassField.subG_Kur_eq_inertiaK hK] at hI ⊢
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles.card_H1ur hrho hI (s := ReciprocityTheory.DiscreteGroups.LocalClassField.frobK p K)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur hK)

theorem card_unr_lev_of_triv : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {ϖ : O},
    Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O G M), (∀ g m, ρ g m = m) →
    ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) → ∀ n : ℕ,
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro p _ K hK O _ _ _ _ ϖ hϖ hp G _ _ i M _ _ e ρ hρ I hI n
  have hpn : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} :=
    Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hp) n)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI := levZ (M := M) p n hpn
  obtain ⟨hfin, hcard⟩ := levKO_card hϖ e n
  haveI := hfin
  let ρ' := levRepZ p n hpn (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  have hcont : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ']
    exact continuous_snd
  calc _ = Nat.card (LCHomLev M (ϖ ^ n) I) := card_torsion_eq_locConstHom_trivial_action ρ hρ I (ϖ ^ n)
    _ = Nat.card (Formalism.GaloisCohomology.unrK ρ') := card_LCHomLev_eq_unrK i ρ hρ I hI n (ϖ ^ n) hpn
    _ = Nat.card (H0 ρ') :=
        card_unramifiedClasses_eq_card_invariants_localGalois hK ρ' hcont (fun σ _ m => hρ' σ m)
    _ = Nat.card (Lev M (ϖ ^ n)) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x g => hρ' g x)
    _ = _ := hcard

end GlobalTheory.ShapeNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulEqZeroOfMul
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.UnramifiedH2Bound

open GlobalTheory.ShapeNeg GlobalTheory.CyclotomicH2Bound

theorem pow_mul_eq_zero_of_mul {p : ℕ} (hp : p.Prime) {n m : ℕ} {b : ℤ} (hb : ¬ ((p : ℤ) ^ m ∣ b))
    {x : ZMod (p ^ n)} (hx : (b : ZMod (p ^ n)) * x = 0) : ((p ^ m : ℕ) : ZMod (p ^ n)) * x = 0 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩

  have hbx : b • x = 0 := by rwa [zsmul_eq_mul]
  have h1 : (addOrderOf x : ℤ) ∣ b := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbx
  have h2 : addOrderOf x ∣ p ^ n := by
    have := addOrderOf_dvd_card (x := x)
    rwa [ZMod.card] at this
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hjm : j < m := by
    by_contra hcon
    push Not at hcon
    apply hb
    rw [hjx] at h1
    exact (pow_dvd_pow (p : ℤ) hcon).trans (by exact_mod_cast h1)
  have h3 : addOrderOf x ∣ p ^ m := by
    rw [hjx]; exact pow_dvd_pow _ hjm.le
  have h4 : (p ^ m : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h3
  rwa [nsmul_eq_mul] at h4

theorem h2_bounded_of_trivial_action : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} → (p : O) ≠ 0 →
    ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) →
    ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M), (∀ g m, ρ g m = m) →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ hp0 M _ _ eM ρ hρ hcont
  have hp : p.Prime := Fact.out

  obtain ⟨σ, N, ζ', hζ'1, hσζ'⟩ :=
    GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity (p := p) (K := K) hK 1 Nat.one_pos
  rw [pow_one] at hσζ'

  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : O) ^ N}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero N hp0) hϖ
  have hfinQ : Finite (O ⧸ Ideal.span {(p : O) ^ N}) := by
    rw [hk]; exact finite_quot hϖ k
  refine ⟨(p ^ N) ^ ((p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  have htriv : ∀ (g : Formalism.GaloisCohomology.GK p K) (m : Lev M (ϖ ^ n)), levRepZ p n h ρ g m = m := by
    intro g m
    rw [levRepZ_apply]
    exact Lev.ext (by rw [levRep_val, hρ])

  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hx₀k : (ϖ ^ n) • x₀ = 0 := Lev.ext (by rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  have hfinL : Finite (Lev M (ϖ ^ n)) := by
    have := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) ?_
    intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n hx₀k t⟩
  obtain ⟨⟨e⟩, -, -, -, hcup⟩ :=
    hTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)

  have hkill : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (m : Lev M (ϖ ^ n)), ((p ^ N : ℕ) : ZMod (p ^ n)) * φ.1 m = 0 := by
    intro φ m
    by_cases hnN : n ≤ N
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p hnN), zero_mul]
    push Not at hnN
    obtain ⟨ζ, hζ⟩ := exists_prim p n
    have hσζn : (σ ζ) ^ (p ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζn
    have hcyc := cycK_eq_of_prim n σ hζ a ha.symm
    have hfixm : ((Formalism.GaloisCohomology.cycK p K n σ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
        φ.1 (levRepZ p n h ρ σ⁻¹ m) = φ.1 m := by
      rw [← twDual_apply]
      exact DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp φ.2 σ) m
    rw [htriv, hcyc] at hfixm
    have hnd : ¬ ((p : ℤ) ^ N ∣ (a : ℤ) - 1) := by
      rintro ⟨d, hd⟩
      apply hσζ'
      have hζ'n : ζ' ^ (p ^ n) = 1 := by
        obtain ⟨c, hc⟩ := pow_dvd_pow p hnN.le
        rw [hc, pow_mul, hζ'1, one_pow]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hζ'n
      have hσ' : σ ζ' = ζ' ^ a := by
        rw [← hj, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
      have hne : ζ' ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero N hp.ne_zero)] at hζ'1
        exact zero_ne_one hζ'1
      have ha' : (a : ℤ) = 1 + ((p ^ N : ℕ) : ℤ) * d := by push_cast; linarith
      rw [hσ', ← zpow_natCast, ha', zpow_add₀ hne, zpow_one, zpow_mul, zpow_natCast, hζ'1,
        one_zpow, mul_one]
    have hb : (((a : ℤ) - 1 : ℤ) : ZMod (p ^ n)) * φ.1 m = 0 := by
      push_cast
      rw [sub_mul, one_mul, hfixm, sub_self]
    exact pow_mul_eq_zero_of_mul hp hnd hb

  have hTcard : Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ≤ p ^ N := by
    have key : ∀ z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0},
        z.1.val = p ^ (n - N) * (z.1.val / p ^ (n - N)) ∧ z.1.val / p ^ (n - N) < p ^ N := by
      intro z
      have hlt : z.1.val < p ^ (n - N) * p ^ N := by
        calc z.1.val < p ^ n := ZMod.val_lt _
          _ ≤ p ^ (n - N + N) := Nat.pow_le_pow_right hp.pos (by omega)
          _ = _ := pow_add _ _ _
      have hdvd : p ^ (n - N) ∣ z.1.val := by
        by_cases hnN : n ≤ N
        · rw [Nat.sub_eq_zero_of_le hnN, pow_zero]; exact one_dvd _
        · push Not at hnN
          have h1 : ((p ^ N * z.1.val : ℕ) : ZMod (p ^ n)) = 0 := by
            rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact z.2
          rw [ZMod.natCast_eq_zero_iff] at h1
          have h2 : p ^ n = p ^ N * p ^ (n - N) := by rw [← pow_add]; congr 1; omega
          have h1' : p ^ N * p ^ (n - N) ∣ p ^ N * z.1.val := by rw [← h2]; exact h1
          exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos N) h1'
      exact ⟨(Nat.mul_div_cancel' hdvd).symm, Nat.div_lt_of_lt_mul hlt⟩
    have hinj : Function.Injective
        (fun z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} => ((z.1.val / p ^ (n - N) : ℕ) : ZMod (p ^ N))) := by
      intro z w hzw
      have hz := key z
      have hw := key w
      have hv := congrArg ZMod.val hzw
      simp only [ZMod.val_cast_of_lt hz.2, ZMod.val_cast_of_lt hw.2] at hv
      apply Subtype.ext
      apply ZMod.val_injective
      rw [hz.1, hw.1, hv]
    have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
    calc _ ≤ Nat.card (ZMod (p ^ N)) := Nat.card_le_card_of_injective _ hinj
      _ = p ^ N := Nat.card_zmod _

  have hval : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (t : O),
      φ.1 (t • x₀) = φ.1 ((Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out • x₀) := by
    intro φ t
    have hmem : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out - t ∈
        Ideal.span {(p : O) ^ N} :=
      Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hout : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out = t + ((p ^ N : ℕ) : O) * s := by
      rw [Nat.cast_pow]; linear_combination -hs
    rw [hout, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, td_add, td_nsmul, nsmul_eq_mul,
      hkill φ, add_zero]
  have hΦ : Function.Injective (fun (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (q : O ⧸ Ideal.span {(p : O) ^ N}) =>
      (⟨φ.1 (q.out • x₀), hkill φ _⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro φ ψ hφψ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    obtain ⟨t, rfl⟩ := hx₀ m
    rw [hval φ t, hval ψ t]
    exact congrArg Subtype.val (congrFun hφψ (Ideal.Quotient.mk _ t))
  have hfinH0 : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Finite.of_injective _ hΦ
  have hH0card : Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) ≤ (p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := by
    calc _ ≤ Nat.card (O ⧸ Ideal.span {(p : O) ^ N} → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) :=
          Nat.card_le_card_of_injective _ hΦ
      _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := Nat.card_fun
      _ ≤ _ := Nat.pow_le_pow_left hTcard _

  have hsmul0 : ∀ φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))), ((p ^ N : ℕ) : ZMod (p ^ n)) • φ = 0 := by
    intro φ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    rw [Submodule.coe_smul, TDual.smul_apply, hkill φ m]
    rfl
  have hΨ : Function.Injective (fun (x : H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))))
      (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) =>
      (⟨e (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x φ), by
        have h0 := congrArg e (congrArg
          (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x) (hsmul0 φ))
        rw [LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.map_zero, LinearEquiv.map_zero,
          smul_eq_mul] at h0
        exact h0⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro x y hxy
    apply hcup.1
    apply LinearMap.ext
    intro φ
    apply e.injective
    exact congrArg Subtype.val (congrFun hxy φ)
  calc Nat.card (H2 (levRepZ p n h ρ))
      = Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := rfl
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))) → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) := Nat.card_le_card_of_injective _ hΨ
    _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.card_fun
    _ ≤ (p ^ N) ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.pow_le_pow_left hTcard _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos hp.pos N) hH0card

end GlobalTheory.UnramifiedH2Bound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality
namespace GlobalTheory.ShapeUnrTriv

open ReciprocityTheory.Gal Formalism.NG Formalism.RepresentationBoundsCohomology.BR ReciprocityTheory.ChartRestriction.T2 GlobalTheory.ShapeNeg

private theorem exists_smul_eq_of_card_ker_pow_eq_of_torsion {O : Type} [CommRing O] {B : Type} [AddCommGroup B]
    [Module O B] (ϖ : O) (q : ℕ) (hq : 0 < q)
    (hcount : ∀ n : ℕ, Nat.card ↥((ϖ ^ n • LinearMap.id : B →ₗ[O] B).ker) = q ^ n)
    (htors : ∀ b : B, ∃ n : ℕ, ϖ ^ n • b = 0) (b : B) : ∃ c : B, ϖ • c = b := by
  obtain ⟨m, hm⟩ := htors b
  have hfin : ∀ n : ℕ, Finite ↥((ϖ ^ n • LinearMap.id : B →ₗ[O] B).ker) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hcount n]; exact (pow_pos hq n).ne')
  have hmaps : ∀ x ∈ (ϖ ^ (m + 1) • LinearMap.id : B →ₗ[O] B).ker,
      (ϖ • LinearMap.id : B →ₗ[O] B) x ∈ (ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    rw [smul_smul, ← pow_succ]
    exact hx
  let f := (ϖ • LinearMap.id : B →ₗ[O] B).restrict hmaps
  have hker : Nat.card ↥(LinearMap.ker f) = q := by
    have e : ↥(LinearMap.ker f) ≃ ↥((ϖ ^ 1 • LinearMap.id : B →ₗ[O] B).ker) :=
      { toFun := fun x => ⟨x.1.1, by
          have := x.2
          simp only [LinearMap.mem_ker, f, LinearMap.restrict_apply, Subtype.ext_iff,
            LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_zero] at this
          simpa using this⟩
        invFun := fun y => ⟨⟨y.1, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at this ⊢
          rw [pow_succ, mul_smul, this, smul_zero]⟩, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at this
          simp only [LinearMap.mem_ker, f, LinearMap.restrict_apply, Subtype.ext_iff,
            LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_zero]
          exact this⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr e, hcount 1, pow_one]
  have hsplit := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv, hker, hcount (m + 1), pow_succ] at hsplit
  have hrange : Nat.card ↥(LinearMap.range f) =
      Nat.card ↥((ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker) := by
    rw [hcount m]
    exact Nat.eq_of_mul_eq_mul_right hq ((mul_comm _ _).trans hsplit.symm)
  have htop : (LinearMap.range f).toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrange
  have hmem : (⟨b, by simpa using hm⟩ : ↥((ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker)) ∈
      LinearMap.range f := by
    change _ ∈ (LinearMap.range f).toAddSubgroup
    rw [htop]
    trivial
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x.1, ?_⟩
  have := congrArg Subtype.val hx
  simpa [f] using this

private theorem card_ker_smul_eq_mul_card_ker_quotient_of_divisible {O : Type} [CommRing O] {A : Type} [AddCommGroup A]
    [Module O A] (S : Submodule O A) (c : O) (hdiv : ∀ b ∈ S, ∃ x ∈ S, c • x = b)
    [Finite ↥((c • LinearMap.id : A →ₗ[O] A).ker)] :
    Nat.card ↥((c • LinearMap.id : A →ₗ[O] A).ker) =
      Nat.card ↥((c • LinearMap.id : ↥S →ₗ[O] ↥S).ker) *
        Nat.card ↥((c • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
  have hmaps : ∀ x ∈ (c • LinearMap.id : A →ₗ[O] A).ker,
      S.mkQ x ∈ (c • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    rw [← LinearMap.map_smul, hx, map_zero]
  let g := S.mkQ.restrict hmaps
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply] at hy
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨z, hzS, hz⟩ := hdiv _ hy
    refine ⟨⟨x - z, ?_⟩, ?_⟩
    · simp [smul_sub, hz]
    · apply Subtype.ext
      simp only [g, LinearMap.restrict_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using hzS
  have eker : ↥(LinearMap.ker g) ≃ ↥((c • LinearMap.id : ↥S →ₗ[O] ↥S).ker) :=
    { toFun := fun x => ⟨⟨x.1.1, by
          have := x.2
          simp only [LinearMap.mem_ker, g, LinearMap.restrict_apply, Subtype.ext_iff,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.coe_zero] at this
          exact this⟩, by
          have := x.1.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
          exact Subtype.ext this⟩
      invFun := fun y => ⟨⟨y.1.1, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
            Subtype.ext_iff, Submodule.coe_smul, Submodule.coe_zero] at this ⊢
          exact this⟩, by
          simp only [LinearMap.mem_ker, g, LinearMap.restrict_apply, Subtype.ext_iff,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.coe_zero]
          exact y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hsplit := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
  rw [Nat.card_congr g.quotKerEquivRange.toEquiv, LinearMap.range_eq_top.mpr hsurj,
    Nat.card_congr eker] at hsplit
  rw [hsplit]
  congr 1
  exact Nat.card_congr Submodule.topEquiv.toEquiv

private theorem card_ker_smul_id_eq_of_linearEquiv {O P Q : Type} [CommRing O] [AddCommGroup P] [Module O P]
    [AddCommGroup Q] [Module O Q] (e : P ≃ₗ[O] Q) (c : O) :
    Nat.card ↥((c • LinearMap.id : P →ₗ[O] P).ker) = Nat.card ↥((c • LinearMap.id : Q →ₗ[O] Q).ker) :=
  Nat.card_congr
    { toFun := fun x => ⟨e x.1, by
        have := x.2
        simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
        rw [← map_smul, this, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have := y.2
        simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
        rw [← map_smul, this, map_zero]⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }


set_option maxHeartbeats 400000 in
theorem _root_.GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality (hT : _root_.Formalism.GaloisCohomology.LocalTateDualityK) (hE : _root_.Formalism.GaloisCohomology.LocalEulerCharK) :
    _root_.ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  unfold _root_.ReciprocityTheory.ChartRestriction.T2.ShapeUnr
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hFr i M _ _ u ρ htriv I hI
  haveI : IsTopologicalRing O := hO.ring
  haveI : CompactSpace O := hO.compact
  haveI : Finite (IsLocalRing.ResidueField O) := _root_.GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact hO.p_mem
  have hpow : ∀ n : ℕ, (p : O) ^ n ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hpϖ n
  let ρ' : Representation O (_root_.Formalism.GaloisCohomology.GK p K) M := MonoidHom.comp ρ i.symm.toMonoidHom
  have htriv' : ∀ g m, ρ' g m = m := fun g m => htriv _ m
  have hdivM : ∀ m : M, ∃ m', ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := _root_.GlobalTheory.KO_divisible_by_uniformiser hϖ (u m)
    exact ⟨u.symm y, u.injective (by simp [hy])⟩
  have hdivMn : ∀ (n : ℕ) (m : M), ∃ m', ϖ ^ n • m' = m := by
    intro n
    induction n with
    | zero => exact fun m => ⟨m, by simp⟩
    | succ k ih =>
      intro m
      obtain ⟨m₁, hm₁⟩ := ih m
      obtain ⟨m₂, hm₂⟩ := hdivM m₁
      exact ⟨m₂, by rw [pow_succ, mul_smul, hm₂, hm₁]⟩
  have hlc : ∀ m : M, IsLocallyConstant fun g => ρ g m := fun m => by
    simp only [htriv]
    exact IsLocallyConstant.const m
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.UnramifiedH2Bound.h2_bounded_of_trivial_action hT hK hϖ hpϖ hO.p_ne u ρ' htriv'
    (fun n h => _root_.GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant ρ' p n (ϖ ^ n) h fun m _ => by
      simp only [htriv']
      exact IsLocallyConstant.const m)
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set A := _root_.ReciprocityTheory.ChartRestriction.T2.HcLC ρ with hA
  have hkey : ∀ n : ℕ, 0 < n → Finite ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ∧
      q ^ n * (q ^ n) ^ d ≤ Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ≤ q ^ n * C * (q ^ n) ^ d ∧
      (n = 1 → Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ≤ q ^ n * q * (q ^ n) ^ d) := by
    intro n hn
    letI := _root_.GlobalTheory.ShapeNeg.levZ (M := M) p n (hpow n)
    haveI : Finite (_root_.GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) :=
      (_root_.GlobalTheory.ShapeNeg.levKO_card hϖ u n).1
    have hcardTL := (_root_.GlobalTheory.ShapeNeg.levKO_card hϖ u n).2
    have hcontn : _root_.ReciprocityTheory.Gal.ContAction (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') :=
      _root_.GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant ρ' p n (ϖ ^ n) (hpow n) fun m _ => by
        simp only [htriv']
        exact IsLocallyConstant.const m
    have htr := _root_.GlobalTheory.ShapeNeg.transfer_card_H0_H1 i ρ p n (ϖ ^ n) (hpow n)
    obtain ⟨hfin1, hfin2⟩ := _root_.GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n _
      (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') hn hcontn
    have heul := hE p K hK n _ (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') hn hcontn
    haveI hH1fin : Finite (_root_.ReciprocityTheory.Gal.H1 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [htr.2]; exact Nat.card_pos.ne')
    obtain ⟨hfinA, hA1⟩ := _root_.GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq ρ ϖ n hdivM hlc hH1fin
    have hinv : Nat.card (↥ρ.invariants ⧸
        (ϖ ^ n • LinearMap.id : ↥ρ.invariants →ₗ[O] ↥ρ.invariants).range) = 1 := by
      haveI : Subsingleton (↥ρ.invariants ⧸
          (ϖ ^ n • LinearMap.id : ↥ρ.invariants →ₗ[O] ↥ρ.invariants).range) := by
        rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
        rintro ⟨x, hx⟩ -
        obtain ⟨y, hy⟩ := hdivMn n x
        refine ⟨⟨y, (Representation.mem_invariants ρ y).mpr fun g => htriv g y⟩, Subtype.ext ?_⟩
        simpa using hy
      exact Nat.card_unique
    have hH0 : Nat.card ↥(_root_.ReciprocityTheory.Gal.H0 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) = q ^ n := by
      have htop : _root_.ReciprocityTheory.Gal.H0 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n)) = ⊤ := by
        unfold _root_.ReciprocityTheory.Gal.H0
        ext x
        simp only [Submodule.mem_top, iff_true, Representation.mem_invariants]
        intro g
        apply _root_.GlobalTheory.ShapeNeg.Lev.ext
        rw [_root_.GlobalTheory.ShapeNeg.levRep_val, htriv]
      rw [htop, Nat.card_congr Submodule.topEquiv.toEquiv, hcardTL]
    have h2pos : 0 < Nat.card (_root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ')) :=
      Nat.card_pos
    have hA2 : Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) =
        q ^ n * Nat.card (_root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ')) *
          (q ^ n) ^ d := by
      rw [← mul_one (Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker)), ← hinv, ← hA1, htr.2,
        heul, ← htr.1, hH0, hcardTL]
    refine ⟨hfinA, ?_, ?_, ?_⟩
    · rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h2pos)
    · rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hC n hn (hpow n)))
    · rintro rfl
      rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (_root_.GlobalTheory.ShapeNeg.card_H2_level_rep_le hT hK hϖ u ρ' (hpow 1) hcontn))
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  have hMtors : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by simp [hn])⟩
  have htorsA : ∀ x : A, ∃ n : ℕ, ϖ ^ n • x = 0 := fun x => by
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.hcLC_exists_pow_smul_eq_zero ρ ϖ hMtors x.1 x.2
    exact ⟨n, Subtype.ext hn⟩
  set S : Submodule O A := Submodule.comap A.subtype (_root_.Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I) with hSdef
  have hS : ∀ n : ℕ, Nat.card ↥((ϖ ^ n • LinearMap.id : S →ₗ[O] S).ker) = q ^ n :=
    _root_.GlobalTheory.ShapeNeg.card_unr_lev_of_triv hK hϖ hpϖ i u ρ htriv I hI
  have hqpos : 0 < q := Nat.card_pos
  have hdivS : ∀ b : S, ∃ c : S, ϖ • c = b :=
    exists_smul_eq_of_card_ker_pow_eq_of_torsion ϖ q hqpos hS fun b => by
      obtain ⟨n, hn⟩ := htorsA b.1
      exact ⟨n, Subtype.ext hn⟩
  have hdivSn : ∀ n : ℕ, ∀ b ∈ S, ∃ x ∈ S, ϖ ^ n • x = b := by
    intro n
    induction n with
    | zero => exact fun b hb => ⟨b, hb, by simp⟩
    | succ k ih =>
      intro b hb
      obtain ⟨x, hxS, hx⟩ := ih b hb
      obtain ⟨y, hy⟩ := hdivS ⟨x, hxS⟩
      refine ⟨y.1, y.2, ?_⟩
      rw [pow_succ, mul_smul, ← hx]
      exact congrArg (fun z : S => ϖ ^ k • z.1) hy
  have hY : ∀ n : ℕ, 0 < n → Finite ↥((ϖ ^ n • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) =
        q ^ n * Nat.card ↥((ϖ ^ n • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
    intro n hn
    obtain ⟨hfin, hlow, -, -⟩ := hkey n hn
    have hsplit := card_ker_smul_eq_mul_card_ker_quotient_of_divisible S (ϖ ^ n) (hdivSn n)
    rw [hS n] at hsplit
    refine ⟨Nat.finite_of_card_ne_zero fun h0 => ?_, hsplit⟩
    rw [h0, mul_zero] at hsplit
    have : 0 < q ^ n * (q ^ n) ^ d := by positivity
    omega
  have hcountY : ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤
        Nat.card ↥((ϖ ^ n • LinearMap.id :
          ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id :
          ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ≤
        C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d) := by
    intro n hn
    rw [card_ker_smul_id_eq_of_linearEquiv Submodule.topEquiv, ← hq, pow_mul]
    obtain ⟨-, hlow, hup, -⟩ := hkey n hn
    rw [(hY n hn).2] at hlow hup
    have hqn : 0 < q ^ n := by positivity
    constructor
    · exact Nat.le_of_mul_le_mul_left hlow hqn
    · exact Nat.le_of_mul_le_mul_left (by rw [mul_assoc] at hup; exact hup) hqn
  have hone : Nat.card ↥((ϖ ^ 1 • LinearMap.id :
      ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ≤
      Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) := by
    rw [card_ker_smul_id_eq_of_linearEquiv Submodule.topEquiv, ← hq]
    obtain ⟨-, -, -, h1⟩ := hkey 1 one_pos
    have h1 := h1 rfl
    rw [(hY 1 one_pos).2] at h1
    have h1' : Nat.card ↥((ϖ ^ 1 • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) ≤ q * q ^ d :=
      Nat.le_of_mul_le_mul_left (by simpa only [pow_one, mul_assoc] using h1) (by simpa using hqpos)
    rw [pow_succ q d, mul_comm (q ^ d) q]
    exact h1'
  have htorsY : ∀ y : A ⧸ S, ∃ n : ℕ, ϖ ^ n • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨n, hn⟩ := htorsA x
    exact ⟨n, by rw [← map_smul, hn, map_zero]⟩
  have hY1 : Finite ↥((ϖ • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
    have := (hY 1 one_pos).1
    rwa [pow_one] at this
  obtain ⟨a, F, _, _, hF, ⟨e⟩⟩ := _root_.GlobalTheory.CofinGen.exists_equiv_pi_prod_finite hϖ htorsY hY1
  haveI := hF
  have hshape := _root_.GlobalTheory.ShapeNeg.Shape.quotShape_of_counts hϖ (⊤ : Submodule O (A ⧸ S)) d a
    (Submodule.topEquiv.trans e) ⟨C, hcountY⟩ hone
  unfold _root_.Formalism.RepresentationBoundsCohomology.JT.QuotShape at hshape ⊢
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := hshape
  let E : (↥(⊤ : Submodule O (A ⧸ S)) ⧸ Submodule.comap (⊤ : Submodule O (A ⧸ S)).subtype ⊥) ≃ₗ[O]
      (A ⧸ S) :=
    (Submodule.quotEquivOfEqBot _ (by ext x; simp)).trans Submodule.topEquiv
  refine ⟨Cy, i1, i2, E.toLinearMap ∘ₗ ι, π ∘ₗ E.symm.toLinearMap, E.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (E.symm y)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx]
    exact E.apply_symm_apply y
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx]
    exact (E.symm_apply_apply (ι x)).symm

end GlobalTheory.ShapeUnrTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDualityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  first | exact @GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | exact GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | (intros; apply GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality <;> assumption)
end
