module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeQuotientLeCocycleSpanDeterminant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCoboundariesAmongBlockCocyclesLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexDvdClassNumber
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UnramHom

section Algebra

variable {O M G Γ : Type} [CommRing O] [AddCommGroup M] [Module O M] [Group G] [CommGroup Γ]

def asHom (f : G → M) (hf : ∀ a b, f (a * b) = f a + f b) : G →* Multiplicative M :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => by rw [hf, ofAdd_add]

theorem length_le {l : ℕ} (hl : l.Prime) (hu : ∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : O)) (L : ℕ∞)
    (hL : Module.length O (Submodule.torsionBy O M (l : O)) ≤ L) (π : G →* Γ) (hπ : Function.Surjective π) (n : ℕ) :
    n ≠ 0 → ∀ N : Subgroup Γ, N.index = n → ∀ C : Submodule O (G → M), (∀ f ∈ C, ∀ a b, f (a * b) = f a + f b) →
      (∀ f ∈ C, ∀ a, π a ∈ N → f a = 0) → Module.length O C ≤ L * (padicValNat l n : ℕ∞) := by
  have := Fact.mk hl
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn N hN C hadd hker
  by_cases h1 : n = 1
  · have hT : N = ⊤ := Subgroup.index_eq_one.1 (hN.trans h1)
    have : C = ⊥ := (Submodule.eq_bot_iff _).2 fun f hf => funext fun a => hker f hf a (hT ▸ trivial)
    subst this
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have := Fact.mk hp
  have : N.FiniteIndex := ⟨hN ▸ hn⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Γ ⧸ N) p (hN ▸ hpn :)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := hπ y
  let N' : Subgroup Γ := (Subgroup.zpowers (π a : Γ ⧸ N)).comap (QuotientGroup.mk' N)
  have hi : p * N'.index = n := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), ← hx, ← Nat.card_zpowers,
      Subgroup.card_mul_index, ← hN]
    rfl
  have hi0 : N'.index ≠ 0 := fun h => hn (by rw [← hi, h, mul_zero])
  have hlt : N'.index < n := by
    rw [← hi]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hi0) hp.one_lt
  let ev : C →ₗ[O] M := (LinearMap.proj a).comp C.subtype
  let C' : Submodule O (G → M) := (LinearMap.ker ev).map C.subtype
  have hC' := ih _ hlt hi0 N' rfl C' (by rintro _ ⟨f, -, rfl⟩; exact hadd f f.2) (by
    rintro _ ⟨f, hf, rfl⟩ b ⟨k, hk⟩
    have hf' : asHom f.1 (hadd f f.2) a = 1 := congrArg Multiplicative.ofAdd (LinearMap.mem_ker.1 hf)
    have h2 : π ((a ^ k)⁻¹ * b) ∈ N := by
      rw [map_mul, map_inv, map_zpow]
      exact QuotientGroup.eq.1 hk
    have h3 : asHom f.1 (hadd f f.2) ((a ^ k)⁻¹ * b) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_mul, map_inv, map_zpow, hf', one_zpow, inv_one, one_mul] at h3
    exact congrArg Multiplicative.toAdd h3)
  have hk : Module.length O (LinearMap.ker ev) = Module.length O C' :=
    (Submodule.equivMapOfInjective _ C.injective_subtype _).length_eq
  have hr : LinearMap.range ev ≤ Submodule.torsionBy O M (p : O) := by
    rintro _ ⟨f, rfl⟩
    have h2 : π (a ^ p) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, map_pow, QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
    have h3 : asHom f.1 (hadd f f.2) (a ^ p) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_pow] at h3
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    exact congrArg Multiplicative.toAdd h3
  have hsum : Module.length O C = Module.length O (LinearMap.ker ev) + Module.length O (LinearMap.range ev) :=
    Module.length_eq_add_of_exact (LinearMap.ker ev).subtype ev.rangeRestrict (Submodule.injective_subtype _)
      ev.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have hr' := Module.length_le_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
  rw [hsum, hk, ← hi, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hp.ne_zero hi0, Nat.cast_add, mul_add, add_comm (L * _)]
  refine add_le_add hC' (hr'.trans ?_)
  by_cases hpl : p = l
  · subst hpl
    rwa [Nat.padicValNat_def, Nat.Prime.multiplicity_self, Nat.cast_one, mul_one]
  · have : Submodule.torsionBy O M (p : O) = ⊥ := (Submodule.eq_bot_iff _).2 fun m hm =>
      ((hu p hp hpl).smul_eq_zero).1 ((Submodule.mem_torsionBy_iff _ _).1 hm)
    rw [this]
    simp

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] {a : O} (ha : a ≠ 0) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  let u : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
  have hu : a • u = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun _ => 1, funext fun j => ?_⟩
    simp [Algebra.smul_def, ha']
  let g : (O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O 1) a :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton O _ ⟨u, hu⟩) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hu)
  refine Module.length_le_of_surjective g ?_
  rintro ⟨m, hm⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨Submodule.Quotient.mk (c 0), Subtype.ext ?_⟩
  show c 0 • u = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h0 : algebraMap O (FractionRing O) (c 0) = a • x 0 := congrFun hc 0
  rw [Pi.smul_apply, Algebra.smul_def, h0, Algebra.smul_def]
  field_simp

end Algebra

section Galois

open ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Mem.UnitIndex Filter
open Neutral.B1 hiding G IsPlaceOver
open GlobalTheory.Mem.Chr hiding Ideles IsUnitAt localIdele diagUnits

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem eq_one_of_class [_root_.NumberField.IsTotallyComplex E] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {B : Type} [CommGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (A : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v)
    (hI : ∀ v, ∀ σ ∈ Ine (F := E) (A v), φ σ = 1) (σ : G E Ω)
    (hσ : toAb E Ω σ ∈ (classHom E).ker.map art) : φ σ = 1 := by
  obtain ⟨x, hx, e⟩ := hσ
  let ψ : Ideles E →* B := (liftAb φ hφ).comp art
  have hψ : Continuous ψ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (ψ.ker : Set (Ideles E)) := (isOpen_discrete {1}).preimage hψ
  have hfin : Finite ψ.range := by
    refine ((isCompact_range hφ).finite_of_discrete.subset ?_).to_subtype
    rintro _ ⟨y, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art y)
    exact ⟨τ, by rw [MonoidHom.comp_apply, ← hτ, liftAb_toAb]⟩
  have hu : ∀ v x, IsUnitAt v x → ψ (localIdele E v x) = 1 := fun v y hy => by
    obtain ⟨τ, hτ, e⟩ := (ha.ine v (A v) (hA v) _).1 ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply, ← e, liftAb_toAb, hI v τ hτ]
  have hle : unitIdl E ⊔ (diagUnits E).range ≤ ψ.ker := by
    refine sup_le (fun b hb => ?_) ?_
    · have e1 : ψ (finPartI E b) = ψ b := congrArg Subtype.val (GlobalTheory.RingCls.map_finPartI ψ.rangeRestrict b)
      rw [MonoidHom.mem_ker, ← e1]
      refine (ψ.ker.isClosed_of_isOpen ho).mem_of_tendsto
        (GlobalTheory.Mem.LocTriv.tendsto_part (finPartI_mem_unitIdl.2 hb) fun _ => rfl) (Eventually.of_forall fun S => ?_)
      refine Subgroup.prod_mem _ fun v _ => ?_
      exact hu v _ (hb v)
    · rintro _ ⟨k, rfl⟩
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have := MonoidHom.mem_ker.1 (hle (ker_classHom_le E hx))
  rwa [MonoidHom.comp_apply, e, liftAb_toAb] at this


omit [IsAlgClosure E Ω] in
theorem index_dvd_classNumber {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ((classHom E).ker.map art).index ∣ classNumber E := by
  refine (Subgroup.index_map_dvd _ ha.quot.surjective).trans ?_
  rw [Subgroup.index_ker, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

end Galois

theorem wkg_one (D : D7) (i : D.nd.Loc) (g : GE D.nd) (m : KOG (D.nd.O i) 1) :
    WKG (chiRatO D.nd i 1) g m = m := by
  have h : chiRatO D.nd i 1 g = chiRatO D.nd i 1 1 := by
    rw [map_one]
    simp [chiRatO, twistM]
  have h2 : WKG (chiRatO D.nd i 1) g = WKG (chiRatO D.nd i 1) 1 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    exact congrArg (fun X : Matrix (Fin 1) (Fin 1) (D.nd.O i) => (Submodule.Quotient.mk
      (Matrix.toLinAlgEquiv' (X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) x) : KOG (D.nd.O i) 1)) h
  rw [h2, map_one]
  rfl

theorem length_le_classNumber : GlobalTheory.Published.GlobalArtinReciprocity →
    ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)),
      C ≤ Z1 (WKG (chiRatO D.nd i 1)) → (∀ v, resIne i C v = ⊥) →
      Module.length (D.nd.O i) ↥C ≤
        lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) := by
  intro H D i C hC hres
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := H D.host.E D.nd.Om
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hadd : ∀ f ∈ C, ∀ a b, f (a * b) = f a + f b := fun f hf a b => by
    rw [(hC hf).2, wkg_one]
  have hl0 : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
    rw [map_natCast, map_zero, ← map_natCast (D.nd.embK i), map_eq_zero] at h1
    exact hl.ne_zero (Nat.cast_eq_zero.1 h1)
  have hu : ∀ p : ℕ, p.Prime → p ≠ D.nd.l i → IsUnit (p : D.nd.O i) := fun p hp hpl => by
    have h1 : IsUnit (p : ℤ_[D.nd.l i]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hl hp).2 hpl.symm))
    simpa using h1.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  have hd := index_dvd_classNumber ha
  have hh : classNumber D.host.E ≠ 0 := classNumber_ne_zero _
  refine (length_le hl hu _ (length_torsionBy_le hl0) (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
    GlobalTheory.HeckeGal.toAb_surjective _ (ne_zero_of_dvd_ne_zero hh hd) _ rfl C hadd fun f hf σ hσ => ?_).trans ?_
  · refine congrArg Multiplicative.toAdd (eq_one_of_class ha (asHom f (hadd f hf)) (hC hf).1 D.nd.plOm.1 D.nd.plOm.2
      (fun v τ hτ => ?_) σ hσ)
    have h1 : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) 1) Subtype.val f ∈ resIne i C v := ⟨f, hf, rfl⟩
    rw [hres v, Submodule.mem_bot] at h1
    exact congrArg Multiplicative.ofAdd (congrFun h1 ⟨τ, hτ⟩)
  · refine mul_le_mul_right (Nat.cast_le.2 ?_) _
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hh).1 ((_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hd)

end GlobalTheory.UnramHom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmer
noncomputable section

namespace GlobalTheory.Cut.SelClass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem length_le_cob_add {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    (C : Submodule R (Γ → M)) (hC : C ≤ ReciprocityTheory.Gal.Z1 rho) (S : Submodule R (ReciprocityTheory.Gal.H1 rho))
    (hS : ∀ f (hf : f ∈ C), (Submodule.Quotient.mk ⟨f, hC hf⟩ : ReciprocityTheory.Gal.H1 rho) ∈ S) :
    Module.length R ↥C ≤ Module.length R ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) + Module.length R ↥S := by

  let ψ : ↥C →ₗ[R] ReciprocityTheory.Gal.H1 rho :=
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype).mkQ ∘ₗ Submodule.inclusion hC
  have hker : ∀ x : ↥C, ψ x = 0 → (x : Γ → M) ∈ ReciprocityTheory.Gal.B1 rho := by
    intro x hx
    have h := (Submodule.Quotient.mk_eq_zero _).1 hx
    simpa using h
  have hrange : LinearMap.range ψ ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hS x.1 x.2
  let K := LinearMap.ker ψ.rangeRestrict
  have hsplit := Module.length_eq_add_of_exact K.subtype ψ.rangeRestrict
    (Submodule.subtype_injective _) ψ.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map _)

  let j : ↥K →ₗ[R] ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) :=
    LinearMap.codRestrict (C ⊓ ReciprocityTheory.Gal.B1 rho) (C.subtype ∘ₗ K.subtype) (fun x => by
      refine ⟨x.1.2, hker x.1 ?_⟩
      have hx : ψ.rangeRestrict x.1 = 0 := x.2
      exact congrArg Subtype.val hx)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hK := Module.length_le_of_injective j hj
  have hI := Module.length_le_of_injective (Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)
  rw [hsplit]
  exact add_le_add hK hI


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem mk_mem_selG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (P : LocPrime l)
    (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
    (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (f : ↥(ReciprocityTheory.Gal.Z1 (WKG M)))
    (hl : ∀ w hw, (fun g => Br.phi (nb w hw) k (f.1 (Br.ι (nb w hw) g).1)) ∈
      HfD (P.PD (nb w hw).Kw) (Br.lat (nb w hw) (M.comp (Dec (F := E) (A.1 w)).subtype)))
    (hu : ∀ v, v ∉ placesOver E l → v ∉ Sig → ∀ g ∈ Ine (F := E) (A.1 v), f.1 g = 0) :
    (Submodule.Quotient.mk f : ReciprocityTheory.Gal.H1 (WKG M)) ∈ Br.selG A l P nb Sig M := by
  unfold Br.selG GaloisCohomology.SelAll GaloisCohomology.bkCond Br.LlG Sel
  refine (Submodule.mem_iInf _).2 fun v => ?_
  rw [Submodule.mem_comap]
  dsimp only
  split_ifs with h1 h2 h3
  · unfold Br.bkG
    refine Submodule.mem_map.2 ⟨_, ?_, rfl⟩
    exact hl v h2
  · exact Submodule.mem_top
  · exact Submodule.mem_top
  · have hv : v ∉ placesOver E l := h1
    unfold GaloisCohomology.unrAt H1ur
    rw [LinearMap.mem_ker]
    unfold ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

    convert (ReciprocityTheory.Gal.B1 _).zero_mem using 1
    funext g
    exact hu v hv h3 _ g.2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  intro D i ρ π C hC hfin hine
  unfold lenCob
  refine length_le_cob_add _ C hC _ (fun f hf => ?_)
  unfold Br.selPi
  refine mk_mem_selG D.nd.plOm (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i) _ (WpO D.nd i ρ π) ⟨f, hC hf⟩ ?_ ?_
  · intro w hw
    exact hfin f hf w hw
  · intro v hv hSig g hg
    have hSv : v ∉ D.nd.S i := fun h => hSig (Or.inl h)
    have hQv : v ∉ D.nd.Q i := fun h => hSig (Or.inr h)

    have hmem : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) D.R.r) Subtype.val f ∈ resIne i C v :=
      Submodule.mem_map_of_mem hf
    rw [hine v hv hSv hQv, Submodule.mem_bot] at hmem
    exact congrFun hmem ⟨g, hg⟩

end GlobalTheory.Cut.SelClass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmerStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  first | exact @GlobalTheory.Cut.SelClass.main | exact GlobalTheory.Cut.SelClass.main | (intros; apply GlobalTheory.Cut.SelClass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOver
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CountL

theorem length_le_of_semilinear {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) : Module.length R M ≤ Module.length S N := by
  have : RingHomSurjective σ := ⟨hσ⟩
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono (Submodule.map f) (Submodule.map_strictMono_of_injective hf)

theorem length_le_inf_comap_add {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (C : Submodule R M) (A H : Submodule S N) (hC : ∀ x ∈ C, f x ∈ A) :
    Module.length R ↥C ≤
      Module.length R ↥(C ⊓ H.comap f) + Module.length S (↥A ⧸ H.comap A.subtype) := by
  let g : ↥C →ₛₗ[σ] (↥A ⧸ H.comap A.subtype) :=
    (H.comap A.subtype).mkQ.comp ((f.domRestrict C).codRestrict A fun x => hC x x.2)
  have hg : ∀ x : ↥C, x ∈ LinearMap.ker g → f x ∈ H := fun x hx =>
    (Submodule.Quotient.mk_eq_zero (H.comap A.subtype)).1 hx
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  refine add_le_add ?_ ?_
  · refine Module.length_le_of_injective
      ((C.subtype.comp (LinearMap.ker g).subtype).codRestrict (C ⊓ H.comap f)
        fun x => ⟨x.1.2, hg x.1 x.2⟩) ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine length_le_of_semilinear hσ ((LinearMap.ker g).liftQ g le_rfl) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_le_forall_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (K : ι → Submodule R M) (C : Submodule R M) (b : ℕ∞)
    (h : ∀ q, ∀ C₀ ≤ C, Module.length R ↥C₀ ≤ Module.length R ↥(C₀ ⊓ K q) + b) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C' ≤ K q) ∧
      Module.length R ↥C ≤ (Q.card : ℕ∞) * b + Module.length R ↥C' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₀, h₁, h₂, h₃⟩ := ih
    refine ⟨C₀ ⊓ K a, inf_le_left.trans h₁, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact inf_le_right
      · exact inf_le_left.trans (h₂ q hq)
    · rw [Finset.card_insert_of_notMem ha]
      refine h₃.trans ((add_le_add le_rfl (h a C₀ h₁)).trans (le_of_eq ?_))
      push_cast
      ring

theorem length_quot_natCast_le {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ) :
    Module.length S (S ⧸ Ideal.span {(p : S)}) ≤ Module.length R (R ⧸ Ideal.span {(p : R)}) := by
  refine length_le_of_semilinear (σ := e.symm.toRingHom) e.symm.surjective
    (Submodule.mapQ (Ideal.span {(p : S)}) (Ideal.span {(p : R)}) e.symm.toRingHom.toSemilinearMap ?_) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨e.symm y, by
      show _ = e.symm (y * p)
      simp⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : e.symm x ∈ Ideal.span {(p : R)} := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton'.2 ⟨e y, ?_⟩)
    simpa using congrArg e hy

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
noncomputable def locFunS {D : D7} (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (GE D.nd → KOG (D.nd.O i) k) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) where
  toFun := locFun i M w hw
  map_add' a b := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  intro D i r Xs k M C e h
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin := finite_placesOver D.host.E (D.nd.l i) hl.ne_zero
  letI : Fintype ↥(placesOver D.host.E (D.nd.l i)) := hfin.fintype
  obtain ⟨C', h₁, h₂, h₃⟩ := exists_le_forall_le
    (fun q : ↥(placesOver D.host.E (D.nd.l i)) =>
      (HfD (Br.PD D.loc D.nbr i q.1 q.2) (Br.locLat D.nbr i q.1 q.2 M)).comap (locFunS i M q.1 q.2))
    C ((e : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i)) (by
      rintro ⟨w, hw⟩ C₀ hC₀
      refine (length_le_inf_comap_add (D.nbr i w hw).eO.surjective (locFunS i M w hw) C₀
        (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M)) _
        (fun f hf => (h w hw).2 f (hC₀ hf))).trans (add_le_add le_rfl ?_)
      refine le_trans (h w hw).1 (mul_le_mul' le_rfl ?_)
      unfold lenOl lenQ
      rw [Br.PD_p]
      exact length_quot_natCast_le (D.nbr i w hw).eO _) Finset.univ
  refine ⟨C', h₁, fun f hf w hw => h₂ ⟨w, hw⟩ (Finset.mem_univ _) hf, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← mul_assoc] at h₃
  rw [Nat.cast_mul]
  exact h₃

end GlobalTheory.Cut.CountL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOverStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_global_cocycles_le_sum_places_over : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  first | exact @GlobalTheory.Cut.CountL.main | exact GlobalTheory.Cut.CountL.main | (intros; apply GlobalTheory.Cut.CountL.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalSelmer
namespace GlobalTheory.Proof.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i) (k : ℕ) (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)), InR' D.nd r S 1 → UnrOut i r Xs → ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i (cocW i r S Xs ψ) v = ⊥ := by
  intro D i r Xs S k ψ hone hU v h1 h2 h3
  have hY : ∀ γ, InY D.nd r S (yg D.nd r S γ) := fun γ =>
    ⟨1, fun _ => 1, fun _ => γ, fun _ => hone, by simp⟩
  have hy : ∀ γ x', yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
    intro γ x'
    simp [yg, rTwO, twistM, sub_mul]
  rw [resIne, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, -, h0, rfl⟩, rfl⟩
  funext γ
  exact h0 _ (hY γ.1) fun x' hx => by rw [hy, hU v h1 h2 h3 _ hx γ.1 γ.2]; simp

end GlobalTheory.Proof.LocalGlobalSelmer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthEqInfKerAddMap
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Peel

theorem length_eq_inf_ker_add_map {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (C : Submodule R M) :
    Module.length R ↥C = Module.length R ↥(C ⊓ LinearMap.ker f) + Module.length R ↥(C.map f) := by
  refine Module.length_eq_add_of_exact (Submodule.inclusion (inf_le_left : C ⊓ LinearMap.ker f ≤ C))
    (f.submoduleMap C) (Submodule.inclusion_injective _) (f.submoduleMap_surjective C) ?_
  intro y
  constructor
  · intro hy
    have hy' : f y = 0 := by
      simpa [LinearMap.submoduleMap_coe_apply] using congrArg Subtype.val hy
    exact ⟨⟨y.1, y.2, hy'⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    ext
    simpa [LinearMap.submoduleMap_coe_apply] using z.2.2

theorem exists_le_map_eq_bot {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N : ι → Type*} [∀ q, AddCommGroup (N q)] [∀ q, Module R (N q)] (f : ∀ q, M →ₗ[R] N q)
    (C : Submodule R M) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C'.map (f q) = ⊥) ∧
      Module.length R ↥C ≤ Module.length R ↥C' + ∑ q ∈ Q, Module.length R ↥(C.map (f q)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert q Q hq ih =>
    obtain ⟨C₀, hC₀, hmap, hlen⟩ := ih
    refine ⟨C₀ ⊓ LinearMap.ker (f q), inf_le_left.trans hC₀, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · rw [eq_bot_iff, ← hmap p hp]
        exact Submodule.map_mono inf_le_left
    · have hsplit := length_eq_inf_ker_add_map (f q) C₀
      have hle : Module.length R ↥(C₀.map (f q)) ≤ Module.length R ↥(C.map (f q)) :=
        Module.length_le_of_injective _ (Submodule.inclusion_injective (Submodule.map_mono hC₀))
      rw [Finset.sum_insert hq]
      calc Module.length R ↥C ≤ Module.length R ↥C₀ + ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := hlen
        _ = Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C₀.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by rw [← hsplit]
        _ ≤ Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by gcongr
        _ = _ := by rw [add_assoc]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ q ∈ Q, resIne i C' q = ⊥) ∧ Module.length (D.nd.O i) ↥C ≤ Module.length (D.nd.O i) ↥C' + ∑ q ∈ Q, Module.length (D.nd.O i) ↥(resIne i C q) := by
  intro D i k C Q
  exact exists_le_map_eq_bot
    (fun q => LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k)
      (Subtype.val : ↥(Ine (F := D.host.E) (D.nd.plOm.1 q)) → GE D.nd)) C Q

end GlobalTheory.Cut.Peel
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CutCore

theorem length_mono {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O ↥A ≤ Module.length O ↥B :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem exists_length_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} (ha : a ≠ 0) :
    ∃ n : ℕ, Module.length O (O ⧸ Ideal.span {a}) = n := by
  have h : Ring.ord O a ≠ ⊤ := by
    rwa [Ring.ord_eq_addVal, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp h
  exact ⟨e, he.symm⟩

theorem length_quot_eq_zero_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} :
    Module.length O (O ⧸ Ideal.span {a}) = 0 ↔ IsUnit a := by
  change Ring.ord O a = 0 ↔ _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_eq_zero_iff]

variable {D : D7} (i : D.nd.Loc)

theorem resIne_eq_bot_of_le {k : ℕ} {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B)
    {v : HeightOneSpectrum (𝓞 D.host.E)} (hB : resIne i B v = ⊥) : resIne i A v = ⊥ :=
  le_bot_iff.mp (hB ▸ Submodule.map_mono h)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lenCob_mono {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B) : lenCob i M A ≤ lenCob i M B :=
  length_mono (inf_le_inf_right _ h)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i))
  (S : IdempotentChoiceData D.nd i)

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => S.T'.one_mem, by
    funext x'
    simp⟩

theorem del_ne_zero (hS : GoodCongruenceObjects D.nd r ρ π S) : del51 D.nd S S.π' ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨h1, -, h3, -⟩, -⟩ := hS
  intro h0
  have hz : (Eel D.nd S S.π').map (toK D.nd i) = 0 := by
    rw [← Matrix.toLin'.map_eq_zero_iff]
    refine LinearMap.ext fun u => ?_
    apply S.e.injective
    rw [Matrix.toLin'_apply, h3 u, h0]
    simp [Prod.ext_iff, funext_iff]
  have := h1 S.π'
  rw [hz, Matrix.rank_zero] at this
  exact zero_ne_one this


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem length_cocRho_le (eρ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs (WpO D.nd i ρ π) eρ) :
    Module.length (D.nd.O i) ↥(cocRho i r S Xs) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eρ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        (((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') +
          Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (WpO D.nd i ρ π) (cocRho i r S Xs) eρ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).1⟩)
  refine hlen.trans (add_le_add le_rfl ?_)
  refine (GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).1) hfin ?_).trans
    (add_le_add ((lenCob_mono i _ hC).trans (GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).1) le_rfl)
  intro v h1 h2 h3
  exact resIne_eq_bot_of_le i hC
    (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ S.ψρ (inR'_one i r S) hU v h1 h2 h3)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_fin_unr (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    ∃ C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1), C ≤ cocChi i r S Xs c ∧
      (∀ f ∈ C, IsFinL i (chiRatO D.nd i ((c : ℕ) + 1)) f) ∧
      (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) ∧
      Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
        (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
          (Module.length (D.nd.O i) ↥C + ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) eχ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).2 c⟩)
  obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 C (D.nd.Q i)
  refine ⟨C', hC'.trans hC, fun f hf => hfin f (hC' hf), ?_, hlen.trans (add_le_add le_rfl
    (hlen'.trans (add_le_add le_rfl (Finset.sum_le_sum fun q hq' => ?_))))⟩
  · intro v h1
    by_cases h3 : v ∈ D.nd.Q i
    · exact hq v h3
    refine resIne_eq_bot_of_le i (hC'.trans hC) ?_
    by_cases h2 : v ∈ D.nd.S i
    · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
      · have h := GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ v (Or.inl h2) hqd c
        rw [lenQ, length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
        exact Submodule.subsingleton_iff_eq_bot.mp h
      · exact GlobalTheory.T.inertiaCocycles_charBlock_otherTypePrime D i r ρ π Xs S hr hS hπ v h2 hp c
    · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ _ (inR'_one i r S) hU v h1 h2 h3
  · exact (length_mono (Submodule.map_mono hC)).trans
      (GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ q (Or.inr hq') (hQ q hq') c)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem length_cocChi_le (hA : GlobalTheory.Published.GlobalArtinReciprocity) (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hH : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        ((2 * lenQ i (del51 D.nd S S.π') + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) *
            (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
              else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ))) +
          ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hunr, hlen⟩ := exists_fin_unr i r ρ π Xs S eχ hr hS hπ hU hSv hQ c hL
  refine hlen.trans (add_le_add le_rfl (add_le_add ?_ le_rfl))
  have hZ := hC.trans ((GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c)
  by_cases hc : (c : ℕ) = 0
  · rw [if_pos hc]
    rw [hc, zero_add] at hZ hfin
    refine (GlobalTheory.UnramHom.length_le_classNumber hA D i C hZ fun v => ?_).trans le_add_self
    by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
    · exact GlobalTheory.CutTrivIne.main D i C v hv fun f hf => (hH v hv).2 (hfin f hf v hv)
    · exact hunr v hv
  · rw [if_neg hc]
    have h2 : 2 ≤ (c : ℕ) + 1 := by omega
    have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
    have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C hZ h2 ht
      (fun f hf w hw => (hH w hw).1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) (hfin f hf w hw)) hunr
    rw [Nat.add_sub_cancel] at h
    exact h.trans (add_le_add ((lenCob_mono i _ hC).trans
      ((GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).2 c)) le_rfl)

theorem sum_fin_ite {t : ℕ} (ht : 0 < t) (h : ℕ) (g : ℕ → ℕ) :
    ∑ c : Fin t, (if (c : ℕ) = 0 then h else g c) = h + ∑ e ∈ Finset.Ioo 0 t, g e := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if c = 0 then h else g c) t]
  have : Finset.range t = insert 0 (Finset.Ioo 0 t) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [this, Finset.sum_insert (by simp), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun e he => if_neg (Finset.mem_Ioo.mp he).1.ne'


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalCore := by
  intro hA D i r ρ π Xs eρ eχ S hr hS hZ hπ hN hU hSv hQ hl hsel hsha
  classical
  obtain ⟨L, hL⟩ := exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (length_quot_eq_zero_iff.mp hL)
  obtain ⟨d, hd⟩ := exists_length_quot (del_ne_zero i r ρ π S hS)
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)
  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set n := (placesOver D.host.E (D.nd.l i)).ncard with hn
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hρ := length_cocRho_le i r ρ π Xs S eρ hr hS hπ hU fun w hw => (hl w hw).2.1
  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      ((n * eχ * L + ((2 * d + L * (if (c : ℕ) = 0 then h else g c)) + ∑ q ∈ D.nd.Q i, z q) : ℕ) : ℕ∞) := by
    intro c
    refine (length_cocChi_le i r ρ π Xs S hA eχ hr hS hπ hU hSv (fun v hv => (hQ v hv).1) c
      (fun w hw => (hl w hw).1) fun w hw => (hl w hw).2.2 _
        (Finset.mem_Icc.mpr ⟨Nat.le_add_left _ _, c.2⟩)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, lenQ, hL, hd]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  rw [lenQ, lenQ, hL, hd, ← hs] at hρ
  have htot := (GlobalTheory.T.length_heckeQuotient_le_cocycleSpan_determinant D i r ρ π Xs S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ c))
  rw [← Nat.cast_sum, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, sum_fin_ite ht] at hnat
  have hvd : D.nd.vdel i = (d : ℚ) / L := by
    rw [← hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2, lenUnit, hL, hd, ENat.toNat_coe, ENat.toNat_coe]
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  rw [hvd, hsp, hsh, hzq, vccOff, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat
  have hq : (a : ℚ) ≤ _ := Nat.cast_le.mpr hnat
  rw [div_le_iff₀ hLq, Ranks.nV]
  push_cast at hq ⊢
  have hd0 : (0 : ℚ) ≤ ((D.R.r : ℚ) + D.R.t) * d := by positivity
  field_simp
  nlinarith [hq, hd0]

end GlobalTheory.CutCore
