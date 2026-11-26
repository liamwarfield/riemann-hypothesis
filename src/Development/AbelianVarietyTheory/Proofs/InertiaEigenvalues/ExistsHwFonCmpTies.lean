module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfOneTmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOfStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholze
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholze
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism

namespace GlobalTheory.WachLattice

section Generic

variable {l : ℕ} [Fact l.Prime] {F : FinExt l} {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData ↥(GK F) Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : ↥(GK F) → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}


set_option maxHeartbeats 2000000 in
theorem build_prism (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (E : WEt I) [Algebra ℤ_[l] O]
    [Nontrivial O] [FiniteDimensional Qp LL] (hO : Function.Injective (algebraMap O LL)) (hp : PD.p = l)
    {PS PW : Obj l ↥(OL F)} (ev : Hom PS PW) (ioH : Hom PS (ainfObj F)) (gH : ↥(GK F) → Hom PS PS)
    (a : PS.A →+* LetA O n) (z : PowerSeries ℤ_[l] →+* PS.A) (π Q : PS.A) (c : WCb l →+* RW)
    (hψ₀ : ∀ x, I.ioE (algebraMap _ R.EE (a x)) = c (inclW l (ainfId F (ioH.f x)))) (ha : Function.Injective a)
    (hinj : Function.Injective I.ioE) (hunit : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x)
    (hγ : ∀ g x, a ((gH g).f x) = letγ (R.γ₀ (Γ.resΓ g)) (a x))
    (hio : ∀ g, ioH.comp (gH g) = (ainfHom F g).comp ioH) (hev : ∀ g, ev.comp (gH g) = ev)
    (hπ : a π = letπ) (hker : RingHom.ker ev.f = Ideal.span {π}) (hI : PS.I = Ideal.span {Q}) (hQ : a Q = R.Q)
    (hloc : IsLocalRing PS.A)
    (hz : ∃ (d : ℕ) (w : Fin d → PS.A), ∀ x, ∃! c : Fin d → PowerSeries ℤ_[l], x = ∑ i, z (c i) * w i)
    {d : ℕ} (o : Module.Basis (Fin d) ℤ_[l] O)
    (hA₀ : ∀ x : LetA O n, ∃! c : Fin d → PS.A, ∀ k, x k = ∑ i, PowerSeries.C (o i) * a (c i) k)
    (hRW : ∀ r : RW, ∃! w : Fin d → WCb l, r = ∑ j, o j • c (w j)) (hcu : ∀ w, IsUnit (c w) → IsUnit w)
    (hcφ : ∀ w, φR (c w) = c (frobW l w)) (hcg : ∀ (g : ↥(GK F)) w, gR g (c w) = c (galW l (g : GQ l) w))
    (hκ : ∀ T : LocLat ↥(GK F) Qp LL O,
      letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
      ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW RW T, ∀ w t, κ (w ⊗ₜ[ℤ_[l]] t) = c w ⊗ₜ[O] t)
    (hreal : ∀ T : LocLat ↥(GK F) Qp LL O, IsCrys PD T.ρ →
      letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
      ∃ (ρ : ↥(GK F) → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (C : FCrys l ↥(OL F))
        (j : C.M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
        Realises F C (ainfObj F) (ainfId F) ↥T.L.T ρ j ∧ ∀ g t, T.actT g t = ρ g t)
    (H : ↥(GK F) → Prop) (hH : ∀ g, H g → Γ.resΓ g = 1)
    (hmem : ∀ (T : LocLat ↥(GK F) Qp LL O) (q : ℕ) (x : Fin q → TW RW T) (A : Matrix (Fin q) (Fin q) R.EE),
      IsUnit A → (∀ g, H g → ∀ i, TWact (gR g) T g (x i) = x i) →
      (∀ j, TWmap φR T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft O (I.ioE (A i j)))
        (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T)) :
    Nonempty (WN E (a.comp z)) := by
  classical
  let _ : ∀ T : LocLat ↥(GK F) Qp LL O, Module ℤ_[l] ↥T.L.T :=
    fun T => Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  have : Nontrivial R.EE := R.EE_inj.nontrivial
  have : Nontrivial RW := hinj.nontrivial
  let ψ : PS.A →+* WCb l := ((inclW l).comp (ainfId F).toRingHom).comp ioH.f
  have hψ1 : ∀ x, ψ x = inclW l (ainfId F (ioH.f x)) := fun _ => rfl
  have hψ : ∀ x, I.ioE (algebraMap _ R.EE (a x)) = c (ψ x) := hψ₀
  have hA : ∀ α : LetA O n, ∃ t : Fin d → PS.A, α = ∑ j, o j • a (t j) := fun α => by
    obtain ⟨t, ht, -⟩ := hA₀ α
    refine ⟨t, funext fun k => ?_⟩
    rw [ht, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (PowerSeries.smul_eq_C_mul _ _).symm
  have hQu : IsUnit (algebraMap _ R.EE (a Q)) := hQ ▸ isUnit_Q R
  have hQ0 : ψ Q ≠ 0 := fun h => (hQu.map I.ioE).ne_zero (by rw [hψ, h, map_zero])
  have := perfect_tilt (l := l)
  have hE := coord_EE I a c ψ π hψ hπ hcu (by rw [hp]; exact WittVector.isAdicCompleteIdealSpanP) o hRW hA
  choose κ hκ using hκ
  choose ρ C j hR hρ using hreal
  choose q b cb hcb h1 h2 h3 h4 using fun T hT => GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor l F PS PW ev ioH gH π Q ψ hψ1 hio hev hker
    (hI ▸ Ideal.mem_span_singleton_self Q) hloc hQ0 _ _ _ _ (hR T hT)
  have hκs := fun T => kappa_smul c (κ T) (hκ T)
  have hκφ : ∀ T y, κ T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) = TWmap φR T (κ T y) :=
    fun T y => kappa_map c (κ T) (hκ T) (κ T) (hκ T) _ _ hcφ _ _ (fun _ => rfl) y
  have hκg : ∀ T hT (g : ↥(GK F)) y, κ T (TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ T hT g) y) =
      TWact (gR g) T g (κ T y) :=
    fun T hT g y => kappa_map c (κ T) (hκ T) (κ T) (hκ T) _ _ (hcg g) _ _ (hρ T hT g) y
  let ν : ∀ T hT, (C T hT).M PS → TW RW T := fun T hT x => κ T (j T hT ((C T hT).tr ioH x))
  have hνs : ∀ T hT (t : PS.A) x, ν T hT (t • x) = c (ψ t) • ν T hT x := fun T hT t x => by
    simp only [ν]
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hκs]; rfl
  have hνsum : ∀ T hT (t : Fin (q T hT) → PS.A),
      ν T hT (∑ i, t i • b T hT i) = ∑ i, c (ψ (t i)) • κ T (cb T hT i) := fun T hT t => by
    simp only [ν]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcb]; exact hνs T hT _ _
  have hν1 : ∀ T hT x, ∃ (k : ℕ) (m : (C T hT).M PS), c (ψ Q) ^ k • TWmap φR T (ν T hT x) = ν T hT m :=
    fun T hT x => by
      obtain ⟨k, m, h⟩ := h1 T hT x
      exact ⟨k, m, by simp only [ν]; rw [← h, hκs, map_pow, hκφ]⟩
  have hν2 : ∀ T hT x, ∃ (k : ℕ) (t : Fin (q T hT) → PS.A),
      c (ψ Q) ^ k • ν T hT x = ∑ i, c (ψ (t i)) • TWmap φR T (κ T (cb T hT i)) := fun T hT x => by
    obtain ⟨k, t, h⟩ := h2 T hT x
    refine ⟨k, t, ?_⟩
    simp only [ν]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_pow, ← hκs, h, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hκs, hκφ]
  have hν3 : ∀ T hT g x, TWact (gR g) T g (ν T hT x) = ν T hT ((C T hT).tr (gH g) x) := fun T hT g x => by
    simp only [ν]
    rw [← h3, hκg]
  have hνb : ∀ T hT i, κ T (cb T hT i) = ν T hT (b T hT i) := fun T hT i => by rw [hcb]
  let L : ∀ T : LocLat ↥(GK F) Qp LL O, Set (TW RW T) := fun T => {y | ∃ hT x, y = ν T hT x}
  have hone : IsCrys PD Γ.one.ρ := GlobalTheory.TrivCrys.isCrys_lat_of_trivial Γ.one Γ.one_triv
  obtain ⟨e₀, bo, he₀, hbo⟩ := one_basis Γ hO o
  refine build E a z c ψ π Q hψ ha hinj hunit hπ hQ hz d o hA hE L ?_ ?_ ?_ ?_ ?_ hone e₀ he₀ ?_
  · intro T hT
    have hbas := kappa_basis c (κ T) (hκ T) (cb T hT)
    obtain ⟨A, hAu, hAφ⟩ := GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert PS.A R.EE (WCb l) RW (TW RW T) ((algebraMap _ R.EE).comp a)
      I.ioE.toRingHom c ψ Q hinj hψ hQu _ (fun i => κ T (cb T hT i)) (fun i => TWmap φR T (κ T (cb T hT i)))
      (fun w hw => (hbas 0).unique hw.symm (by simp))
      (fun i => by
        obtain ⟨k, m, h⟩ := hν1 T hT (b T hT i)
        exact ⟨k, (b T hT).repr m, by rw [hνb, h, ← hνsum, (b T hT).sum_repr]⟩)
      (fun i => by rw [hνb]; exact hν2 T hT _)
    have hm := hmem T _ (fun i => κ T (cb T hT i)) A hAu (fun g hg i => by
      have e : gH g = Hom.id PS := Hom.ext' (RingHom.ext fun x => ha (by
        rw [hγ, hH g hg, map_one]; rfl))
      rw [hνb, hν3, e, FCrys.tr_id]) (fun i => by
        rw [hAφ]
        exact Finset.sum_congr rfl fun i _ => (map_mulLeft _ _).symm)
    choose x hx using hm
    refine ⟨q T hT, x, card_basis T o (cb T hT), by simpa only [hx] using hbas, fun y => ?_⟩
    simp only [hx, ← hνsum]
    constructor
    · rintro ⟨_, m, rfl⟩
      exact ⟨(b T hT).repr m, by rw [(b T hT).sum_repr]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨hT, _, rfl⟩
  · rintro T hT _ ⟨_, x, rfl⟩
    obtain ⟨k, m, h⟩ := hν1 T hT x
    exact ⟨k, hT, m, h⟩
  · rintro T hT _ ⟨_, x, rfl⟩
    obtain ⟨k, t, h⟩ := hν2 T hT x
    exact ⟨k, _, t, _, fun i => ⟨hT, _, hνb T hT i⟩, h⟩
  · rintro T hT g _ ⟨_, x, rfl⟩
    obtain ⟨y, hy⟩ := h4 T hT g x
    refine ⟨_, ⟨hT, y, rfl⟩, ?_⟩
    rw [hν3, ← hνs, ← hy]
    simp only [ν, map_sub]
  · rintro T T' f hT hT' _ ⟨_, x, rfl⟩
    obtain ⟨f', hf, hf'⟩ := exists_restrict (Z := ℤ_[l]) f
    obtain ⟨x', hx'⟩ := full ioH BS (hR T hT) (hR T' hT') f' (fun g t => by rw [← hρ, ← hρ, hf']) x
    refine ⟨hT', x', ?_⟩
    simp only [ν]
    rw [hx']
    exact (kappa_map c (κ T) (hκ T) (κ T') (hκ T') LinearMap.id LinearMap.id (fun _ => rfl) f' _ hf _).symm
  · intro y
    have key : ∀ t : Fin d → PS.A, κ Γ.one (∑ i, inclW l (ainfId F (ioH.f (t i))) ⊗ₜ[ℤ_[l]] bo i) =
        I.ioE (algebraMap _ R.EE (∑ i, o i • a (t i))) • ((1 : RW) ⊗ₜ[O] e₀) := fun t => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hκ, hbo, Algebra.smul_def (o i) (a _), map_mul, ← IsScalarTower.algebraMap_apply, map_mul,
        AlgHom.commutes, hψ₀, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    have hr := range_trivial ioH BS (hR _ hone)
      (fun g x => by rw [← hρ]; exact Subtype.ext (Γ.one_triv g x)) bo
    constructor
    · rintro ⟨_, x, rfl⟩
      obtain ⟨t, ht⟩ := (hr _).1 ⟨x, rfl⟩
      exact ⟨_, by rw [← key, ← ht]⟩
    · rintro ⟨α, rfl⟩
      obtain ⟨t, rfl⟩ := hA α
      obtain ⟨x, hx⟩ := (hr _).2 ⟨t, rfl⟩
      exact ⟨hone, x, by rw [← key, hx]⟩

end Generic


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → WachEx AI := by
  intro BS l _ P AI tied K s LL hG Γ R I hW E
  obtain ⟨PS, PW, ev, ioH, gH, a, z, π, Q, ha, hio, -, hγ, hioH, hev, hπ, -, hker, hI, hQ, hz, hloc, -, hS, hA⟩ :=
    GlobalTheory.T.exists_wach_prism_over_integers l P AI K s LL hG Γ R I hW
  obtain ⟨hinj, hunit, -, -⟩ := GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hW
  obtain ⟨d, ⟨o⟩⟩ := exists_basis_OL LL
  have := LL.2
  have := Module.Free.of_basis o
  have := Module.Finite.of_basis o
  have : Nontrivial R.EE := R.EE_inj.nontrivial
  have : Nontrivial (RW LL) := hinj.nontrivial
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  change Nonempty (WN E _)
  rw [← hz]
  refine build_prism BS E hO (P.PD_p K) ev ioH gH a z π Q
    (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] ↥(OL LL) ⊗[ℤ_[l]] WCb l).toRingHom
    (fun x => ?_) ha hinj hunit hγ hioH hev hπ hker hI hQ hloc hS o (hA d o) (coord_tensor o)
    (fun w => isUnit_of_one_tmul w) (fun w => ?_) (fun g w => ?_) (GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel l K LL) (fun T hT => ?_)
    (fun g => P.χQ (g : GQ l) = 1) (fun g hg => resΓ_eq_one Γ hO g ?_)
    (GlobalTheory.T.witt_twist_invariant_basis_change l P AI K s LL hG Γ R I hW E)
  · rw [I.ioE_ext, hio]
    exact Algebra.TensorProduct.map_tmul _ _ _ _
  · exact Algebra.TensorProduct.map_tmul _ _ _ _
  · rw [← locAinf_actWCbHom_eq AI]
    exact Algebra.TensorProduct.map_tmul _ _ _ _
  · obtain ⟨C, j, h⟩ := (BS l K _ _ (isAinf_ainfObj K)).1 P AI ⟨tied⟩ LL T hT
    exact ⟨_, C, j, h, fun _ _ => rfl⟩
  · rw [P.PD_χ, hg, Units.val_one]

end GlobalTheory.WachLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholzeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → WachEx AI := by
  first | exact @GlobalTheory.WachLattice.main | exact GlobalTheory.WachLattice.main | (intros; apply GlobalTheory.WachLattice.main <;> assumption)
end
end

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem exists_hw_fon_cmp_ties : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
      (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) →
      ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) ∧ Nonempty (Formalism.MainNotions.LocalSituation.Ties L A H F) := by
  intro hBS L A hT
  obtain ⟨H, F, hC⟩ := GlobalTheory.T.exists_hwOf_fonOf_cmpOf' L A hT (fun l _ => GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze hBS l (L l) (A l) (hT l))
  exact ⟨H, F, hC, ⟨⟨fun l _ => Classical.choice (GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod l (L l) (A l) (hT l))⟩⟩⟩

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilled
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LocInv

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [(Submodule.mem_bot _).1 hx, zero_smul]

theorem dual_eq_one {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ)
    (v : PlE D.host) (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (σ : GE N)
    (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) : ρ σ = 1 := by
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hl
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hvl (N.plOm.2 v) (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  have h2 : eps0 X i σ = 1 := by
    rw [eps0, MonoidHom.comp_apply, h1, map_one]
  have h3 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s h v hl hS _ (N.plOm.2 v) σ hσ
  apply Units.ext
  rw [hρ σ, Tdual, h2, ← Tgl_coe, h3]
  simp

theorem local_invariants_killed : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  intro _ D N X bkP i s _ M R n d A₀ L z P hM hz hL hSt A _ _ _ _ κ Q ρ t a hQ hSet _ hρ hch ha Y _ _ _ _ v hv m hm
  obtain ⟨hG, hloc, -, hκo, hκl, -, hQl, -⟩ := hSet
  have hκl' : ∀ g, ∃ k : ℕ, κ⁻¹ g ^ (X.l i ^ k) = 1 := fun g => by
    obtain ⟨k, hk⟩ := hκl g
    exact ⟨k, by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]⟩
  by_cases hS : v ∈ Spl i
  · have hker : (κ⁻¹).ker = κ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h0 := (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hG v hS A κ⁻¹ (hker ▸ hκo) hκl' Y
      (tors_of_finite A Y) ρ (Or.inr hρ)).1
    have : m ∈ H0 ((repOn ρ κ⁻¹ Y).comp (DecV N v).subtype) := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => hm g.1 g.2
    rw [h0, Submodule.mem_bot] at this
    rw [this, smul_zero]
  have hvQ : v ∈ Q := hv.resolve_left hS
  obtain ⟨q, hq⟩ := (hQ v).1 hvQ
  rcases q with b | q
  · have hA : ∀ w, Over (P (.inl b)) w → w ∉ X.S0 i ∧ normV w % X.l i = 1 := fun w hw => by
      obtain ⟨-, -, -, h0, -, hn⟩ := hSt.1.1 _ w hw
      exact ⟨h0, mod_l_eq_one i hM hn⟩
    have hp := hA v hq
    have hn := GlobalTheory.ScalarFrob.natCast_eq_one_of_mod i hp.2
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    obtain ⟨c, c0, c1, hc⟩ := GlobalTheory.ScalarFrob.frob_scalar_place i s bkP hG hz hL.1 hA (hSt.2.1 b).2 hq hσ
    have hc' : ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) =
        c⁻¹ • 1 := by
      rw [hρ, GlobalTheory.ScalarFrob.dual_of_scalar i s (GlobalTheory.ScalarFrob.eps_frob i hp.1 hn hσ) c0 hc]
    rw [GlobalTheory.ScalarFrob.eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ (hκl' σ) (inv_ne_one.2 c1) hc'
      (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm σ hσ.1), smul_zero]
  · obtain ⟨γ, hγ, hd⟩ := (hSt.1.2.2 (.inr q)).2.2.2.2 v hq _ (N.plOm.2 v) (Multiplicative.ofAdd 1)
    have hρ1 := dual_eq_one bkP i s hG.1 hρ v (hQl v hvQ) hS γ hγ
    have hk := hch γ
    haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (Fact.out : (X.l i).Prime).one_lt⟩
    rw [Finset.prod_eq_single (Sum.inr q)] at hk
    · have hd' : d (P (.inr q)) γ = Multiplicative.ofAdd 1 := hd
      simp only [hd', toAdd_ofAdd, ZMod.val_one, pow_one] at hk
      have hinv : ((κ⁻¹ γ : Aˣ) : A) = 1 + a (.inr q) * t := by
        rw [MonoidHom.inv_apply]
        exact Units.inv_eq_of_mul_eq_one_right hk
      have e := hm γ (Ine_le_Dec _ hγ)
      have e2 : repOn ρ κ⁻¹ Y γ m = (1 + a (.inr q) * t) • m := by
        simp [repOn, hρ1, matAct_one, ← hinv]
      rw [e2, add_smul, one_smul, add_eq_left, mul_smul] at e
      exact ((ha q).smul_eq_zero).1 e
    · intro q' _ hne
      have hn : ¬ Over (P q') v := fun h' => hne (hSt.1.2.1 _ _ (over_trans h' (over_symm hq)))
      have : d (P q') γ = 1 := (hSt.1.2.2 q').2.2.2.1 v hn _ (N.plOm.2 v) γ hγ
      simp [this]
    · simp

end GlobalTheory.NewPrime.LocInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilledStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariants_killed_alt : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  first | exact @GlobalTheory.NewPrime.LocInv.local_invariants_killed | exact GlobalTheory.NewPrime.LocInv.local_invariants_killed | (intros; apply GlobalTheory.NewPrime.LocInv.local_invariants_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

theorem latT_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  intro l _ Γ _ a m ρs t M h1 h2

  set Λ : Fin m → Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    fun k => Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) with hΛ
  have hsum : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]), ∑ y ∈ t k, zOm l (c y) • y ∈ Λ k := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hone : ∀ k, (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ Λ k := by
    intro k
    obtain ⟨c, hc⟩ := h1 k
    rw [← hc]; exact hsum k c
  have hstab : ∀ k g, ∀ x ∈ Λ k, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k := by
    intro k g x hx
    refine Submodule.span_induction (p := fun x _ => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨c, hc⟩ := h2 k g y hy
      rw [hc]; exact hsum k c
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← zOm_smul, Matrix.mul_smul, zOm_smul]
      exact Submodule.smul_mem _ _ hx

  have hsingle : ∀ k, ∀ x ∈ Λ k, Pi.single k x ∈ latL t 0 := by
    intro k x hx
    have : (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) x ∈ latL t 0 := by
      have hle : (Λ k).map (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) ≤ latL t 0 := by
        rw [hΛ, Submodule.map_span, latL]
        refine Submodule.span_mono ?_
        rintro _ ⟨y, hy, rfl⟩
        refine Set.mem_iUnion.2 ⟨k, y, hy, ?_⟩
        simp
      exact hle (Submodule.mem_map_of_mem hx)
    simpa using this
  have hT : latT ρs t M ≤ latL t 0 := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [show tup ρs g = ∑ k, Pi.single k (tup ρs g k) from (Finset.univ_sum_single _).symm]
      refine Submodule.sum_mem _ fun k _ => hsingle k _ ?_
      have := hstab k g 1 (hone k)
      simpa [tup] using this
    · rw [latL, Submodule.span_le]
      intro z hz
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
      refine hsingle k _ ?_
      have : ((l : ℤ_[l]) ^ M) • y ∈ Λ k := Submodule.smul_mem _ _ (Submodule.subset_span hy)
      rw [← zOm_smul, map_pow, map_natCast] at this
      exact this
  have hfg0 : (latL t (0 : ℕ)).FG := by
    rw [latL]
    refine Submodule.fg_span ?_
    exact Set.finite_iUnion fun k => (t k).finite_toSet.image _
  have hfg : (latT ρs t M).FG := hfg0.of_le hT
  haveI : Module.Finite ℤ_[l] (latT ρs t M) := Module.Finite.iff_fg.2 hfg
  have hinj : Function.Injective (zOm l) :=
    (algebraMap ℚ_[l] (Om l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI tf0 : Module.IsTorsionFree ℤ_[l] (Om l) := .of_smul_eq_zero fun c x h => by
    rw [← zOm_smul, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by simpa using h)
    · right; exact h
  haveI tf1 : Module.IsTorsionFree ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    inferInstanceAs (Module.IsTorsionFree ℤ_[l] (Fin a → Fin a → Om l))
  haveI : Module.IsTorsionFree ℤ_[l] (latT ρs t M) := inferInstance
  haveI : Module.Free ℤ_[l] (latT ρs t M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] (latT ρs t M)
  refine ⟨_, fun s => (b s : Fin m → Matrix (Fin a) (Fin a) (Om l)), ?_, fun s => (b s).2, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
    exact b.linearIndependent.map' (latT ρs t M).subtype (Submodule.ker_subtype _)
  · intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [zOm_smul]
    exact this.symm

end GlobalTheory.TraceConjugationCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledProductSpanLattice_exists_padic_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  first | (exact @GlobalTheory.TraceConjugationCover.latT_basis) | (exact GlobalTheory.TraceConjugationCover.latT_basis) | (intros; apply GlobalTheory.TraceConjugationCover.latT_basis  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleCompose
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleCompose
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BCCancel

variable {R S T X Y : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem cancel_comm (f : X →ₗ[R] Y) (z : T ⊗[S] (S ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R S T T Y ((f.baseChange S).lTensor T z) =
      f.baseChange T (AlgebraTensorModule.cancelBaseChange R S T T X z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem bij_up (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange S)) :
    Function.Bijective (f.baseChange T) := by
  have hl : Function.Bijective ((f.baseChange S).lTensor T) := by
    exact (LinearEquiv.lTensor T (LinearEquiv.ofBijective _ hf)).bijective
  have hfun : ⇑(f.baseChange T) = AlgebraTensorModule.cancelBaseChange R S T T Y ∘
      (f.baseChange S).lTensor T ∘ (AlgebraTensorModule.cancelBaseChange R S T T X).symm := by
    funext z
    simp only [Function.comp_apply, cancel_comm, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).bijective.comp
    (hl.comp (AlgebraTensorModule.cancelBaseChange R S T T X).symm.bijective)

theorem bij_down [Module.FaithfullyFlat S T] (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange T)) :
    Function.Bijective (f.baseChange S) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective S T]
  have hfun : ⇑((f.baseChange S).lTensor T) = (AlgebraTensorModule.cancelBaseChange R S T T Y).symm ∘
      f.baseChange T ∘ AlgebraTensorModule.cancelBaseChange R S T T X := by
    funext z
    simp only [Function.comp_apply, ← cancel_comm, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).symm.bijective.comp
    (hf.comp (AlgebraTensorModule.cancelBaseChange R S T T X).bijective)

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP.BCCancel

theorem bij_lin {A B C N N' N'' : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    [Module B N'] [IsScalarTower A B N'] [AddCommGroup N''] [Module A N''] [Module B N''] [Module C N'']
    [IsScalarTower B C N''] [IsScalarTower A B N''] [IsScalarTower A C N'']
    (u : N →ₗ[A] N') (v : N' →ₗ[B] N'') (hv : IsBaseChange C v)
    (hw : IsBaseChange C ((v.restrictScalars A).comp u)) :
    Function.Bijective ((u.liftBaseChange B).baseChange C) := by
  set L := u.liftBaseChange B
  have h0 := TensorProduct.isBaseChange A N B
  have hc : IsBaseChange C ((v ∘ₗ L : B ⊗[A] N →ₗ[B] N'').restrictScalars A ∘ₗ TensorProduct.mk A B N 1) := by
    convert hw using 1
    ext x
    simp [L, LinearMap.liftBaseChange_tmul]
  have h1 : IsBaseChange C (v ∘ₗ L) := IsBaseChange.of_comp h0 hc
  have hfun : ⇑(L.baseChange C) = hv.equiv.symm ∘ h1.equiv := by
    funext z
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c p => simp [IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [hfun]
  exact hv.equiv.symm.bijective.comp h1.equiv.bijective

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP

theorem semiBC_of_cover : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h →
    ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N']
    [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N')
    (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w →
    SemiBC u := by
  intro l _ R _ B C h hc A _ k N _ _ _ _ N' _ _ _ _ N'' _ _ u v w hw hv hwb
  letI : Algebra A B.A := k.toAlgebra
  letI : Algebra B.A C.A := h.f.toAlgebra
  letI : Algebra A C.A := (h.f.comp k).toAlgebra
  haveI : IsScalarTower A B.A C.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module A N' := Module.compHom N' k
  haveI : IsScalarTower A B.A N' := ⟨fun a b x => mul_smul (k a) b x⟩
  letI : Module B.A N'' := Module.compHom N'' h.f
  letI : Module A N'' := Module.compHom N'' (h.f.comp k)
  haveI : IsScalarTower B.A C.A N'' := ⟨fun a b x => mul_smul (h.f a) b x⟩
  haveI : IsScalarTower A C.A N'' := ⟨fun a b x => mul_smul (h.f (k a)) b x⟩
  haveI : IsScalarTower A B.A N'' := ⟨fun a b x => by
    show h.f (k a * b) • x = h.f (k a) • (h.f b • x)
    rw [map_mul, mul_smul]⟩
  let u' : N →ₗ[A] N' := { toFun := u, map_add' := u.map_add, map_smul' := fun a x => u.map_smulₛₗ a x }
  let v' : N' →ₗ[B.A] N'' := { toFun := v, map_add' := v.map_add, map_smul' := fun a x => v.map_smulₛₗ a x }
  let w' : N →ₗ[A] N'' := { toFun := w, map_add' := w.map_add, map_smul' := fun a x => w.map_smulₛₗ a x }
  have hv' : IsBaseChange C.A v' := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange B.A C.A N' N'' v v' fun _ => rfl).1 hv
  have hw' : IsBaseChange C.A ((v'.restrictScalars A).comp u') := by
    have := (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A C.A N N'' w w' fun _ => rfl).1 hwb
    convert this using 1
    ext x
    exact (hw x).symm
  set L := u'.liftBaseChange B.A
  have hC : Function.Bijective (L.baseChange C.A) := BCCancel.bij_lin u' v' hv' hw'
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := hc.ff 1
  have hQ : Function.Bijective (L.baseChange (C.A ⧸ adI C ^ 1)) := BCCancel.bij_up (S := C.A) L hC
  have hB : Function.Bijective (L.baseChange (B.A ⧸ adI B ^ 1)) :=
    BCCancel.bij_down (T := C.A ⧸ adI C ^ 1) L hQ
  haveI : IsAdicComplete (adI B) B.A := B.complete
  have hJ : adI B ^ 1 ≤ Ideal.jacobson ⊥ := (pow_one (adI B)).le.trans (IsAdicComplete.le_jacobson_bot (adI B))
  have hL : Function.Bijective L := GlobalTheory.T.bijective_of_bijective_baseChange_quotient_jacobson B.A (adI B ^ 1) hJ (B.A ⊗[A] N) N' L hB
  have hu' : IsBaseChange B.A u' :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective L hL) fun x => by
      simp [L, LinearMap.liftBaseChange_tmul]
  exact (GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange A B.A N N' u u' fun _ => rfl).2 hu'

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleComposeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_projective_module_compose : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N'] [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N') (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w → SemiBC u := by
  first | exact @GlobalTheory.BSP.semiBC_of_cover | exact GlobalTheory.BSP.semiBC_of_cover | (intros; apply GlobalTheory.BSP.semiBC_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfComm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMem
open scoped BigOperators

namespace GlobalTheory.CentralIdemIntegral

theorem isIntegral_trace_of_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι L) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine Multiset.sum_induction (IsIntegral ℤ) _ (fun a b ha hb => ha.add hb) isIntegral_zero ?_
  intro μ hμ

  have hroot := Polynomial.isRoot_of_mem_roots hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : Matrix.mulVec A v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

  have hpowv : ∀ k : ℕ, Matrix.mulVec (A ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hμpow : μ ^ (n + 1) = μ := by
    have h1 := hpowv (n + 1)
    rw [hA, hAv] at h1
    have h2 : (μ ^ (n + 1) - μ) • v = 0 := by rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0

  refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
  · rw [Polynomial.degree_X]
    exact_mod_cast (show 1 < n + 1 by omega)
  · simp [hμpow]

theorem isIntegral_trace {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical

  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have h := isIntegral_trace_of_algClosed (A.map φ) hn (by rw [← Matrix.map_pow, hA])
  rw [← AddMonoidHom.map_trace] at h
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h

theorem trace_leftMulMatrix {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by

  have hdiag : ∀ g : G, (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)) g g = x.coeff 1 := by
    intro g
    rw [LinearMap.toMatrixAlgEquiv_apply]
    change (x * MonoidAlgebra.single g 1).coeff g = x.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem isIntegral_card_mul_coeff {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by
  classical

  set y : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hy
  have hcoeff : y.coeff 1 = e.coeff g := by
    rw [hy, MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv, mul_one]
  have hidem : IsIdempotentElem e := he
  have hypow : y ^ (Fintype.card G + 1) = y := by
    rw [hy, (show Commute e (MonoidAlgebra.single g⁻¹ 1) from hc _).mul_pow, hidem.pow_succ_eq,
      MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one, one_mul]
  have hM := isIntegral_trace
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K) (Algebra.lmul K (MonoidAlgebra K G) y))
    (n := Fintype.card G) Fintype.card_ne_zero (by rw [← map_pow, ← map_pow, hypow])
  rw [trace_leftMulMatrix, hcoeff] at hM
  exact hM

theorem card_mul_coeff_mem :
    ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  intro G O K _ _ _ _ _ _ _ _ _ e he hc g
  exact (IsIntegrallyClosed.isIntegral_iff (R := O)).1
    (isIntegral_card_mul_coeff e he hc g).tower_top

end GlobalTheory.CentralIdemIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulCoeffMemStatement
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent : ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  first | exact @GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | exact GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem | (intros; apply GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfComm
noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.IdemAlg

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem idem_integral (i : X.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  have : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  have : CharZero (FractionRing (X.O i)) :=
    charZero_of_injective_ringHom (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hc := card_eq (N := N)
  have : Finite (G0g N) := Nat.finite_of_card_ne_zero (hc ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  let : Fintype (G0g N) := Fintype.ofFinite _
  choose c hcc using GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent (G0g N) (X.O i) (FractionRing (X.O i)) (Y.eAlg i b) (Y.eAlg_idem i b)
    (Y.eAlg_central i b)
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  ext g
  rw [hc, Nat.card_eq_fintype_card]
  simp [hcc]

theorem admALG_of_commG : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := fun D h =>
  (GlobalTheory.TwistInputsTest.admissibleGoodIdempotent_iff_reduced D.nexp).2 fun i hi b => ⟨idem_integral D.nexp i b, h i hi b⟩

end GlobalTheory.IdemAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfCommStatement
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admALG_of_commG_var : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := by
  first | exact @GlobalTheory.IdemAlg.admALG_of_commG | exact GlobalTheory.IdemAlg.admALG_of_commG | (intros; apply GlobalTheory.IdemAlg.admALG_of_commG <;> assumption)
end
end
