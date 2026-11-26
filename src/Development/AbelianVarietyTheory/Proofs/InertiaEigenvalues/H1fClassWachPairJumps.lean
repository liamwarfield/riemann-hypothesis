module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExten
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATopStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseField
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  have hQ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  rw [← algebraMap_smul ((HW l).W K s LL h).EE (((HW l).W K s LL h).Q ^ m) x,
    ((F l).E K s LL h).tie.jD_smul, ((F l).E K s LL h).tie.ioE_ext, map_pow, hQ, map_pow]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  have hB := GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0
  have hB3 := hB.2.2 T (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl (↥(OL LL)) ↥T.L.T)
    (fun g t => rfl)
  have hid : (TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap) = LinearMap.id := TensorProduct.map_id
  have hR := hB3.1
  have hN := hB3.2 hT (restrict_crys D hle T hT)
  have hy1 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') ∈
      Set.range (((F l).E K s LL h).tie.jD T) := hR ▸ ⟨_, ⟨y', rfl⟩, rfl⟩
  have hy2 : TensorProduct.map (LinearMap.id : RW LL →ₗ[↥(OL LL)] RW LL)
      (LinearEquiv.refl (↥(OL LL)) ↥T.L.T).toLinearMap
      (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y')) ∈
      ((F l).E K s LL h).tie.jD T '' (((HW l).W K s LL h).N T : Set (((HW l).W K s LL h).DD T)) :=
    hN ▸ ⟨_, ⟨_, hy', rfl⟩, rfl⟩
  have hm1 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  have hm2 := LinearMap.congr_fun hid (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T)
      (((HW l).W K' s LL h').Q ^ m • y'))
  refine hy1.elim fun y hy => hy2.elim fun z hz => ⟨y, ?_, hy.trans hm1⟩
  show ((HW l).W K s LL h).Q ^ m • y ∈ ((HW l).W K s LL h).N T
  have e : z = ((HW l).W K s LL h).Q ^ m • y := by
    apply ((F l).E K s LL h).tie.jD_inj T
    rw [hz.2, hm2, jD_Qpow, jD_Qpow, hy, hm1]
    rfl
  exact e ▸ hz.1

end GlobalTheory.NL.TransitionThirdCase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseFieldStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  first | exact @GlobalTheory.NL.TransitionThirdCase.main | exact GlobalTheory.NL.TransitionThirdCase.main | (intros; apply GlobalTheory.NL.TransitionThirdCase.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPair
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPair
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.ExtClassKs

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_ext [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (T Z : LocLat G Qp LL O) (htriv : ∀ g x, Z.ρ g x = x) (e₀ : ↥Z.L.T) (he₀ : (e₀ : Z.V) ≠ 0)
    (hone : Z.L.T = Submodule.span O {(e₀ : Z.V)}) (zc : ↥(latticeCocycles T.L)) :
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (et : ↥Y.L.T),
      IsSESLat (Qp := Qp) ι π ∧ π.f et = e₀ ∧ Module.finrank LL Y.V = Module.finrank LL T.V + 1 ∧
        ∀ g, ι.f ((zc : G → T.V) g) = Y.ρ g et - et := by
  let Yt : LocLat G Qp LL O := GlobalTheory.FiniteAdm.extLat hinj T zc
  let ι : LatHom T.L Yt.L :=
    { f := LinearMap.inl LL T.V LL
      equiv := fun g x => by
        change ((T.ρ g x, 0) : T.V × LL) = (T.ρ g x + (0 : LL) • (zc : G → T.V) g, 0)
        simp
      cont := by
        change Continuous fun x : T.V => ((x, 0) : T.V × LL)
        exact continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, 0, map_zero _⟩ }
  haveI : ContinuousSMul LL Z.V := IsModuleTopology.toContinuousSMul LL Z.V
  let π : LatHom Yt.L Z.L :=
    { f := (LinearMap.toSpanSingleton LL Z.V (e₀ : Z.V)).comp (LinearMap.snd LL T.V LL)
      equiv := fun g x => by
        rw [htriv]
        rfl
      cont := by
        change Continuous fun x : T.V × LL => x.2 • (e₀ : Z.V)
        exact continuous_snd.smul continuous_const
      T_le := by
        rintro ⟨v, a⟩ ⟨-, o, rfl⟩
        change (algebraMap O LL o) • (e₀ : Z.V) ∈ Z.L.T
        rw [algebraMap_smul]
        exact Z.L.T.smul_mem o e₀.2 }
  refine ⟨Yt, ι, π, ⟨((0 : T.V), (1 : LL)), Submodule.zero_mem _, 1, map_one (algebraMap O LL)⟩,
    ⟨LinearMap.inl_injective, ?_, ?_, ?_, ?_⟩, one_smul LL (e₀ : Z.V), ?_, ?_⟩
  · intro w
    have hw : w ∈ Submodule.span LL {(e₀ : Z.V)} := by
      rw [← Submodule.span_span_of_tower O, ← hone, Z.L.span]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), a), rfl⟩
  · intro w hw
    rw [hone] at hw
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨((0 : T.V), algebraMap O LL o), ⟨Submodule.zero_mem _, o, rfl⟩,
      algebraMap_smul LL o (e₀ : Z.V)⟩
  · rintro ⟨w, a⟩
    constructor
    · intro h0
      have ha : a = 0 := (smul_eq_zero.1 (show a • (e₀ : Z.V) = 0 from h0)).resolve_right he₀
      exact ⟨w, Prod.ext rfl ha.symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact zero_smul LL (e₀ : Z.V)
  · intro y hy
    exact hy.1
  · change Module.finrank LL (T.V × LL) = _
    rw [Module.finrank_prod, Module.finrank_self]
  · intro g
    change (((zc : G → T.V) g, 0) : T.V × LL) =
      ((T.ρ g 0 + (1 : LL) • (zc : G → T.V) g - 0, 1 - 1) : T.V × LL)
    simp

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem generic [T2Space LL] [IsTopologicalRing LL] (E : EtTie W RA RW inclR φR gR πA)
    (hinj : Function.Injective (algebraMap O LL)) (hR : Function.Injective (algebraMap O RW))
    (hdense : ∀ M : Submonoid ↥W.GKs, IsClosed (M : Set ↥W.GKs) →
      (∀ g : ↥W.GKs, W.resΓ (g : G) = 1 → g ∈ M) → (∀ g : ↥W.GKs, W.resΓ (g : G) = W.gam → g ∈ M) →
      ∀ g, g ∈ M)
    (T : LocLat G Qp LL O) (hGKs : W.GKs = ⊤) (M p : ℕ)
    (hBK : ∀ (Y : LocLat G Qp LL O) (ι : T.V →ₗ[LL] Y.V), (∀ g x, ι (T.ρ g x) = Y.ρ g (ι x)) →
      Function.Injective ι → Module.finrank LL Y.V = Module.finrank LL T.V + 1 →
      ∀ x : Y.V, x ∉ LinearMap.range ι → ∀ c : G → T.V, (∀ g, ι (c g) = Y.ρ g x - x) →
      (∃ y : T.V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ g y - y) → IsCrys PD Y.ρ)
    (hlift : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L), IsCrys PD Y.ρ →
      IsSESLat (Qp := Qp) ι π →
      ∃ c : ℕ, ∀ z ∈ W.N W.one, ∃ y ∈ W.N Y, W.map π y = (p : LetA O n) ^ c • z)
    (hint : p8 W T M) (κ : LatticeCohomology (resLat T W.GKs)) (hκ : κ ∈ H1fIntegralCyclotomicLayer W T) :
    ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ M) ∧ z ∈ aN W T W.X ∧
      W.cl T ⟨(y, z), hyz⟩ = (p ^ c : ℕ) • κ := by
  obtain ⟨c₀, hc₀, rfl⟩ := hκ
  obtain ⟨xB, hxB⟩ : ∃ x : T.V ⊗[Qp] B, ∀ g : ↥W.GKs,
      (c₀ : ↥W.GKs → T.V) g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (g : G) x - x := hc₀.2.2
  have hmem : ∀ g, g ∈ W.GKs := fun g => by rw [hGKs]; exact Subgroup.mem_top g
  have hz1 : (fun g => (c₀ : ↥W.GKs → T.V) ⟨g, hmem g⟩) ∈ latticeCocycles T.L :=
    ⟨⟨c₀.2.1.1.comp (Continuous.subtype_mk continuous_id hmem),
      fun g g' => c₀.2.1.2 ⟨g, hmem g⟩ ⟨g', hmem g'⟩⟩, fun g _ => c₀.2.2 ⟨g, hmem g⟩ (Set.mem_univ _)⟩
  obtain ⟨e, e₀, hspan, hje, hN⟩ := E.one_e
  have hone : W.one.L.T = Submodule.span O {(e₀ : W.one.V)} := by
    have h1 := congrArg (Submodule.map W.one.L.T.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  have he₀ : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨e', he', hsp⟩ := W.one_line
    have : e' ∈ W.one.L.T := by rw [hsp]; exact Submodule.mem_span_singleton_self e'
    rw [hone, h0, Submodule.span_singleton_eq_bot.2 rfl] at this
    exact he' ((Submodule.mem_bot _).1 this)
  have hφe : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγe : ∀ g, W.γD W.one g e = e := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have h1 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
    rw [E.jD_act, hje]
    simp [TWact, h1]
  have heN : e ∈ W.N W.one := by rw [hN]; exact Submodule.mem_span_singleton_self e
  obtain ⟨Y, ι, π, et, hS, hπ, hrk, hc⟩ := exists_ext hinj T W.one W.one_triv e₀ he₀ hone ⟨_, hz1⟩
  have hY : IsCrys PD Y.ρ := hBK Y ι.f ι.equiv hS.1 hrk et
    (fun hx => he₀ (by rw [← hπ]; exact (hS.2.2.2.1 _).2 hx)) _ hc ⟨xB, fun g => hxB ⟨g, hmem g⟩⟩
  obtain ⟨k, hk⟩ := hlift Y ι π hY hS
  obtain ⟨x, hxN, hxπ⟩ := hk e heN
  have hxπ' : W.map π x = ((p : O) ^ k) • e := by
    rw [hxπ, ← algebraMap_smul (LetA O n) ((p : O) ^ k) e, map_pow, map_natCast]
  obtain ⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩ := hint Y ι π hS hY e heN hφe hγe x hxN _ hxπ'
  have hιinj : Function.Injective (W.map ι) := by
    intro a b hab
    apply E.jD_inj T
    apply GlobalTheory.Cyc.DictKs.lTensor_inj hS RW
    have h1 := congrArg (E.jD Y) hab
    rw [E.jD_map, E.jD_map] at h1
    exact h1
  have key : W.map ι ((W.γD T W.gam y - y) - (W.φD T z - z)) = W.map ι 0 := by
    rw [map_zero, map_sub, map_sub, map_sub, W.map_γ, W.map_φ, hyι, hzι, LocWach.γ, map_sub, map_sub,
      W.φγ_comm]
    abel
  have hyz : (y, z) ∈ W.divisibleCocycles T := by
    have h0 := hιinj key
    rw [sub_eq_add_neg] at h0
    exact h0
  refine ⟨k, y, z, hyz, hy, hz, ?_⟩
  refine (GlobalTheory.Cyc.DictKs.generic E hR hdense T Y W.one ι π hS (((p : O) ^ k) • et) (((p : O) ^ k) • e₀) x
    (by
      rw [Submodule.coe_smul, Submodule.coe_smul, ← hπ, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        map_smul, algebraMap_smul])
    (by rw [hxπ', map_smul, hje, TensorProduct.tmul_smul]) ⟨(y, z), hyz⟩ hyι hzι (((p : O) ^ k) • c₀)
    (fun g => by
      have h1 := hc g
      change ι.f ((c₀ : ↥W.GKs → T.V) g) = _ at h1
      change ι.f (((p : O) ^ k) • (c₀ : ↥W.GKs → T.V) g) = _
      rw [Submodule.coe_smul, ← algebraMap_smul LL ((p : O) ^ k) (et : Y.V),
        ← algebraMap_smul LL ((p : O) ^ k) ((c₀ : ↥W.GKs → T.V) g), map_smul, map_smul, h1, smul_sub])).trans ?_
  rw [Submodule.Quotient.mk_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

end Generic


set_option maxHeartbeats 1600000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT hGKs M hh hJ κ hκ
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  refine generic E (fun a b hab => Subtype.ext hab) (GlobalTheory.Cyc.DictKs.algebraMap_RW_inj LL)
    (GlobalTheory.Cyc.DictKs.dense_gen (D.loc l) (D.locA l) K s LL h _ ((HW l).W_s K s LL h)) T hGKs (mx M) l
    ?_ ?_ (GlobalTheory.T.p8_of_cmpOf D HW F Cm l K s LL h T M hh hT hJ) κ hκ
  · intro Y ι h1 h2 h3 x h4 c h5
    exact (GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Y.V Y.ρ ι
      h1 h2 h3 hT x h4 c h5).1
  · intro Y ι π hY hS
    exact (GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T Y _ ι π hT hY (Formalism.MainNotions.LiftingTheory.gen_one_crys _) hS).imp
      fun c hc z hz => (hc z hz).1

end GlobalTheory.NL.ExtClassKs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPairStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1f_class_of_wach_pair : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.GKs = ⊤ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  first | exact @GlobalTheory.NL.ExtClassKs.main | exact GlobalTheory.NL.ExtClassKs.main | (intros; apply GlobalTheory.NL.ExtClassKs.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosed
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosedX

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem jD_aN_eq_range_gen {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}
    {s : ℕ} {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (T : Lt K LL) (a : AA K LL) :
    ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T a : Set (W.DD T)) =
      Set.range fun c : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (c i)) • y i := by
  obtain ⟨S, hS⟩ := W.N_fg T
  let n : Fin S.card → W.DD T := fun i => (S.equivFin.symm i : W.DD T)
  have hrange : Set.range n = (S : Set (W.DD T)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2
    · intro hz; exact ⟨S.equivFin ⟨z, hz⟩, by simp [n]⟩
  have hspan : W.N T = Submodule.span (AA K LL) (Set.range n) := by rw [hrange, hS]
  refine ⟨S.card, fun i => E.tie.jD T (a • n i), ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hx
    rw [hspan] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AA K LL)).1 hm
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [GlobalTheory.NL.WkRange.jD_smul_letter]
    exact smul_comm _ _ _
  · rintro ⟨c, rfl⟩
    refine ⟨∑ i, c i • (a • n i), ?_, ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, c i • n i, ?_, ?_⟩
      · rw [hspan]
        exact (Submodule.mem_span_range_iff_exists_fun (AA K LL)).2 ⟨c, rfl⟩
      · simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum]
        exact Finset.sum_congr rfl fun i _ => GlobalTheory.NL.WkRange.jD_smul_letter E T _ _

theorem jD_XN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := jD_aN_eq_range_gen ((F l).E K s LL h) T ((HW l).W K s LL h).X
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosedX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWachImageIsClosedStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weakTopology_wachImage_isClosed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosedX.jD_XN_closed | exact GlobalTheory.WeakClosedX.jD_XN_closed | (intros; apply GlobalTheory.WeakClosedX.jD_XN_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Xstab
noncomputable section

namespace GlobalTheory.NL.XStab

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem φpow_γA (k : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

theorem X_dvd_γX (g : W.Gam) : W.X ∣ W.γA g W.X := by
  obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X :=
    PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1
  have h1 : W.γA g letπ = letπ * (fun _ => c) := by
    funext i
    simp [LocWach.γA, letγ, letπ, hc]
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩
  rw [LocWach.X, ← φpow_γA, h1, map_mul]

theorem γD_mem_aN_X (T : LocLat G Qp LL O) (δ : W.Gam) (x : W.DD T) (hx : x ∈ aN W T W.X) :
    W.γD T δ x ∈ aN W T W.X := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := X_dvd_γX W δ
  refine ⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩
  change W.X • c • W.γD T δ y = W.γD T δ (W.X • y)
  rw [γD_smulA, hc, mul_smul]

end Generic

theorem xstab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (δ : ((HW l).W K s LL h).Gam) (x : ((HW l).W K s LL h).DD T), x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X → ((HW l).W K s LL h).γD T δ x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X :=
  fun _ HW l _ K s LL h T δ x hx => γD_mem_aN_X ((HW l).W K s LL h) T δ x hx

end GlobalTheory.NL.XStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystalline
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (((HW l).W K s LL h).GKs : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥((HW l).W K s LL h).GKs := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  letI := τ
  haveI hT2 : T2Space (TW (RW LL) T) := hτ.1
  have hTG : IsTopologicalAddGroup (TW (RW LL) T) := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let a : ↥((HW l).W K s LL h).GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
    (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
  have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
    fun g x => rfl
  have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
    intro g g' x
    simp only [ha1]
    exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
      (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
  have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
    GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
  have haj : ∀ g (w : ((HW l).W K s LL h).DD T), a g (((F l).E K s LL h).tie.jD T w) =
      ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ (g : ↥(GK K))) w) :=
    fun g w => (((F l).E K s LL h).tie.jD_act T (g : ↥(GK K)) w).symm
  let J : AddSubgroup (TW (RW LL) T) :=
    (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X).toAddSubgroup.map (((F l).E K s LL h).tie.jD T).toAddMonoidHom
  have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X,
      ((F l).E K s LL h).tie.jD T w = x := fun x => AddSubgroup.mem_map
  have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
    have : (J : Set (TW (RW LL) T)) = ((F l).E K s LL h).tie.jD T ''
        (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T)) := by
      ext x
      exact (hJm x).trans Iff.rfl
    rw [this]; exact hclo
  have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
    intro g x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj]
    exact (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1, rfl⟩
  have hJk : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
    intro h' hh x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj, hl1 h' hh, ((HW l).W K s LL h).γD_one]
  haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
  haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
  haveI hCS : ContinuousSub (TW (RW LL) T) :=
    ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
  have hZc : Continuous (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) := by
    unfold Zf
    exact (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
      (((hact b).comp continuous_subtype_val).sub continuous_const)
  have hZm : ∀ g g', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b (g * g') =
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g + a g (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g') := by
    intro g g'
    have e : (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
        ⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
          ⟨T.ρ (g : ↥(GK K)) ((c : ↥((HW l).W K s LL h).GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
      Subtype.ext (c.2.1.2 g g')
    have hz : ∀ g'', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g'' =
        (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g'', GlobalTheory.HerrClassMaps.mem_T c g''⟩ : ↥T.L.T) +
          (a g'' b - b) := fun _ => rfl
    simp only [hz, map_add (f := _), map_sub, ha1t, hamul, e, TensorProduct.tmul_add]
    abel
  have hZk' : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b h' = 0 :=
    fun h' hh => hZk h' (hl1 h' hh)
  have hzJ : ((F l).E K s LL h).tie.jD T z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystallineStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  first | exact @GlobalTheory.NL.ZVal.zval | exact GlobalTheory.NL.ZVal.zval | (intros; apply GlobalTheory.NL.ZVal.zval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValues
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValues
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.HerrClassUniq

theorem cocycle_eq {l : ℕ} [Fact l.Prime] {G V LL : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [T2Space LL]
    [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (a : G → V → V) (c c' : G → V) (hc : Continuous c) (hc' : Continuous c')
    (ha : ∀ x, a 1 x = x)
    (hcc : ∀ g h, c (g * h) = c g + a g (c h)) (hcc' : ∀ g h, c' (g * h) = c' g + a g (c' h))
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (hker : ∀ h, lam h = 1 → c h = c' h) (hg₀ : c g₀ = c' g₀) :
    c = c' := by
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa [ha] using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa [ha] using this
  let S : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := fun {a b} ha hb => by
        change c (a * b) = c' (a * b)
        rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
      one_mem' := by
        change c 1 = c' 1
        rw [h1, h1']
      inv_mem' := fun {a} ha => by
        change c a⁻¹ = c' a⁻¹
        have e1 := hcc a⁻¹ a
        have e2 := hcc' a⁻¹ a
        rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
        rw [inv_mul_cancel, h1'] at e2
        exact add_right_cancel (e1.symm.trans e2) }
  have hS : IsClosed (S : Set G) := by
    have : {g | c g = c' g} = ⋂ f : Module.Dual LL V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')
  funext g
  have hcl : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem (show g₀ ∈ S from hg₀) n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hcl.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨x, hx, hxg⟩ := hmem
  have h2 : g * x⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hxg, mul_inv_cancel])
  have h3 : g ∈ S := by simpa using S.mul_mem h2 hx
  exact h3

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem val_eq_of_Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c c' : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) (e : Zf AI T H c b g = Zf AI T H c' b g) :
    (c : ↥H → T.V) g = (c' : ↥H → T.V) g := by
  unfold Zf at e
  exact congrArg Subtype.val ((GlobalTheory.WittTensorFixed.main l K LL T).2.2 (add_right_cancel e))


set_option maxHeartbeats 1000000 in
theorem cocycle_eq_lat {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K)) (hH : IsClosed (H : Set ↥(GK K)))
    (c c' : ↥(latticeCocycles (resLat T H)))
    (lam : ↥H →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : ↥H)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (hker : ∀ h, lam h = 1 → (c : ↥H → T.V) h = (c' : ↥H → T.V) h)
    (hg₀ : (c : ↥H → T.V) g₀ = (c' : ↥H → T.V) g₀) : c = c' := by
  haveI := GlobalTheory.HerrClassMaps.compact_GK K
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.1 hH.isCompact
  haveI := T.mtop
  exact Subtype.ext (cocycle_eq (LL := ↥LL.1) (V := T.V) (fun (g : ↥H) (x : T.V) => T.ρ (g : ↥(GK K)) x) c c' c.2.1.1 c'.2.1.1
    (fun x => by simp) c.2.1.2 c'.2.1.2 lam hlam g₀ h₀ hker hg₀)


set_option maxHeartbeats 2000000 in
theorem class_of_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  intro D HW F l _ K s LL h T c b y z hyz g₀ hg₀ hb hk hz
  refine (cl_fit D HW F K s LL h T y z hyz b hb).elim fun cW hW => ?_
  refine (lam_exists D HW K s LL h).elim fun lam hl => ?_
  have e : c = cW := cocycle_eq_lat T _ hl.2.2.2.2 c cW lam hl.1 g₀ ((hl.2.2.1 g₀).2 hg₀)
    (fun g hg => val_eq_of_Zf (D.locA l) T _ c cW b g
      ((hk g ((hl.2.1 g).1 hg)).trans (hW.2.1 g ((hl.2.1 g).1 hg)).symm))
    (val_eq_of_Zf (D.locA l) T _ c cW b g₀ (hz.trans (hW.2.2 g₀ hg₀).symm))
  exact (congrArg Submodule.Quotient.mk e).trans hW.1

end GlobalTheory.NL.HerrClassUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValuesStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herr_class_of_cocycle_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  first | exact @GlobalTheory.NL.HerrClassUniq.class_of_values | exact GlobalTheory.NL.HerrClassUniq.class_of_values | (intros; apply GlobalTheory.NL.HerrClassUniq.class_of_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelations
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.HerrCocycleCriterion

theorem herr_of_tie {O D M : Type} [CommRing O] [AddCommGroup D] [Module O D] [AddCommGroup M]
    [Module O M] (γ φ : D →ₗ[O] D) (g Φ : M →ₗ[O] M) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (y z : D) (b t : M) (hγ : j (γ y) = g (j y)) (hφ : j (φ z) = Φ (j z))
    (hc : Φ (g b) = g (Φ b)) (ht : Φ t = t) (hy : Φ b - b = j y) (hz : t + (g b - b) = j z) :
    (y, z) ∈ herrCocycles γ φ := by
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  apply hj
  rw [map_zero, map_add (f := _), map_neg, map_sub, map_sub, hγ, hφ, ← hy, ← hz, map_add (f := _), map_sub, map_sub,
    hc, ht]
  abel

theorem TWmap_one {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R]
    [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWmap f T ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t := by
  simp [TWmap]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cocyc : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  intro D HW F l _ K s LL h T c b y z g₀ hg hy hz
  have h1 := ((F l).E K s LL h).tie.jD_act T (g₀ : ↥(GK K)) y
  rw [hg] at h1
  exact herr_of_tie _ _ _ _ _ (((F l).E K s LL h).tie.jD_inj T) y z b _ h1
    (((F l).E K s LL h).tie.jD_φ T z)
    (GlobalTheory.HerrClassMaps.TWmap_act _ _ (GlobalTheory.HerrClassMaps.phi_gRW (D.locA l) LL _) T _ b)
    (TWmap_one _ T _) hy hz

end GlobalTheory.NL.HerrCocycleCriterion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelationsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herr_cocycle_of_witt_tensor_relations : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  exact @GlobalTheory.NL.HerrCocycleCriterion.cocyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExt
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpRestrict

open GlobalTheory.DRFil

theorem jump_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  intro l _ P AI T K K' LL hle V _ _ _ _ _ ρ hc τ' a hj
  have := K.2
  have := K'.2
  have := LL.2
  set τ := τ'.comp (IntermediateField.inclusion hle) with hτ
  have hF := isField_dR T
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) hF ρ (filSpans T K LL ρ (crys T K LL ρ hc).1) τ
  set e' := idem (K := ↥K'.1) P.R.BdR (LL := ↥LL.1) τ' with he'
  set e := idem (K := ↥K.1) P.R.BdR (LL := ↥LL.1) τ with he
  have hee : e' * e = e' := by
    obtain ⟨n, x, c, hc1, hc2⟩ := idem_repr (K := ↥K.1) P.R.BdR τ
    rw [he, hc1]
    have := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ' n x (fun i => IntermediateField.inclusion hle (c i))
    exact (this.trans (by rw [← hc2]; rfl)).trans (one_smul _ _)
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ'
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V e' (d i)) k := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r hr i => ?_, fun n y hy => ?_⟩
    · exact sm_idem_mem_DdRE (P.PD K') _ τ' (GlobalTheory.Per.TiedRestrict.ddR_le hle ρ (hA.mem i).1.1)
    · refine sm_idem_mem_FilV (P.PD K') τ' ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (hA.mem i).2
    · have h1 := hA.indep (fun i => r i * e') (by
        rw [← hr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_mul])
      calc e' * r i = (e' * e) * r i := by rw [hee]
        _ = e * (r i * e') := by ring
        _ = 0 := h1 i
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']
        exact hr i
      · have h2 : sm ℚ_[l] P.R.BdR ↥LL.1 V e' y =
            sm ℚ_[l] P.R.BdR ↥LL.1 V e' (sm ℚ_[l] P.R.BdR ↥LL.1 V e y) := by
          rw [← sm_mul, hee]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h2, hy', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_comm]
  rw [hA'.isJumpV_iff] at hj
  exact hA.isJumpV_iff a |>.2 hj

end GlobalTheory.Per.JumpRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExtStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJump_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  first | exact @GlobalTheory.Per.JumpRestrict.jump_restrict | exact GlobalTheory.Per.JumpRestrict.jump_restrict | (intros; apply GlobalTheory.Per.JumpRestrict.jump_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumps
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent

set_option maxHeartbeats 40000000 in
private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  obtain ⟨y, hy, hjy⟩ := GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  exact ⟨y, hy, hjy⟩

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  obtain ⟨y, hy, hjy⟩ := descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  obtain ⟨z, hz, hjz⟩ := GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz'
  obtain ⟨b', hb'⟩ := (GlobalTheory.WittTensorFixed.main l K' LL (resLt (K := K) (K' := K') (LL := LL) hle T)).1
    (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  obtain ⟨c', hc'cl, hc'0, hc'g⟩ := cl_fit D HW F K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) y' z' hyz' b' hb'
  obtain ⟨c, hcc', hZf⟩ := push_cocycle (D.locA l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop c'
  have hb : TWmap (φRW LL) T (toTW hle T b') - toTW hle T b' = ((F l).E K s LL h).tie.jD T y := by
    rw [toTW_φ, hb', hjy]
  have hone : ∀ g : ↥((HW l).W K s LL h).GKs,
      ((HW l).W K' s LL h').resΓ ((fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g : ↥((HW l).W K' s LL h').GKs) : ↥(GK K')) = 1 ↔
        ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g =>
    (resΓ_one_iff (D.loc l) K' LL _ ((HW l).W K' s LL h') _).trans
      (resΓ_one_iff (D.loc l) K LL _ ((HW l).W K s LL h) _).symm
  have hzero : ∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 →
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') g = 0 := by
    intro g hg
    rw [hZf b' g, hc'0 _ ((hone g).2 hg), toTW_zero]
  obtain ⟨lam', hlam'c, hlam'1, hlam'g, ⟨g', hg'⟩, -⟩ := lam_exists D HW K' s LL h'
  let lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l] := lam'.comp (fHom ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlamc : Continuous lam := hlam'c.comp (fMap_cont ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlam1 : ∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g hg =>
    (hone g).1 ((hlam'1 _).1 hg)
  have hfe : fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = Multiplicative.ofAdd 1 := by
    show lam' (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g')) = _
    rw [hfe, hg']
  have hZ₁ : Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') =
      ((F l).E K s LL h).tie.jD T z := by
    rw [hZf b' _, hfe, hc'g g' ((hlam'g g').1 hg'), hjz]
  have hall := GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline D HW F l K s LL h T hT c (toTW hle T b') lam hlamc hlam1 hzero _ hg₁ z hz hZ₁
  obtain ⟨lamK, -, -, hlamKg, ⟨g₀, hg₀⟩, -⟩ := lam_exists D HW K s LL h
  have hγ := (hlamKg g₀).1 hg₀
  obtain ⟨z₀, hz₀, hZ₀⟩ := hall g₀
  have hyz := GlobalTheory.T.herr_cocycle_of_witt_tensor_relations D HW F l K s LL h T c (toTW hle T b') y z₀ g₀ hγ hb hZ₀
  exact ⟨y, z₀, hyz, hy, hz₀, c, c',
    GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c (toTW hle T b') y z₀ hyz g₀ hγ hb hzero hZ₀, hc'cl, hcc'⟩


set_option maxHeartbeats 4000000 in
theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT M hh hJ κ hκ
  obtain ⟨K', h', hle, hK0, htop, hiff⟩ := base_setup D HW K s LL h
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K' := fun g => (hiff _).1 g.2
  have hT' := restrict_crys D hle T hT
  have hJ' := restrict_jumps D HW K s LL h K' h' hle T hT M hh hJ
    (fun τ' a hj => @GlobalTheory.T.hodgeTateJump_restrict_finite_ext l _ (D.loc l) (D.locA l) (D.locT l) K K' LL hle T.V _ _ _ _ _ T.ρ hT τ' a hj)
  obtain ⟨cκ, cκ', hcκ, hcκ'f, hcκ'⟩ := pull_h1f (D.loc l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm κ hκ
  obtain ⟨n, y', z', hyz', hy', hz', hcl'⟩ := GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' _ hcκ'f
  haveI : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  rw [hmx] at hy'
  obtain ⟨y, z, hyz, hy, hz, c, c', hc, hc', hcc'⟩ :=
    descend D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT (mx M) y' z' hyz' hy' hz'
  exact ⟨n, y, z, hyz, hy, hz, hc.symm.trans ((push_class hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm hm' htop c cκ c' cκ' hcc' hcκ'
    _ (hc'.trans hcl')).trans (congrArg ((l ^ n : ℕ) • ·) hcκ))⟩


set_option maxHeartbeats 4000000 in
theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumpsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1f_class_wach_pair_filtration_jumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  first | exact @GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex | exact GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex | (intros; apply GlobalTheory.NL.CrystallineDescent.pow_smul_from_complex <;> assumption)
end
