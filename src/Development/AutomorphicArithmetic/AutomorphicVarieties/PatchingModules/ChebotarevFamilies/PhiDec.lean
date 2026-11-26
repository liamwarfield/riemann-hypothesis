module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

theorem UpperTheory.V.Pa.phiDec :
    LocalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → PhiCond (Dec (F := F) A) l := by
  intro hLF l hl F Ω _ _ _ _ _ A v hA
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (Dec (F := F) A) (l ^ 1) := phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hLF F Ω l 1 M A ρ v one_pos hA hρ
    exact f1
  rwa [pow_one] at key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.IpEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.ipEq :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), (∀ u, (residOf r).Ip u = r.Ip u ∧ (residOf r).Ip u = (globOf r V0).frame.Iu u) ∧ ∀ [IsNoetherianRing O] (B : UniversalOrdinaryDeterminantRing r), augmentationIdealKernel (pairOf B.u) = {z | z ∈ B.GroupAlgebraKernelIdeal} := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r
  have h1 : ∀ u, (residOf r).Ip u = r.Ip u := by
    intro u
    refine le_antisymm (residOf_Ip_le r u) ?_
    rintro g ⟨⟨γ, hγ, rfl⟩, h2⟩
    refine ⟨⟨⟨γ, Ine_le_Dec _ hγ⟩, ⟨hγ, ?_⟩, rfl⟩, h2⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i
  have h2 : ∀ u, (residOf r).Ip u = (globOf r V0).frame.Iu u := by
    intro u
    refine le_antisymm inf_le_left (le_inf le_rfl ?_)
    rintro g ⟨γ, ⟨-, h⟩, rfl⟩
    exact Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h i
  refine ⟨fun u => ⟨h1 u, h2 u⟩, ?_⟩
  intro _ B
  have h3 : (pairOf B.u).D.CH ∪ pairGens (pairOf B.u) = B.E0gens := by
    unfold pairGens UniversalOrdinaryDeterminantRing.E0gens
    simp only [h1]
    rw [Set.union_assoc]
    rfl
  have h4 : (pairOf B.u).D.chBar (pairGens (pairOf B.u)) = B.GroupAlgebraKernelIdeal :=
    congrArg (closureIdeal (maximalIdeal B.B)) h3
  exact congrArg (fun K : TwoSidedIdeal (MonoidAlgebra B.B V0.frame.G₀) => {z | z ∈ K}) h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiGS
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have e : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = ((g⁻¹ • x).out : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hm := QuotientGroup.eq.mp e
  simpa [mul_inv_rev, mul_assoc] using hm

private theorem core_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H K : Subgroup Γ)
    [Finite (Γ ⧸ H)] (hK : IsOpen (K : Set Γ)) (hKH : K ≤ H) :
    ∃ U : Set Γ, IsOpen U ∧ (1 : Γ) ∈ U ∧ ∀ k ∈ U, ∀ y : Γ ⧸ H, (y.out)⁻¹ * k * y.out ∈ K ∧ k • y = y := by
  refine ⟨⋂ y : Γ ⧸ H, (fun k => (y.out)⁻¹ * k * y.out) ⁻¹' (K : Set Γ), ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun y =>
      hK.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · simp
  · intro k hk y
    have hy : (y.out)⁻¹ * k * y.out ∈ K := Set.mem_iInter.mp hk y
    refine ⟨hy, ?_⟩
    rw [← QuotientGroup.out_eq' y, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have hi := H.inv_mem (hKH hy)
    simpa [mul_assoc] using hi

private theorem mult_map_mul_right_eq_of_chi_eq_one {Γ : Type} [Group Γ] (H : Subgroup Γ) (g g' : Γ) (x : Γ ⧸ H)
    (h : (g⁻¹ * g') • (g⁻¹ • x) = g⁻¹ • x) : g'⁻¹ • x = g⁻¹ • x := by
  calc g'⁻¹ • x = (g⁻¹ * g')⁻¹ • (g⁻¹ • x) := by
        rw [← mul_smul]
        congr 1
        group
    _ = g⁻¹ • x := by rw [inv_smul_eq_iff, h]

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  obtain ⟨U₀, hU₀o, hU₀1, hU₀⟩ := core_lemma H H hH le_rfl
  have hρ : ContAction (permR (ZMod n) H) := by
    show Continuous fun p : Γ × (Γ ⧸ H → ZMod n) => permR (ZMod n) H p.1 p.2
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨g, m⟩
    have hmem : {p : Γ × (Γ ⧸ H → ZMod n) | g⁻¹ * p.1 ∈ U₀ ∧ p.2 = m} ∈ nhds (g, m) := by
      apply IsOpen.mem_nhds
      · exact (hU₀o.preimage (continuous_const.mul continuous_fst)).inter
          ((isOpen_discrete {m}).preimage continuous_snd)
      · simp [hU₀1]
    filter_upwards [hmem] with p hp
    obtain ⟨hk, hp2⟩ := hp
    show permR (ZMod n) H p.1 p.2 = permR (ZMod n) H g m
    rw [hp2]
    funext y
    rw [permR_apply, permR_apply, mult_map_mul_right_eq_of_chi_eq_one H g p.1 y (hU₀ _ hk (g⁻¹ • y)).2]
  have hcoc : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) →
      (fun (g : Γ) (x : Γ ⧸ H) => Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩))
        ∈ Z1 (permR (ZMod n) H) := by
    intro φ hφ
    show Continuous _ ∧ _
    constructor
    · have hKo : IsOpen ((φ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
        rw [Subgroup.coe_map]
        exact hH.isOpenMap_subtype_val _ hφ
      obtain ⟨U, hUo, hU1, hU⟩ := core_lemma H (φ.ker.map H.subtype) hKo (Subgroup.map_subtype_le _)
      apply IsLocallyConstant.continuous
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have hmem : {g' : Γ | g⁻¹ * g' ∈ U} ∈ nhds g :=
        (hUo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [hU1])
      filter_upwards [hmem] with g' hk
      funext x
      obtain ⟨hK, hfix⟩ := hU _ hk (g⁻¹ • x)
      obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.mp hK
      have e1 := mult_map_mul_right_eq_of_chi_eq_one H g g' x hfix
      have e2 : (⟨(x.out)⁻¹ * g' * (g'⁻¹ • x).out, sec_mem H g' x⟩ : H) =
          ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩ * b := by
        apply Subtype.ext
        show (x.out)⁻¹ * g' * (g'⁻¹ • x).out = (x.out)⁻¹ * g * (g⁻¹ • x).out * (b : Γ)
        rw [show (b : Γ) = _ from hbv, e1]
        group
      show Multiplicative.toAdd (φ _) = Multiplicative.toAdd (φ _)
      rw [e2, map_mul, (MonoidHom.mem_ker).mp hb, mul_one]
    · intro g h
      funext x
      simp only [Pi.add_apply, permR_apply]
      rw [← toAdd_mul, ← map_mul]
      refine congrArg (fun y : H => Multiplicative.toAdd (φ y)) (Subtype.ext ?_)
      show (x.out)⁻¹ * (g * h) * ((g * h)⁻¹ • x).out =
        (x.out)⁻¹ * g * (g⁻¹ • x).out * (((g⁻¹ • x).out)⁻¹ * h * (h⁻¹ • (g⁻¹ • x)).out)
      rw [mul_inv_rev, mul_smul]
      group
  haveI := h (Γ ⧸ H → ZMod n) (permR (ZMod n) H) hρ
  refine Finite.of_injective (fun χ : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} =>
    (Submodule.Quotient.mk ⟨_, hcoc χ.1 χ.2⟩ : H1 (permR (ZMod n) H))) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hEq
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp ((Submodule.Quotient.eq _).mp hEq))
  apply Subtype.ext
  ext h0
  obtain ⟨x0, hx0⟩ : ∃ x0 : Γ ⧸ H, x0 = ((1 : Γ) : Γ ⧸ H) := ⟨_, rfl⟩
  have ha : x0.out ∈ H := by
    have e : ((x0.out : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) := by rw [QuotientGroup.out_eq', hx0]
    simpa using H.inv_mem (QuotientGroup.eq.mp e)
  obtain ⟨g, hg⟩ : ∃ g : Γ, g = x0.out * h0 * (x0.out)⁻¹ := ⟨_, rfl⟩
  have hgH : g ∈ H := hg ▸ H.mul_mem (H.mul_mem ha h0.2) (H.inv_mem ha)
  have hgx0 : g⁻¹ • x0 = x0 := by
    rw [hx0, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using hgH
  have hel : ∀ (y : Γ ⧸ H) (hy : y = g⁻¹ • x0) (pr : (x0.out)⁻¹ * g * y.out ∈ H),
      (⟨(x0.out)⁻¹ * g * y.out, pr⟩ : H) = h0 := by
    intro y hy pr
    apply Subtype.ext
    show (x0.out)⁻¹ * g * y.out = (h0 : Γ)
    rw [hy, hgx0, hg]
    group
  have hx : m (g⁻¹ • x0) - m x0 =
      Multiplicative.toAdd (φ ⟨(x0.out)⁻¹ * g * (g⁻¹ • x0).out, sec_mem H g x0⟩) -
        Multiplicative.toAdd (ψ ⟨(x0.out)⁻¹ * g * (g⁻¹ • x0).out, sec_mem H g x0⟩) :=
    congrFun (congrFun hm g) x0
  rw [hel _ rfl, hgx0, sub_self] at hx
  have hx' : (0 : ZMod n) = Multiplicative.toAdd (φ h0) - Multiplicative.toAdd (ψ h0) := hx
  have h2 : Multiplicative.toAdd (φ h0) = Multiplicative.toAdd (ψ h0) :=
    (sub_eq_zero (G := ZMod n)).mp hx'.symm
  exact Multiplicative.toAdd.injective h2

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.phiGS :
    GlobalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), PhiCond V.frame.Γ l := by
  intro hGF l _ L Ω _ _ _ _ _ _ s V
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Plc (Lp L)), (S : Set (Plc (Lp L))) = V.S' :=
    ⟨V.fin.toFinset, V.fin.coe_toFinset⟩
  show PhiCond (ReciprocityTheory.Gal.GS Ω V.S') l
  rw [← hS]
  have key : PhiCond (ReciprocityTheory.Gal.GS Ω (S : Set (Plc (Lp L)))) (l ^ 1) := by
    apply phi_condition_of_finite_cohomology
    intro M _ _ _ _ _ ρ hρ
    have habove : ReciprocityTheory.Gal.ContainsAbove S l := by
      intro v hv
      have hv' : v ∈ V.S' := V.sub (Or.inl hv)
      rw [← hS] at hv'
      exact_mod_cast hv'
    exact (hGF (Lp L) Ω l 1 M S ρ one_pos habove hρ).2.1
  rw [pow_one] at key
  exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PLNormal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ProkerPL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prokerPL :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (I : Type) [Group I] [TopologicalSpace I] [IsTopologicalGroup I] (f : I →* Γ) (H : Subgroup Γ), Continuous f → (∀ g, f g ∈ H) → ∀ g ∈ GlobalTheory.TameQuot.proKer l I, f g ∈ PL l H := by
  intro l _ Γ _ _ _ _ _ I _ _ _ f H hf hfH g hg
  unfold PL
  simp only [Subgroup.mem_iInf]
  intro U hU
  let φ : I →* Γ ⧸ U.toSubgroup := (QuotientGroup.mk' U.toSubgroup).comp f
  haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hp : IsPGroup l φ.range := by
    rintro ⟨y, x, rfl⟩
    obtain ⟨e, he⟩ := hU (f x) (hfH x)
    refine ⟨e, Subtype.ext ?_⟩
    show φ x ^ l ^ e = 1
    rw [← map_pow]
    show (QuotientGroup.mk (f (x ^ l ^ e)) : Γ ⧸ U.toSubgroup) = 1
    rw [QuotientGroup.eq_one_iff, map_pow]
    exact he
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hker : φ.ker = U.toSubgroup.comap f := by
    ext x
    simp [φ, QuotientGroup.eq_one_iff]
  have hopen : IsOpen (φ.ker : Set I) := by
    rw [hker]
    exact U.isOpen.preimage hf
  have h2 := GlobalTheory.TameQuot.mem_proKer.1 hg φ.ker inferInstance hopen
    ⟨n, by rw [Subgroup.index_ker, hn]⟩
  rw [hker] at h2
  exact h2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open scoped Pointwise in
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ t ∈ Ine (F := k) B, g⁻¹ * t * g ∈ Ine (F := k) A := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have hm : ∀ x, g x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hv : ∀ x, B.valuation (g x) < 1 ↔ A.valuation x < 1 := fun x => by
    rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hm, ← map_inv₀, hm,
      map_eq_zero_iff _ g.injective]
  refine ⟨g, fun t ht => ⟨?_, fun x hx => ?_⟩⟩
  · show (g⁻¹ * t * g) • A = A
    have h1 : t • B = B := ht.1
    rw [mul_smul, mul_smul, hg, h1, ← hg, inv_smul_smul]
  · rw [← hv, map_sub]
    have e : g ((g⁻¹ * t * g) x) = t (g x) := mul_inv_apply _
    rw [e]
    exact ht.2 _ ((B.valuation_le_one_iff _).2 ((hm x).2 ((A.valuation_le_one_iff _).1 hx)))

open scoped Pointwise in
private theorem res_ine {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (g : G L Ω) : resP L Ω g ∈ Ine (F := Lp L) A ↔ g ∈ Ine (F := L) A := Iff.rfl

private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (HeightOneSpectrum (𝓞 k))} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

private theorem PL_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) : (PL l H).Normal := by
  refine ⟨fun x hx g => ?_⟩
  unfold PL at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro U hU
  exact U.isNormal'.conj_mem _ (hx U hU) g

theorem UpperTheory.V.Pa.kerLe :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (h : (globOf r V).Hom (globOf r V0)) (H : Subgroup (globOf r V0).Γ) (q : ℕ) (v : Fin q → Plc (Lp L)) (B : Fin q → ValuationSubring Ω) (τ : Fin q → G L Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → V.S' = V0.S' ∪ Set.range v → (∀ j, v j ∉ V0.S' ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ GlobalTheory.TameQuot.IsProGen L (B j) l (τ j)) → (∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1) ∧ (∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l, ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p)) ∧ h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ)) ⊔ PL l (H.comap h.p)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ n r h H q v B τ hp hS hj
  have h1 : ∀ j, ∀ g ∈ Ine (F := L) (B j), h.p (V.pr g : GS Ω V.S') = 1 := fun j g hg =>
    (hp (resP L Ω g)).trans (ine_NS (hj j).1 (hj j).2.1 ((res_ine _ _).2 hg))
  let π : G (Lp L) Ω →* (globOf r V).Γ := toGS Ω V.S'
  have hπ : Continuous π := continuous_toGS Ω V.S'
  have h2 : ∀ j, ∀ g ∈ GlobalTheory.TameQuot.ineKer L (B j) l,
      ((V.pr g : GS Ω V.S') : (globOf r V).Γ) ∈ PL l (H.comap h.p) := by
    rintro j _ ⟨g, hg, rfl⟩
    refine prokerPL l (globOf r V).Γ (Ine (F := L) (B j))
      (π.comp ((resP L Ω).comp (Ine (F := L) (B j)).subtype)) (H.comap h.p)
      (hπ.comp (continuous_resP.comp continuous_subtype_val)) (fun x => ?_) g hg
    have : h.p (π (resP L Ω x)) = 1 := h1 j x x.2
    show h.p (π (resP L Ω x)) ∈ H
    rw [this]
    exact H.one_mem
  refine ⟨h1, h2, ?_⟩
  haveI := PL_normal l (H.comap h.p)
  set N : Subgroup (globOf r V).Γ := Subgroup.normalClosure (Set.range fun j => ((V.pr (τ j) : GS Ω V.S') : (globOf r V).Γ))
    ⊔ PL l (H.comap h.p) with hN
  haveI : N.Normal := by rw [hN]; infer_instance
  haveI hK : N.topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hc : IsClosed ((N.topologicalClosure.comap π : Subgroup (G (Lp L) Ω)) : Set (G (Lp L) Ω)) :=
    (Subgroup.isClosed_topologicalClosure N).preimage hπ
  have h3 : ∀ j, ∀ g ∈ Ine (F := L) (B j), π (resP L Ω g) ∈ N.topologicalClosure := fun j g hg => by
    have hc' : IsClosed (((N.topologicalClosure.comap π).comap (resP L Ω) : Subgroup (G L Ω)) : Set (G L Ω)) :=
      hc.preimage continuous_resP
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hc' ((hj j).2.2.2.2 hg)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.le_topologicalClosure N
        ((le_sup_left : _ ≤ N) (Subgroup.subset_normalClosure ⟨j, rfl⟩))
    · intro x hx
      exact Subgroup.le_topologicalClosure N ((le_sup_right : _ ≤ N) (h2 j x hx))
  have h4 : NS Ω V0.S' ≤ N.topologicalClosure.comap π := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨u, hu, A, hA, ht⟩ := ht
    by_cases hu' : u ∈ V.S'
    · rw [hS] at hu'
      obtain ⟨j, rfl⟩ := hu'.resolve_left hu
      obtain ⟨g, hg⟩ := conj_ine (hj j).2.1 hA
      have h5 := hg t ht
      obtain ⟨x, hx⟩ := (hj j).2.2.1 (Ine_le_Dec _ h5)
      have h6 : g⁻¹ * t * g ∈ N.topologicalClosure.comap π := by
        rw [← hx] at h5 ⊢
        exact h3 j x ((res_ine _ _).1 h5)
      have h7 := (hK.comap π).conj_mem _ h6 g
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at h7
    · have : π t = 1 := ine_NS hu' hA ht
      show π t ∈ N.topologicalClosure
      rw [this]
      exact one_mem _
  intro x hx
  obtain ⟨g, rfl⟩ : ∃ g, π g = x := QuotientGroup.mk_surjective x
  have h8 : toGS Ω V0.S' g = 1 := (hp g).symm.trans hx
  exact h4 ((QuotientGroup.eq_one_iff g).1 h8)
end
