module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite
public import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CountableCompactOpen
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Inj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

end GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank
end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HermRank
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.RankPolData
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.FinOrbit
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HermAbs
noncomputable section

namespace GlobalTheory.ThK.Dbl.Herm

open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem exists_rep (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] :
    ∃ T : U →ₗ[ℂ] Y, ∀ x, ∀ y ∈ Y, ⟪(T x : U), y⟫_ℂ = b x y := by
  have := FiniteDimensional.complete ℂ Y
  have ex : ∀ x, ∃ t : Y, ∀ y : Y, ⟪t, y⟫_ℂ = b x y := fun x =>
    ⟨(InnerProductSpace.toDual ℂ Y).symm (LinearMap.toContinuousLinearMap (b x ∘ₗ Y.subtype)), fun y => by simp⟩
  choose t ht using ex
  refine ⟨⟨⟨t, fun x x' => ext_inner_right ℂ fun y => ?_⟩, fun c x => ext_inner_right ℂ fun y => ?_⟩, fun x y hy => ht x ⟨y, hy⟩⟩
  · simp [inner_add_left, ht]
  · simp [inner_smul_left, ht]

def homsF {K : Type} [Group K] (κ : K →* Module.End ℂ U) (f : U) : Submodule ℂ (orb κ f →ₗ[ℂ] U) where
  carrier := {L | ∀ k x, L ⟨κ k x.1, span_orbit_stab κ f k _ x.2⟩ = κ k (L x)}
  add_mem' := fun {a b} ha hb k x => by simp [ha k x, hb k x]
  zero_mem' := fun k x => by simp
  smul_mem' := fun c a ha k x => by simp [ha k x]

theorem exists_eigen {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) {ι : Type} [Finite ι] (l : ι → U →ₗ[ℂ] ℂ)
    (hl : ∀ x, (∀ i k, l i (κ k x) = 0) → x = 0) (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (κ k x) (κ k y) = b x y)
    (f : U) (h0 : f ≠ 0) : ∃ (x : U) (c : ℂ), x ≠ 0 ∧ ∀ y, b x y = c * ⟪x, y⟫_ℂ := by
  have := hf f
  have : FiniteDimensional ℂ (homsF κ f) := by
    let ev : homsF κ f →ₗ[ℂ] (ι → Module.Dual ℂ (orb κ f)) :=
      LinearMap.pi fun i => (LinearMap.llcomp ℂ _ _ _ (l i)) ∘ₗ (homsF κ f).subtype
    refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun L hL => Subtype.ext (LinearMap.ext fun x => ?_))
    refine hl _ fun i k => ?_
    rw [← L.2 k x]
    exact LinearMap.congr_fun (congrFun hL i) _
  let Z : Submodule ℂ U := Submodule.map₂ (LinearMap.id : (orb κ f →ₗ[ℂ] U) →ₗ[ℂ] _) (homsF κ f) ⊤
  have fZ : FiniteDimensional ℂ Z := Module.Finite.iff_fg.2
    (Submodule.FG.map₂ _ (Module.Finite.iff_fg.1 inferInstance) (Module.Finite.fg_top))
  have mZ : ∀ L ∈ homsF κ f, ∀ x, L x ∈ Z := fun L hL x => Submodule.apply_mem_map₂ _ hL trivial
  have sZ : ∀ k, ∀ z ∈ Z, κ k z ∈ Z := fun k => show Z ≤ Z.comap (κ k) from
    Submodule.map₂_le.2 fun L hL x _ => by
      show κ k (L x) ∈ Z
      rw [← hL k x]; exact mZ L hL _
  have orth : ∀ y ∈ Zᗮ, ∀ z ∈ Z, b z y = 0 := fun y hy => by
    have := hf y
    have yZ : orb κ y ≤ Zᗮ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact orth_stab κ hi Z sZ k y hy)
    obtain ⟨T, hT⟩ := exists_rep b (orb κ y)
    have eq : ∀ k x, (T (κ k x) : U) = κ k (T x) := fun k x => by
      have : T (κ k x) = ⟨κ k (T x), span_orbit_stab κ y k _ (T x).2⟩ := ext_inner_right ℂ fun u => by
        have e : (u : U) = κ k (κ k⁻¹ u) := by rw [← Module.End.mul_apply, ← map_mul]; simp
        show ⟪(T (κ k x) : U), (u : U)⟫_ℂ = ⟪κ k (T x), (u : U)⟫_ℂ
        rw [hT _ _ u.2, e, hb, hi, hT _ _ (span_orbit_stab κ y k⁻¹ _ u.2)]
      rw [this]
    refine show Z ≤ LinearMap.ker (b.flip y) from Submodule.map₂_le.2 fun L hL x _ => ?_
    show b (L x) y = 0
    have h1 : (T (L x) : U) ∈ Z := mZ ((orb κ y).subtype ∘ₗ T ∘ₗ L) (fun k x => by
      show (T (L _) : U) = κ k (T (L x))
      rw [hL k x, eq]) x
    rw [← hT _ _ (mem_orb κ y)]
    exact hy _ h1
  obtain ⟨T, hT⟩ := exists_rep b Z
  have : Nontrivial Z := ⟨⟨f, mZ (orb κ f).subtype (fun _ _ => rfl) ⟨f, mem_orb κ f⟩⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T ∘ₗ Z.subtype)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨x, starRingEnd ℂ c, fun h => hx.2 (Subtype.ext h), fun y => ?_⟩
  have e : T x = c • x := hx.apply_eq_smul
  have hy := Z.sub_starProjection_mem_orthogonal y
  have e1 := orth _ hy x x.2
  have e2 := hy _ x.2
  rw [map_sub, sub_eq_zero] at e1
  rw [inner_sub_right, sub_eq_zero] at e2
  rw [e1, e2, ← hT _ _ (Z.starProjection_apply_mem y), e, Submodule.coe_smul, inner_smul_left]

end GlobalTheory.ThK.Dbl.Herm

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Herm

open scoped InnerProductSpace Cardinal
open PositivityTheory.ThKF.Abs Topology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P : Type} [AddCommGroup P] [Module ℂ P]

theorem fin_orbit [BaireSpace G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hu : Function.Injective u)
    (hc : ∀ x, Continuous (u x)) (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ P ≤ ℵ₀) (x : P) {C : Set G}
    (hC : IsCompact C) : ∃ V : Submodule ℂ P, FiniteDimensional ℂ V ∧ ∀ g ∈ C, ρ g x ∈ V := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ P
  have : Countable (Module.Basis.ofVectorSpaceIndex ℂ P) := Cardinal.mk_le_aleph0_iff.1 (b.mk_eq_rank''.trans_le hr)
  let V : Finset (Module.Basis.ofVectorSpaceIndex ℂ P) → Submodule ℂ P := fun t => Submodule.span ℂ (t.image b)
  have o : Continuous fun g => u (ρ g x) := continuous_pi fun h => by
    simp only [he]; exact (hc x).comp (continuous_const.mul continuous_id)
  obtain ⟨t, g₀, h₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun t => {g | ρ g x ∈ V t}) (fun t => by
      have : IsClosed ((V t).map u : Set (G → ℂ)) := Submodule.closed_of_finiteDimensional _
      convert this.preimage o using 1
      ext g
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => (hu e ▸ hy : ρ g x ∈ V t)⟩)
    (Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨(b.repr (ρ g x)).support, by
      simpa [V] using b.mem_span_repr_support (ρ g x)⟩)
  refine hC.induction_on ⟨⊥, inferInstance, by simp⟩ (fun s s' h ⟨W, h1, h2⟩ => ⟨W, h1, fun g hg => h2 g (h hg)⟩)
    (fun s s' ⟨W, h1, h2⟩ ⟨W', h1', h2'⟩ => ⟨W ⊔ W', inferInstance, fun g hg =>
      hg.elim (fun h => Submodule.mem_sup_left (h2 g h)) fun h => Submodule.mem_sup_right (h2' g h)⟩) fun k _ => ?_
  refine ⟨(fun g => g₀ * k⁻¹ * g) ⁻¹' {g | ρ g x ∈ V t}, mem_nhdsWithin_of_mem_nhds
    ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 h₀)),
    (V t).map (ρ (k * g₀⁻¹)), inferInstance, fun g hg => ⟨_, hg, ?_⟩⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem line [LocallyCompactSpace G] [T2Space G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hc : ∀ x, Continuous (u x))
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (hK' : IsCompact (K : Set G)) {Ω : Set G} (hΩ : IsCompact Ω)
    (cov : ∀ g, ∃ g' ∈ Ω, ∀ x, u x g = u x g') (b c : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (hb : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (hi : ∀ g x y, c (ρ g x) (ρ g y) = c x y)
    (hs : ∀ x y, starRingEnd ℂ (c y x) = c x y) (hp : ∀ x, 0 ≤ (c x x).re) (hd : ∀ x, c x x = 0 → u x = 0)
    (b1 : LinearMap.ker u ≤ b.ker) (b2 : LinearMap.ker u ≤ b.flip.ker) (c2 : LinearMap.ker u ≤ c.flip.ker)
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, b x y = lam * c x y := by
  by_cases h0 : ∀ x, u x = 0
  · exact ⟨0, fun x y => by rw [b1 (h0 x)]; simp⟩
  push Not at h0
  obtain ⟨f, hf⟩ := h0
  have c1 : LinearMap.ker u ≤ c.ker := fun x hx => LinearMap.ext fun y => by
    rw [← hs, show c y x = 0 from LinearMap.congr_fun (c2 hx) y]; simp
  have st : ∀ g, LinearMap.ker u ≤ (LinearMap.ker u).comap (ρ g) := fun g x hx => funext fun h => by
    rw [he, show u x = 0 from hx]; rfl
  let U := P ⧸ LinearMap.ker u
  let π : P →ₗ[ℂ] U := (LinearMap.ker u).mkQ
  have sj : ∀ z : U, ∃ x, π x = z := (LinearMap.ker u).mkQ_surjective
  let b' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ b b1 b2
  let c' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ c c1 c2
  let ρ' : G →* Module.End ℂ U :=
    { toFun := fun g => Submodule.mapQ _ _ (ρ g) (st g)
      map_one' := LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp)
      map_mul' := fun g h => LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp) }
  let u' : U →ₗ[ℂ] (G → ℂ) := (LinearMap.ker u).liftQ u le_rfl
  have iu : Function.Injective u' := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  let core : InnerProductSpace.Core ℂ U :=
    { inner := fun x y => c' x y
      conj_inner_symm := fun z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hs x y
      re_inner_nonneg := fun z => by obtain ⟨x, rfl⟩ := sj z; exact hp x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun z hz => by obtain ⟨x, rfl⟩ := sj z; exact (Submodule.Quotient.mk_eq_zero _).2 (hd x hz) }
  letI : NormedAddCommGroup U := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ U := InnerProductSpace.ofCore core.toCore
  obtain ⟨t, -, ht⟩ := hΩ.elim_nhds_subcover (fun g => (fun h => g⁻¹ * h) ⁻¹' K) fun g _ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (hK.mem_nhds (by simpa using K.one_mem))
  obtain ⟨z, lam, hz, e⟩ := exists_eigen (U := U) (ρ'.comp K.subtype)
    (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hi k x y)
    (fun z => by
      obtain ⟨V, h1, h2⟩ := fin_orbit ρ' u' iu (fun z => by obtain ⟨x, rfl⟩ := sj z; exact hc x)
        (fun g z h => by obtain ⟨x, rfl⟩ := sj z; exact he g x h) (u.quotKerEquivRange.rank_eq.trans_le hr) z hK'
      exact Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k k.2)))
    (fun i : t => LinearMap.proj i.1 ∘ₗ u')
    (fun z hz => by
      obtain ⟨x, rfl⟩ := sj z
      refine (Submodule.Quotient.mk_eq_zero _).2 (funext fun g => ?_)
      obtain ⟨g', h1, h2⟩ := cov g
      obtain ⟨i, hi, h3⟩ := Set.mem_iUnion₂.1 (ht h1)
      have : u (ρ (i⁻¹ * g') x) i = 0 := hz ⟨i, hi⟩ ⟨_, h3⟩
      rwa [he, mul_inv_cancel_left, ← h2] at this)
    b' (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hb k x y) (π f)
    (fun h => hf ((Submodule.Quotient.mk_eq_zero _).1 h))
  obtain ⟨x₀, rfl⟩ := sj z
  let N : Submodule ℂ P := LinearMap.ker (b - lam • c)
  have mN : ∀ x, x ∈ N ↔ ∀ y, b x y = lam * c x y := fun x => by
    simp [N, LinearMap.ext_iff, sub_eq_zero]
  refine (irr N (fun x hx => (mN x).2 fun y => ?_) fun g x hx => (mN _).2 fun y => ?_).elim
    (fun h => absurd ((Submodule.Quotient.mk_eq_zero _).2 (h ((mN x₀).2 fun y => e (π y)))) hz)
    fun h => ⟨lam, fun x => (mN x).1 (h ▸ trivial)⟩
  · rw [b1 hx, c1 hx]; simp
  · rw [show y = ρ g (ρ g⁻¹ y) by rw [← Module.End.mul_apply, ← map_mul]; simp, hb, hi, (mN x).1 hx]

end GlobalTheory.ThK.Dbl.Herm

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Cardinal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def CptOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∃ K : Subgroup (UA σ Y.J), IsOpen (K : Set (UA σ Y.J)) ∧ IsCompact (K : Set (UA σ Y.J))

def PolRank : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀

namespace Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

theorem rank_polData (hM : M.IsGood B.ψ) (h : Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀) : Module.rank ℂ (PolData B M) ≤ ℵ₀ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let p : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → Af F) → ℂ) →ₗ[ℂ] Fn F n d :=
    LinearMap.mk₂ ℂ (fun f g => pureA F f g) (fun _ _ _ => funext fun _ => add_mul _ _ _)
      (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
      (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)
  have le : PolData B M ≤ Submodule.map₂ p (M.Pol B.ψ B.emb) (SB _) := Submodule.span_le.2 (by
    rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    exact e f ▸ Submodule.apply_mem_map₂ p hf hg)
  refine (Submodule.rank_mono le).trans ?_
  rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  refine (LinearMap.rank_le_domain _).trans ?_
  rw [rank_tensorProduct']
  exact (mul_le_mul' h (GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank.rank_SB_le _)).trans Cardinal.aleph0_mul_aleph0.le

def Il {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' om) (hc : ∀ Φ ∈ schA F _, M.Conv om Φ) :
    schA F (Fin n × Fin d) →ₗ[ℂ] (UA σ W.J → ℂ) where
  toFun Φ := M.I om Φ
  map_add' Φ Ψ := funext (PositivityTheory.ThKG.I_add hw hc Φ.2 Ψ.2)
  map_smul' c Φ := funext (PositivityTheory.ThKG.I_smul M om c Φ)

theorem I_rt (Φ : Fn F n d) (g h : UA σ W.J) : M.I om (om (1, g) Φ) h = M.I om Φ (h * g) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem exists_form {J : Matrix (Fin n) (Fin n) E} (c : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u u' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (hc : ∀ x, Continuous (u x)) (hc' : ∀ x, Continuous (u' x)) (hi : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u x (γ * g) = u x g)
    (hi' : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u' x (γ * g) = u' x g) (ρ : UA σ J →* Module.End ℂ P)
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (he' : ∀ g x h, u' (ρ g x) h = u' x (h * g)) :
    ∃ b : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ, (∀ x y, b x y = pet μ D (u y) (u' x)) ∧ ∀ g x y, b (ρ g x) (ρ g y) = b x y := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (c.fin _ _ hμ hD).ne
  have ii : ∀ x y, Integrable (fun g => u y g * star (u' x g)) (μ.restrict D) := fun x y => by
    have h := (hc y).mul (hc' x).star
    obtain ⟨C, hC⟩ := c.bdd h fun γ hγ g => by simp only [Pi.mul_apply, Pi.star_apply, hi y γ hγ, hi' x γ hγ]
    exact Integrable.of_bound h.aestronglyMeasurable C (Eventually.of_forall hC)
  haveI := c.cnt
  haveI := c.right μ hμ
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => pet μ D (u y) (u' x))
    (fun x x' y => ?_) (fun a x y => ?_) (fun x y y' => ?_) (fun a x y => ?_), fun _ _ => rfl, fun g x y => ?_⟩
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x' y)]; simp [mul_add]
  · simp [pet, ← integral_const_mul, mul_left_comm]
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x y')]; simp [add_mul]
  · simp [pet, ← integral_const_mul, mul_assoc]
  · simp only [LinearMap.mk₂'ₛₗ_apply, pet, he, he']
    exact PositivityTheory.ThKF.L2.integral_right hD (fun h => u y h * star (u' x h)) (fun γ hγ h => by rw [hi y γ hγ, hi' x γ hγ]) g

theorem line_cpt {J : Matrix (Fin n) (Fin n) E} (cW : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u v v' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (ρ : UA σ J →* Module.End ℂ P) (H : ∀ w ∈ ({u, v, v'} : Set _), (∀ x, Continuous (w x)) ∧
      (∀ x, ∀ γ ∈ ratU σ J, ∀ g, w x (γ * g) = w x g) ∧ (∀ g x h, w (ρ g x) h = w x (h * g)) ∧ ∀ x, u x = 0 → w x = 0)
    (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀) (K : Subgroup (UA σ J)) (k1 : IsOpen (K : Set (UA σ J)))
    (k2 : IsCompact (K : Set (UA σ J)))
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, pet μ D (v x) (v' y) = lam * pet μ D (u x) (u y) := by
  obtain ⟨a1, a2, a3, a4⟩ := H u (by simp)
  obtain ⟨b1, b2, b3, b4⟩ := H v (by simp)
  obtain ⟨c1, c2, c3, c4⟩ := H v' (by simp)
  obtain ⟨b, eb, ib⟩ := exists_form cW hμ hD b1 c1 b2 c2 ρ b3 c3
  obtain ⟨c, ec, ic⟩ := exists_form cW hμ hD a1 a1 a2 a2 ρ a3 a3
  obtain ⟨Ω, hΩ, cov⟩ := cW.cov
  have := cW.lc
  have := cW.t2
  obtain ⟨lam, hl⟩ := line ρ u a1 a3 hr K k1 k2 hΩ (fun g => (cov g).elim fun γ hγ => ⟨_, hγ.2, fun x => (a2 x γ hγ.1 g).symm⟩)
    b c ib ic (fun x y => by rw [ec, ec, pet, pet, ← integral_conj]; simp [mul_comm])
    (fun x => by
      rw [ec, pet, show (fun h => u x h * star (u x h)) = fun h => ((‖u x h‖ ^ 2 : ℝ) : ℂ) from
        funext fun h => by simp [Complex.mul_conj'], integral_complex_ofReal]
      exact integral_nonneg fun _ => by positivity)
    (fun x hx => cW.eq_zero hμ hD (a1 x) (a2 x) (ec x x ▸ hx))
    (fun x hx => LinearMap.ext fun y => by rw [eb, c4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, eb, b4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, ec, a4 x hx]; simp [pet]) irr
  exact ⟨lam, fun x y => by rw [← eb, ← ec, hl]⟩

end Herm

open Herm in
theorem hermLine_of (hC : CptAll) (hK : CptOpen) (hR : PolRank) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t s' t'
  have T := h.triple
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨K, k1, k2⟩ := hK F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨-, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  obtain ⟨st1, st2⟩ := hS F E σ B a a' G X om om' R Rf h hp hq
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf h
  have z0 : (0 : Fn F a (a + a') × Fn F a' (a + a')) ∈ pairs B G X R Rf :=
    ⟨zero_mem _, X.T, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  let P : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) :=
    { carrier := pairs B G X R Rf
      zero_mem' := z0
      add_mem' := fun hx hy => by simpa using st1 _ hx _ hy 1
      smul_mem' := fun c x hx => by simpa using st1 _ z0 _ hx c }
  have s1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM (m3 _ _ y.2.1 y.2.2).1
  have s2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM' (m3 _ _ y.2.1 y.2.2).2.1
  let I₁ := Il T.weil fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) (Or.inr (by omega))).1 Φ hΦ).1
  let I₂ := Il T.weil' fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) (Or.inr (by omega))).1 Φ hΦ).1
  let j₂ := (LinearMap.snd ℂ _ _ ∘ₗ P.subtype).codRestrict _ s2
  let io : ℂ → ℂ → P →ₗ[ℂ] (UA σ G.W.J → ℂ) := fun s t =>
    s • I₁ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ P.subtype).codRestrict _ s1 + t • I₂ ∘ₗ j₂
  have eio : ∀ s t y, io s t y = comb G om om' s t y.1 := fun _ _ _ => rfl
  have e01 : ∀ y, io 0 1 y = G.M'.I om' y.1.2 := fun y => by simp [eio, comb]
  let ρ : UA σ G.W.J →* Module.End ℂ P :=
    { toFun := fun g => ((om (1, g)).prodMap (om' (1, g))).restrict fun y hy => st2 y hy g
      map_one' := LinearMap.ext fun y => Subtype.ext (show (om 1 y.1.1, om' 1 y.1.2) = y.1 by simp)
      map_mul' := fun g g' => LinearMap.ext fun y => Subtype.ext
        (show (om (1, g * g') y.1.1, om' (1, g * g') y.1.2) = (om (1, g) (om (1, g') y.1.1), om' (1, g) (om' (1, g') y.1.2)) by
          simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]) }
  have he : ∀ s t g y x, io s t (ρ g y) x = io s t y (x * g) := fun s t g y x =>
    show s * G.M.I om (om (1, g) y.1.1) x + t * G.M'.I om' (om' (1, g) y.1.2) x = _ by rw [I_rt, I_rt]; rfl
  have cc : ∀ s t y, Continuous (io s t y) := fun s t y =>
    (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega)) _ (s1 y)).const_smul s).add
      (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega)) _ (s2 y)).const_smul t)
  have ci : ∀ s t y, ∀ γ ∈ ratU σ G.W.J, ∀ g, io s t y (γ * g) = io s t y g := fun s t y γ hγ g => by
    have b1 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 _ (s1 y)).2.1 1 (one_mem _) γ hγ
    have b2 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 _ (s2 y)).2.1 1 (one_mem _) γ hγ
    simp only [one_mul] at b1 b2
    simp only [eio, comb, Pi.add_apply, Pi.smul_apply, Model.I, b1, b2]
  have nul : ∀ s t (y : P), PolMatch B G X R Rf y.1.1 0 → io s t y = 0 := fun s t y hy => by
    have := st1 _ y.2 (y.1.1, 0) ⟨zero_mem _, hy⟩ (-1)
    rw [show y.1 + (-1 : ℂ) • (y.1.1, 0) = (0, y.1.2) by ext <;> simp] at this
    rw [eio, comb, f1 _ hy, f2 _ y.2.1 this.2]; simp
  have irr : ∀ N : Submodule ℂ P, LinearMap.ker (io 0 1) ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) →
      (∀ y ∈ N, PolMatch B G X R Rf y.1.1 0) ∨ N = ⊤ := fun N h1 h2 =>
    (hJ F E σ B a a' G X om om' R Rf h hp hq (N.map P.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      (fun y hy h0 => ⟨⟨y, hy⟩, h1 (nul 0 1 ⟨y, hy⟩ h0), rfl⟩) (by rintro _ ⟨y, hy, rfl⟩ g; exact ⟨_, h2 g y hy, rfl⟩)).imp
      (fun h y hy => h _ ⟨y, hy, rfl⟩) fun h => eq_top_iff.2 fun y _ => by
        obtain ⟨z, hz, e⟩ := h y.2
        exact (Subtype.ext e : z = y) ▸ hz
  have ker : ∀ s t y, io 0 1 y = 0 → io s t y = 0 := fun s t y hy => by
    refine (irr _ le_rfl fun g x hx => funext fun z => ?_).elim (fun h => nul s t y (h y hy)) fun h0 => ?_
    · rw [he, show io 0 1 x = 0 from hx]; rfl
    · obtain ⟨Φ', r1, r2⟩ := (hN F E σ B a a' G X om om' T).2 hq
      obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
      exact absurd ((e01 ⟨(Φ, Φ'), r1.2, hΦ⟩).symm.trans (h0.ge trivial)) r2
  have le : LinearMap.range (io 0 1) ≤ ((PolData B G.M').comap (schA F _).subtype).map I₂ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨j₂ y, (m3 _ _ y.2.1 y.2.2).2.1, (e01 y).symm⟩
  obtain ⟨lam, hl⟩ := line_cpt cW hμ hD (u := io 0 1) (v := io s t) (v' := io s' t') ρ
    (by rintro _ (rfl | rfl | rfl) <;> exact ⟨cc _ _, ci _ _, he _ _, ker _ _⟩)
    ((Submodule.rank_mono le).trans ((rank_map_le _ _).trans
      ((Submodule.comapSubtypeEquivOfLe (PositivityTheory.ThKG.polData_le T.geo.hM')).rank_eq.trans_le
        (rank_polData T.geo.hM' (hR F E σ B _ _ _ _ _ _ _ _ _ T.base T.geo.hV' T.geo.hW))))) K k1 k2
    fun N h1 h2 => (irr N h1 h2).imp_left fun h y hy => nul 0 1 y (h y hy)
  exact ⟨lam, fun y hy y' hy' => hl ⟨y, hy⟩ ⟨y', hy'⟩⟩

end GlobalTheory.ThK.Dbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Cardinal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele _root_.GlobalTheory.ThK.Dbl.Dense

namespace Herm

theorem ode_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (h0 : f 0 = 0) (x : V) (c : ℂ)
    (h : ∀ t : ℝ, fderiv ℝ f (t • x) x = t * c * f (t • x)) : f x = 0 := by
  have d : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) * t * c / 2))) 0 t := fun t => by
    have h1 := (f.hasFDerivAt (t • x)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    refine (h1.mul (((h2.mul h2).mul_const c).div_const 2).neg.cexp).congr_deriv ?_
    simp only [one_smul, h, Function.comp, id, Pi.neg_apply, Pi.mul_apply]
    ring
  have := is_const_of_deriv_eq_zero (fun t => (d t).differentiableAt) (fun t => (d t).deriv) 1 0
  simpa [h0] using this

theorem exists_stable {M ι : Type} [AddCommGroup M] [Module ℂ M] [Countable ι] (D : ι → Module.End ℂ M) (G : Submodule ℂ M)
    [FiniteDimensional ℂ G] : ∃ N : Submodule ℂ M, G ≤ N ∧ Module.rank ℂ N ≤ ℵ₀ ∧ ∀ i, ∀ x ∈ N, D i x ∈ N := by
  obtain ⟨s, rfl⟩ := Module.Finite.iff_fg.1 ‹_›
  refine ⟨Submodule.span ℂ (Set.range fun z : List ι × s => (z.1.map D).prod z.2),
    Submodule.span_mono fun x hx => ⟨([], ⟨x, hx⟩), rfl⟩,
    (rank_span_le _).trans (Cardinal.mk_range_le.trans Cardinal.mk_le_aleph0), fun i => ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem _ h => obtain ⟨⟨l, x⟩, rfl⟩ := h; exact Submodule.subset_span ⟨(i :: l, x), by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {X : Spc F E n} {W : Spc F E d} {κ : Type} [Fintype κ]

def dL (p : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : Module.End ℂ (SInf F κ) where
  toFun := dOp p.1 p.2
  map_add' f g := by simp only [dOp, LineDeriv.lineDerivOp_add, map_add (f := _), smul_add]; abel
  map_smul' c f := by
    rw [dOp, dOp, LineDeriv.lineDerivOp_smul, smul_add, RingHom.id_apply]
    congr 1
    ext y
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply (Dense.linForm p.2).hasTemperateGrowth, smul_eq_mul,
      Complex.real_smul]
    ring

theorem dL_apply (p) (f : SInf F κ) (y) :
    dL p f y = fderiv ℝ f y p.1 + (-(2 * Real.pi * Complex.I)) * ((tr κ y p.2 : ℝ) : ℂ) * f y := dOp_apply _ _ _ _

theorem actsD_dL (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (dL (fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) f) := fun r hr x => by
  have hab : ∀ t, evI F t = 0 → t • M.co.e u = 0 := fun t ht => by rw [← map_smul, hu t ht, map_zero]
  simp only [Model.heisLine, Darboux.rho, map_smul]
  exact hasDerivAt_dOp ψ hψ _ _ (fun t ht => congrArg Prod.fst (hab t ht)) (fun t ht => congrArg Prod.snd (hab t ht)) f r hr x

theorem exists_vac (M : Model σ X W) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (ε : InfinitePlace F → ℤˣ) : ∃ G : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ G ∧ ∀ f₀ : SInf F (Fin n × Fin d),
      (∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ∀ f f' : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f₀ f → ActsD (evI F) (M.heisLine B.ψ u') f₀ f' →
          f' = Complex.I • f) → f₀ ∈ G := by
  have h := hB.cm
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure σ h B.emb M.co.e fun w => ((ε w : ℤ) : ℝ) • cs (X.θ w) (W.θ w)
  have hA : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← h.2.2.2, hX.herm]
  have hC : ∀ w, (Complex.I • W.J.map (B.emb w).1)ᴴ = Complex.I • W.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2, hW.skew]
    simp
  have sj : Function.Surjective (LinearMap.fst ℝ _ _ ∘ₗ J ∘ₗ LinearMap.inr ℝ _ _) := by
    refine LinearMap.injective_iff_surjective.1 ((injective_iff_map_eq_zero _).2 fun b hb => ?_)
    have hb : (J (0, b)).1 = 0 := hb
    let e : AF F := (fun w => ((ε w : ℤ) : w.Completion), 0)
    have he : ∀ w, (e • S (0, b)).map (piInf (B.emb w)) = ((ε w : ℤ) : ℝ) • (S (0, b)).map (piInf (B.emb w)) := fun w => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def, map_mul, show algebraMap (AF F) (AE F E) e = e ⊗ₜ 1 from rfl, piInf_tmul]
      simp [e]
    have es : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b =>
      map_sub (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    have t := trace_symp (X := X) (W := W) h B.emb (e • S (0, b)) (S (J (0, b)))
    rw [M.co.form, es, map_smul] at t
    simp only [dotProduct, evI_sum, evI_mul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, congrFun (sev _).1, hb, Pi.zero_apply,
      mul_zero, zero_mul, Finset.sum_const_zero, sub_zero, map_zero, he, sJ] at t
    have q : ∀ w x, hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (((ε w : ℤ) : ℝ) • x) ((((ε w : ℤ) : ℝ) • cs (X.θ w) (W.θ w)) x) =
        hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) x (cs (X.θ w) (W.θ w) x) := fun w x => by
      rcases Int.units_eq_one_or (ε w) with h | h <;> simp [h, hf, Matrix.map_neg]
    simp only [q] at t
    have nn : ∀ w, 0 ≤ -(2 * (hf (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((S (0, b)).map (piInf (B.emb w)))
        (cs (X.θ w) (W.θ w) ((S (0, b)).map (piInf (B.emb w))))).re) := fun w => by
      by_cases hv : (S (0, b)).map (piInf (B.emb w)) = 0
      · simp [hv, hf]
      · linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) hv]
    have z : S (0, b) = 0 := eq_of_piInf h B.emb (sAt _) (fun c _ => smul_zero c) fun w => by
      by_contra hv
      have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => nn w).1 t.symm w (Finset.mem_univ _)
      linarith [hf_neg (hA w) (hC w) (hX.cartan w) (hW.cartan w) (x := (S (0, b)).map (piInf (B.emb w))) (by simpa using hv)]
    have := (sev (0, b)).2
    rw [z, map_zero] at this
    exact this.symm.trans (funext fun _ => evI_zero)
  refine ⟨⨅ p, LinearMap.ker (dL (J p) - Complex.I • dL p), ?_, fun f₀ H => (Submodule.mem_iInf _).2 fun p => ?_⟩
  · let ev : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ := ⟨⟨fun f => f 0, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    refine Module.Finite.of_injective (ev ∘ₗ Submodule.subtype _) ((injective_iff_map_eq_zero _).2 fun f hf => ?_)
    ext x
    obtain ⟨b, hb⟩ := sj x
    have hb : (J (0, b)).1 = x := hb
    refine ode_zero f.1 hf x (2 * Real.pi * Complex.I * (tr _ x (J (0, b)).2 - Complex.I * tr _ x b)) fun t => ?_
    have : dL (J (0, b)) f.1 (t • x) - Complex.I * dL (0, b) f.1 (t • x) = 0 :=
      DFunLike.congr_fun (show (dL (J (0, b)) - Complex.I • dL (0, b)) f.1 = 0 from (Submodule.mem_iInf _).1 f.2 (0, b)) (t • x)
    simp only [dL_apply, hb, map_zero, map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul] at this
    linear_combination this
  · have := H _ _ (sAt p) (sAt (J p)) (fun w => by rw [sJ]; ext i j; simp [cs, mul_assoc]) _ _
      (actsD_dL M hB.std (sAt p) f₀) (actsD_dL M hB.std (sAt (J p)) f₀)
    rw [(sev p).1, (sev p).2, (sev _).1, (sev _).2] at this
    exact sub_eq_zero.2 this

end Herm

open Herm in
theorem polRank : PolRank := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW
  choose G h1 h2 using exists_vac M hB hX hW
  let b := Module.finBasis ℝ ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
  obtain ⟨N, n1, n2, n3⟩ := exists_stable (fun i => dL (b i)) (⨆ ε, G ε)
  have all : ∀ p, ∀ f ∈ N, dL p f ∈ N := fun p f hf => by
    induction b.mem_span p using Submodule.span_induction with
    | mem p h => obtain ⟨i, rfl⟩ := h; exact n3 i f hf
    | zero => convert N.zero_mem; ext y; simp [dL_apply]
    | add p q _ _ hp hq => convert N.add_mem hp hq; ext y; simp [dL_apply]; ring
    | smul t p _ hp => convert N.smul_mem (t : ℂ) hp; ext y; simp [dL_apply]; ring
  refine (Submodule.rank_mono (show M.Pol B.ψ B.emb ≤ N from sInf_le ?_)).trans n2
  refine ⟨fun f₀ ⟨ε, H⟩ => n1 (Submodule.mem_iSup_of_mem ε (h2 ε f₀ H)), fun u hu f hf f₁ H => ?_⟩
  rw [actsD_unique M hB.std hu H]
  exact all (_, _) f hf

end GlobalTheory.ThK.Dbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele Dense PositivityTheory.ThKF
open PositivityTheory.ThK (kc_ring adele_t2Space kc_smul kc_closedU kc_cont_mat isCompact_of_units)
open GlobalTheory.CompanionTheory.SW.Core (Oh)

attribute [local instance] kc_ring adele_t2Space kc_smul

namespace Herm

theorem map_star_mul' {a b c : Type} [Fintype b] (x : Matrix a b ℂ) (y : Matrix b c ℂ) :
    (x * y).map star = x.map star * y.map star := Matrix.map_mul (f := starRingEnd ℂ)

theorem cpt_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) :
    ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g, gᵀ * M * g.map star = M → g ∈ C := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨ε, e1, e2⟩ : ∃ ε : ℂ, ε * ε = 1 ∧ Aᵀ * M * A.map star = ε • 1 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · refine ⟨-1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | (simp only [Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, neg_smul, one_smul, Matrix.one_apply, Sum.inr.injEq])
    · refine ⟨1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [Matrix.one_apply]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Aᵀ * N = (1 : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) := ⟨ε • (M * A.map star), by rw [Matrix.mul_smul, ← Matrix.mul_assoc, e2, smul_smul, e1, one_smul]⟩
  have hN' : N * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 hN
  have h1 : A * Nᵀ = 1 := by simpa using congrArg Matrix.transpose hN'
  have h2 : A.map star * Nᵀ.map star = 1 := by rw [← map_star_mul', h1]; simp
  refine ⟨(fun u : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => A * u * Nᵀ) '' Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall 0 1,
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const), fun g hg =>
    ⟨Nᵀ * g * A, fun k _ i _ => ?_, by
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]⟩⟩
  have e3 : N * Nᵀ.map star = ε • M := by
    have : N * (Aᵀ * M * A.map star) * Nᵀ.map star = M := by
      simp only [← Matrix.mul_assoc, hN', Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← this, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e1, one_smul, Matrix.mul_one]
  have e4 : (Nᵀ * g * A)ᵀ * (Nᵀ * g * A).map star = 1 := by
    calc _ = Aᵀ * (gᵀ * (N * Nᵀ.map star) * g.map star) * A.map star := by
          simp only [map_star_mul', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.mul_smul, Matrix.smul_mul, hg, Matrix.mul_smul, Matrix.smul_mul, e2, smul_smul, e1, one_smul]
  generalize Nᵀ * g * A = u at e4
  have e5 : ∑ l, ‖u l i‖ ^ 2 = 1 := by
    have := congrFun (congrFun e4 i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq, Complex.star_def,
      Complex.mul_conj'] at this
    exact_mod_cast this
  rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← e5]
  exact Finset.single_le_sum (f := fun l => ‖u l i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}


variable (F) in
def fA : Af F →+ AF F := AddMonoidHom.inr (Ainf F) (Af F)

theorem fA_mul (x : Af F) (a : AF F) : fA F x * a = fA F (x * a.2) := Prod.ext (zero_mul _) rfl

theorem cont_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (Continuous.comp (g := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) (continuous_pi fun v => ?_)
    (continuous_algebraMap ℝ _)) continuous_const
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem exists_arch_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ T : (InfinitePlace F → ℂ) → AE F E, Continuous T ∧ ∀ a, a = T (fun w => piInf (τ w) a) + fA F 1 • a := by
  choose x x1 x2 using GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ
  have sm : ∀ w (t : AF F) (a : AE F E), piInf (τ w) (t • a) =
      InfinitePlace.Completion.extensionEmbedding w (evInf F w t) * piInf (τ w) a := fun w t a => by
    rw [Algebra.smul_def, map_mul, PositivityTheory.ThKEst.LatArchPf.piInf_alg]
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x (Pi.single w 1) + realAd F (z w).im • x (Pi.single w Complex.I)),
    continuous_finsetSum _ fun w _ =>
      by have := cont_realAd (F := F); fun_prop, fun a => ?_⟩
  rw [← sub_eq_iff_eq_add, ← sub_eq_zero]
  refine eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_
  · have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hc
    have h2 : c * fA F 1 = c := Prod.ext ((mul_zero _).trans h1.symm) (mul_one _)
    have h3 : ∀ t z, c • realAd F t • x z = 0 := fun t z => by rw [smul_comm, x1 _ c hc, smul_zero]
    rw [smul_sub, smul_sub, smul_smul c, h2]
    simp only [sub_self, Finset.smul_sum, smul_add, h3, add_zero, Finset.sum_const_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sub, map_sum, map_add (f := _), sm, x2, PositivityTheory.ThKEst.LatArchPf.emb_realAd h.1]
      rw [show evInf F w (fA F 1) = 0 from rfl, Finset.sum_eq_single w (fun v _ hv => by simp [Pi.single_eq_of_ne hv.symm])
        (by simp)]
      simp


variable (F E) in
def lamF : AddSubgroup (AE F E) where
  carrier := (fun x : Ix E → Af F => ∑ i, fA F (x i) • bA F i) '' Set.univ.pi fun _ => Oh F
  zero_mem' := ⟨0, fun _ _ v => zero_mem _, Finset.sum_eq_zero fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x + y, fun i _ v => add_mem (hx i trivial v) (hy i trivial v), ?_⟩
    simp [Finset.sum_add_distrib, add_smul]
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨-x, fun i _ v => neg_mem (hx i trivial v), ?_⟩
    simp

theorem lamF_mul {a b : AE F E} (ha : a ∈ lamF F E) (hb : b ∈ lamF F E) : a * b ∈ lamF F E := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Finset.sum_mul_sum]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  obtain ⟨c, hc⟩ := bA_mul (F := F) i j
  rw [smul_mul_smul_comm, hc, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [smul_comm]
  refine zsmul_mem (⟨Pi.single k (x i * y j), fun l _ v => ?_, ?_⟩ : _ ∈ lamF F E) _
  · by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact mul_mem (hx i trivial v) (hy j trivial v)
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  · refine (Finset.sum_eq_single k (fun l _ h => by simp [Pi.single_eq_of_ne h]) (by simp)).trans ?_
    rw [Pi.single_eq_same, fA_mul]
    rfl

theorem lamF_cpt : IsCompact (lamF F E : Set (AE F E)) :=
  (isCompact_univ_pi fun _ => GlobalTheory.CompanionTheory.SW.Core.AfTop.isCompact_Oh F).image (continuous_finsetSum _ fun i _ =>
    Continuous.fun_smul (f := fun x : Ix E → Af F => fA F (x i)) (continuous_const.prodMk (continuous_apply i))
      continuous_const)

theorem lamF_nhds : ∀ᶠ a in 𝓝 (0 : AE F E), fA F 1 • a ∈ lamF F E := by
  obtain ⟨S, hS⟩ := exists_sectionC (F := F) (E := E)
  have hSc : Continuous S := IsModuleTopology.continuous_of_linearMap S
  have : ∀ᶠ a in 𝓝 (0 : AE F E), ∀ i, (S a i).2 ∈ Oh F := eventually_all.2 fun i =>
    (continuous_snd.comp ((continuous_apply i).comp hSc)).continuousAt.eventually_mem
      ((GlobalTheory.CompanionTheory.SW.Core.AfTop.isOpen_Oh F).mem_nhds (show (S 0 i).2 ∈ Oh F by rw [map_zero]; exact fun v => zero_mem _))
  refine this.mono fun a ha => ⟨fun i => (S a i).2, fun i _ => ha i, ?_⟩
  conv_rhs => rw [← hS a, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [smul_smul, fA_mul, one_mul]

def kInt (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) where
  carrier := {g | ∀ i j, fA F 1 • (mat g - 1) i j ∈ lamF F E ∧
    fA F 1 • (mat g⁻¹ - 1) i j ∈ lamF F E}
  one_mem' := fun i j => by simp [mat_one']
  mul_mem' := fun {g h} hg hh => by
    have key : ∀ A B : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, fA F 1 • (A - 1) i j ∈ lamF F E) →
        (∀ i j, fA F 1 • (B - 1) i j ∈ lamF F E) →
        ∀ i j, fA F 1 • (A * B - 1) i j ∈ lamF F E := fun A B hA hB i j => by
      have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
      have e2 : fA F 1 * fA F 1 = fA F 1 := Prod.ext (mul_zero _) (mul_one _)
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, smul_add, smul_add, Finset.smul_sum]
      refine add_mem (add_mem (sum_mem fun k _ => ?_) (hA i j)) (hB i j)
      rw [← e2, ← smul_mul_smul_comm]
      exact lamF_mul (hA i k) (hB k j)
    refine fun i j => ⟨key _ _ (fun i j => (hg i j).1) (fun i j => (hh i j).1) i j, ?_⟩
    rw [mul_inv_rev]
    exact key _ _ (fun i j => (hh i j).2) (fun i j => (hg i j).2) i j
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem kInt_open (J : Matrix (Fin n) (Fin n) E) : IsOpen (kInt σ J : Set (UA σ J)) := by
  have hm := kc_cont_mat (σ := σ) J
  refine (kInt σ J).isOpen_of_mem_nhds (g := 1) (show ∀ᶠ g in 𝓝 1, ∀ i j, _ from
    eventually_all.2 fun i => eventually_all.2 fun j => Eventually.and ?_ ?_)
  · exact (((hm.sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds
  · exact ((((hm.comp continuous_inv).sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds

end Herm

open Herm in
theorem cptOpen : CptOpen := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  refine ⟨kInt σ Y.J, kInt_open _, ?_⟩
  have : ∀ w, ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g : UA σ Y.J, (mat g).map (piInf (B.emb w)) ∈ C := fun w => by
    have e : ∀ g : UA σ Y.J, ((mat g).map (piInf (B.emb w)))ᵀ * Y.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star =
        Y.J.map (B.emb w).1 := fun g => by
      have := congrArg (·.map (piInf (B.emb w))) (show (mat g)ᵀ * incM F Y.J * (mat g).map (cA σ) = incM F Y.J from g.2)
      simp only [Matrix.map_mul, map_incM, Matrix.transpose_map] at this
      convert this using 2
      ext i j
      exact (piInf_cA hB.cm _ _).symm
    rcases hY with h | h
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (e g)⟩
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (by rw [Matrix.mul_smul, Matrix.smul_mul, e])⟩
  choose C h1 h2 using this
  obtain ⟨T, t1, t2⟩ := exists_arch_section hB.cm B.emb
  let f : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (AE F E) → Matrix (Fin n) (Fin n) (AE F E) :=
    fun p i j => T (fun w => p.1 w i j) + (p.2 i j + fA F 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
  have cf : Continuous f := continuous_matrix fun i j =>
    (t1.comp (continuous_pi fun w => ((continuous_apply w).comp continuous_fst).matrix_elem i j)).add
      ((continuous_snd.matrix_elem i j).add continuous_const)
  have key : ∀ g ∈ kInt σ Y.J, mat g ∈ f '' (Set.univ.pi C ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ => (lamF F E : Set _)) :=
    fun g hg => ⟨(fun w => (mat g).map (piInf (B.emb w)), fun i j => fA F 1 • (mat g - 1) i j),
      ⟨fun w _ => h2 w g, fun i _ j _ => (hg i j).1⟩, by
        ext i j
        simp only [f, Matrix.sub_apply, ← smul_add, sub_add_cancel, Matrix.map_apply]
        exact (t2 _).symm⟩
  exact isCompact_of_units _ (kc_closedU Y.J) _ ((kInt σ Y.J).isClosed_of_isOpen (kInt_open _)) _
    (((isCompact_univ_pi h1).prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => lamF_cpt)).image cf)
    fun k hk => ⟨key k hk, key k⁻¹ (inv_mem hk)⟩

theorem hermLine_of' (hC : CptAll) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine :=
  hermLine_of hC cptOpen polRank hS hJ hF hN hW hB hI hM

end GlobalTheory.ThK.Dbl

end
