module

public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferContinuousOfContinuousOn
namespace GlobalTheory

open scoped BigOperators

theorem transfer_continuous_of_continuousOn : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); ∀ f : G → X, ContinuousOn f H → Continuous (tr f) := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ hH hρ tr f hf
  show Continuous (fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)))
  refine continuous_finsetSum _ (fun q _ => ?_)
  refine continuous_iff_continuousAt.2 (fun g₀ => ?_)
  have hsmul : ∀ g : G, g • q = ((g * q.out : G) : G ⧸ H) := by
    intro g
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let ψ : G → G := fun g => (g * q.out)⁻¹ * (g₀ • q).out
  have hψc : Continuous ψ := by fun_prop
  let V : Set G := ψ ⁻¹' (H : Set G)
  have hVo : IsOpen V := hH.preimage hψc
  have key : ∀ g ∈ V, g • q = g₀ • q := by
    intro g hg
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g₀ • q).out : G ⧸ H) := QuotientGroup.eq.2 hg
    rw [hsmul g, h1, QuotientGroup.out_eq']
  have hg₀ : g₀ ∈ V := by
    show (g₀ * q.out)⁻¹ * (g₀ • q).out ∈ H
    apply QuotientGroup.eq.1
    rw [QuotientGroup.out_eq', hsmul]
  have hmem : ∀ g ∈ V, (g₀ • q).out⁻¹ * g * q.out ∈ H := by
    intro g hg
    have h1 := QuotientGroup.eq.1 (show (((g₀ • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) by
      rw [QuotientGroup.out_eq', ← hsmul g, key g hg])
    simpa [mul_assoc] using h1
  have hV : V ∈ nhds g₀ := hVo.mem_nhds hg₀
  have hc : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
    have hφ : Continuous (fun g : G => (g₀ • q).out⁻¹ * g * q.out) := by fun_prop
    have hw : ContinuousWithinAt (fun g => f ((g₀ • q).out⁻¹ * g * q.out)) V g₀ :=
      ContinuousWithinAt.comp (g := f) (f := fun g : G => (g₀ • q).out⁻¹ * g * q.out) (t := (H : Set G))
        (hf _ (hmem g₀ hg₀)) hφ.continuousWithinAt (fun g hg => hmem g hg)
    exact (hρ _).continuousAt.comp (hw.continuousAt hV)
  refine hc.congr ?_
  filter_upwards [hV] with g hg
  rw [key g hg]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCocycleFormula
namespace GlobalTheory

open QuotientGroup

theorem transfer_cocycle_formula :
    ∀ (R G X : Type) [CommRing R] [Group G] [AddCommGroup X] [Module R X]
      (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)],
      (fun tr : (G → X) → G → X =>
        (∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H) ∧
        (∀ f : G → X, (∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ρ a (f b)) →
          ∀ a b, tr f (a * b) = tr f a + ρ a (tr f b)) ∧
        (∀ (f : G → X) (x : X), (∀ h ∈ H, f h = ρ h x - x) →
          ∀ g, tr f g = ρ g (∑ q : G ⧸ H, ρ q.out x) - ∑ q : G ⧸ H, ρ q.out x) ∧
        (∀ f : G → X, (∀ a b, f (a * b) = f a + ρ a (f b)) →
          ∀ g, tr f g = H.index • f g +
            (ρ g (∑ q : G ⧸ H, f q.out) - ∑ q : G ⧸ H, f q.out)))
        (fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))) := by
  intro R G X _ _ _ _ ρ H _
  have mem : ∀ (g : G) (q : G ⧸ H), (g • q).out⁻¹ * g * q.out ∈ H := by
    intro g q
    have h1 : (((g • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rw [mul_assoc]
    exact QuotientGroup.eq.mp h1
  have reidx : ∀ (g : G) (F : G ⧸ H → X), ∑ q, F (g • q) = ∑ q, F q := fun g F =>
    Equiv.sum_comp (MulAction.toPerm g) F
  have rmul : ∀ (s t : G) (y : X), ρ s (ρ t y) = ρ (s * t) y := by
    intro s t y
    rw [map_mul, mul_apply_eq_comp]
  refine ⟨mem, ?_, ?_, ?_⟩
  · intro f hf a b
    have key : ∀ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
        = ρ (a • (b • q)).out (f ((a • (b • q)).out⁻¹ * a * (b • q).out))
          + ρ a (ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out))) := by
      intro q
      rw [mul_smul]
      have e : (a • b • q).out⁻¹ * (a * b) * q.out
          = ((a • b • q).out⁻¹ * a * (b • q).out) * ((b • q).out⁻¹ * b * q.out) := by group
      rw [e, hf _ (mem a (b • q)) _ (mem b q), map_add (f := _), rmul, rmul]
      congr 3
      group
    show ∑ q : G ⧸ H, ρ ((a * b) • q).out (f (((a * b) • q).out⁻¹ * (a * b) * q.out))
      = ∑ q : G ⧸ H, ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out))
        + ρ a (∑ q : G ⧸ H, ρ (b • q).out (f ((b • q).out⁻¹ * b * q.out)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, map_sum,
      reidx b (fun q => ρ (a • q).out (f ((a • q).out⁻¹ * a * q.out)))]
  · intro f x hf g
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = ρ g (ρ q.out x) - ρ (g • q).out x := by
      intro q
      rw [hf _ (mem g q), map_sub, rmul, rmul]
      congr 2
      group
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, map_sum,
      reidx g (fun q => ρ q.out x)]
  · intro f hf g
    have f1 : f 1 = 0 := by
      have := hf 1 1
      simp only [mul_one, map_one, one_apply_eq_self] at this
      exact left_eq_add.mp this
    have finv : ∀ s : G, ρ s (f s⁻¹) = - f s := by
      intro s
      have := hf s s⁻¹
      rw [mul_inv_cancel, f1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have key : ∀ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))
        = (f g + ρ g (f q.out)) - f (g • q).out := by
      intro q
      rw [mul_assoc, hf, map_add (f := _), finv, rmul, mul_inv_cancel, map_one, one_apply_eq_self, hf]
      abel
    show ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      map_sum, reidx g (fun q => f q.out), Finset.sum_const, Finset.card_univ,
      Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace GlobalTheory.InducedSectionsSpanStatement

section General

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def trCochain (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O) :
    (G → T.V) →ₗ[O] (G' → T.V) where
  toFun f g := ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply, Finset.smul_sum]

theorem trCochain_apply (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O)
    (f : G → T.V) (g : G') : trCochain ι T f g = ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out))) := rfl

theorem trCochain_Z1T [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCocycles (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCocycles T.L := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho
      (fun g => IsModuleTopology.continuous_of_linearMap (T.ρ g))
      (fun g => c (Function.invFun ι g)) ?_
    have h1 : (ι.range : Set G') = ι '' Set.univ := by
      rw [Set.image_univ]; rfl
    rw [h1, he.isInducing.continuousOn_image_iff]
    have h2 : ((fun g => c (Function.invFun ι g)) ∘ ι) = c := by
      funext g; simp only [Function.comp_apply, hj]
    rw [h2]
    exact hcont.continuousOn
  · refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.1
      (fun g => c (Function.invFun ι g)) ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, hj, hj, hj]
    exact hcoc a b
  · intro g _
    rw [trCochain_apply]
    exact Submodule.sum_mem _ fun q _ => T.L.stable _ _ (hT _ (Set.mem_univ _))

theorem trCochain_B1T (ι : G →* G') (hι : Continuous ι) (hinj : Function.Injective ι)
    [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCoboundaries (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCoboundaries T.L := by
  obtain ⟨x, hx, rfl⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun hinj
  refine ⟨∑ q : G' ⧸ ι.range, T.ρ q.out x,
    Submodule.sum_mem _ fun q _ => T.L.stable _ _ hx, ?_⟩
  funext g
  symm
  refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.2.1
    (fun g => T.ρ (ι (Function.invFun ι g)) x - x) x ?_ g
  rintro _ ⟨a, rfl⟩
  rw [hj]

def corH1 [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) : LatticeCohomology (LiftingTheory.resLoc ι hι T).L →ₗ[O] LatticeCohomology T.L :=
  Submodule.mapQ _ _
    (((trCochain ι T).comp (latticeCocycles (LiftingTheory.resLoc ι hι T).L).subtype).codRestrict (latticeCocycles T.L)
      (fun c => trCochain_Z1T ι hι he ho T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact trCochain_B1T ι hι he.injective T c hc)

theorem corH1_res [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L) :
    corH1 ι hι he ho T (LiftingTheory.resH1 ι hι T κ) = ((ι.range.index : ℕ) : O) • κ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  obtain ⟨c, ⟨hcont, hcoc⟩, hT⟩ := c
  refine ⟨∑ q : G' ⧸ ι.range, c q.out,
    Submodule.sum_mem _ fun q _ => hT _ (Set.mem_univ _), ?_⟩
  funext g
  have H := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  have h4 := H.2.2.2 c hcoc g
  have hj : ∀ q : G' ⧸ ι.range, ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out))
      = (g • q).out⁻¹ * g * q.out := fun q => Function.invFun_eq (H.1 g q)
  change T.ρ g (∑ q : G' ⧸ ι.range, c q.out) - ∑ q : G' ⧸ ι.range, c q.out
    = ∑ q : G' ⧸ ι.range, T.ρ (g • q).out
        (c (ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))) - ((ι.range.index : ℕ) : O) • c g
  simp only [hj]
  simp only at h4
  rw [h4, Nat.cast_smul_eq_nsmul]
  abel

theorem corH1_natural [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (κ : LatticeCohomology (LiftingTheory.resLoc ι hι T₁).L) :
    corH1 ι hι he ho T₂ ((LiftingTheory.resHom ι hι F).H1map κ) = F.H1map (corH1 ι hι he ho T₁ κ) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext g
  change ∑ q : G' ⧸ ι.range, T₂.ρ (g • q).out
        (F.f (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
    = F.f (∑ q : G' ⧸ ι.range, T₁.ρ (g • q).out
        (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => (F.equiv _ _).symm

variable {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

def repVB (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) :
    Representation LL G' (T.V ⊗[Qp] B) where
  toFun g := actVB PD' T.ρ g
  map_one' := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]
  map_mul' g h := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]

theorem actVB_tmul_one (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) (g : G')
    (x : T.V) : actVB PD' T.ρ g (x ⊗ₜ[Qp] (1 : B)) = T.ρ g x ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem actVB_res (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b)
    (T : LocLat G' Qp LL O) (g : G) (x : T.V ⊗[Qp] B) :
    actVB PD (LiftingTheory.resLoc ι hι T).ρ g x = actVB PD' T.ρ (ι g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hact]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem coreCor_of_isOpen [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR)
    (PD' : PeriodData G' Qp K₀' K' B BdR) (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [ι.range.FiniteIndex]
    (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) :
    LiftingTheory.coreCor PD PD' LL O ι hι ι.range.index := by
  haveI : Fintype (G' ⧸ ι.range) := Fintype.ofFinite _
  refine ⟨?_, corH1 ι hι he ho, corH1_res ι hι he ho, ?_, corH1_natural ι hι he ho⟩
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := LiftingTheory.resFun_Z1T ι hι T c c.2
    refine ⟨⟨LiftingTheory.resFun ι T c, hz⟩, ⟨hz, hz.1, x, fun g => ?_⟩, rfl⟩
    rw [actVB_res PD PD' ι hι hact]
    exact hx (ι g)
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := trCochain_Z1T ι hι he ho T c c.2
    have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
    refine ⟨⟨trCochain ι T c, hz⟩,
      ⟨hz, hz.1, ∑ q : G' ⧸ ι.range, actVB PD' T.ρ q.out x, fun g => ?_⟩, rfl⟩
    have h3 := (GlobalTheory.transfer_cocycle_formula LL G' _ (repVB PD' T) ι.range).2.2.1
      (fun g => c.1 (Function.invFun ι g) ⊗ₜ[Qp] (1 : B)) x (by
        rintro _ ⟨a, rfl⟩
        have := hx a
        rw [actVB_res PD PD' ι hι hact] at this
        rw [hj]
        exact this) g
    refine Eq.trans ?_ h3
    change trCochain ι T c g ⊗ₜ[Qp] (1 : B) = _
    rw [trCochain_apply, sum_tmul]
    exact Finset.sum_congr rfl fun q _ => (actVB_tmul_one PD' T _ _).symm

end General

open Formalism.BasicNotions.Loc

theorem GK_index_eq_finrank {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    (GK K).index = Module.finrank ℚ_[l] ↥K.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K.1).symm

theorem inclusion_GK_index {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (hle : GK K ≤ GK K') :
    (Subgroup.inclusion hle).range.index * Module.finrank ℚ_[l] ↥K'.1
      = Module.finrank ℚ_[l] ↥K.1 := by
  rw [Subgroup.inclusion_range, ← GK_index_eq_finrank, ← GK_index_eq_finrank]
  exact Subgroup.relIndex_mul_index hle

end GlobalTheory.InducedSectionsSpanStatement

namespace GlobalTheory

open Formalism.BasicNotions.Loc

theorem res_cor_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    LiftingTheory.adm20 D HW F := by
  intro D HW F l _ K K' _ hle LL
  haveI := K.2
  haveI := K'.2
  have hidx := InducedSectionsSpanStatement.inclusion_GK_index K K' hle
  have hpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  have hpos' : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
  have hg : Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1
      = (Subgroup.inclusion hle).range.index := by
    rw [← hidx, Nat.mul_div_cancel _ hpos']
  haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨fun h => by
    rw [h, zero_mul] at hidx; omega⟩
  rw [hg]
  refine InducedSectionsSpanStatement.coreCor_of_isOpen _ _ _ _ (Topology.IsEmbedding.inclusion hle) ?_ ?_
  · rw [Subgroup.inclusion_range]
    exact (IntermediateField.fixingSubgroup_isOpen K.1).preimage continuous_subtype_val
  · intro g b
    rw [(D.loc l).PD_actB, (D.loc l).PD_actB]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_corestriction_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm20 D HW F := by
  first | exact @GlobalTheory.res_cor_H1f | exact GlobalTheory.res_cor_H1f | (intros; apply GlobalTheory.res_cor_H1f <;> assumption)
end
