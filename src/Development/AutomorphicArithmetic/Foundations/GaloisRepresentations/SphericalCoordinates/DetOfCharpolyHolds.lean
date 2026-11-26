module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBaseImm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKillsMat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEigTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PBallChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumWOff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExtendEmb
open NumberField

namespace UpperTheory.Gal.W2

theorem extendEmb_of : ExtendEmb := by
  intro F _ _ φ
  have hker : RingHom.ker φ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  refine ⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩
  exact (IsFractionRing.lift_algebraMap (K := F) hinj c).symm

end UpperTheory.Gal.W2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PConjCharpoly
namespace UpperTheory.Gal.W2

theorem conjCharpoly_of : ConjCharpoly := by
  intro V _ _ _ d hd τ G A hτ hG
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := τ.linearEquivOfInjective hτ (by simp [hd])
  let b : Module.Basis (Fin d) ℂ V := (Pi.basisFun ℂ (Fin d)).map e.symm
  have hM : LinearMap.toMatrix b b G = A := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h1 : b j = e.symm (Pi.single j 1) := by simp [b]
    have h2 : ∀ v, b.repr v i = e v i := fun v => by simp [b, Pi.basisFun_repr]
    rw [h2, h1]
    change τ (G (e.symm (Pi.single j 1))) i = A i j
    rw [hG]
    have h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]
      exact e.apply_symm_apply _
    rw [h3, Matrix.mulVec_single_one]
    rfl
  rw [← hM, LinearMap.charpoly_toMatrix]

end UpperTheory.Gal.W2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocTan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem affineMap_hasFDerivAt (hTri : UpperTheory.Gal.W2.TriCharpoly) {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (Θ : W →ₗ[ℂ] W) (R : V →ₗ[ℂ] W) (c : V × W) (G : V × W → V × W)
    (hG : ∀ v, G v = (T v.1, Θ v.2 + R v.1) + c) (v₀ : V × W) :
    ∃ G' : (V × W) →L[ℂ] (V × W), HasFDerivAt G G' v₀ ∧
      (G' : (V × W) →ₗ[ℂ] (V × W)).charpoly = T.charpoly * Θ.charpoly := by
  unfold UpperTheory.Gal.W2.TriCharpoly at hTri
  let Gl : (V × W) →ₗ[ℂ] (V × W) :=
    LinearMap.prod (T ∘ₗ LinearMap.fst ℂ V W) (Θ ∘ₗ LinearMap.snd ℂ V W + R ∘ₗ LinearMap.fst ℂ V W)
  let G' : (V × W) →L[ℂ] (V × W) := LinearMap.toContinuousLinearMap Gl
  refine ⟨G', ?_, ?_⟩
  · have hfun : G = fun v => G' v + c := by
      funext v
      rw [hG v]
      rfl
    rw [hfun]
    exact G'.hasFDerivAt.add_const c
  · have hc : (G' : (V × W) →ₗ[ℂ] (V × W)) = Gl := rfl
    rw [hc]
    exact hTri V W T Θ R Gl (fun v w => rfl)

theorem UpperTheory.Gal.W2.locTan_of :
    UpperTheory.Gal.W2.TanChart → UpperTheory.Gal.W2.PerNear → UpperTheory.Gal.W2.BaseImm → UpperTheory.Gal.W2.PtHol → UpperTheory.Gal.W2.PtImm → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.TriCharpoly → UpperTheory.Gal.W2.LocTan := by
  intro hTan hPer hBase hHol hImm hFib hCorr hTri
  unfold UpperTheory.Gal.W2.TanChart at hTan
  unfold UpperTheory.Gal.W2.PerNear at hPer
  unfold UpperTheory.Gal.W2.BaseImm at hBase
  unfold UpperTheory.Gal.W2.PtHol at hHol
  unfold UpperTheory.Gal.W2.PtImm at hImm
  unfold UpperTheory.Gal.W2.PtFibre at hFib
  unfold UpperTheory.Gal.W2.CorrChart at hCorr
  unfold UpperTheory.Gal.W2.LocTan
  intro O _ bar g ρ D X s A _ S d hsm k Z sZ c₁ c₂ h₁ h₂ P₀ M₀ hP₀ hM co hco ga H hfix T hT L hL z₀ hz₀ y hy At hAt
  have hCsp : ∀ b, co b ∈ Csp bar ρ M₀ := by
    intro b
    have hco' := hco
    unfold IsCoordC at hco'
    rw [← hco'.2]
    exact LinearMap.mem_range_self co b
  obtain ⟨B0, hB0o, h0B0, hB0⟩ := hPer O bar g ρ D P₀ M₀ hP₀ hM d co hCsp
  have hB0' := hB0
  unfold PELU.IsHolPeriods at hB0'
  choose x hx using hz₀
  let sec : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Sp ℂ ⟶ (KS.pow A k).left) :=
    fun bz => S.pt k (perC P₀ (co bz.1)) bz.2
  let R : (Fin d → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ) :=
    { toFun := fun b j => -(co (T b) *ᵥ star (P₀ (x j)))
      map_add' := by
        intro a b
        funext j
        simp only [map_add (f := _), Matrix.add_mulVec, Pi.add_apply, neg_add]
      map_smul' := by
        intro c b
        funext j
        simp [Matrix.smul_mulVec] }
  let c : (Fin d → ℂ) × (Fin k → Fin g → ℂ) := (0, fun j => -(P₀ (x j)))
  let G : (Fin d → ℂ) × (Fin k → Fin g → ℂ) → (Fin d → ℂ) × (Fin k → Fin g → ℂ) :=
    fun v => (T v.1, fibMap H L v.2 - fun j => perC P₀ (co (T v.1)) (x j))
  have hG : ∀ v, G v = (T v.1, fibMap H L v.2 + R v.1) + c := by
    intro v
    refine Prod.ext ?_ ?_
    · show T v.1 = T v.1 + 0
      rw [add_zero]
    · funext j
      show fibMap H L v.2 j - perC P₀ (co (T v.1)) (x j) =
        fibMap H L v.2 j + -(co (T v.1) *ᵥ star (P₀ (x j))) + -(P₀ (x j))
      rw [perC_apply]
      abel
  obtain ⟨G', hG'd, hG'c⟩ := affineMap_hasFDerivAt hTri T (fibMap H L) R c G hG ((0 : Fin d → ℂ), z₀)
  have hfix0 : G ((0 : Fin d → ℂ), z₀) = ((0 : Fin d → ℂ), z₀) := by
    refine Prod.ext (map_zero T) ?_
    funext j
    show fibMap H L z₀ j - perC P₀ (co (T 0)) (x j) = z₀ j
    rw [map_zero T, map_zero co, perC_zero, hx j, sub_sub_cancel]
  have hsec0 : (y : Sp ℂ ⟶ (KS.pow A k).left) = sec ((0 : Fin d → ℂ), z₀) := by
    show _ = S.pt k (perC P₀ (co 0)) z₀
    rw [map_zero co, perC_zero]
    exact hy
  have hev : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), sec v ≫ c₂ = sec (G v) ≫ c₁ := by
    have hTc : Continuous (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1) :=
      (LinearMap.continuous_of_finiteDimensional T).comp continuous_fst
    have hT0 : Filter.Tendsto (fun v : (Fin d → ℂ) × (Fin k → Fin g → ℂ) => T v.1)
        (𝓝 ((0 : Fin d → ℂ), z₀)) (𝓝 0) := by
      have := hTc.tendsto ((0 : Fin d → ℂ), z₀)
      simpa using this
    have h1 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), v.1 ∈ B0 :=
      (continuous_fst.tendsto ((0 : Fin d → ℂ), z₀)).eventually (hB0o.eventually_mem h0B0)
    have h2 : ∀ᶠ v in 𝓝 ((0 : Fin d → ℂ), z₀), T v.1 ∈ B0 :=
      hT0.eventually (hB0o.eventually_mem h0B0)
    filter_upwards [h1, h2] with v hv1 hv2
    obtain ⟨b, z⟩ := v
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hv1
    have hPTb : PELU.IsPeriod D ρ (perC P₀ (co (T b))) := hB0'.1 (T b) hv2
    have hPTb' : PELU.IsPeriod D ρ (perC P₀ (H * co b * (H.map star)⁻¹)) := by
      rw [← hT b]
      exact hPTb
    have step := hCorr O bar g ρ D X s A S k Z c₁ c₂ P₀ M₀ hP₀ hM ga H hfix L hL (co b) hPb hPTb' z
    show S.pt k (perC P₀ (co b)) z ≫ c₂ =
      S.pt k (perC P₀ (co (T b))) (fibMap H L z - fun j => perC P₀ (co (T b)) (x j)) ≫ c₁
    rw [step, ← hT b]
    congr 1
    refine ((hFib O bar g ρ D X s A S k _ hPTb).2.2.2.1 _ _).mpr ?_
    intro j
    refine ⟨x j, ?_⟩
    simp [hT b]
  have hflat := hImm O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) 0 hB0o h0B0 hB0
    (hBase O bar g ρ D X s A S d hsm P₀ M₀ hP₀ hM co hco) z₀
  have hhol := hHol O bar g ρ D X s A S k d B0 (fun b => perC P₀ (co b)) hB0o hB0
  have hsecs : ∀ v ∈ B0 ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)),
      sec v ≫ ((KS.pow A k).hom ≫ s) = spMap (RingHom.id ℂ) := by
    rintro ⟨b, z⟩ ⟨hb, -⟩
    have hPb : PELU.IsPeriod D ρ (perC P₀ (co b)) := hB0'.1 b hb
    show S.pt k (perC P₀ (co b)) z ≫ ((KS.pow A k).hom ≫ s) = _
    rw [← Category.assoc, (hFib O bar g ρ D X s A S k _ hPb).1 z, S.ov _ hPb]
  have hfr : Module.finrank ℂ ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) = d + k * g := by
    simp [Module.finrank_pi_fintype]
  have key := hTan ((Fin d → ℂ) × (Fin k → Fin g → ℂ)) (d + k * g) hfr Z (KS.pow A k).left sZ
    ((KS.pow A k).hom ≫ s) c₁ c₂ h₁ h₂ (B0 ×ˢ Set.univ) sec ((0 : Fin d → ℂ), z₀)
    (hB0o.prod isOpen_univ) ⟨h0B0, trivial⟩ hhol hsecs hflat G G' hG'd hfix0 hev y hsec0 At hAt
  rw [key, hG'c]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExpImm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.expImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PbFlat → UpperTheory.Gal.W2.ExpImm0 → UpperTheory.Gal.W2.ExpImm := by
  intro hcomp hpre hpb h0 X A _ g y e he z₀ w hw
  apply h0 X A g y e he w
  have hsplit : ∀ z, e z = e (-z₀) * e (z₀ + z) := by
    intro z
    rw [← he.1, neg_add_cancel_left]
  have hhol : IsHolTo Set.univ (fun z => Over.Hom.left (e (z₀ + z))) :=
    GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp (φ := fun z => z₀ + z) he.2.2.1 isOpen_univ
      (by fun_prop) (Set.mapsTo_univ _ _)
  have hflat : Flat (fun z => Over.Hom.left (e (z₀ + z))) 0 w := by
    have hd : HasFDerivAt (fun z : Fin g → ℂ => z₀ + z) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
      (hasFDerivAt_id 0).const_add z₀
    refine (hpre (Fin g → ℂ) (Fin g → ℂ) A.left Set.univ (fun z => Over.Hom.left (e z)) he.2.2.1
      (fun z => z₀ + z) _ 0 w hd (Set.mem_univ _)).2 ?_
    simpa using hw
  have hpbA : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct A A)
  have h1 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (fst A A).left) =
      fun _ => (e (-z₀)).left := by
    funext z
    rw [← Over.comp_left, lift_fst]
  have h2 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (snd A A).left) =
      fun z => (e (z₀ + z)).left := by
    funext z
    rw [← Over.comp_left, lift_snd]
  have hconstHol : IsHolTo Set.univ (fun _ : Fin g → ℂ => (e (-z₀)).left) := by
    intro U f
    refine ⟨?_, differentiableOn_const _⟩
    by_cases hU : ⊤ ≤ (e (-z₀)).left ⁻¹ᵁ U
    · simp [hU]
    · simp [hU]
  have hconstFlat : Flat (fun _ : Fin g → ℂ => (e (-z₀)).left) 0 w := by
    intro U f _
    simp
  have hs : Flat (fun z => (lift (e (-z₀)) (e (z₀ + z))).left) 0 w := by
    refine hpb (Fin g → ℂ) _ A.left A.left X (fst A A).left (snd A A).left A.hom A.hom hpbA Set.univ
      _ 0 w isOpen_univ (Set.mem_univ _) ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h1]
      exact hconstHol
    · beta_reduce
      rw [h2]
      exact hhol
    · beta_reduce
      rw [h1]
      exact hconstFlat
    · beta_reduce
      rw [h2]
      exact hflat
  have hfe : (fun z => (e z).left) =
      fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (μ : A ⊗ A ⟶ A).left := by
    funext z
    rw [← Over.comp_left, ← Hom.mul_def, ← hsplit]
  rw [hfe]
  exact hcomp (Fin g → ℂ) _ A.left (μ : A ⊗ A ⟶ A).left _ 0 w hs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExpImm0Of
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem expImm0_of : ExpImm0 := by
  intro X A _ g y e he w hw
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  have hv0 : IsDerivAt0 (fun z => Over.Hom.left (e z)) 0 (Over.Hom.left v) := by
    refine ⟨hv.1, fun U h f => (hv.2 U h f).trans ?_⟩
    have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ Over.Hom.left v = Over.Hom.left (e 0) := hv.1
    have h' : ⊤ ≤ (Over.Hom.left (e 0)) ⁻¹ᵁ U := by
      rw [← hb]
      exact fun x _ => h trivial
    rw [hw U f h', map_zero]
  exact (he.2.2.2.2 v hv.1).unique hv hv0

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPiLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.piLattice_of :
    UpperTheory.Gal.W2.PiLattice := by
  intro g k Λ hd hs
  constructor
  · let φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ) :=
      fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩
    refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
    · refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    · intro x y hxy
      apply Subtype.ext
      funext i
      have := congrArg (fun z => (z i : Fin g → ℂ)) hxy
      simpa [φ] using this
  · rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hs]; trivial
    have hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map
        (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤
        Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hv
      · simp [hj]
    exact hmap ⟨w i, hw, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open GlobalTheory.HolHom in
theorem UpperTheory.Gal.W2.flatAffine_of :
    UpperTheory.Gal.W2.FlatAffine := by
  intro V _ _ Y B s v₀ w hB hv₀ hs W hW hsW hder U f hU
  have hhol := holAt_of_isHolTo hs hv₀
  have hpU := (le_preimage_iff _ _).1 hU
  have hpW := (le_preimage_iff _ _).1 hsW
  obtain ⟨g, hgle, hpg⟩ := hW.exists_basicOpen_le (V := U) ⟨_, hpU⟩ hpW
  have hDW : Y.basicOpen g ≤ W := Y.basicOpen_le g
  letI := (Y.presheaf.map (homOfLE hDW).op).hom.toAlgebra
  haveI := hW.isLocalization_basicOpen g
  obtain ⟨⟨h, ⟨_, k, rfl⟩⟩, e⟩ :=
    IsLocalization.surj (Submonoid.powers g) ((Y.presheaf.map (homOfLE hgle).op).hom f)
  simp only [RingHom.algebraMap_toAlgebra] at e
  have hD0 : ⊤ ≤ s v₀ ⁻¹ᵁ Y.basicOpen g := (le_preimage_iff _ _).2 hpg
  have hev : ∀ᶠ v in 𝓝 v₀, ⊤ ≤ s v ⁻¹ᵁ Y.basicOpen g := (hhol _ hD0).1
  have heq : (fun v => valAt' (s v) W h) =ᶠ[𝓝 v₀]
      (fun v => valAt' (s v) U f * valAt' (s v) W g ^ k) := by
    filter_upwards [hev] with v hv
    have e' := congrArg (HolHom.evalHom (s v) _ hv) e
    simp only [map_mul, map_pow, ← valR_eq] at e'
    rw [valR_res (s v) hgle f hv, valR_res (s v) hDW g hv, valR_res (s v) hDW h hv] at e'
    simp only [valAt'_eq_valR]
    exact e'.symm
  have hFd := (hhol U hU).2 f
  have hGd := (hhol W hsW).2 g
  have hHd := (hhol W hsW).2 h
  have hL := (hFd.hasFDerivAt.mul (hGd.hasFDerivAt.pow k)).congr_of_eventuallyEq heq
  have huniq := hL.unique hHd.hasFDerivAt
  have hw := congrArg (fun L => L w) huniq
  have hG0 : valAt' (s v₀) W g ≠ 0 := (le_basicOpen_iff _ hsW g).1 hD0
  simp [hder g, hder h, hG0] at hw
  exact hw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerLin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.perLin_of :
    UpperTheory.Gal.W2.PerLin := by
  intro O _ bar g ρ D P P' H hP hH hc hP'
  have hdet : LinearMap.det (Matrix.toLin' H) ≠ 0 := by rwa [LinearMap.det_toLin']
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearMap.equivOfDetNeZero _ hdet
  have happ : ∀ z, h z = H *ᵥ z := fun z => rfl
  have key := IsPeriod.comp_linearEquiv O bar D g ρ ρ P h hP (fun a z => by
    rw [happ, happ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc])
  have hEq : P' = (↑h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).toAddMonoidHom.comp P := by
    ext x
    simp [hP', happ]
  rw [hEq]
  exact key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetReal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.detReal_of :
    UpperTheory.Gal.W2.DetReal := by
  intro W _ _ _ f
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.mul_conj]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanDeriv
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem tanDeriv_of : TanDeriv := by
  intro V _ _ Y s' B s v₀ hB hv₀ hs hss y hy W hyW
  have hv₀S : v₀ ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} := ⟨hv₀, by rw [← hy]; exact hyW⟩
  have hnhds : {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} ∈ 𝓝 v₀ := (hs W 0).1.mem_nhds hv₀S
  have hval : ∀ v (hv : v ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}) (b : Sec s' W),
      valAt' (s v) W b = CxPts.ev s' (RingHom.id ℂ) W b ⟨s v, hss v hv.1⟩ := by
    intro v hv b
    simp only [valAt', CxPts.ev, valR, dif_pos hv.2]
    rfl
  let g : Sec s' W → V → ℂ := fun b v => valAt' (s v) W b
  have hd : ∀ b, DifferentiableAt ℂ (g b) v₀ := fun b =>
    ((hs W b).2 v₀ hv₀S).differentiableAt ((hs W b).1.mem_nhds hv₀S)
  have hadd : ∀ b c, g (b + c) =ᶠ[𝓝 v₀] g b + g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b + c) = valAt' (s v) W b + valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_add _ _ _)
  have hmul : ∀ b c, g (b * c) =ᶠ[𝓝 v₀] g b * g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b * c) = valAt' (s v) W b * valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_mul _ _ _)
  have hconst : ∀ a : ℂ, ∀ᶠ v in 𝓝 v₀, g (algebraMap ℂ (Sec s' W) a) v = a := fun a =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (algebraMap ℂ (Sec s' W) a) = a
      rw [hval v hv]
      exact CxPts.ev_algX (show (⟨s v, hss v hv.1⟩ : CxPts s' (RingHom.id ℂ)) ∈ CxPts.ptsIn s' (RingHom.id ℂ) W from hv.2) a)
  have hyeq : (⟨s v₀, hss v₀ hv₀S.1⟩ : CxPts s' (RingHom.id ℂ)) = y := Subtype.ext hy.symm
  have hv0 : ∀ b, g b v₀ = CxPts.evHom hyW b := fun b => by
    change valAt' (s v₀) W b = _
    rw [hval v₀ hv₀S b, hyeq]
    exact CxPts.ev_eq hyW b
  have hφa : ∀ a : ℂ, CxPts.evHom hyW (algebraMap ℂ (Sec s' W) a) = a := fun a =>
    (CxPts.ev_eq hyW _).symm.trans (CxPts.ev_algX hyW a)
  letI : Module (Sec s' W) (V →L[ℂ] ℂ) := Module.compHom _ (CxPts.evHom hyW)
  haveI : IsScalarTower ℂ (Sec s' W) (V →L[ℂ] ℂ) := ⟨fun a b m => by
    change (CxPts.evHom hyW (a • b)) • m = a • ((CxPts.evHom hyW b) • m)
    have h1 : CxPts.evHom hyW (a • b) = a * CxPts.evHom hyW b :=
      (congrArg (CxPts.evHom hyW) (Algebra.smul_def a b)).trans
        ((map_mul (CxPts.evHom hyW) _ _).trans (congrArg (· * CxPts.evHom hyW b) (hφa a)))
    exact (congrArg (· • m) h1).trans (mul_smul _ _ _)⟩
  let L : Sec s' W →ₗ[ℂ] (V →L[ℂ] ℂ) :=
    { toFun := fun b => fderiv ℂ (g b) v₀
      map_add' := fun b c => by
        change fderiv ℂ (g (b + c)) v₀ = fderiv ℂ (g b) v₀ + fderiv ℂ (g c) v₀
        rw [(hadd b c).fderiv_eq, fderiv_add (hd b) (hd c)]
      map_smul' := fun a b => by
        change fderiv ℂ (g (a • b)) v₀ = a • fderiv ℂ (g b) v₀
        have h' : g (a • b) =ᶠ[𝓝 v₀] fun v => a * g b v := by
          rw [Algebra.smul_def]
          filter_upwards [hmul (algebraMap ℂ _ a) b, hconst a] with v h1 h2
          rw [h1, Pi.mul_apply, h2]
        rw [h'.fderiv_eq, fderiv_const_mul (hd b)] }
  let D : Derivation ℂ (Sec s' W) (V →L[ℂ] ℂ) := Derivation.mk' L (fun b c => by
    change fderiv ℂ (g (b * c)) v₀ =
      (CxPts.evHom hyW b) • fderiv ℂ (g c) v₀ + (CxPts.evHom hyW c) • fderiv ℂ (g b) v₀
    rw [(hmul b c).fderiv_eq, fderiv_mul (hd b) (hd c), hv0 b, hv0 c])
  refine ⟨D.liftKaehlerDifferential.restrictScalars ℂ, fun b ω => ?_, fun b => ?_⟩
  · change D.liftKaehlerDifferential (b • ω) = _
    rw [LinearMap.map_smul]
    exact congrArg (· • D.liftKaehlerDifferential ω) (CxPts.ev_eq hyW b).symm
  · change D.liftKaehlerDifferential (KaehlerDifferential.D ℂ _ b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_map_ext {X : Scheme.{0}} {A : Over X} {k : ℕ} {T : Scheme.{0}}
    (a b : T ⟶ (GlobalTheory.KS.pow A k).left) (h0 : a ≫ (GlobalTheory.KS.pow A k).hom = b ≫ (GlobalTheory.KS.pow A k).hom)
    (h : ∀ j, a ≫ (GlobalTheory.KS.pr A j).left = b ≫ (GlobalTheory.KS.pr A j).left) : a = b := by
  let Y : Over X := Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)
  let fa : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk a rfl
  let fb : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk b h0.symm
  have hab : fa = fb := by
    unfold GlobalTheory.KS.pow at fa fb ⊢
    apply Limits.Pi.hom_ext
    intro j
    ext
    simp only [Over.comp_left, Over.homMk_left, fa, fb]
    exact h j
  exact congrArg (fun f => f.left) hab

section
variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D : PLat O bar}
  {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {A : Over X} [GrpObj A] (S : Sheet s A D ρ) (k : ℕ)

private theorem pt_hom (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) :
    S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P :=
  Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)

private theorem pt_pr (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) (j : Fin k) :
    S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left := by
  unfold Sheet.pt GlobalTheory.KS.pr
  rw [← Over.comp_left]
  exact congrArg Over.Hom.left (Limits.Pi.lift_comp_π _ j)

private theorem ex_sub (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ρ P) (a b : Fin g → ℂ) :
    S.ex P a = S.ex P (a - b) * S.ex P b := by
  have h := S.exp P hP
  unfold IsExp at h
  have e := h.1 (a - b) b
  rwa [sub_add_cancel] at e

end

theorem UpperTheory.Gal.W2.ptFibre_of :
    UpperTheory.Gal.W2.PtFibre := by
  intro O _ bar g ρ D X s A _ S k P hP
  have hE := S.exp P hP
  unfold IsExp at hE
  have hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P' :=
    fun P' w => Over.w (S.ex P' w)
  refine ⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩
  · intro y hy
    have hc : ∀ j : Fin k, ∃ w, S.ex P w =
        Over.homMk (U := Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by
          show _ = S.u P
          rw [Category.assoc, Over.w]
          exact hy) := fun j => hE.2.1 _
    choose z hz using hc
    refine ⟨z, pow_map_ext _ _ ?_ ?_⟩
    · rw [hy, pt_hom]
    · intro j
      rw [pt_pr, hz j]
      rfl
  · intro z z'
    constructor
    · intro heq j
      have e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left := by
        rw [← pt_pr S k P z j, ← pt_pr S k P z' j, heq]
      have e2 : S.ex P (z j) = S.ex P (z' j) := Over.OverMorphism.ext e1
      have e3 : S.ex P (z j - z' j) = 1 := by
        have e4 := ex_sub S P hP (z j) (z' j)
        rw [e2] at e4
        exact mul_eq_right.mp e4.symm
      exact (S.ker P hP _).mp e3
    · intro hr
      apply pow_map_ext
      · rw [pt_hom, pt_hom]
      · intro j
        rw [pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]
  · intro P' h hP' hx z
    have hu' : S.u P' = S.u P := by
      calc S.u P' = (S.ex P' (h 0)).left ≫ A.hom := (hu P' (h 0)).symm
        _ = (S.ex P 0).left ≫ A.hom := by rw [S.lin P P' h hP hP' hx 0]
        _ = S.u P := hu P 0
    apply pow_map_ext
    · rw [pt_hom, pt_hom, hu']
    · intro j
      rw [pt_pr, pt_pr]
      exact S.lin P P' h hP hP' hx (z j)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTriCharpoly
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.triCharpoly_of :
    UpperTheory.Gal.W2.TriCharpoly := by
  intro V W _ _ _ _ _ _ T Θ R G hG
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  have hM : LinearMap.toMatrix (bV.prod bW) (bV.prod bW) G =
      Matrix.fromBlocks (LinearMap.toMatrix bV bV T) 0 (LinearMap.toMatrix bV bW R)
        (LinearMap.toMatrix bW bW Θ) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, hG]
  rw [← LinearMap.charpoly_toMatrix G (bV.prod bW), ← LinearMap.charpoly_toMatrix T bV,
    ← LinearMap.charpoly_toMatrix Θ bW, hM, Matrix.charpoly_fromBlocks_zero₁₂]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatComp_of :
    UpperTheory.Gal.W2.FlatComp := by
  intro V _ _ Y Y' f s v₀ w h U a hU
  have hU' : ⊤ ≤ s v₀ ⁻¹ᵁ (f ⁻¹ᵁ U) := hU
  have e : (fun v => valAt' (s v ≫ f) U a) =
      fun v => valAt' (s v) (f ⁻¹ᵁ U) ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom a) :=
    funext fun v => GlobalTheory.ExpCoord.valAt'_comp (s v) f U a
  rw [e]
  exact h _ _ hU'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatPre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatPre_of :
    UpperTheory.Gal.W2.FlatPre := by
  intro V _ _ V' _ _ Y B s hs φ φ' v₀ w hφ hB
  have key : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ s (φ v₀) ⁻¹ᵁ U →
      fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ w =
        fderiv ℂ (fun b => valAt' (s b) U f) (φ v₀) (φ' w) := by
    intro U f hU
    obtain ⟨hopen, hdiff⟩ := hs U f
    have hmem : φ v₀ ∈ {b ∈ B | ⊤ ≤ s b ⁻¹ᵁ U} := ⟨hB, hU⟩
    have hd : DifferentiableAt ℂ (fun b => valAt' (s b) U f) (φ v₀) :=
      (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
    have hc := hd.hasFDerivAt.comp v₀ hφ
    have he : fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ = _ := hc.fderiv
    rw [he]
    rfl
  constructor
  · intro h U f hU
    rw [← key U f hU]
    exact h U f hU
  · intro h U f hU
    rw [key U f hU]
    exact h U f hU
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHolPi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_zero_hom_isIso {X : Scheme.{0}} (A : Over X) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let t : Over.mk (𝟙 X) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let u : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 X) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have h1 : u ≫ t = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨t.left, ?_, ?_⟩⟩
  · have h2 := congrArg Over.Hom.left h1
    simpa [u] using h2
  · simpa using Over.w t

private noncomputable def tailMap {X : Scheme.{0}} (A : Over X) (k : ℕ) : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
  Pi.lift fun j => GlobalTheory.KS.pr A j.succ

private theorem tailMap_pr {X : Scheme.{0}} (A : Over X) (k : ℕ) (j : Fin k) :
    tailMap A k ≫ GlobalTheory.KS.pr A j = GlobalTheory.KS.pr A j.succ := by
  simp [tailMap, GlobalTheory.KS.pr]

set_option maxHeartbeats 400000 in
private theorem pow_succ_isPullback {X : Scheme.{0}} (A : Over X) (k : ℕ) :
    IsPullback (GlobalTheory.KS.pr A (0 : Fin (k + 1))).left (tailMap A k).left A.hom (GlobalTheory.KS.pow A k).hom := by
  refine Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk (GlobalTheory.KS.pr A (0 : Fin (k + 1))) (tailMap A k)) ?_
  refine BinaryFan.IsLimit.mk _ (fun f g => Pi.lift (Fin.cases f (fun j => g ≫ GlobalTheory.KS.pr A j))) ?_ ?_ ?_
  · intro T f g
    simp [GlobalTheory.KS.pr]
  · intro T f g
    refine Pi.hom_ext _ _ fun j => ?_
    simp [tailMap, GlobalTheory.KS.pr]
  · intro T f g m h1 h2
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h1 h2
    refine Pi.hom_ext (f := fun _ : Fin (k + 1) => A) (m : T ⟶ ∏ᶜ fun _ : Fin (k + 1) => A) _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [← h1, GlobalTheory.KS.pr]
    · rw [← h2]
      simp [tailMap, GlobalTheory.KS.pr]

theorem UpperTheory.Gal.W2.holPi_of :
    UpperTheory.Gal.W2.HolPi := by
  intro V _ _ X A k
  induction k with
  | zero =>
    intro B s hB h0 _
    haveI := pow_zero_hom_isIso A
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h0 (inv (GlobalTheory.KS.pow A 0).hom)) ?_
    intro b _
    simp
  | succ k ih =>
    intro B s hB h0 hj
    refine GlobalTheory.HolPullback.isHolTo_of_components V B _ _ _ _ _ _ _ _ s (pow_succ_isPullback A k) hB (hj 0) ?_
    apply ih B (fun v => s v ≫ (tailMap A k).left) hB
    · refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr h0 ?_
      intro b _
      simp only [Category.assoc, Over.w]
    · intro j
      refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr (hj j.succ) ?_
      intro b _
      simp only [Category.assoc]
      rw [← Over.comp_left, tailMap_pr]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_mul_spherical_coordinates {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

private theorem det_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    (A.map star).det = star A.det := by
  exact (RingHom.map_det (starRingEnd ℂ) A).symm

private theorem hermForm_mulVec_mulVec {g : ℕ} (M H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (H *ᵥ z) (H *ᵥ w) = hermForm (Hᵀ * M * H.map star) z w := by
  rw [PerCoordU.herm_mulVec_left, PerCoordU.herm_mulVec_right]

private theorem eq_of_mulVec_period_eq {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, A *ᵥ P x = B *ᵥ P x) : A = B := by
  have e := PerCoordU.ext_per hP (f := PeriodCoord.realMap A 0) (f' := PeriodCoord.realMap B 0)
    (fun x => by simp [PeriodCoord.realMap_apply, h])
  exact (PeriodCoord.realMap_inj e).1

private theorem eq_of_hermForm_im_eq_on_periods {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {N N' : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x y, (hermForm N (P x) (P y)).im = (hermForm N' (P x) (P y)).im) : N = N' := by
  apply PerCoordU.sesq_ext
  have h1 : PeriodCoord.imForm N = PeriodCoord.imForm N' := by
    apply PerCoordU.ext_per hP
    intro x
    apply PerCoordU.ext_per hP
    intro y
    simp only [PeriodCoord.imForm_apply]
    exact h x y
  intro z w
  rw [← PeriodCoord.imForm_apply, ← PeriodCoord.imForm_apply, h1]

private theorem inv_mul_comm_of_mul_comm_of_det_unit {g : ℕ} (X N : Matrix (Fin g) (Fin g) ℂ) (hN : IsUnit N.det)
    (h : X * N = N * X) : N⁻¹ * X = X * N⁻¹ := by
  calc N⁻¹ * X = N⁻¹ * X * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
    _ = N⁻¹ * (X * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = N⁻¹ * (N * X) * N⁻¹ := by rw [h]
    _ = X * N⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN, Matrix.one_mul]

theorem UpperTheory.Gal.W2.adExists_of :
    UpperTheory.Gal.W2.AdExists := by
  intro O _ bar g ρ D P₀ M₀ hP hM ga H hF
  obtain ⟨⟨m, hm, hEF⟩, hga⟩ := hF
  obtain ⟨_, hpos, hIm⟩ := hM
  have hform : Hᵀ * M₀ * H.map star = (m : ℂ) • M₀ := by
    apply eq_of_hermForm_im_eq_on_periods hP
    intro x y
    have hs : hermForm ((m : ℂ) • M₀) (P₀ x) (P₀ y) = (m : ℂ) * hermForm M₀ (P₀ x) (P₀ y) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
    rw [← hermForm_mulVec_mulVec, ← hga x, ← hga y, hIm, hEF, hs, Complex.mul_im, hIm]
    simp
  have hdM : M₀.det ≠ 0 := PeriodCoord.det_ne_zero_of_pos hpos
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hform
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, det_map_star',
      Matrix.det_smul] at e
    simp [hdM, hm.ne'] at e
  have hcomm : ∀ a, ρ a * H = H * ρ a := by
    intro a
    apply eq_of_mulVec_period_eq hP
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hga x, ← hP.1 a (ga x), ← hP.1 a x,
      ← hga (a • x), LinearMap.map_smul]
  refine ⟨hdet, hcomm, ?_⟩
  intro C hC
  set N := H.map star with hNdef
  have hNu : IsUnit N.det := by
    rw [hNdef, det_map_star']
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  have hNtu : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
  have hc' : ∀ b, (ρ b).map star * N = N * (ρ b).map star := by
    intro b
    rw [hNdef, ← map_star_mul_spherical_coordinates, ← map_star_mul_spherical_coordinates, hcomm]
  have hC' : (Cᵀ * M₀)ᵀ = Cᵀ * M₀ ∧
      ∀ a, Cᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * (Cᵀ * M₀) := hC
  obtain ⟨hS1, hS2⟩ := hC'
  have hHM : Hᵀ * M₀ = (m : ℂ) • (M₀ * N⁻¹) := by
    calc Hᵀ * M₀ = Hᵀ * M₀ * N * N⁻¹ := by
          rw [Matrix.mul_assoc (Hᵀ * M₀), Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
      _ = (m : ℂ) • (M₀ * N⁻¹) := by rw [hform, Matrix.smul_mul]
  have hkey : (H * C * N⁻¹)ᵀ * M₀ = (m : ℂ) • (N⁻¹ᵀ * (Cᵀ * M₀) * N⁻¹) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hHM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  show ((H * C * N⁻¹)ᵀ * M₀)ᵀ = (H * C * N⁻¹)ᵀ * M₀ ∧
    ∀ a, (H * C * N⁻¹)ᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * ((H * C * N⁻¹)ᵀ * M₀)
  rw [hkey]
  generalize Cᵀ * M₀ = S at hS1 hS2 ⊢
  constructor
  · simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hS1,
      Matrix.mul_assoc]
  · intro a
    have c1 : N⁻¹ * (ρ (bar a)).map star = (ρ (bar a)).map star * N⁻¹ :=
      inv_mul_comm_of_mul_comm_of_det_unit _ N hNu (hc' (bar a))
    have hX : (ρ a)ᴴ * Nᵀ = Nᵀ * (ρ a)ᴴ := by
      rw [← PerCoordU.map_star_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hc' a]
    have c2 : Nᵀ⁻¹ * (ρ a)ᴴ = (ρ a)ᴴ * Nᵀ⁻¹ := inv_mul_comm_of_mul_comm_of_det_unit _ _ hNtu hX
    rw [Matrix.transpose_nonsing_inv]
    calc (m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹) * (ρ (bar a)).map star
        = (m : ℂ) • (Nᵀ⁻¹ * S * (N⁻¹ * (ρ (bar a)).map star)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (S * (ρ (bar a)).map star) * N⁻¹) := by
          rw [c1]; simp only [Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * ((ρ a)ᴴ * S) * N⁻¹) := by rw [hS2 a]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (ρ a)ᴴ * S * N⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (ρ a)ᴴ * ((m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹)) := by
          rw [c2]; simp only [Matrix.mul_smul, Matrix.mul_assoc]
end

namespace UpperTheory.Gal.W2

theorem TanDeriv_holds : TanDeriv := tanDeriv_of

theorem FlatAffine_holds : FlatAffine := flatAffine_of

theorem ConjCharpoly_holds : ConjCharpoly := conjCharpoly_of

theorem TanChart_holds : TanChart := tanChart_of TanDeriv_holds FlatAffine_holds ConjCharpoly_holds

theorem TanExists_holds : TanExists := tanExists_of

theorem FlatComp_holds : FlatComp := flatComp_of

theorem FlatPre_holds : FlatPre := flatPre_of

theorem PbFlat_holds : PbFlat := pbFlat_of FlatAffine_holds

theorem ExpImm0_holds : ExpImm0 := expImm0_of

theorem ExpImm_holds : ExpImm := expImm_of FlatComp_holds FlatPre_holds PbFlat_holds ExpImm0_holds

theorem HolPi_holds : HolPi := holPi_of

theorem PerNear_holds : PerNear := perNear_of

theorem PerCoordLoc_holds : PerCoordLoc := perCoordLoc_of

theorem PerLin_holds : PerLin := perLin_of

theorem AdExists_holds : AdExists := adExists_of

theorem BaseImm_holds : BaseImm := baseImm_of PerNear_holds PerCoordLoc_holds

theorem PtFibre_holds : PtFibre := ptFibre_of

theorem PtHol_holds : PtHol := ptHol_of HolPi_holds PtFibre_holds

theorem PtImm_holds : PtImm := ptImm_of FlatComp_holds FlatPre_holds PtFibre_holds ExpImm_holds

theorem TriCharpoly_holds : TriCharpoly := triCharpoly_of

theorem DetOfCharpoly_holds : DetOfCharpoly := detOfCharpoly_of

theorem CorrChart_holds : CorrChart := corrChart_of AdExists_holds PerLin_holds PtFibre_holds

theorem LocTan_holds : LocTan := locTan_of TanChart_holds PerNear_holds BaseImm_holds PtHol_holds PtImm_holds PtFibre_holds CorrChart_holds TriCharpoly_holds

theorem DetReal_holds : DetReal := detReal_of

theorem TorusCount_holds : TorusCount := torusCount_of DetReal_holds

theorem PiLattice_holds : PiLattice := piLattice_of

theorem LocSum_holds : LocSum := locSum_of LocTan_holds TorusCount_holds PiLattice_holds PtFibre_holds CorrChart_holds DetOfCharpoly_holds

theorem SimDiag_holds : SimDiag := simDiag_of

theorem ExtendEmb_holds : ExtendEmb := extendEmb_of

theorem KillsMat_holds : KillsMat := killsMat_of

theorem HSep_holds : HSep := hSep_of

theorem DiagExists_holds : DiagExists := diagExists_of SimDiag_holds ExtendEmb_holds KillsMat_holds HSep_holds

theorem TypeCount_holds : TypeCount := typeCount_of

theorem TraceLat_holds : TraceLat := traceLat_of

theorem TraceDual_holds : TraceDual := traceDual_of

theorem NewtonPoly_holds : NewtonPoly := newtonPoly_of

theorem PowSumRat_holds : PowSumRat := powSumRat_of TraceLat_holds TraceDual_holds

theorem RootsFull_holds : RootsFull := rootsFull_of TypeCount_holds PowSumRat_holds NewtonPoly_holds KillsMat_holds

theorem MarkDiag_holds : MarkDiag := markDiag_of TypeCount_holds

theorem TspDiag_holds : TspDiag := tspDiag_of

theorem BallChar_holds : BallChar := ballChar_of TypeCount_holds TspDiag_holds

theorem CspDim_holds : CspDim := cspDim_of SimDiag_holds ExtendEmb_holds TypeCount_holds MarkDiag_holds BallChar_holds

theorem FibDet_holds : FibDet := fibDet_of

theorem FibW_holds : FibW := fibW_of

theorem EvIntegral_holds : EvIntegral := evIntegral_of

theorem EigTop_holds : EigTop := eigTop_of AdExists_holds DiagExists_holds TypeCount_holds RootsFull_holds MarkDiag_holds BallChar_holds FibDet_holds FibW_holds EvIntegral_holds

theorem RootSumW_holds : RootSumW := rootSumW_of

theorem RootSumWOff_holds : RootSumWOff := rootSumWOff_of

end UpperTheory.Gal.W2
