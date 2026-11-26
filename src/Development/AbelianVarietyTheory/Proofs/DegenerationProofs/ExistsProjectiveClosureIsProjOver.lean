module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RegularOfBoundedAtPadicAlgClPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points GlobalTheory.ProjSpace GlobalTheory.TuplePoint

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {n : ℕ} {t : Fin (n + 1) → Ω}

theorem exists_div_of_closure_ratios_eq_top
    (h : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤) {i : Fin (n + 1)}
    (hi : t i ≠ 0) (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i),
      ∃ b ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a / b = x := by
  have hle : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure ((Algebra.adjoin o (Set.range fun j => t j / t i)).toSubring : Set Ω) := by
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
    · rw [← div_div_div_cancel_right₀ hi]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hx := hle (h ▸ Subfield.mem_top x)
  rwa [Subfield.mem_closure_iff, Subring.closure_eq] at hx

section Closed

variable {ht : t ≠ 0} {Z : Scheme.{0}} {ξ : Sp Ω ⟶ Z} {π : Z ⟶ PSpace o n} (hπ : ξ ≫ π = point o t ht)

include hπ

theorem exists_valF_preimage_chart_iff [IsClosedImmersion π] {i : Fin (n + 1)} (hi : t i ≠ 0) (x : Ω) :
    (∃ f : Γ(Z, π ⁻¹ᵁ chart o n i), valF ξ _ f = x) ↔ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i) := by
  have h := (le_point_preimage_iff (o := o) (ht := ht) i).2 hi
  have key : ∀ g, valF ξ _ ((π.app (chart o n i)).hom g) = (valMap (point o t ht) _ h).hom g := fun g => by
    rw [← valR_eq, ← hπ]
    exact (valR_comp ξ π _ g).symm
  rw [← SetLike.mem_coe, ← range_valMap_point h]
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := π.app_surjective _ (isAffineOpen_chart o n i) f
    exact ⟨g, (key g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, key g⟩

end Closed

theorem exists_valF_eq_div {Z : Scheme.{0}} (ξ : Sp Ω ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (a b : Γ(Z, U))
    (hb : valF ξ U b ≠ 0) : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b ∧
      ∃ f : Γ(Z, Z.basicOpen b), valF ξ _ f = valF ξ U a / valF ξ U b := by
  have hle : ⊤ ≤ ξ ⁻¹ᵁ Z.basicOpen b := (le_preimage_basicOpen_iff _ hU b).2 (isUnit_iff_ne_zero.2 hb)
  have hu : IsUnit (resG _ (Z.basicOpen_le b) b) :=
    RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace b
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have h1 : valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) b * c) = 1 :=
    (congrArg _ hc).trans (valR_one _ _ hle)
  rw [valR_mul _ _ hle] at h1
  have h2 : ∀ s, valR ξ (Z.basicOpen b) (resG _ (Z.basicOpen_le b) s) = valF ξ U s :=
    fun s => valR_res _ _ hle _
  refine ⟨hle, resG _ (Z.basicOpen_le b) a * c, (valR_mul _ _ hle _ _).trans ?_⟩
  rw [h2 b] at h1
  rw [h2 a, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]

theorem RatModel.isCl_of_isClosedImmersion (M : RatModel o Ω) {ht : t ≠ 0} (π : M.Z ⟶ PSpace o n)
    [IsClosedImmersion π] (hπ : M.pt ≫ π = point o t ht) : M.IsCl t := by
  have h1 : ∀ (k : Fin (n + 1)) (z : M.Z), z ∈ π ⁻¹ᵁ chart o n k → M.Div t k z := fun k z hz =>
    have hW := M.top_le_preimage_pt ⟨z, hz⟩
    ⟨ne_zero_of_le hπ hW le_rfl, fun j => ⟨_, pullRatio π _ k le_rfl j, hz, valR_pullRatio hπ hW le_rfl j⟩⟩
  have h2 : ∀ (i : Fin (n + 1)) (z : M.Z), M.Div t i z → z ∈ π ⁻¹ᵁ chart o n i := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_mem_chart o n (π z)
    have hk' : z ∈ π ⁻¹ᵁ chart o n k := hk
    have hu := ((h1 k z hk').div_iff_isUnit i).1 hz
    have e : (⟨t i / t k, (h1 k z hk').2 i⟩ : M.O z) =
        ⟨_, RatModel.valF_mem_O hk' (pullRatio π _ k le_rfl i)⟩ :=
      Subtype.ext (valR_pullRatio hπ (M.top_le_preimage_pt ⟨z, hk'⟩) le_rfl i).symm
    rw [e, RatModel.isUnit_valF_iff hk', basicOpen_pullRatio] at hu
    exact hu.2
  refine ⟨fun z => (exists_mem_chart o n (π z)).imp fun k hk => h1 k z hk, fun i hi => ?_⟩
  refine ⟨π ⁻¹ᵁ chart o n i, (isAffineOpen_chart o n i).preimage π,
    Set.ext fun z => ⟨h1 i z, h2 i z⟩, ?_⟩
  ext x
  rw [RatModel.mem_ringOn_iff_exists ⟨_, h2 i _ (RatModel.div_genericPoint hi)⟩,
    exists_valF_preimage_chart_iff hπ hi]

theorem exists_isCl_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ n t ⟨i, hi⟩ h
  have ht : t ≠ 0 := Function.ne_iff.2 ⟨i, hi⟩
  let φ := point o t ht
  have hsep : IsProper (PSpace.str o n) :=
    projProper o _ _ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hqc : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ PSpace.str o n) := by
      rw [point_str]
      infer_instance
    exact QuasiCompact.of_comp φ (PSpace.str o n)
  have hπ : φ.toImage ≫ φ.imageι = point o t ht := φ.toImage_imageι
  have hW := le_preimage_chart hπ hi
  let M : RatModel o Ω :=
    { Z := φ.image
      s := φ.imageι ≫ PSpace.str o n
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := φ.toImage
      pt_s := by rw [← Category.assoc, hπ, point_str]
      gen := by
        have e : Set.range φ.toImage = {φ.toImage (IsLocalRing.closedPoint Ω)} :=
          Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, by
            rintro _ ⟨w, rfl⟩
            rw [Subsingleton.elim w (IsLocalRing.closedPoint Ω)]⟩
        have hd : IsGenericPoint (φ.toImage (IsLocalRing.closedPoint Ω)) Set.univ := by
          rw [isGenericPoint_def, ← e]
          exact φ.toImage.denseRange.closure_range
        rw [e, hd.eq (genericPoint_spec _)]
      onto := fun x => by
        obtain ⟨_, ha, _, hb, rfl⟩ := exists_div_of_closure_ratios_eq_top h hi x
        obtain ⟨a, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 ha
        obtain ⟨b, rfl⟩ := (exists_valF_preimage_chart_iff hπ hi _).2 hb
        by_cases h0 : valF φ.toImage _ b = 0
        · exact ⟨_, b, ⟨_, hW (x := IsLocalRing.closedPoint Ω) trivial⟩, by rw [h0, div_zero]⟩
        · obtain ⟨hle, f, hf⟩ := exists_valF_eq_div _ hW a b h0
          exact ⟨_, f, ⟨_, hle (x := IsLocalRing.closedPoint Ω) trivial⟩, hf⟩ }
  exact ⟨M, M.isCl_of_isClosedImmersion φ.imageι hπ, n, φ.imageι, inferInstance, rfl⟩

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.exists_projectiveClosure_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (n : ℕ) (t : Fin (n + 1) → Ω), (∃ i, t i ≠ 0) → Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ → ∃ M : RatModel o Ω, M.IsCl t ∧ IsProjOver M.s := by
  first | exact @GlobalTheory.ZH.exists_isCl_isProjOver | exact GlobalTheory.ZH.exists_isCl_isProjOver | (intros; apply GlobalTheory.ZH.exists_isCl_isProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNest
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.Nest
variable {O : Type} [CommRing O] (N : NumD O)

theorem wQ_nest {n k l : ℕ} (hk : Odd k) (hl : Odd l) (e : l = n * (k * n)) (p'' : N.QT l) (p : N.QT k)
    (hy : p''.1.1 = p.1.1 ^ n) (hg : p.1.2 = p''.1.2 ^ n) :
    N.wQ p * mulq N.θ N.σ n p''.1.2.b ^ k = N.wQ p'' := by
  subst e
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hc : N.c p.1.1.toAdd = p''.1.2.b ^ (k * n) := by
    rw [← N.QT_pow_b p, hb, ← pow_mul']
  have hy' : p''.1.1.toAdd = n • p.1.1.toAdd := by rw [hy, toAdd_pow]
  obtain ⟨hA, hB⟩ := (SymLift.wQ_iff N hk p (N.wQ p)).mp rfl
  refine (SymLift.wQ_iff N hl p'' _).mpr ⟨?_, ?_⟩
  · simp only [NumD.tk, hg, NumD.Gt.pow_b] at hA
    have ps := NumD.Gt.pow_s p''.1.2 n p.1.1.toAdd
    have ss := PsiQuadratic.s_nsmul N p''.1.2 n p.1.1.toAdd
    have db := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n 0 p''.1.2.b p''.1.2.b).2.2.1
    have cm1 := CubeBalance.cubN_mul N.cub n (k * n) p''.1.2.b p''.1.2.b
    have cm2 := CubeBalance.cubN_mul N.cub k n p''.1.2.b p''.1.2.b
    have sw := CubeBalance.cubN_swap N.cub k n (p''.1.2.b ^ n) p''.1.2.b
    rw [hc] at ps ss
    rw [← pow_mul'] at sw
    simp only [NumD.tk]
    rw [hy']
    apply Additive.ofMul.injective
    replace hA := congrArg Additive.ofMul hA
    replace ps := congrArg Additive.ofMul ps
    replace ss := congrArg Additive.ofMul ss
    replace db := congrArg Additive.ofMul db
    replace cm1 := congrArg Additive.ofMul cm1
    replace cm2 := congrArg Additive.ofMul cm2
    replace sw := congrArg Additive.ofMul sw
    simp only [ofMul_mul, ofMul_pow] at hA ps ss db cm1 cm2 sw ⊢
    linear_combination (norm := module) hA - (k : ℤ) • db + sw + ps - ss - cm1 - (n : ℤ) • cm2
  · rw [hb] at hB
    have hψ := PsiQuadratic.ψ_nsmul N n p.1.1.toAdd
    have hm1 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n (k * n) p''.1.2.b p''.1.2.b).1
    have hm2 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k n p''.1.2.b p''.1.2.b).1
    rw [hc] at hψ
    rw [hy']
    apply Additive.ofMul.injective
    replace hB := congrArg Additive.ofMul hB
    replace hψ := congrArg Additive.ofMul hψ
    replace hm1 := congrArg Additive.ofMul hm1
    replace hm2 := congrArg Additive.ofMul hm2
    simp only [ofMul_mul, ofMul_pow] at hB hψ hm1 hm2 ⊢
    linear_combination (norm := module)
      ((n : ℤ) ^ 2) • hB - hψ - hm1 - ((n : ℤ) ^ 2) • hm2

theorem txT_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  intro O _ N n m hn hm p'' p hy hg χ
  have hw := wQ_nest N hm.pow (hn.mul hm).pow (by ring) p'' p hy hg
  have hq := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m n p''.1.2.b p''.1.2.b).1
  rw [mul_comm m n] at hq
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hu : N.wQ p'' / mulq N.θ N.σ (n * m) p''.1.2.b = N.wQ p / mulq N.θ N.σ m p.1.2.b := by
    rw [← hw, hq, hb, mul_div_mul_right_eq_div]
  simp only [NumD.txT]
  rw [hu, hg, ← pow_mul]

end GlobalTheory.Ex.Nest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNestStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationSeriesTerms_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  first | exact @GlobalTheory.Ex.Nest.txT_nest | exact GlobalTheory.Ex.Nest.txT_nest | (intros; apply GlobalTheory.Ex.Nest.txT_nest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem exists_mul_pow_mem_O_of_isAffineOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ V, u ∈ M.O z) (hφ : ∀ z ∈ V, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ n : ℕ, ∀ z ∈ V, φ * u ^ n ∈ M.O z := by
  obtain ⟨g, rfl⟩ := (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 hu)
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : g = 0 := (basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h)
    exact hu0 (by rw [h0, ← M.res_apply V hne, map_zero])
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg (x := φ)).1 (mem_ringOn.2 fun z hz =>
    hφ z (M.Z.basicOpen_le g hz)
      ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2)
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
  exact ⟨n, fun z hz => h1 ▸ valF_mem_O hz a⟩


variable (M) in
theorem noetherianSpace_of_isNoetherianRing [IsNoetherianRing o] : TopologicalSpace.NoetherianSpace M.Z := by
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  have : AlgebraicGeometry.IsNoetherian M.Z := {}
  infer_instance

theorem exists_forall_mul_pow_mem_O [IsNoetherianRing o] (W : M.Z.Opens)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ W, u ∈ M.O z) (hφ : ∀ z ∈ W, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * u ^ C ∈ M.O z := by
  have := M.noetherianSpace_of_isNoetherianRing
  have hmono : ∀ z ∈ W, ∀ m n : ℕ, m ≤ n → φ * u ^ m ∈ M.O z → φ * u ^ n ∈ M.O z := by
    intro z hz m n hmn h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [pow_add, ← _root_.mul_assoc]
    exact mul_mem h (pow_mem (hu z hz) k)
  have hcov : (W : Set M.Z) ⊆ ⋃ n : ℕ, {z | φ * u ^ n ∈ M.O z} := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W) (x := z) hz
    obtain ⟨n, hn⟩ := exists_mul_pow_mem_O_of_isAffineOpen hV ⟨z, hzV⟩ hu0 (fun w hw => hu w (hle hw))
      (fun w hw => hφ w (hle hw))
    exact Set.mem_iUnion.2 ⟨n, hn z hzV⟩
  obtain ⟨s, hs⟩ := (TopologicalSpace.NoetherianSpace.isCompact (W : Set M.Z)).elim_finite_subcover _
    (fun n => M.isOpen_setOf_mem_O _) hcov
  refine ⟨s.sup id, fun C hC z hz => ?_⟩
  obtain ⟨n, hn, h⟩ := Set.mem_iUnion₂.1 (hs hz)
  exact hmono z hz n C ((Finset.le_sup (f := id) hn).trans hC) h

theorem exists_forall_mul_prod_div_pow_mem_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o] (J : Type)
      (t : J → Ω) (W : M.Z.Opens) (j : J), (∀ z ∈ W, M.Div t j z) → ∀ (I : Finset J) (φ : Ω),
      (∀ z ∈ W, (∀ i ∈ I, M.Div t i z) → φ ∈ M.O z) → (∀ i ∈ I, t i ≠ 0) →
      ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * (∏ i ∈ I, t i / t j) ^ C ∈ M.O z := by
  intro o Ω _ _ _ M _ J t W j hj I φ hφ hI
  by_cases hW : ∃ z, z ∈ W
  swap
  · exact ⟨0, fun _ _ z hz => (hW ⟨z, hz⟩).elim⟩
  obtain ⟨z₀, hz₀⟩ := hW
  have hj0 : t j ≠ 0 := (hj z₀ hz₀).1
  have hu0 : (∏ i ∈ I, t i / t j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => div_ne_zero (hI i hi) hj0
  refine exists_forall_mul_pow_mem_O W hu0 (fun z hz => prod_mem fun i _ => (hj z hz).2 i) fun z hz hinv => ?_
  refine hφ z hz fun i hi => ((hj z hz).div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨div_ne_zero (hI i hi) hj0, ?_⟩)
  have hmem := mul_mem (prod_mem (S := M.O z) (t := I.erase i) fun k _ => (hj z hz).2 k) hinv
  have e : (∏ k ∈ I.erase i, t k / t j) * (∏ k ∈ I, t k / t j)⁻¹ = (t i / t j)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← _root_.mul_assoc, Finset.mul_prod_erase I (fun k => t k / t j) hi, mul_inv_cancel₀ hu0]
  exact e ▸ hmem

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem isIntegrallyClosed_stalk_of_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) {z : M.Z} (hz : z ∈ U)
    (h : ∀ x : Ω, IsIntegral (M.ringOn U) x → x ∈ M.ringOn U) :
    IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have : Nonempty U := ⟨⟨z, hz⟩⟩
  have : IsFractionRing (M.ringOn U) Ω := isFractionRing_ringOn hU hne
  have : IsIntegrallyClosed (M.ringOn U) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, h x hx⟩, rfl⟩
  have : IsIntegrallyClosed Γ(M.Z, U) := IsIntegrallyClosed.of_equiv (M.sectionsEquiv U hne).symm
  let _ := TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (⟨z, hz⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hz⟩
  exact isIntegrallyClosed_of_isLocalization (M.Z.presheaf.stalk z) _
    (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨z, hz⟩).asIdeal)

theorem IsNm.isNormalScheme {J : Type} {t : J → Ω} (h : M.IsNm t) : IsNormalScheme M.Z := by
  obtain ⟨hd, hU⟩ := h
  have key : ∀ z : M.Z, IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
    intro z
    obtain ⟨i, hi⟩ := hd z
    obtain ⟨U, hUa, hUeq, hmem⟩ := hU i hi.1
    have hz : z ∈ (U : Set M.Z) := hUeq ▸ hi
    refine isIntegrallyClosed_stalk_of_ringOn hUa hz fun x hx => ?_
    set A := Algebra.adjoin o (Set.range fun j => t j / t i)
    have hle : A ≤ M.ringOn U := fun y hy => (hmem y).2 (isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
    let : Algebra A (M.ringOn U) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    have : IsScalarTower A (M.ringOn U) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsIntegral A (M.ringOn U) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (M.ringOn U) Ω) Subtype.val_injective).1
        ((hmem y).1 y.2)⟩
    exact (hmem x).2 (isIntegral_trans x hx)
  exact ⟨fun z => (M.stalkHom_injective z).isDomain _, key⟩

theorem div_prod_iff {J J' : Type} {t : J → Ω} {t' : J' → Ω} {i : J} {i' : J'} {z : M.Z} :
    M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hi' : t' i' ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨⟨hi, fun j => ?_⟩, ⟨hi', fun j' => ?_⟩⟩
    · simpa [mul_div_mul_right _ _ hi'] using h (j, i')
    · simpa [mul_div_mul_left _ _ hi] using h (i, j')
  · rintro ⟨⟨hi, h⟩, ⟨hi', h'⟩⟩
    refine ⟨mul_ne_zero hi hi', fun q => ?_⟩
    rw [mul_div_mul_comm]
    exact mul_mem (h q.1) (h' q.2)

theorem div_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} {q : ∀ a, JJ a} {z : M.Z} :
    M.Div (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) q z ↔ ∀ a, M.Div (tt a) (q a) z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hne : ∀ a, tt a (q a) ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 h0 a (Finset.mem_univ a)
    intro a
    refine ⟨hne a, fun j => ?_⟩
    have hj := h (Function.update q a j)
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single a] at hj
    · simpa using hj
    · intro b _ hb
      simp [Function.update_of_ne hb, div_self (hne b)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · intro h
    refine ⟨Finset.prod_ne_zero_iff.2 fun a _ => (h a).1, fun q' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun a _ => (h a).2 (q' a)

theorem hasDiv_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} :
    M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a) := by
  simp only [RatModel.HasDiv]
  constructor
  · intro h a z
    obtain ⟨q, hq⟩ := h z
    exact ⟨q a, div_finprod_iff.1 hq a⟩
  · intro h z
    choose q hq using fun a => h a z
    exact ⟨q, div_finprod_iff.2 hq⟩

end RatModel

theorem isNm_normal_and_div_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) (t : J → Ω), (M.IsNm t → IsNormalScheme M.Z) ∧ (∀ (J' : Type) (t' : J' → Ω) (i : J) (i' : J') (z : M.Z), M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z) ∧ (∀ (A : Type) [Fintype A] (JJ : A → Type) (tt : ∀ a, JJ a → Ω), M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a)) := by
  intro o Ω _ _ _ M J t
  exact ⟨fun h => h.isNormalScheme, fun J' t' i i' z => RatModel.div_prod_iff,
    fun A _ JJ tt => RatModel.hasDiv_finprod_iff⟩

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftOfRetraction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatLift

theorem exists_lift_of_retraction {X B Z : Scheme.{0}} [IsAffine Z] (q : X ⟶ B) [IsAffineHom q] {V : B.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, q ⁻¹ᵁ V) ⟶ Γ(B, V)) (hr : q.app V ≫ r = 𝟙 _) (b : Z ⟶ B)
    (hb : ⊤ ≤ b ⁻¹ᵁ V) : ∃ x : Z ⟶ X, x ≫ q = b := by
  refine ⟨Z.isoSpec.hom ≫ Spec.map (b.appLE V ⊤ hb) ≫ Spec.map r ≫ (hV.preimage q).fromSpec, ?_⟩
  simp only [Category.assoc]
  rw [← hV.SpecMap_appLE_fromSpec q (hV.preimage q) le_rfl, Scheme.Hom.appLE_eq_app, ← Spec.map_comp_assoc (q.app V) r, hr,
    Spec.map_id, Category.id_comp, hV.SpecMap_appLE_fromSpec b (isAffineOpen_top Z) hb, IsAffineOpen.fromSpec_top,
    Iso.hom_inv_id_assoc]

theorem exists_retraction {A C X : Type} [CommRing A] [CommRing C] [AddCommGroup X] (f : A →+* C)
    (g : Multiplicative X →* C)
    (h : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _))) :
    ∃ r : C →+* A, r.comp f = RingHom.id A := by
  let e := RingEquiv.ofBijective _ h
  let a : AddMonoidAlgebra A X →+* A :=
    AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A) (fun _ _ => Commute.all _ _)
  refine ⟨a.comp e.symm.toRingHom, RingHom.ext fun c => ?_⟩
  have : e.symm (f c) = AddMonoidAlgebra.single 0 c := by
    rw [RingEquiv.symm_apply_eq]
    simp [e, AddMonoidAlgebra.liftNCRingHom]
  simp [this, a, AddMonoidAlgebra.liftNCRingHom]

attribute [local instance] SplitExt.free SplitExt.finite

theorem exists_point_over :
    ∀ (F : Type) [Field F] (E : SplitExt (Spec (CommRingCat.of F))) (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G) (b : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ E.B), ∃ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G, x ≫ Dat.q = b := by
  intro F _ E G _ Dat b
  let b' : Spec (CommRingCat.of F) ⟶ E.B.left := b.left
  let p : Spec (CommRingCat.of F) := default
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB (b' p)
  have hp : b' p ∈ E.chart j := by
    have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
    exact this.ge (Set.mem_iInter.2 hj)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVj⟩ :=
    E.B.left.isBasis_affineOpens.exists_subset_of_mem_open hp (E.chart j).2
  obtain ⟨r, hr⟩ := exists_retraction _ _ (Dat.coord j V hV hVj)
  have := Dat.q_affine
  obtain ⟨x, hx⟩ := exists_lift_of_retraction Dat.q.left hV (CommRingCat.ofHom r) (CommRingCat.hom_ext hr) b'
    (fun y _ => by
      obtain rfl : y = p := Subsingleton.elim _ _
      exact hpV)
  refine ⟨Over.homMk x ?_, Over.OverMorphism.ext hx⟩
  rw [← Over.w Dat.q, ← Category.assoc, hx]
  exact Over.w b

end GlobalTheory.RatLift
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsLift

theorem exists_pow_eq_hom {X M : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup M] (n : ℕ)
    (h : ∀ m : M, ∃ r : M, r ^ n = m) (f : Multiplicative X →* M) :
    ∃ g : Multiplicative X →* M, g ^ n = f := by
  choose r hr using h
  let b := Module.Free.chooseBasis ℤ X
  let g : X →ₗ[ℤ] Additive M :=
    b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))
  have hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [g, LinearMap.smul_apply, Module.Basis.constr_basis]
    rw [← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)

theorem exists_pow_eq_unit (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n)
    (m : Γ(Sp k, ⊤)ˣ) : ∃ r : Γ(Sp k, ⊤)ˣ, r ^ n = m := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e m.val) (n := n) hn
  have h1 : (e.symm z) ^ n = m.val := by
    rw [← map_pow, hz, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega : n ≠ 0)).1 (h1 ▸ m.isUnit)
  exact ⟨hu.unit, Units.ext (by simpa using h1)⟩

theorem exists_pow_eq_torus (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] (n : ℕ) (hn : 1 ≤ n) (t : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X) :
    ∃ s : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X, s ^ n = t := by
  let e := splitTorusPointsEquiv (Sp k) X (Out.baseOver (Sp k))
  obtain ⟨g, hg⟩ := exists_pow_eq_hom n (exists_pow_eq_unit k n hn) (e t)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact hg

theorem points_lift :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G) (n : ℕ), 1 ≤ n → (∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b) ∧ (∀ b : Out.baseOver (Sp k) ⟶ E.B, b ^ n = 1 → ∃ x : Out.baseOver (Sp k) ⟶ G, x ^ n = 1 ∧ x ≫ D.q = b) ∧ ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 → ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
  intro k _ _ E G _ _ D n hn
  have := D.q_hom
  have := D.i_hom
  have h1 : ∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b :=
    RatLift.exists_point_over k E G D
  have h3 : ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 →
      ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_pow_eq_torus k E.X n hn (D.isKernel.lift x (toUnit _) hx)
    refine ⟨s ≫ D.i, ?_, ?_⟩
    · rw [Category.assoc, D.isKernel.w, ← Category.assoc, comp_toUnit]
      rfl
    · rw [← MonObj.pow_comp, hs, D.isKernel.lift_fst]
  refine ⟨h1, fun b hb => ?_, h3⟩
  obtain ⟨x, hx⟩ := h1 b
  obtain ⟨y, hy, hyx⟩ := h3 (x ^ n) (by rw [MonObj.pow_comp, hx, hb])
  refine ⟨x * y⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hyx, mul_inv_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hy, inv_one, _root_.mul_one]

end GlobalTheory.TorsLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfSplitAll
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem SplitAll.fieldPoint {Z : Scheme.{0}} {G : Over Z} [GrpObj G] (h : SplitAll G) (K : Type) [Field K]
    (t : Sp K ⟶ Z) : ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G) := by
  obtain ⟨z, r, rfl⟩ : ∃ (z : Z) (r : Sp K ⟶ Sp (Z.residueField z)), t = r ≫ Z.fromSpecResidueField z :=
    ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t).symm⟩
  obtain ⟨E, ⟨d⟩⟩ := h z
  have : IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).inv)
  obtain ⟨E', _, _, _, _, hE'⟩ := gtBaseChange _ _ r E _ ⟨d⟩
  exact ⟨E', isGt_of_iso (pullCompIso r (Z.fromSpecResidueField z) G).symm hE'⟩

theorem isSemiAbelian_of_splitAll : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], SplitAll G → IsSemiAbelian G ∧ (∀ (K : Type) [Field K] (t : Sp K ⟶ Z), ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G)) ∧ ∀ x : Z, ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField x) k), FiniteDimensional (Z.residueField x) k ∧ Algebra.IsSeparable (Z.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField x) k)) ≫ Z.fromSpecResidueField x)).obj G) := by
  intro Z G _ hc hs hsep hq h
  refine ⟨⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩, h.fieldPoint, fun x => ⟨Z.residueField x, inferInstance, inferInstance, inferInstance,
      inferInstance, h.fieldPoint _ _⟩⟩
  · obtain ⟨E, hE⟩ := h.fieldPoint K q
    have hg : GeometricallyConnected (pullback.snd G.hom q) :=
      (UnitRigidity.smooth_geometricallyConnected_of_isGt E _ hE).2
    rw [← (pullbackLeftPullbackSndIso G.hom q (𝟙 _) ≪≫ pullback.congrHom rfl (Category.id_comp q)).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K (𝟙 _)
  · obtain ⟨E, hE⟩ := h.fieldPoint Ω q
    exact nonempty_torusExtension_of_isGt E _ hE

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsRegular
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem locallyOfFiniteType_int [Algebra.FiniteType ℤ o] :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  haveI := M.lft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  infer_instance

theorem flat_int_sections [CharZero Ω] (U : M.Z.Opens) : Module.Flat ℤ Γ(M.Z, U) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨n, hn⟩, ha⟩
  rw [Submodule.mem_bot]
  rcases (U : Set M.Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.coe_injective hU
    exact Subsingleton.elim _ _
  · have h : n • M.res U hU a = 0 := by
      rw [← map_zsmul, show n • a = 0 from ha, map_zero]
    exact (map_eq_zero_iff _ (M.res_injective U hU)).1
      ((smul_eq_zero.1 h).resolve_left (nonZeroDivisors.ne_zero hn))

theorem flat_int [CharZero Ω] (π : M.Z ⟶ Sp ℤ) : Flat π := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : M.Z.affineOpens => U)
    (iSup_affineOpens_eq_top _) fun U => ?_
  have e : (π.appLE ⊤ U le_top).hom =
      (algebraMap ℤ Γ(M.Z, U)).comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom := by
    have e' : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv ≫ π.appLE ⊤ U le_top).hom = algebraMap ℤ Γ(M.Z, U) :=
      RingHom.ext_int _ _
    rw [← e', ← CommRingCat.hom_comp, Iso.hom_inv_id_assoc]
  rw [e]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.bijective)
    (RingHom.flat_algebraMap_iff.2 (flat_int_sections M U))

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH.MinorModel

end GlobalTheory.ZH.MinorModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusPointEqOneOfAxes
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem splitTorus_point_eq_one_of_axes (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K))
    (G : Over (Sp K)) [GrpObj G] (h : E.IsGt G) (X : Type) [AddCommGroup X]
    (t : G ⊗ G ⟶ splitTorus (Sp K) X)
    (h₁ : lift (𝟙 G) (1 : G ⟶ G) ≫ t = 1) (h₂ : lift (1 : G ⟶ G) (𝟙 G) ≫ t = 1) : t = 1 := by
  have key : ∀ (a : G ⟶ G ⊗ G), a ≫ t = 1 → ∀ χ : X, a.left.appTop.hom
      (splitTorusPointsEquiv (Sp K) X (G ⊗ G) t (Multiplicative.ofAdd χ)).val = 1 := by
    intro a ha χ
    have := splitTorusPointsEquiv_val (Sp K) X G (a ≫ t) χ
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_one] at this
    rw [splitTorusPointsEquiv_val]
    exact this.symm
  apply (splitTorusPointsEquiv (Sp K) X (G ⊗ G)).injective
  rw [map_one]
  ext χ
  exact unit_eq_one_of_axes_of_isGt K E G h _ (Units.isUnit _) (key _ h₁ χ) (key _ h₂ χ)

theorem isMonHom_of_isGt_of_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E E' : SplitExt (Sp K)) (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'], E.IsGt G → E'.IsGt G' → ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → IsMonHom f := by
  intro K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf
  have := D.q_hom
  have := D.i_hom
  have hk := D.isKernel
  have hq : IsMonHom (f ≫ D.q) := GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety K E G h E'.B E'.isAbelian (f ≫ D.q) (by
    rw [reassoc_of% hf]; exact IsMonHom.one_hom D.q)
  have hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1 := by
    intro W
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let d : G ⊗ G ⟶ G' := ((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hd : d ≫ D.q = 1 := by
    simp only [d]
    rw [GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc,
      Category.assoc, div_self']
  let t : G ⊗ G ⟶ splitTorus (Sp K) E'.X := hk.lift d (toUnit _) (by rw [hd, Hom.one_def])
  have ht : t ≫ D.i = d := hk.lift_fst _ _ _
  have inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1 := fun a ha =>
    hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)
  have t1 : t = 1 := by
    refine splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']
  rw [t1, MonObj.one_comp] at ht
  have hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp ht.symm
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
  rw [hm]
  congr 1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpeciaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemiAbelian_of_proper_generic_torusExtension_special : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  first | exact @GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | exact GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension | (intros; apply GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension <;> assumption)
end
