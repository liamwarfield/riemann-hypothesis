module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MinimalVectorStabilizerProperty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbReOfMinimalVectorStabilizer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GoodRealFormOfRealPartOfRealInvolution
open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.good_real_form_of_real_part_of_real_involution :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe := by
  intro hRP hRI L _ _ _ N σ hσ
  have G := UpperTheory.V.KT.good L N
  have hqc : ∀ (y : NZ L N) (k : HS L N), qc L N y k = q k (y : Lat L N) := fun y k => by
    simp [qc, ev_apply]
  have hpoly : ∀ h : HR L N, h ∈ ConeExtensionAcyclic.poly (qr L N) → (h : HS L N) ∈ ConeExtensionAcyclic.poly (qc L N) :=
    fun h hh y => by
      have := hh y
      rw [qr_apply] at this
      rw [hqc]
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨S, hS, hev⟩ := G.locFin _ (hpoly h hh)
    refine ⟨S, hS, ?_⟩
    have := (continuous_subtype_val.tendsto h).eventually hev
    filter_upwards [this] with h' hh' y hy
    rw [qr_apply, ← hqc]
    exact hh' y hy
  · obtain ⟨k, hk⟩ := G.nonempty
    obtain ⟨k', hk', -⟩ := hRP L N σ hσ k
    have hinv := (hRI L N σ hσ).1
    refine ⟨k', fun y => ?_⟩
    have hne : sLat σ (y : Lat L N) ≠ 0 := by
      intro h0
      apply y.2
      funext a
      have := congrFun h0 a
      simp only [sLat, Pi.zero_apply] at this
      show (y : Lat L N) a = 0
      rw [← hinv ((y : Lat L N) a), this, map_zero]
    have h1 := hk y
    have h2 := hk ⟨_, hne⟩
    rw [hqc] at h1 h2
    rw [qr_apply, hk']
    have h2' : 1 ≤ q k (sLat σ (y : Lat L N)) := h2
    linarith
  · exact G.closed.preimage continuous_subtype_val
  · intro c hc k hk
    exact G.smul_mem c hc _ hk
  · intro h hh
    exact G.sub (hpoly h hh)
  · obtain ⟨x, hx⟩ := G.pos
    refine ⟨x.comp (HR L N).subtypeL, fun k hk hk0 => ?_⟩
    exact hx _ hk (fun h => hk0 (Subtype.ext h))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedCommOfBoundedEquiv
theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h1
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h2
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ProjPermOfLiftEquiv
open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCMIntegralOfExistsCM
open NumberField in
theorem UpperTheory.exists_CM_integral_of_exists_CM :
    UpperTheory.V.Af.BA.ExCM → UpperTheory.V.Af.BA.ExCMInt := by
  intro h F _ _ _
  obtain ⟨L, i1, i2, i3, i, s, hs, hfix⟩ := h F
  refine ⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩
  · intro w x
    exact hs w.embedding (x : L)
  · intro x y hxy
    have h1 : i (x : F) = i (y : F) := congrArg (fun z : 𝓞 L => (z : L)) hxy
    exact RingOfIntegers.ext (i.injective h1)
  · intro x
    constructor
    · intro hx
      have h1 : s (x : L) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hx
      obtain ⟨y, hy⟩ := (hfix _).1 h1
      have hi : IsIntegral ℤ y := by
        have h2 : IsIntegral ℤ (i.toIntAlgHom y) := by
          have : i.toIntAlgHom y = (x : L) := hy
          rw [this]
          exact x.isIntegral_coe
        exact (isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2
      exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩
    · rintro ⟨y, hy⟩
      have h1 : i (y : F) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hy
      exact RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepBoundedOverOfSumBoundCoindRetract
open CategoryTheory in
theorem UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.BA.CoindRetract → UpperTheory.V.Af.BA.BddOver := by
  intro hSum hRet
  unfold UpperTheory.V.Af.BA.BddOver
  intro G _ S hS hB
  unfold UpperTheory.V.Af.CohB.Bdd at hB ⊢
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, fun A => ?_⟩
  obtain ⟨π, ι, hπι⟩ := hRet G S hS A
  have hq : ∀ q, Module.rank ℂ ↑(groupCohomology A q) ≤
      Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q) := by
    intro q
    have h1 := hSum G Unit A (fun _ => Rep.coind S.subtype (Rep.res S.subtype A))
      (fun _ => π) (fun _ => ι) (by rw [Fintype.sum_unique]; exact hπι) q
    rw [Fintype.sum_unique,
      ((groupCohomology.coindIso (Rep.res S.subtype A) q).toLinearEquiv).rank_eq] at h1
    exact h1
  calc UpperTheory.V.Af.CohB.totCoh A
      = Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology A q)) := rfl
    _ ≤ Cardinal.sum (fun q => Module.rank ℂ ↑(groupCohomology (Rep.res S.subtype A) q)) :=
      Cardinal.sum_le_sum _ _ hq
    _ = UpperTheory.V.Af.CohB.totCoh (Rep.res S.subtype A) := rfl
    _ ≤ c * Module.rank ℂ ↑(Rep.res S.subtype A) := hc _
    _ = c * Module.rank ℂ ↑A := rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingFixedPointsEquiv
theorem UpperTheory.building_fixed_points_equiv :
    UpperTheory.V.Af.BA.FixEquiv := by
  intro A B _ _ i σ N hi hσ
  have hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n := Fin N) i g ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by
    intro g
    change Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) =
      Matrix.GeneralLinearGroup.map (n := Fin N) i g
    ext a b
    exact (hσ _).2 ⟨g a b, rfl⟩
  have hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y := by
    intro X Y h
    ext a b
    exact hi (congrFun (congrFun h a) b)
  have hpre : ∀ g : GL (Fin N) B,
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) →
      ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin N) σ g = g := hg
    have h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b := by
      intro a b
      refine (hσ _).1 ?_
      have := congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'
      exact this
    choose X hX using h1
    exact ⟨Matrix.of X, by ext a b; exact hX a b⟩
  refine ⟨(MulEquiv.ofBijective
    ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩
  · intro g k h
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin N) i g =
      Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h
    apply Units.ext
    apply hM
    exact congrArg Units.val h1
  · rintro ⟨g, hg⟩
    obtain ⟨X, hX⟩ := hpre g hg
    obtain ⟨Y, hY⟩ := hpre g⁻¹ (inv_mem hg)
    refine ⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.mul_inv
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.inv_mul
    · apply Subtype.ext
      apply Units.ext
      exact hX
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicRepDimensionBounded
open UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_rep_dimension_bounded :
    UpperTheory.V.Af.BA.DimBdd := by
  classical
  unfold UpperTheory.V.Af.BA.DimBdd
  intro Γ I _ _ K hfin hstab0
  have hre : ∀ {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (t : K.Tup q) (g : Γ),
      g • t = t → g • K.re f t = K.re f t := by
    intro p q f t g hg
    show K.re f (g • t) = K.re f t
    rw [hg]
  have hst : ∀ (p : ℕ) (t : K.Tup p), Finite ↥(MulAction.stabilizer Γ t) := by
    intro p t
    haveI := hstab0 (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)
    have hle : MulAction.stabilizer Γ t ≤
        MulAction.stabilizer Γ (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t) :=
      fun g hg => hre _ t g hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  refine ⟨hst, ?_⟩
  obtain ⟨R, hRfin, hR⟩ := hfin
  haveI : Finite ↥R := hRfin.to_subtype
  let V : K.Tup 1 → K.Tup 0 := fun r => K.re (fun _ : Fin 1 => (0 : Fin 2)) r
  haveI : ∀ r : ↥R, Finite ↥(MulAction.stabilizer Γ (V r.1)) := fun r => hstab0 _
  refine ⟨Nat.card (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))), ?_⟩
  intro p hp t ht
  let v : K.Tup 0 := K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t
  let e : Fin (p+1) → K.Tup 1 := fun j => K.re (![0, j] : Fin 2 → Fin (p+1)) t
  have hev : ∀ j, V (e j) = v := fun j => Subtype.ext (funext fun _ => rfl)
  let k : ↥R → Γ := fun r => if h : ∃ g : Γ, g • v = V r.1 then Classical.choose h else 1
  let gsel : Fin (p+1) → Γ := fun j => Classical.choose (hR (e j))
  have hgsel : ∀ j, gsel j • e j ∈ R := fun j => Classical.choose_spec (hR (e j))
  let rsel : Fin (p+1) → ↥R := fun j => ⟨gsel j • e j, hgsel j⟩
  have hgv : ∀ j, gsel j • v = V (rsel j).1 := by
    intro j
    show gsel j • v = gsel j • V (e j)
    rw [hev j]
  have hk : ∀ j, k (rsel j) • v = V (rsel j).1 := by
    intro j
    have hex : ∃ g : Γ, g • v = V (rsel j).1 := ⟨gsel j, hgv j⟩
    have hkj : k (rsel j) = Classical.choose hex := dif_pos hex
    rw [hkj]
    exact Classical.choose_spec hex
  have hmem : ∀ j, gsel j * (k (rsel j))⁻¹ ∈ MulAction.stabilizer Γ (V (rsel j).1) := by
    intro j
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    have h1 : (k (rsel j))⁻¹ • V (rsel j).1 = v := by
      rw [inv_smul_eq_iff]
      exact (hk j).symm
    rw [h1, hgv j]
  let φ : Fin (p+1) → Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1)) :=
    fun j => ⟨rsel j, ⟨gsel j * (k (rsel j))⁻¹, hmem j⟩⟩
  let ψ : (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))) → K.Tup 1 :=
    fun x => ((x.2 : Γ) * k x.1)⁻¹ • x.1.1
  have hψ : ∀ j, ψ (φ j) = e j := by
    intro j
    show ((gsel j * (k (rsel j))⁻¹) * k (rsel j))⁻¹ • (gsel j • e j) = e j
    rw [inv_mul_cancel_right, inv_smul_smul]
  have hinj : Function.Injective φ := by
    intro j j' hjj
    apply ht
    have h1 : e j = e j' := by rw [← hψ j, ← hψ j', hjj]
    have h2 := congrArg (fun x : K.Tup 1 => x.1 1) h1
    exact h2
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ShapiroFunctorialOfCoinductionBijective
open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.shapiro_functorial_of_coinduction_bijective :
    UpperTheory.V.Af.CohB.ToCoInj → UpperTheory.V.Af.CohB.ToCoSurj → UpperTheory.V.Af.CohB.ShapiroFun := by
  intro hi hs Γ X Y _ _ _ p hp y hy d ξ
  let e := LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩
  have he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g =
      Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap := by
    intro g
    refine LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)
    change funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1
    rw [map_mul]
    rfl
  let i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ)) :=
    Rep.mkIso (Representation.Equiv.mk e he)
  unfold totCoh
  congr 1
  funext q
  exact (((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫
    groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupsCommensurable
open UpperTheory.V.Af UpperTheory.V.Af.CohB GlobalTheory.CuspRep in
private theorem relIndex_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem comm_comap {G H : Type} [Group G] [Group H] (f : H →* G) (U K : Subgroup G)
    (h : U.relIndex K ≠ 0) : (U.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h0
  exact h (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le f K) h0)

theorem UpperTheory.arithmetic_subgroups_commensurable :
    UpperTheory.V.Af.CohB.ArithComm := by
  intro F _ _ n Γ hΓ g U hUo hUc
  set U' := U.comap (MulAut.conj g⁻¹).toMonoidHom with hU'
  have hc : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g⁻¹ * x * g) := by fun_prop
  have hc' : Continuous (fun x : GL (Fin n) (GlobalTheory.CuspRep.Af F) => g * x * g⁻¹) := by fun_prop
  have e1 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g⁻¹ * x * g) ⁻¹' U := by
    ext x; simp [hU']
  have e2 : (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) = (fun x => g * x * g⁻¹) '' U := by
    rw [e1]
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  have ho : IsOpen (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e1 ▸ hUo.preimage hc
  have hk : IsCompact (U' : Set (GL (Fin n) (GlobalTheory.CuspRep.Af F))) := e2 ▸ hUc.image hc'
  have h1 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact U' _ ho (UpperTheory.V.Af.isCompact_KLev (F := F) (n := n) le_rfl))
  have h2 := comm_comap (UpperTheory.V.Af.CohB.ratAf F n) _ _
    (relIndex_open_compact _ U' (UpperTheory.V.Af.isOpen_KLev (F := F) (n := n) le_rfl) hk)
  have h3 : Γ.relIndex ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)) ≠ 0 := fun h0 =>
    hΓ.index_ne_zero (by
      rw [← Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_eq_zero_of_le_right le_top h0)
  have h4 := Subgroup.relIndex_inf_ne_zero h3 h1
  have h5 : ((UpperTheory.V.Af.KLev F n 1).comap (UpperTheory.V.Af.CohB.ratAf F n)).relIndex (Γ ⊓ UpperTheory.V.Af.CohB.arith g U) ≠ 0 :=
    fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  first
    | exact ⟨h4, h5⟩
    | exact ⟨⟨h4⟩, ⟨h5⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsInjective
open scoped Matrix

theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupLevelOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem alg_mem_Ohat {F : Type} [Field F] [NumberField F] (x : F) :
    algebraMap F (Af F) x ∈ Ohat F ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [← GlobalTheory.AdelicMatLat.algebraMap_mem_iff, GlobalTheory.AdelicMatLat.mem_intAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem UpperTheory.arithmetic_subgroup_level_one :
    UpperTheory.V.Af.CohB.ArithOne := by
  intro F _ _ n
  ext g
  rw [Subgroup.mem_comap, mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    rw [← map_inv] at hb
    have ha' : ∀ a b, ∃ r : 𝓞 F, (r : F) = g a b := fun a b => (alg_mem_Ohat _).1 (ha a b)
    have hb' : ∀ a b, ∃ r : 𝓞 F, (r : F) = (g⁻¹ : GL (Fin n) F) a b := fun a b => (alg_mem_Ohat _).1 (hb a b)
    choose A hA using ha'
    choose B hB using hb'
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F)) := fun x y h =>
      Matrix.ext fun a b => IsFractionRing.injective (𝓞 F) F (congrFun (congrFun h a) b)
    have eA : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of A) = g.val :=
      Matrix.ext fun a b => hA a b
    have eB : RingHom.mapMatrix (m := Fin n) (algebraMap (𝓞 F) F) (Matrix.of B) = (g⁻¹).val :=
      Matrix.ext fun a b => hB a b
    refine ⟨⟨Matrix.of A, Matrix.of B, inj ?_, inj ?_⟩, Units.ext eA⟩
    · rw [map_mul, map_one, eA, eB]; exact g.mul_inv
    · rw [map_mul, map_one, eA, eB]; exact g.inv_mul
  · rintro ⟨k, rfl⟩
    have h1 : ∀ (k : GL (Fin n) (𝓞 F)) a b, (CohB.ratAf F n
        (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F) k)) a b ∈ Ohat F :=
      fun k a b => (alg_mem_Ohat _).2 ⟨k a b, rfl⟩
    refine ⟨h1 k, fun a b => ?_, fun a b => ⟨_, ?_, by rw [Nat.cast_one]; exact (one_mul _).symm⟩⟩
    · rw [← map_inv, ← map_inv]; exact h1 _ a b
    · refine sub_mem (h1 k a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelSubgroupIndexBoundOfCardOhat
private theorem index_closed_dyadic_subgroup {G H A : Type} [Group G] [Group H] [Group A] [Finite A] (j : G →* H) (hj : Function.Injective j)
    (f : G →* A) (K : Subgroup G) :
    (f.ker.map j).relIndex (K.map j) ≠ 0 ∧ (f.ker.map j).relIndex (K.map j) ≤ Nat.card A := by
  rw [Subgroup.relIndex_map_map_of_injective _ _ hj]
  have h1 : f.ker.relIndex ⊤ = Nat.card f.range := by rw [Subgroup.relIndex_top_right, Subgroup.index_ker]
  have h0 : f.ker.relIndex ⊤ ≠ 0 := by rw [h1]; exact Nat.card_pos.ne'
  refine ⟨fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top h0).trans ?_
  rw [h1]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

private theorem card_GL_le (R : Type) [CommRing R] [Finite R] (n : ℕ) :
    Nat.card (GL (Fin n) R) ≤ Nat.card R ^ (n * n) := by
  have h : Nat.card (GL (Fin n) R) ≤ Nat.card (Fin n → Fin n → R) :=
    Nat.card_le_card_of_injective (fun g : GL (Fin n) R => (g.val : Fin n → Fin n → R))
      fun x y h => Units.ext h
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul] at h
  simpa using h

theorem UpperTheory.level_subgroup_index_bound_of_card_ohat :
    UpperTheory.V.Af.CohB.CardOhat → UpperTheory.V.Af.CohB.KLevIdx := by
  intro hC F _ _ n N hN
  obtain ⟨hfin, hcard⟩ := hC F N hN
  have hj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (UpperTheory.V.Af.Ohat F).subtype) := fun x y h =>
    Units.ext (Matrix.ext fun a b => Subtype.ext
      (congrArg (fun z : GL (Fin n) (GlobalTheory.CuspRep.Af F) => z a b) h))
  haveI : Finite (Matrix (Fin n) (Fin n) (↥(UpperTheory.V.Af.Ohat F) ⧸ Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})) :=
    inferInstanceAs (Finite (Fin n → Fin n → _))
  haveI : Finite (GL (Fin n) (↥(UpperTheory.V.Af.Ohat F) ⧸ Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})) :=
    Finite.of_injective _ Units.val_injective
  obtain ⟨h0, h1⟩ := index_closed_dyadic_subgroup _ hj
    (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})))
    (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}))).ker
  refine ⟨h0, h1.trans ((card_GL_le _ n).trans ?_)⟩
  rw [pow_mul (N : ℕ)]
  exact Nat.pow_le_pow_left hcard _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitBoundOfShapiroFunctorial
theorem UpperTheory.orbit_bound_of_shapiro_functorial :
    UpperTheory.V.Af.CohB.ShapiroFun → UpperTheory.V.Af.CohB.OrbBound := by
  intro h Γ Y _ _ y hB
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, ?_⟩
  intro X _ p hp hsurj D hD d ξ
  rw [h Γ X Y p hp y hsurj d ξ]
  refine (hc _).trans ?_
  have h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D := hD
  have hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y) :=
    Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt Cardinal.natCast_lt_aleph0)
  have hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) =
      Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d := by
    change Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _
    rw [rank_pi]
    simp only [rank_fun', Fintype.card_fin]
    rw [Cardinal.sum_const']
  rw [hr]
  push_cast
  rw [mul_assoc]
  gcongr
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardOhatQuotientNatCast
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

private theorem card_int_mod (F : Type) [Field F] [NumberField F] (N : ℕ) :
    Nat.card (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) = N ^ Module.finrank ℚ F := by
  have h := Ideal.absNorm_span_singleton (N : 𝓞 F)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  rw [h, ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow,
    Int.natAbs_natCast]

theorem UpperTheory.card_ohat_quotient_natCast :
    UpperTheory.V.Af.CohB.CardOhat := by
  intro F _ _ N hN
  have hm : ∀ x : Af F, x ∈ Ohat F ↔ x ∈ Formalism.UG.intAd F := fun x => by
    rw [Ohat, Subring.mem_iInf]
    rfl
  let f : 𝓞 F →+* ↥(Ohat F) :=
    ((algebraMap F (Af F)).comp (algebraMap (𝓞 F) F)).codRestrict (Ohat F) fun a =>
      mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F a)
  let g : (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) →+* (↥(Ohat F) ⧸ Ideal.span {(N : ↥(Ohat F))}) :=
    Ideal.quotientMap _ f (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨s, c, hc, e⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod N hN y.1 ((hm _).1 y.2)
    refine ⟨Ideal.Quotient.mk _ s, ?_⟩
    change Ideal.Quotient.mk _ (f s) = _
    refine (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨c, (hm _).2 hc⟩, Subtype.ext ?_⟩)).symm
    change y.1 - algebraMap F (Af F) (algebraMap (𝓞 F) F s) = (N : Af F) * c
    exact sub_eq_of_eq_add' e
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Nat.finite_of_card_ne_zero (by rw [card_int_mod]; exact pow_ne_zero _ (by omega))
  exact ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans (card_int_mod F N).le⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsSurjective
open scoped Matrix in
theorem UpperTheory.cohomology_to_coinvariants_surjective :
    UpperTheory.V.Af.CohB.ToCoSurj := by
  intro Γ X Y _ _ _ p hp y h d ξ F
  choose c hc using h
  have hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y := fun x => by
    change p (c x • x) = y
    rw [hp, hc]
  have key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 →
      ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z := by
    intro g g' z z' hz
    have hz' : z.1 = (g * g'⁻¹) • z'.1 := by rw [mul_smul, ← hz, smul_inv_smul]
    have hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y := by
      have h1 : p z.1 = y := z.2
      have h2 : p z'.1 = y := z'.2
      rw [hz', hp, h2] at h1
      exact h1
    have h3 := congrFun (F.2 ⟨_, hs⟩ g') z
    have h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z' := by
      apply Subtype.ext
      change (g * g'⁻¹)⁻¹ • z.1 = z'.1
      rw [hz', inv_smul_smul]
    change F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3
    rw [h4, inv_mul_cancel_right] at h3
    rw [h3, map_mul, Matrix.mulVec_mulVec]
  refine ⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩
  apply Subtype.ext
  funext g z
  rw [UpperTheory.V.Af.CohB.toCo_apply]
  exact key g _ z _ (by simp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiberCard
theorem UpperTheory.adelic_cohomology_fiber_card :
    UpperTheory.V.Af.CohB.FibCard := by
  intro G _ U U' h hne y
  set e := Subgroup.quotientEquivProdOfLE h with he
  have key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  have e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U') :=
    { toFun := fun x => (e x.1).2
      invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change e.symm (y, (e x).2) = x
        rw [← hx, ← key]
        exact e.symm_apply_apply x
      right_inv := by
        intro b
        change (e (e.symm (y, b))).2 = b
        rw [Equiv.apply_symm_apply] }
  rw [Cardinal.mk_congr e1]
  have : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hne
  rw [← Nat.cast_card]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicDoubleCosets
open NumberField IsDedekindDomain GlobalTheory.CuspRep

private theorem ohat_of {F : Type} [Field F] [NumberField F] {x : Af F} (hx : x ∈ PIW.ClassFinD.Ohat F) :
    x ∈ UpperTheory.V.Af.Ohat F :=
  UpperTheory.V.Af.mem_Ohat.2 (GroundTheory.Global.mem_integralFiniteAdeles.2 hx)

theorem UpperTheory.finite_adelic_double_cosets :
    UpperTheory.V.Af.CohB.FinDC := by
  intro F _ _ n
  obtain ⟨S, hS⟩ := PIW.ClassFinD.borelKGL_of GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles PIW.ClassFinD.idele_class_finite F n
  refine ⟨S, fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS g
  refine ⟨γ, s, hs, k, UpperTheory.V.Af.mem_KLev.2 ⟨fun a b => ohat_of (hk.1 a b), fun a b => ohat_of (hk.2 a b),
    fun a b => ⟨_, sub_mem (ohat_of (hk.1 a b)) (ohat_of (PIW.ClassFinD.matInt_one F n a b)), ?_⟩⟩, hx⟩
  rw [Nat.cast_one, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologySumBound
private theorem UpperTheory.V.Af.CohB.cardSum_eq (I : Type) [hI : Fintype I] :
    ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i := by
  refine Fintype.induction_empty_option (P := fun I _ => ∀ f : I → Cardinal.{0}, Cardinal.sum f = ∑ i, f i)
    ?_ ?_ ?_ I
  · intro α β _ e h f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Equiv.sum_comp e f, ← h]
    exact Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := fun b => (f b).out) e).symm
  · intro f
    simp [Cardinal.sum]
  · intro α _ h f
    rw [Fintype.sum_option, ← h]
    have e0 : (Σ o : Option α, (f o).out) ≃ (f none).out ⊕ (Σ a : α, (f (some a)).out) :=
      { toFun := fun x => match x with
          | ⟨none, y⟩ => Sum.inl y
          | ⟨some a, y⟩ => Sum.inr ⟨a, y⟩
        invFun := fun x => match x with
          | Sum.inl y => ⟨none, y⟩
          | Sum.inr ⟨a, y⟩ => ⟨some a, y⟩
        left_inv := by rintro ⟨_ | a, y⟩ <;> rfl
        right_inv := by rintro (y | ⟨a, y⟩) <;> rfl }
    have e := Cardinal.mk_congr e0
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_out] at e
    exact e

open CategoryTheory in
theorem UpperTheory.cohomology_sum_bound :
    UpperTheory.V.Af.CohB.SumBound := by
  intro Γ I _ _ A B π ι h q
  let F : Rep.{0} ℂ Γ ⥤ ModuleCat.{0} ℂ :=
    groupCohomology.cochainsFunctor ℂ Γ ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) q
  have hF : ∑ i, F.map (π i) ≫ F.map (ι i) = 𝟙 (F.obj A) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← F.map_id, ← h, F.map_sum]
    simp only [Functor.map_comp]
  change Module.rank ℂ (F.obj A) ≤ ∑ i, Module.rank ℂ (F.obj (B i))
  let φ : F.obj A →ₗ[ℂ] (∀ i, F.obj (B i)) := LinearMap.pi fun i => (F.map (π i)).hom
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := congrArg (fun f => ModuleCat.Hom.hom f x) hF
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : (F.map (π i)).hom x = 0 := congrFun hx i
    rw [h2, map_zero]
  have h3 := LinearMap.rank_le_of_injective φ hφ
  rw [rank_pi] at h3
  rw [← UpperTheory.V.Af.CohB.cardSum_eq]
  simpa using h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyBoundedEquiv
theorem UpperTheory.cohomology_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv := by
  intro Γ Γ' _ _ ⟨φ⟩ ⟨c, hc⟩
  refine ⟨c, fun A => ?_⟩
  have key := hc (Rep.res φ.toMonoidHom A)
  have heq : ∀ q, Module.rank ℂ (groupCohomology (Rep.res φ.toMonoidHom A) q) =
      Module.rank ℂ (groupCohomology A q) := fun q =>
    ((groupCohomology.mapIso φ (LinearEquiv.refl ℂ A.V) (fun g => rfl) q).toLinearEquiv).rank_eq
  unfold UpperTheory.V.Af.CohB.totCoh at key ⊢
  simp only [heq] at key
  exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbsoluteBoundOfPartialBoundOfOrbitBound
open UpperTheory.V.Af.CohB in
theorem UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound :
    UpperTheory.V.Af.CohB.PartBound → UpperTheory.V.Af.CohB.OrbBound → UpperTheory.V.Af.CohB.AbsBound := by
  intro hP hO Γ Y _ _ hT hB
  obtain ⟨T, hT⟩ := hT
  choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)
  refine ⟨∑ t, cf t, ?_⟩
  intro X _ p hp D hD d ξ
  let r : MulAction.orbitRel.Quotient Γ Y → ↥T := fun q =>
    ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩
  let cl : X → ↥T := fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))
  have hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x := by
    intro γ x
    simp only [cl, hp]
    congr 1
    exact Quotient.sound ⟨γ, rfl⟩
  refine (hP Γ X ↥T cl hcl d ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1 := by
    rintro ⟨x, hx⟩
    change cl x = t at hx
    obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))
    refine ⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩
    rw [mul_smul]
    simp only at hh ⊢
    rw [hh]
    exact congrArg Subtype.val hx
  refine hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D
    (le_trans (Cardinal.mk_le_of_injective
      (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1}))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))) (hD t.1)) d ξ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiniteOrbitBound
theorem UpperTheory.adelic_cohomology_finite_orbit_bound :
    UpperTheory.V.Af.CohB.FinOrbAbs := by
  classical
  intro G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩
  haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero
  haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU
  refine ⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image
    (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩
  obtain ⟨h, t, ht, k, hk, rfl⟩ := hT g
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ h⁻¹
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
  have huU : (((u : K) : G))⁻¹ ∈ U := U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)
  refine ⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩,
    _, huU, ?_⟩
  · simp [ht]
  · simp only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul]
    group
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyRankEqHomologyRank
open CategoryTheory

theorem UpperTheory.cohomology_rank_eq_homology_rank :
    UpperTheory.V.Af.CohB.RankHomology := by
  intro C q
  have h1 : Function.Surjective (C.homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h2 : Function.Injective (C.iCycles q).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (LinearMap.rank_le_of_surjective _ h1).trans (LinearMap.rank_le_of_injective _ h2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartBoundOfSumBound
private theorem card_sum_finset_swap {I : Type} (s : Finset I) (f : ℕ → I → Cardinal.{0}) :
    (Cardinal.sum fun q => ∑ i ∈ s, f q i) = ∑ i ∈ s, Cardinal.sum fun q => f q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Cardinal.sum_add_distrib', ih]

theorem UpperTheory.cohomology_part_bound_of_sum_bound :
    UpperTheory.V.Af.CohB.SumBound → UpperTheory.V.Af.CohB.PartSplit → UpperTheory.V.Af.CohB.PartBound := by
  intro h1 h2 Γ X I _ _ _ c hc d ξ
  obtain ⟨π, ι, h⟩ := h2 Γ X I c hc d ξ
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [← card_sum_finset_swap]
  exact Cardinal.sum_le_sum _ _ fun q => h1 Γ I _ _ π ι h q
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartSplit
open CategoryTheory UpperTheory.V.Af.CohB

theorem UpperTheory.cohomology_part_split :
    UpperTheory.V.Af.CohB.PartSplit := by
  classical
  intro Γ X I _ _ _ c hc d ξ
  let p : ∀ i, (X → Fin d → ℂ) →ₗ[ℂ] (↥(part c hc i) → Fin d → ℂ) := fun i =>
    { toFun := fun f x => f x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : ∀ i, (↥(part c hc i) → Fin d → ℂ) →ₗ[ℂ] (X → Fin d → ℂ) := fun i =>
    { toFun := fun f x => if h : c x = i then f ⟨x, h⟩ else 0
      map_add' := fun f g => funext fun x => by
        by_cases h : c x = i <;> simp [h]
      map_smul' := fun a f => funext fun x => by
        by_cases h : c x = i <;> simp [h] }
  refine ⟨fun i => Rep.ofHom ⟨p i, fun γ => ?_⟩, fun i => Rep.ofHom ⟨e i, fun γ => ?_⟩, ?_⟩
  · refine LinearMap.ext fun f => funext fun x => ?_
    rfl
  · refine LinearMap.ext fun f => funext fun x => ?_
    change (if h : c x = i then (funRep ↥(part c hc i) ξ γ f) ⟨x, h⟩ else 0) =
      Matrix.mulVec (ξ γ) (if h : c (γ⁻¹ • x) = i then f ⟨γ⁻¹ • x, h⟩ else 0)
    by_cases h : c x = i
    · rw [dite_eq_left h, dite_eq_left ((hc _ _).trans h)]
      rfl
    · rw [dite_eq_right h, dite_eq_right (fun h' => h ((hc _ _).symm.trans h')), Matrix.mulVec_zero]
  · apply Rep.hom_ext
    rw [Rep.sum_hom]
    apply Representation.IntertwiningMap.ext
    refine LinearMap.ext fun f => funext fun x => ?_
    rw [Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply, Finset.sum_apply]
    change ∑ i, (if h : c x = i then f x else 0) = f x
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CohBoundFree
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.BddArith
open NumberField

open CategoryTheory UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_cx : BddCx := by
  intro Γ I _ _ K hx ho hs
  obtain ⟨hst, D, hD⟩ := UpperTheory.adelic_rep_dimension_bounded Γ I K (ho 1) hs
  obtain ⟨h0, h1, h2⟩ := UpperTheory.exactCOf_of_exactBase UpperTheory.exactBase_integral_to_complex Γ I K hx
  obtain ⟨P, hP, he⟩ := UpperTheory.repResolution_exists Γ (fun p => PC Γ (K.Tup p)) K.d (augC Γ (K.Tup 0))
    (fun p => UpperTheory.projPerm_of_liftEquiv UpperTheory.pins_of_closed_subgroup_padic_character_inv Γ _ (hst p)) h0 h1 h2
  obtain ⟨a0, aD⟩ := UpperTheory.rep_hom_alternating_sum_eq_zero Γ I K
  obtain ⟨e, he1, he2⟩ := he K.alt (by rw [a0, Category.id_comp]) (UpperTheory.altChain_of_permSplit UpperTheory.perm_split_fin_succ Γ I K)
  refine UpperTheory.adelic_rep_bounded_of_degree_bounded Γ (fun q => ?_) ⟨D, fun q hq A => UpperTheory.ext_vanishing_of_resolution_endo Γ P e he1 q (he2 q (aD q (hD q hq))) A⟩
  obtain ⟨c, hc⟩ := UpperTheory.permutation_module_homology_rank Γ _ (ho q)
  exact ⟨c, fun A => (UpperTheory.rankCohHom_of_rankHomology UpperTheory.cohomology_rank_eq_homology_rank Γ P q _ (hP q) A).trans (hc A)⟩

open UpperTheory.V.Af.BA in
private theorem UpperTheory.V.Af.bddArith_fix : BddFix :=
  have hg : GoodRe := UpperTheory.good_real_form_of_real_part_of_real_involution UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant
  have ha : ActRe := UpperTheory.real_structure_action_of_real_involution UpperTheory.adelic_realPart_invariant
  have hs : SpanRe := UpperTheory.real_span_of_good_real_form UpperTheory.adelicBaseChange_realPart UpperTheory.adelic_realPart_invariant hg
  UpperTheory.bddFix_of_bounded_complex UpperTheory.V.Af.bddArith_cx hg ha hs
    (UpperTheory.orbRe_of_minimal_vector_stabilizer UpperTheory.fixedOrbits_finite_representatives UpperTheory.adelic_realPart_invariant ha hs UpperTheory.minimal_orbit_representatives UpperTheory.minimal_vector_stabilizer_property) UpperTheory.minimal_vector_stabilizer_property

theorem UpperTheory.V.Af.bddArith :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Subgroup.Commensurable Γ (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)).range → UpperTheory.V.Af.CohB.Bdd ↥Γ := by
  intro F _ _ hF n Γ hΓ
  have hO : UpperTheory.V.Af.CohB.Bdd (GL (Fin n) (𝓞 F)) := by
    rcases hF with hF | hF
    · exact UpperTheory.bounded_complex_of_bounded_simplicial_complex UpperTheory.V.Af.bddArith_cx F n
    · obtain ⟨L, _, _, _, i, σ, hσ, hi, hf⟩ := UpperTheory.exists_CM_integral_of_exists_CM UpperTheory.exists_CM_extension F
      exact UpperTheory.cohomology_bounded_equiv _ _ (UpperTheory.building_fixed_points_equiv _ _ i σ n hi hf) (UpperTheory.V.Af.bddArith_fix L n σ hσ)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap (𝓞 F) F)) := by
    intro g k e
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact RingOfIntegers.coe_injective (congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F) a b) e)
  exact UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv UpperTheory.cohomology_bounded_equiv UpperTheory.adelic_rep_bounded_of_subgroup_bounded (UpperTheory.adelic_rep_bounded_over_of_sum_bound_coind_retract UpperTheory.cohomology_sum_bound UpperTheory.coind_retract_of_finite_index) _ Γ _ hΓ
    (UpperTheory.cohomology_bounded_equiv _ _ ⟨MonoidHom.ofInjective hinj⟩ hO)
end

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.CuspRep CategoryTheory UpperTheory.V.Af UpperTheory.V.Af.CohB

@[reducible] private def act {G H : Type} [Group G] [Group H] (ι : H →* G) (Γ : Subgroup H) (U : Subgroup G) :
    MulAction ↥Γ (G ⧸ U) := MulAction.compHom _ (ι.comp Γ.subtype)

private theorem gen (hE : BddEquiv) (hA : AbsBound) (hF : FibCard) {G H : Type} [Group G] [Group H] (ι : H →* G)
    (Γ : Subgroup H) (U : Subgroup G) (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ u ∈ U, g = ι γ * t * u)
    (S : G → Subgroup H) (hS : ∀ g γ, γ ∈ S g ↔ g⁻¹ * ι γ * g ∈ U) (hB : ∀ g, Bdd ↥(Γ ⊓ S g)) :
    ∃ c : ℕ, ∀ U' : Subgroup G, U' ≤ U → U'.relIndex U ≠ 0 → ∀ D : ℕ, U'.relIndex U ≤ D →
      ∀ (d : ℕ) (ξ : ↥Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (@funRep ↥Γ _ (G ⧸ U') (act ι Γ U') d ξ)) ≤ (c * D * d : ℕ) := by
  classical
  letI := act ι Γ U
  have hsm : ∀ (γ : ↥Γ) (g : G), γ • (g : G ⧸ U) = ((ι γ.1 * g : G) : G ⧸ U) := fun _ _ => rfl
  obtain ⟨T, hT'⟩ := hT
  obtain ⟨c, hc⟩ := hA ↥Γ (G ⧸ U)
    ⟨T.image (↑), fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨γ, hγ, t, ht, u, hu, rfl⟩ := hT' g
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, Finset.mem_image.2 ⟨t, ht, ?_⟩⟩
      rw [hsm, QuotientGroup.eq]
      simpa [mul_assoc] using hu⟩
    (fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have e : MulAction.stabilizer ↥Γ (g : G ⧸ U) = (Γ ⊓ S g).subgroupOf Γ := by
        ext γ
        rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hS,
          mul_assoc]
        exact ⟨fun h => ⟨γ.2, h⟩, fun h => h.2⟩
      exact hE ↥(Γ ⊓ S g) _
        ⟨((MulEquiv.subgroupCongr e).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm⟩ (hB g))
  refine ⟨c, fun U' hle h0 D hD d ξ => ?_⟩
  letI := act ι Γ U'
  exact hc (G ⧸ U') (Subgroup.quotientMapOfLE hle)
    (fun γ x => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rfl) D
    (fun y => by rw [hF _ _ _ hle h0 y]; exact_mod_cast hD) d ξ

private theorem levelRep_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F))
    (U : Subgroup (GL (Fin n) (Af F))) {d : ℕ} (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    levelRep Γ U ξ = @funRep ↥Γ _ (GL (Fin n) (Af F) ⧸ U) (act (ratAf F n) Γ U) d (ξ.comp Γ.subtype) := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun f => funext fun x => ?_
  change ξ γ *ᵥ f ((ratAf F n γ.1)⁻¹ • x) = ξ γ *ᵥ f ((ratAf F n (γ.1)⁻¹) • x)
  rw [map_inv]

private theorem cohBound_of (hE : BddEquiv) (hA : AbsBound) (hF : FibCard)
    (hO : FinOrbAbs) (hI : KLevIdx) (hD : FinDC) (h1 : ArithOne) (hC : ArithComm) :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) := by
  intro F _ _ hF' n Γ hΓ
  obtain ⟨c, hc⟩ := gen hE hA hF (ratAf F n) Γ (KLev F n 3)
    (hO _ _ (ratAf F n) Γ (KLev F n 3) (KLev F n 1) hΓ (hI F n 3 (by norm_num)).1 (hD F n))
    (fun g => arith g (KLev F n 3)) (fun g γ => mem_arith) fun g => (bddArith F hF' n _
      (h1 F n ▸ hC F n Γ hΓ g _ (by apply isOpen_KLev; norm_num) (by apply isCompact_KLev; norm_num)))
  refine ⟨c * 3 ^ (Module.finrank ℚ F * (n * n)), Module.finrank ℚ F * (n * n), fun M hM d ξ => ?_⟩
  have hle : KLev F n (3 * M) ≤ KLev F n 3 := KLev_le_of_dvd (dvd_mul_right 3 M)
  have hle1 : KLev F n 3 ≤ KLev F n 1 := KLev_le_of_dvd (one_dvd 3)
  obtain ⟨hi0, hi⟩ := hI F n (3 * M) (by omega)
  have hr0 : (KLev F n (3 * M)).relIndex (KLev F n 3) ≠ 0 := fun h => hi0 (Subgroup.relIndex_eq_zero_of_le_right hle1 h)
  have hr : (KLev F n (3 * M)).relIndex (KLev F n 3) ≤ (3 * M) ^ (Module.finrank ℚ F * (n * n)) :=
    (Subgroup.relIndex_le_of_le_right hle1 hi0).trans hi
  have key := hc _ hle hr0 _ hr d (ξ.comp Γ.subtype)
  rw [← levelRep_eq] at key
  have e : c * 3 ^ (Module.finrank ℚ F * (n * n)) * M ^ (Module.finrank ℚ F * (n * n)) * d =
      c * (3 * M) ^ (Module.finrank ℚ F * (n * n)) * d := by rw [mul_pow, mul_assoc c]
  rw [e]
  exact key

theorem UpperTheory.V.Af.cohBoundFree :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) :=
  cohBound_of UpperTheory.cohomology_bounded_equiv
    (UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound (UpperTheory.cohomology_part_bound_of_sum_bound UpperTheory.cohomology_sum_bound UpperTheory.cohomology_part_split) (UpperTheory.orbit_bound_of_shapiro_functorial (UpperTheory.shapiro_functorial_of_coinduction_bijective UpperTheory.cohomology_to_coinvariants_injective UpperTheory.cohomology_to_coinvariants_surjective)))
    UpperTheory.adelic_cohomology_fiber_card UpperTheory.adelic_cohomology_finite_orbit_bound (UpperTheory.level_subgroup_index_bound_of_card_ohat UpperTheory.card_ohat_quotient_natCast) UpperTheory.finite_adelic_double_cosets UpperTheory.arithmetic_subgroup_level_one UpperTheory.arithmetic_subgroups_commensurable
end

