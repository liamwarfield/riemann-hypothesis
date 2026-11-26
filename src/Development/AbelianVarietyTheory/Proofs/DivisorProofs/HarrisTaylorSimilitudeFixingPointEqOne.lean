module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTQuotRigid

theorem objMap_comp_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem eq_one_of_fixes_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
      (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
      IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  intro p _ D R _ b N h M hN hNp hM X s s₁ u lev hlev ρ hρ k _ _ y a hya
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨-, -, m, hm⟩ := hρ a
  obtain ⟨o, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N X (Sp k) s y u
  obtain ⟨c, hc⟩ := objMap_comp_φ n m
  have key : ∀ (f : Sp k ⟶ X), f = y → ∀ mm : ObjMap o u f, mm.φ = n.φ := by
    intro f hf mm
    subst hf
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ mm n
  have hφ : n.φ ≫ m.φ = n.φ := by rw [← hc]; exact key _ hya c

  have hx : ∀ x, y ≫ (sympTwist a lev x).left = y ≫ (lev x).left := by
    intro x
    have ht : (y ≫ (sympTwist a lev x).left) ≫ u.A.hom = 𝟙 (Sp k) ≫ y := by
      rw [Category.assoc, Over.w]
      rfl
    have hσ := n.cart.1.lift_fst (y ≫ (sympTwist a lev x).left) (𝟙 _) ht
    have e1 : (y ≫ (sympTwist a lev x).left) ≫ m.φ = y ≫ (lev x).left := by
      rw [Category.assoc, hm x, ← Category.assoc, hya]
    rw [← e1, ← hσ, Category.assoc, hφ]

  let β : cycAway M →+* k := (Spec.preimage (y ≫ s₁)).hom
  have hβ : y ≫ s₁ = spMap β := by
    change y ≫ s₁ = Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ s₁)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hpow : β (zetaAway M) ^ M = 1 := by rw [← map_pow, zetaAway_pow_self hM.ne', map_one]
  let z : kˣ := Units.ofPowEqOne _ M hpow hM.ne'
  have hcl := (hlev.2.2 k y β z hβ rfl).1
  have hunit : ∀ x, (toUnit (Over.mk y) ≫ lev x).left = y ≫ (lev x).left := by
    intro x
    rw [Over.comp_left]
    congr 1
  have hfix : ∀ x, (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x) =
      reduceMod M x := by
    intro x
    set c := liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))
    have hsame : toUnit (Over.mk y) ≫ lev c = toUnit (Over.mk y) ≫ lev x := by
      ext1
      rw [hunit, hunit]
      exact hx x
    have hsplit : lev c = lev (c - x) * lev x := by rw [← hlev.1, sub_add_cancel]
    have h1 : toUnit (Over.mk y) ≫ lev (c - x) = 1 := by
      rw [hsplit, comp_mul] at hsame
      exact mul_eq_right.1 hsame
    obtain ⟨d, hd⟩ := (hcl (c - x)).1 h1
    have hr : reduceMod M c = reduceMod M x := by
      have : c = x + M • d := by rw [← hd]; abel
      rw [this]
      funext i
      simp [reduceMod]
    exact (reduceMod_liftMod _).symm.trans hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := hfix (liftMod v)
  rw [reduceMod_liftMod] at this
  exact this

end GlobalTheory.HTQuotRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  first | (exact @GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (exact GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (intros; apply GlobalTheory.HTQuotRigid.eq_one_of_fixes_point  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.DimBasic

theorem dim_image {W T : Type*} [TopologicalSpace W] [TopologicalSpace T] {e : W → T}
    (he : Topology.IsEmbedding e) (S : Set W) :
    topologicalKrullDim (e '' S) = topologicalKrullDim S := by
  have h := topologicalKrullDim_eq_of_isEmbedding (he.comp Topology.IsEmbedding.subtypeVal)
    (Z := e '' S) (by rw [Set.range_comp, Subtype.range_coe])
  exact h

theorem dim_closure_eq_zero_iff {T : Type*} [TopologicalSpace T] [T0Space T] (x : T) :
    topologicalKrullDim (closure ({x} : Set T)) = 0 ↔ IsClosed ({x} : Set T) := by
  constructor
  · intro h
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
      (show Order.krullDim (IrreducibleCloseds (closure ({x} : Set T))) ≤ 0 from h.le)
    refine closure_subset_iff_isClosed.1 fun w hw => ?_
    let s : closure ({x} : Set T) := ⟨x, subset_closure rfl⟩
    let t : closure ({x} : Set T) := ⟨w, hw⟩
    have hst : s ⤳ t := Topology.IsInducing.subtypeVal.specializes_iff.1
      (specializes_iff_mem_closure.2 hw)
    let A : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
    have hBA : B ≤ A := hmax A hAB
    have hts : t ⤳ s := specializes_iff_closure_subset.2 hBA
    have e := (hst.antisymm hts).eq
    exact Set.mem_singleton_iff.2 (congrArg Subtype.val e).symm
  · intro h
    rw [h.closure_eq]
    have : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
    let pt : ({x} : Set T) := ⟨x, rfl⟩
    have : Nonempty (IrreducibleCloseds ({x} : Set T)) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    refine le_antisymm (Order.krullDim_nonpos_iff_forall_isMax.2 fun a b _ => ?_) Order.krullDim_nonneg
    intro y _
    have ha : (a : Set ({x} : Set T)) = Set.univ := a.isIrreducible.nonempty.eq_univ
    show y ∈ (a : Set ({x} : Set T))
    rw [ha]; trivial

theorem ringKrullDim_le_one (k : Type) [CommRing k] [Module.Finite ℤ k] : ringKrullDim k ≤ 1 := by
  have : Algebra.IsIntegral ℤ k := inferInstance
  calc ringKrullDim k ≤ ringKrullDim ℤ :=
        Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap ℤ k))
          fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem dim_pspace_le (k : Type) [CommRing k] [Module.Finite ℤ k] (N : ℕ) :
    topologicalKrullDim (PSpace k N) ≤ (N + 1 : ℕ) := by
  have := IsNoetherianRing.of_finite ℤ k
  have hk := ringKrullDim_le_one k
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
  refine ⟨_, (ProjSpace.chart k N i).isOpen, hi, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι k N i).isOpenEmbedding.isEmbedding
    (congrArg SetLike.coe (ProjSpace.opensRange_chartι k N i))]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (R := MvPolynomial {j // j ≠ i} k)).trans_le ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp
  exact (add_le_add_left hk _).trans_eq (add_comm _ _)

theorem finite_residueField (k : Type) [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) (hp : IsProjOver p) {x : X} (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨N, j, _, hj⟩ := hp
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hf : IsFinite (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ (X.residueField x)), RingHom.finite_algebraMap] at hf
  obtain ⟨ℓ, _⟩ := CharP.exists (X.residueField x)
  rcases CharP.char_is_prime_or_zero (X.residueField x) ℓ with hℓ | rfl
  · have := Fact.mk hℓ
    let := ZMod.algebra (X.residueField x) ℓ
    have := Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (X.residueField x)
    exact Module.finite_of_finite (ZMod ℓ)
  · have := CharP.charP_to_charZero (X.residueField x)
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := X.residueField x)
      (RingHom.injective_int _) (Field.toIsField _)) Int.not_isField

theorem hasDim_map_iff {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ) :
    HasDim (i y) d ↔ HasDim y d := by
  unfold HasDim
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq,
    dim_image i.isClosedEmbedding.isEmbedding]

theorem hasDim_genericPoint_iff (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ) :
    HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  unfold HasDim
  rw [(genericPoint_spec Y).def]
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]

end GlobalTheory.MixHt.DimBasic

namespace GlobalTheory.MixHt


open DimBasic in
theorem hasDim_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p →
    (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧
    (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧
    (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧
    (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
    (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  intro k _ X p h
  have := h.finite
  refine ⟨?_, fun x d d' hd hd' => ?_, fun x => ?_, fun x hx => finite_residueField k p h.isProjOver hx,
    fun Y i _ y d => hasDim_map_iff i y d, fun Y _ d => hasDim_genericPoint_iff Y d⟩
  · obtain ⟨N, j, _, -⟩ := h.isProjOver
    refine ⟨N + 1, fun x => ?_⟩
    have h₁ : topologicalKrullDim (closure ({x} : Set X)) ≤ (N + 1 : ℕ) :=
      (topologicalKrullDim_subspace_le X _).trans
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans (dim_pspace_le k N))
    let pt : closure ({x} : Set X) := ⟨x, subset_closure rfl⟩
    have : Nonempty (IrreducibleCloseds (closure ({x} : Set X))) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set X)) := Order.krullDim_nonneg
    unfold HasDim
    generalize topologicalKrullDim (closure ({x} : Set X)) = a at *
    induction a with
    | bot => exact absurd h₂ (by simp)
    | coe a =>
      induction a with
      | top => exact absurd h₁ (by rw [not_le]; exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _))
      | coe a => exact ⟨a, by exact_mod_cast h₁, rfl⟩
  · unfold HasDim at hd hd'
    exact_mod_cast hd.symm.trans hd'
  · unfold HasDim
    exact_mod_cast dim_closure_eq_zero_iff x

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧ (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧ (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  first | exact @GlobalTheory.MixHt.hasDim_basic | exact GlobalTheory.MixHt.hasDim_basic | (intros; apply GlobalTheory.MixHt.hasDim_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPoint
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem frame_eventually_near : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  intro F _ σ X ι _ m k E y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    (hP τ).2.2.2⟩

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.ChernCalc.frame_eventually_near | exact GlobalTheory.ChernCalc.frame_eventually_near | (intros; apply GlobalTheory.ChernCalc.frame_eventually_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanks
noncomputable section

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem finrank_iSup_of_indep {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

theorem rankOn_eq_finrank_span (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ D.host.E) :
    rankOn U Z G = finrank c.F (Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G))) := by
  have hset : (partLat U Z G : Set (cuspW Xo c U G)) =
      Submodule.inclusion (cuspOn_le U Z G) '' (latOn U Z G : Set (cuspOn U Z G)) := by
    simp [partLat]
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.inclusion_injective (cuspOn_le U Z G)) _))

end GlobalTheory.RankAdd

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem cuspOn_comap_indep {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E) :
    iSupIndep (fun Z : Comp Xo c => (cuspOn U Z G).comap (cuspW Xo c U G).subtype) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), (cuspOn U j G).comap (cuspW Xo c U G).subtype) ≤
      LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact GlobalTheory.CuspSplit.idem_mul_eq_zero (Ne.symm hj) (Submodule.mem_comap.1 hy)
  have h0 := hle hx'
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply] at h0
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x :=
        (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (Submodule.mem_comap.1 hx)).symm
    _ = 0 := h0


set_option maxHeartbeats 1000000 in
theorem rankW_eq_finsum_rankOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  intro D H Dw l Xo c r U x V dict G hU hG
  obtain ⟨-, -, -, hsup⟩ := GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)

  obtain ⟨-, ⟨s, hs⟩, htop⟩ := hG
  haveI : FiniteDimensional c.F (cuspW Xo c U G) := by
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [← htop, ← hs, Submodule.span_span_of_tower]
  set S : Comp Xo c → Submodule c.F (cuspW Xo c U G) :=
    fun Z => Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) with hSdef
  have hspan : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⨆ Z, S Z := by
    apply le_antisymm
    · rw [Submodule.span_le, ← hsup]
      intro y hy
      have hle : (⨆ Z : Comp Xo c, partLat U Z G) ≤ (⨆ Z, S Z).restrictScalars (𝓞 c.F) :=
        iSup_le fun Z z hz => (le_iSup S Z) (Submodule.subset_span hz)
      exact hle hy
    · exact iSup_le fun Z => Submodule.span_mono (by rw [← hsup]; exact le_iSup (fun Z => partLat U Z G) Z)
  have hind : iSupIndep S := (cuspOn_comap_indep U G).mono fun Z =>
    Submodule.span_le.2 fun y hy => Submodule.mem_comap.2 (GlobalTheory.CuspSplit.coe_mem_of_mem_partLat hy)
  rw [finsum_eq_sum_of_fintype]
  show finrank c.F (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))) = _
  rw [hspan, finrank_iSup_of_indep S hind]
  exact Finset.sum_congr rfl fun Z _ => (rankOn_eq_finrank_span U Z G).symm

end GlobalTheory.RankAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanksStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supLattice_rank_eq_sum_component_ranks : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  first | exact @GlobalTheory.RankAdd.rankW_eq_finsum_rankOn | exact GlobalTheory.RankAdd.rankW_eq_finsum_rankOn | (intros; apply GlobalTheory.RankAdd.rankW_eq_finsum_rankOn <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwistRank

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem rkK_eq_of_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) : Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  have hmap : (Submodule.span K (L : Set V)).map (φ : V →ₗ[K] W) = Submodule.span K (L' : Set W) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro f hf
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    · rw [Submodule.span_le]
      intro g hg
      refine ⟨a⁻¹ • (a • φ.symm g), Submodule.smul_mem _ _ (Submodule.subset_span (R := K) (hout g hg)), ?_⟩
      show φ (a⁻¹ • (a • φ.symm g)) = g
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul, φ.apply_symm_apply]
  unfold Formalism.HN.rkK
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem rankOn_twist {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) :
    rankOn U Z (G + G₀) = rankOn U Z G := by
  obtain ⟨φ, -, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := Good.exists_twist_scalar s
  exact rkK_eq_of_equiv φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _))

theorem cuspW_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') :
    cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem rankOn_congr (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : rankOn U Z G = rankOn U Z G' := by
  have e : cuspOn U Z G = cuspOn U Z G' := by rw [cuspOn, cuspOn, cuspW_congr hU h]
  unfold rankOn latOn
  rw [e]

theorem psi_nonempty : Nonempty (Psi H) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : φ (H.rt : E) = H.rt0
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨conjEmb φ, conj_mem h⟩⟩

theorem exists_twSec_par (hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {a : ℝ} (hF : FlatExistsAt U x a) (Z : Comp Xo c) (w : Psi H → ℤ) :
    Nonempty (TwSec U x Z (wtOf Dw (parWt Dw w) 0)) := by
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF Z τ).1.some
  obtain ⟨τ₀⟩ := psi_nonempty (H := H)
  have hp : HasPts U Z := (sF τ₀).hasPts
  let s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ) :=
    (FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _)
  refine ⟨TwSec.ofConst s (GlobalTheory.FlatTwisting.finite_sum_flDefect w) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq s)
    fun G hG f hf => ?_⟩
  have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl)
    (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
  rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem wtOf_zero_nat (k : ℕ) : wtOf Dw 0 (k : ℤ) = k • wtOf Dw 0 1 := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_smul]; exact wtOf_zero
  | succ k ih =>
    rw [succ_nsmul, ← ih, ← wtOf_add]
    simp

end Gen

end GlobalTheory.TwistRank

namespace GlobalTheory.TwistRank

end GlobalTheory.TwistRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_smoothOfRelativeDimension_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X →
      ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  intro K _ X _ hX
  haveI := hX.smooth
  haveI := hX.geomConnected
  haveI : ConnectedSpace X.left := GeometricallyConnected.connectedSpace X.hom X.hom.isOpenMap
  obtain ⟨x₀⟩ := (inferInstance : ConnectedSpace X.left).toNonempty
  exact exists_dim_of_preconnected X.hom x₀

end GlobalTheory.AV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExistStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists : ∀ (K : Type) [Field K] (X : Over (Sp K)) [GrpObj X], IsAbelianScheme X → ∃ g : ℕ, SmoothOfRelativeDimension g X.hom := by
  first | (exact @GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (exact GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme) | (intros; apply GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem pullback_eq_chart : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  intro M M' _ _ n n' A A' f α hf hα x i h
  have key : ∀ (j : A.ι) (hj : f x.pt ∈ (A.e j).source),
      pull (fderiv ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd) (α ⟨(j, f x.pt), hj⟩) =
        pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
    intro j hj
    have hc := hα.compat ⟨(j, f x.pt), hj⟩ ⟨(i, f x.pt), h⟩ rfl
    rw [hc, ← GlobalTheory.T.pullbackComplexFormsLinearMap_comp]
    have hx : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
    have hxt : x.crd ∈ x.ch.target := x.ch.map_source x.2
    have hopen : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source)) :=
      x.ch.isOpen_inter_preimage_symm ((A.e j).open_source.preimage hf.1)
    have hmem : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source) := by
      refine ⟨hxt, ?_⟩
      simp only [Set.mem_preimage, hx]
      exact hj
    have hd1 : DifferentiableAt ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd :=
      (hf.2 x.1.1 j).differentiableAt (hopen.mem_nhds hmem)
    have hopen2 : IsOpen ((A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source) :=
      (A.e j).isOpen_inter_preimage_symm (A.e i).open_source
    have hmem2 : A.e j (f x.pt) ∈ (A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source := by
      refine ⟨(A.e j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.e j).left_inv hj]
      exact h
    have hd2 : DifferentiableAt ℂ (A.e i ∘ (A.e j).symm) (A.e j (f x.pt)) :=
      (A.holo j i).differentiableAt (hopen2.mem_nhds hmem2)
    have hpt : (A.e j ∘ f ∘ x.ch.symm) x.crd = A.e j (f x.pt) := by
      simp only [Function.comp, hx]
    have hcomp := fderiv_comp x.crd (hpt ▸ hd2) hd1
    rw [hpt] at hcomp
    have hev : (A.e i ∘ (A.e j).symm) ∘ (A.e j ∘ f ∘ x.ch.symm) =ᶠ[𝓝 x.crd] A.e i ∘ f ∘ x.ch.symm := by
      filter_upwards [hopen.mem_nhds hmem] with v hv
      have hv' : f (x.ch.symm v) ∈ (A.e j).source := hv.2
      simp only [Function.comp, (A.e j).left_inv hv']
    rw [← hev.fderiv_eq, hcomp]
  exact key _ (A.cover (f x.pt)).choose_spec

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_pullback_eq_chart_expression : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  first | exact @GlobalTheory.CxForm.pullback_eq_chart | exact GlobalTheory.CxForm.pullback_eq_chart | (intros; apply GlobalTheory.CxForm.pullback_eq_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.MixNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ChernNull

theorem chart_null_dom {k : Type} [CommRing k] [IsDomain k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (σ : k →+* ℂ) (hσ : Function.Injective σ) {D : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hgen : genericPoint X ∉ Z) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem part_compl_null : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ _ X _ p σ hσ _ D L ε U hU
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hU
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl
    fun c => by
      have e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
        ext y
        simp [mem_ptsIn]
      rw [e]
      exact chart_null_dom σ hσ hZ hgen c

end GlobalTheory.MixNull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  first | exact @GlobalTheory.MixNull.part_compl_null | exact GlobalTheory.MixNull.part_compl_null | (intros; apply GlobalTheory.MixNull.part_compl_null <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleApprox

theorem relAmple_of_lbIso_self {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L L' : LB A.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' L) (hA : Out.RelAmple A L) : Out.RelAmple A L' := by
  have e' : LBIso L' (L.pull (𝟙 _)) := e.chartPull (chartPullId _) (Geo.Tor.chartPullPull L _ _ rfl)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 S) (φ := 𝟙 A.left)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hL hL' e' hA

variable {R : Type} [CommRing R] {R₁ : Subring R} [IsNoetherianRing R₁] {A₀ : Over (Sp R₁)} [IsProper A₀.hom]
  [Flat A₀.hom] {M : LB A₀.left} {B : Over (Sp R)} {φ : B.left ⟶ A₀.left} {N : LB B.left}

theorem exists_basicOpen (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) (x : PrimeSpectrum R) :
    ∃ r : R₁, (r : R) ∉ x.asIdeal ∧
      Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r))).obj A₀)
        (M.pull (pullback.fst A₀.hom (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r)))) := by
  let k := x.asIdeal.ResidueField
  let xr : R₁ →+* k := (algebraMap R k).comp R₁.subtype
  let p : Ideal R₁ := RingHom.ker xr
  have : p.IsPrime := RingHom.ker_isPrime xr
  let g := algebraMap R₁ p.ResidueField
  let i : p.ResidueField →+* k := Ideal.ResidueField.lift p xr le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = xr := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p xr le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (algebraMap R k) ≫ spMap R₁.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  have hfib : Out.RelAmple ((Over.pullback (spMap g)).obj A₀) (M.pull (pullback.fst A₀.hom (spMap g))) :=
    FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hM _) (GlobalTheory.lbIso_refl (LB.isLB_pull hM _))
      (FibreAmple.relAmple_of_factor hM hφ h₂ _ hu hN e hB)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre A₀ hM g (FibreAmple.residueField_fraction p) hfib
  refine ⟨r, fun hx => hr (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 ?_)), hA⟩
  exact Ideal.algebraMap_residueField_eq_zero.2 hx

theorem relAmple_spread_subring (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) :
    ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (B₂ : Over (Sp R₂))
      (π : B₂.left ⟶ A₀.left), IsPullback π B₂.hom A₀.hom (spMap (Subring.inclusion h)) →
        Out.RelAmple B₂ (M.pull π) := by
  classical
  choose r hr hA using exists_basicOpen hM hφ hN e hB
  have hspan : Ideal.span (Set.range fun x => (r x : R)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range fun x => (r x : R)) := by
    change (1 : R) ∈ Ideal.span _
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨c.support.image c, fun R₂ h hF B₂ π hπ => ?_⟩
  have hcR : ∀ x ∈ c.support, c x ∈ R₂ := fun x hx => hF (Finset.mem_image_of_mem c hx)
  have : IsProper B₂.hom := MorphismProperty.of_isPullback (P := @IsProper) hπ ‹_›
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ B₂ (M.pull π) (pull_isLB hM π) inferInstance inferInstance
    fun s => ?_
  obtain ⟨x, -, hxs⟩ : ∃ x ∈ c.support, Subring.inclusion h (r x) ∉ (s : PrimeSpectrum R₂).asIdeal := by
    by_contra hne
    push_neg at hne
    have key : (∑ y ∈ c.support.attach, (⟨c y, hcR y y.2⟩ : R₂) * Subring.inclusion h (r y)) = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one, ← hc, Finsupp.sum]
      exact Finset.sum_attach c.support (fun y => c y • (r y : R))
    apply (s : PrimeSpectrum R₂).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← key]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _ (hne y y.2)
  let D : (Sp R₁).Opens := PrimeSpectrum.basicOpen (r x)
  let U : (Sp R₂).Opens := PrimeSpectrum.basicOpen (Subring.inclusion h (r x))
  refine ⟨U, hxs, ?_⟩
  have sq : IsPullback ((B₂.hom ⁻¹ᵁ U).ι ≫ π) (B₂.hom ∣_ U) A₀.hom (U.ι ≫ spMap (Subring.inclusion h)) :=
    (isPullback_morphismRestrict B₂.hom U).flip.paste_horiz hπ
  have hrange : Set.range (U.ι ≫ spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : U.ι z ∈ (U : Set (Sp R₂)) := by
      first
        | exact (Scheme.Opens.range_ι U) ▸ ⟨z, rfl⟩
        | (rw [← Scheme.Opens.range_ι U]; exact ⟨z, rfl⟩)
        | exact z.2
    exact hz
  have hA' := FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₀.hom D.ι) sq
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hM _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hM _)) (hA x)
  have : IsProper (Over.mk (B₂.hom ∣_ U)).hom := inferInstanceAs (IsProper (B₂.hom ∣_ _))
  exact relAmple_of_lbIso_self (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)
    (FibreAmple.lbIso_pull_pull hM _ _) hA'

end GlobalTheory.AmpleApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem topologicalKrullDim_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  intro K _ A
  haveI : Nonempty A.X.left := ⟨A.origin⟩
  exact GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.X.hom A.dim A.smooth

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_abVar_eq_dim : ∀ (K : Type) [Field K] (A : AbVar K), topologicalKrullDim A.X.left = (A.dim : ℕ) := by
  first | exact @GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | exact GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim | (intros; apply GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim <;> assumption)
end
end
