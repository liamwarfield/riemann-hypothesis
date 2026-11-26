module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Hcptgen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem injective_ringOfIntegers_toComplex {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    Function.Injective g := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  have h : Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = RingHom.ker (g.comp (algebraMap ℤ (𝓞 F))) :=
    RingHom.comap_ker _ _
  change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = ⊥
  rw [h, (RingHom.injective_iff_ker_eq_bot _).1]
  have e : g.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [e]
  exact Int.cast_injective

theorem exists_comp_eq_of_ringOfIntegers {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    ∃ g' : F →+* ℂ, g'.comp (algebraMap (𝓞 F) F) = g :=
  ⟨IsFractionRing.lift (injective_ringOfIntegers_toComplex g), by
    ext a
    simp⟩

theorem exists_spMap_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp (𝓞 F))
    (u : Sp ℂ ⟶ X) : ∃ g' : F →+* ℂ, u ≫ s = spMap g' ≫ spMap (algebraMap (𝓞 F) F) := by
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_ringOfIntegers (Spec.preimage (u ≫ s)).hom
  refine ⟨g', ?_⟩
  rw [← spMap_comp, hg']
  exact (Spec.map_preimage (u ≫ s)).symm

theorem polarisedAt_of_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z hz
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₁ : (z ≫ 𝔐.f) p ∈ abLocus Y.t.G := by
    have := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (z p)).2 hz
    simpa using this

  obtain ⟨g', hg'⟩ := exists_spMap_of_ringOfIntegers Y.s (z ≫ 𝔐.f)
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (z ≫ 𝔐.f) (spMap g') hg'
  have hw : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _

  have h₂ : w p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    show (pullback.fst Y.s _) (w p) ∈ abLocus Y.t.G
    have : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w p) = (z ≫ 𝔐.f) p := by
      rw [← hw]; simp
    rw [this]; exact h₁
  have h₃ : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  haveI := Y.jQ_open
  let v : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w h₃
  have hv : v ≫ Y.jQ ≫ pullback.fst _ _ = z ≫ 𝔐.f := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hw]

  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ pullback.fst _ _) (_ : SABMap t' Y.t q),
      Nonempty (SABMap t' Y.oF.t v) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hv.symm n
  obtain ⟨w₂, g₂, -⟩ := m₃.lin
  obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
  exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_point_polarised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hcpt_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) :=
  @PositivityTheory.HtPt.Hcptgen.hcpt_generic

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_free_integral_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point | exact GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

def lieModelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add (f := _), M.add]
  smul c v := by rw [map_smul, M.smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDet
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem place_eq_zpow_ordE (v : FinitePlace L) {x : L} (hx : x ≠ 0) :
    v x = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) ^ (-Formalism.L2.Ker.ordE v.maximalIdeal x) := by
  have hw : IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x ≠ 0 := by
    rwa [ne_eq, Valuation.zero_iff]
  rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def]
  unfold Formalism.L2.Ker.ordE
  rw [neg_neg]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw).symm⟩
  rw [hk, WithZero.log_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  simp [WithZero.exp, WithZero.log]

theorem relIndex_map_of_integral (v : FinitePlace L) (S : Matrix (Fin n) (Fin n) L)
    (hS : ∀ i j, v (S i j) ≤ 1) (hdet : S.det ≠ 0) (f : (Fin n → L) →+ (Fin n → L))
    (hf : ∀ x, f x = S *ᵥ x) (Λ : AddSubgroup (Fin n → L)) (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1) :
    Λ.map f ≤ Λ ∧ (((Λ.map f).relIndex Λ : ℕ) : ℝ) = (v S.det)⁻¹ := by
  have hint : ∀ a : L, v a ≤ 1 ↔ Formalism.L2.Col.IntAt v.maximalIdeal a := fun a => by
    rw [place_le_one_iff, GlobalTheory.CharValCompare.intAt_iff]
  have hle : Λ.map f ≤ Λ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    rw [hΛ] at hy ⊢
    intro i
    rw [hf]
    show v (∑ j, S i j * y j) ≤ 1
    exact place_sum_le_one v _ _ (fun j _ => place_mul_le_one v (hS i j) (hy j))
  refine ⟨hle, ?_⟩
  have key := GlobalTheory.IdxDet.relIndex_mulVec L (Fin n) v.maximalIdeal S Λ (Λ.map f) hdet
    (fun x => by rw [hΛ]; exact forall_congr' fun i => hint (x i))
    (fun x => by
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩)
    hle
  rw [place_eq_zpow_ordE v hdet, _root_.zpow_neg, inv_inv]
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  exact key'

theorem gIdx_locAt_frame (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L)
    (T : Matrix (Fin n) (Fin n) L) (hdet : T.det ≠ 0) :
    gIdx (locAt v (frame T)).toAddSubgroup
      (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  set Λ := (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup with hΛdef
  have hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1 := fun x => mem_locAt_frame_one
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → L) →+ (Fin n → L), ∀ x, M x = T *ᵥ x :=
    ⟨(Matrix.mulVecLin T).toAddMonoidHom, fun x => rfl⟩
  have hTΛ : (locAt v (frame T)).toAddSubgroup = Λ.map M := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_locAt_frame, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).2 hy, hM y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).1 hy, hM y⟩
  have hMinj : Function.Injective M := by
    intro x y hxy
    rw [hM, hM] at hxy
    have h := congrArg (fun z => T⁻¹ *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet)] using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers L))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => T p.1 p.2)
  set c : L := algebraMap (NumberField.RingOfIntegers L) L b with hcdef
  have hc0 : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hcv : v c ≤ 1 := place_int_le_one v b
  have hcT : ∀ i j, v ((c • T) i j) ≤ 1 := by
    intro i j
    obtain ⟨r, hr⟩ := hb (i, j) (Finset.mem_univ _)
    rw [Matrix.smul_apply]
    have : c • T i j = algebraMap (NumberField.RingOfIntegers L) L r := by
      rw [hr, smul_eq_mul, Algebra.smul_def]
      all_goals rfl
    rw [this]
    exact place_int_le_one v r
  have hcI : ∀ i j, v ((c • (1 : Matrix (Fin n) (Fin n) L)) i j) ≤ 1 := by
    intro i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · simpa using hcv
    · simpa using place_int_le_one v 0
  obtain ⟨a, ha⟩ : ∃ a : (Fin n → L) →+ (Fin n → L), ∀ x, a x = c • x :=
    ⟨DistribSMul.toAddMonoidHom _ c, fun x => rfl⟩
  have hdetI : (c • (1 : Matrix (Fin n) (Fin n) L)).det = c ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdetT : (c • T).det = c ^ n * T.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc0
  have h1 := relIndex_map_of_integral v (c • (1 : Matrix (Fin n) (Fin n) L)) hcI
    (by rw [hdetI]; exact hcn) a (fun x => by rw [ha]; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]) Λ hΛ
  have h2 := relIndex_map_of_integral v (c • T) hcT (by rw [hdetT]; exact mul_ne_zero hcn hdet) (a.comp M)
    (fun x => by
      rw [AddMonoidHom.comp_apply, ha, hM]
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]) Λ hΛ
  have hpos : ∀ y : L, y ≠ 0 → 0 < v y := fun y hy => NumberField.FinitePlace.pos_iff.mpr hy
  have hr1 : (Λ.map a).relIndex Λ ≠ 0 := by
    intro h0
    have := h1.2
    rw [h0, Nat.cast_zero, hdetI] at this
    exact (inv_pos.mpr (hpos _ hcn)).ne' this.symm
  have hr2 : (Λ.map (a.comp M)).relIndex Λ ≠ 0 := by
    intro h0
    have := h2.2
    rw [h0, Nat.cast_zero, hdetT] at this
    exact (inv_pos.mpr (hpos _ (mul_ne_zero hcn hdet))).ne' this.symm
  rw [hTΛ, gIdx_frac Λ M a hMinj (fun x => by rw [ha, hM, hM, ha, Matrix.mulVec_smul]) h1.1 hr1 h2.1 hr2,
    h1.2, h2.2, hdetI, hdetT, Real.log_inv, Real.log_inv]
  have hm : v (c ^ n * T.det) = v (c ^ n) * v T.det := by
    rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply,
      NumberField.FinitePlace.coe_apply, map_mul]
  rw [hm, Real.log_mul (hpos _ hcn).ne' (hpos _ hdet).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDetStatement
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_index_frame_log_det : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L), T.det ≠ 0 → gIdx (locAt v (frame T)).toAddSubgroup (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame <;> assumption)
end
end
