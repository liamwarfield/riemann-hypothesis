module

public import Mathlib

@[expose] public section

/-!
# Parabolic, Borel, and Iwahori Subgroups & Double-Coset Indicators

Constructs block-triangular parabolic subgroups (`parab`), Borel subgroups (`borel`), and
Iwahori subgroups (`iwahori` / `iwGL`) of `GL_n` over a nonarchimedean local field `k`
(specifically the `p`-adic completion of a number field `F`, proved here to be a
`IsNonarchimedeanLocalField`), together with the indicator function `dcos` of an Iwahori
double coset `I t I` and its left/right `I`-invariance.
-/

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.Pl
    (E : Type) [Field E] [NumberField E] : Type :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.GLw
    {E : Type} [Field E] [NumberField E] (n : ℕ)
    (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) : Type :=
  GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)

theorem UpperTheory.Reformulated.B.BorelApproximation.aux3
    (k : Type) [Field k] : SubsemiringClass (Subring k) k :=
  inferInstance

theorem UpperTheory.Reformulated.B.BorelApproximation.aux4
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    IsLocalRing ↥(ValuativeRel.valuation k).integer :=
  inferInstance

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.blk
    {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) : α :=
  (e.symm i).fst

theorem UpperTheory.Reformulated.B.BorelApproximation.aux6
    (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}
    (hx : x ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)})
    (hy : y ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)}) :
    x * y ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)} :=
  Matrix.BlockTriangular.mul hx hy

theorem UpperTheory.Reformulated.B.BorelApproximation.aux7
    (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) :
    (1 : GL n R) ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)} :=
  Matrix.blockTriangular_one

theorem UpperTheory.Reformulated.B.BorelApproximation.aux8
    (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}
    (hx : x ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)}) :
    x⁻¹ ∈ {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e)} := by
  have hx : Matrix.BlockTriangular (x : Matrix n n R)
      (UpperTheory.Reformulated.B.BorelApproximation.blk e) := hx
  letI := x.invertible
  change Matrix.BlockTriangular ((x⁻¹ : GL n R) : Matrix n n R)
    (UpperTheory.Reformulated.B.BorelApproximation.blk e)
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.parab
    (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) : Subgroup (GL n R) where
  carrier := {g : GL n R | Matrix.BlockTriangular (g : Matrix n n R)
    (UpperTheory.Reformulated.B.BorelApproximation.blk e)}
  mul_mem' := UpperTheory.Reformulated.B.BorelApproximation.aux6 R e
  one_mem' := UpperTheory.Reformulated.B.BorelApproximation.aux7 R e
  inv_mem' := UpperTheory.Reformulated.B.BorelApproximation.aux8 R e

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.points
    (n : Type) : (x : n) × Unit ≃ n :=
  Equiv.sigmaUnique n (fun _ => Unit)

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.borel
    (R : Type) [CommRing R] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    Subgroup (GL n R) :=
  UpperTheory.Reformulated.B.BorelApproximation.parab R
    (UpperTheory.Reformulated.B.BorelApproximation.points n)

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwahori
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n k) :=
  Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
    (Subgroup.comap
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue ↥(ValuativeRel.valuation k).integer))
      (UpperTheory.Reformulated.B.BorelApproximation.borel
        (IsLocalRing.ResidueField ↥(ValuativeRel.valuation k).integer) n))

@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.complRel
    {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ValuativeRel (IsDedekindDomain.HeightOneSpectrum.adicCompletion F p) :=
  ValuativeRel.ofValuation Valued.v

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.exists_near {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : adicCompletion F p)
    (hx : Valued.v x ≤ 1) :
    ∃ a : NumberField.RingOfIntegers F, Valued.v (x - algebraMap _ (adicCompletion F p) a) < 1 := by
  have hb : {y : adicCompletion F p | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simpa using hy
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F p).mem_nhds hb
  have hk : Valued.v (algebraMap F (adicCompletion F p) k - x) < 1 := hk
  have hv : ∀ y : F, Valued.v (algebraMap F (adicCompletion F p) y) = p.valuation F y :=
    fun y => valuedAdicCompletion_eq_valuation' p y
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hv, ← sub_add_cancel (algebraMap F (adicCompletion F p) k) x]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer p hk1 1
  refine ⟨a, ?_⟩
  rw [← hv, map_sub, ← IsScalarTower.algebraMap_apply, Units.val_one] at ha
  rw [Valuation.map_sub_swap, ← sub_add_sub_cancel _ (algebraMap F (adicCompletion F p) k)]
  exact Valuation.map_add_lt _ ha hk

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.finite_residue {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (adicCompletionIntegers F p)) := by
  have hfin : Finite (NumberField.RingOfIntegers F ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  have hmax : ∀ y : adicCompletionIntegers F p, Valued.v y.1 < 1 →
      IsLocalRing.residue _ y = 0 := fun y hy => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let φ : NumberField.RingOfIntegers F →+* IsLocalRing.ResidueField (adicCompletionIntegers F p) :=
    (IsLocalRing.residue _).comp (algebraMap _ _)
  have hker : ∀ a ∈ p.asIdeal, φ a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem p a).2 ha
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal φ hker) fun z => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.BorelApproximation.exists_near p x.1 x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.lift_mk, eq_comm, ← sub_eq_zero]
  have := hmax (x - algebraMap _ _ a) ha
  rwa [map_sub] at this

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
private theorem UpperTheory.Reformulated.B.BorelApproximation.locCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LocallyCompactSpace (adicCompletion F p) := by
  have h := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := adicCompletion F p)).2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (adicCompletionIntegers F p)),
      UpperTheory.Reformulated.B.BorelApproximation.finite_residue p⟩
  exact locallyCompact_of_proper

theorem UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported
    {F : Type} [Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    @IsNonarchimedeanLocalField (p.adicCompletion F) _
      (UpperTheory.Reformulated.B.BorelApproximation.complRel p) _ := by
  letI := UpperTheory.Reformulated.B.BorelApproximation.complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (fun {s} => Valued.is_topological_valuation s)
  haveI := UpperTheory.Reformulated.B.BorelApproximation.locCompact p
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).2 inferInstance
  exact {}

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwGL
    {E : Type} [Field E] [NumberField E] (n : ℕ)
    (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E) :
    Subgroup (UpperTheory.Reformulated.B.BorelApproximation.GLw n w) :=
  letI := UpperTheory.Reformulated.B.BorelApproximation.complRel w
  haveI := UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported w
  UpperTheory.Reformulated.B.BorelApproximation.iwahori (w.adicCompletion E) (Fin n)

noncomputable def UpperTheory.Reformulated.B.BorelApproximation.dcos
    {E : Type} [Field E] [NumberField E] (n : ℕ)
    (w : UpperTheory.Reformulated.B.BorelApproximation.Pl E)
    (t y : UpperTheory.Reformulated.B.BorelApproximation.GLw n w) : ℂ :=
  open Classical in
  if ∃ x ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w,
      ∃ z ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL n w, y = x * t * z then
    1
  else
    0

theorem UpperTheory.Reformulated.B.BorelApproximation.dcos_left
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {m : ℕ}
    {w : UpperTheory.Reformulated.B.BorelApproximation.Pl E}
    (t k g : UpperTheory.Reformulated.B.BorelApproximation.GLw m w)
    (hk : k ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL m w) :
    UpperTheory.Reformulated.B.BorelApproximation.dcos m w t (k * g) =
      UpperTheory.Reformulated.B.BorelApproximation.dcos m w t g := by
  unfold UpperTheory.Reformulated.B.BorelApproximation.dcos
  refine congrArg (fun P : Prop => @ite ℂ P (Classical.propDecidable P) 1 0) (propext ⟨?_, ?_⟩)
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k⁻¹ * x, mul_mem (inv_mem hk) hx, z, hz, ?_⟩
    rw [mul_assoc k⁻¹, mul_assoc k⁻¹, ← h, inv_mul_cancel_left]
  · rintro ⟨x, hx, z, hz, h⟩
    refine ⟨k * x, mul_mem hk hx, z, hz, ?_⟩
    rw [h, mul_assoc k, mul_assoc k]

theorem UpperTheory.Reformulated.B.BorelApproximation.dcos_right
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {m : ℕ}
    {w : UpperTheory.Reformulated.B.BorelApproximation.Pl E}
    (t k g : UpperTheory.Reformulated.B.BorelApproximation.GLw m w)
    (hk : k ∈ UpperTheory.Reformulated.B.BorelApproximation.iwGL m w) :
    UpperTheory.Reformulated.B.BorelApproximation.dcos m w t (g * k) =
      UpperTheory.Reformulated.B.BorelApproximation.dcos m w t g := by
  unfold UpperTheory.Reformulated.B.BorelApproximation.dcos
  refine @if_congr _ _ _ (Classical.propDecidable _) (Classical.propDecidable _) _ _ _ _
    ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k⁻¹, Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hk), by
      rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, z, hz, h⟩
    exact ⟨x, hx, z * k, Subgroup.mul_mem _ hz hk, by rw [h, mul_assoc (x * t)]⟩
