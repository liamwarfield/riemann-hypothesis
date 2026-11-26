module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

def VertPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ u : T, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) ∧
        ∀ (d : ℕ) (g : MRing (fun _ : Unit => T)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun _ => d) →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : K') * aeval y g = a * y ⟨(), t⟩ ^ d)

def VertPointInj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def VertPointSurj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal → locLen m (sectionQuot y (aeval y s)) ≠ 0 →
        ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def VertPointMultChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def SectionQuotLocal.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (t : T), m.IsPrime →
        (∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          locLen m (sectionQuot y (aeval y s)) = locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain

noncomputable section

namespace CurveAffineCharts

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

theorem exists_chart (hy : IsArithVar (mCoordIdeal y) 1) : ∃ t : T, y ⟨(), t⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := hy.2.1.2.2 ()
  refine ⟨t, fun h0 => ht ?_⟩
  simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]


omit [Fintype T] in
theorem mem_integer_of_mem_chartRingZ [NumberField K'] (v : HeightOneSpectrum (𝓞 K')) (t : T)
    (ht : ∀ u, v.valuation K' (y ⟨(), u⟩) ≤ v.valuation K' (y ⟨(), t⟩)) {b : K'}
    (hb : b ∈ chartRingZ y (fun _ => t)) : b ∈ (v.valuation K').integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation K' (y ⟨(), t⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (ht u)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem mem_integralClosure_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' b hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _))
    (mem_curveRing.mp hb (fun _ => t) (fun _ => hyt))

theorem finite [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) : Module.Finite ℤ (curveRing y) := by
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ K' :=
    { toFun := fun b => ⟨b, mem_integralClosure_of_mem_curveRing y hy b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg (fun z : integralClosure ℤ K' => (z : K')) h)

theorem mem_blockFnField_of_mem_curveRing [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1)
    {b : K'} (hb : b ∈ curveRing y) : b ∈ blockFnField y := by
  obtain ⟨t, ht⟩ := exists_chart y hy
  have hbt := mem_curveRing.mp hb (fun _ => t) (fun _ => ht)
  clear hb
  induction hbt using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_nat_mul_mem_adjoin [CharZero K'] {S : Set K'} {x : K'} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ?_⟩
    have hq : (q.den : K') * algebraMap ℚ K' q = (q.num : K') := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [hq]
    exact intCast_mem _ _
  | add x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x + z) = (m : K') * ((n : K') * x) + (n : K') * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ m) hnx) (mul_mem (natCast_mem _ n) hmz)
  | mul x z _ _ hx hz =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : K') * (x * z) = ((n : K') * x) * ((m : K') * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem hnx hmz


omit [Fintype T] in
theorem mem_adjoin_of_mem_blockFnField [NumberField K'] (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ blockFnField y) :
    x ∈ Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
  have hle : blockFnField y ≤
      IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, -, rfl⟩
    have hp : y p / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    rw [← div_div_div_cancel_right₀ ht]
    exact div_mem hp hq
  exact hle hx

theorem exists_nat_mul_mem_curveRing [NumberField K'] {x : K'} (hx : x ∈ blockFnField y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * x ∈ curveRing y := by
  classical
  have key : ∀ t : T, ∃ n : ℕ, n ≠ 0 ∧ (y ⟨(), t⟩ ≠ 0 → (n : K') * x ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, one_ne_zero, fun h => (h ht).elim⟩
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin (mem_adjoin_of_mem_blockFnField y t ht hx)
      exact ⟨n, hn, fun _ => h⟩
  choose N hN0 hN using key
  refine ⟨∏ t, N t, Finset.prod_ne_zero_iff.mpr (fun t _ => hN0 t), ?_⟩
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := hN (c ()) (hc ())
  rw [← hc'] at h1
  have e : ((∏ t, N t : ℕ) : K') * x =
      ((∏ t ∈ Finset.univ.erase (c ()), N t : ℕ) : K') * ((N (c ()) : K') * x) := by
    rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ (c ()))]
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ _) h1

theorem finrank_eq [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) :
    Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) := by
  have := finite y hy
  let b := Module.finBasis ℤ (curveRing y)
  let ι : curveRing y →ₗ[ℤ] K' := (curveRing y).subtype.toAddMonoidHom.toIntLinearMap
  have hliZ : LinearIndependent ℤ (ι ∘ b) :=
    b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ (ι ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspan : Submodule.span ℚ (Set.range (ι ∘ b)) =
      Subalgebra.toSubmodule (blockFnField y).toSubalgebra := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_blockFnField_of_mem_curveRing y hy (b i).2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_mul_mem_curveRing y hx
      have h1 : (⟨_, hnx⟩ : curveRing y) ∈ Submodule.span ℤ (Set.range b) := by
        rw [b.span_eq]; trivial
      have h2 : (n : K') * x ∈ Submodule.span ℤ (Set.range (ι ∘ b)) := by
        rw [Set.range_comp, ← Submodule.map_span]
        exact Submodule.mem_map_of_mem h1
      have h3 : (n : K') * x ∈ Submodule.span ℚ (Set.range (ι ∘ b)) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ h2
      have h4 : x = (n : ℚ)⁻¹ • ((n : K') * x) := by
        rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]
      rw [h4]
      exact Submodule.smul_mem _ _ h3
  rw [← IntermediateField.finrank_eq_finrank_subalgebra, ← Subalgebra.finrank_toSubmodule, ← hspan,
    finrank_span_eq_card hliQ, Fintype.card_fin]

end CurveAffineCharts

theorem CurveCharts.proof (hc : ClosedPointChart.Statement) : CurveCharts.Statement :=
  fun T _ K' _ _ y hy =>
    ⟨CurveAffineCharts.finite y hy, CurveAffineCharts.finrank_eq y hy, hc T K' y hy⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualStackedDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ), F'.lattice ≤ F.lattice → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    F.withStdMetric.degree - F'.withStdMetric.degree = ∑ t, Real.log |(a t : ℝ)|

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))


end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

def OneBlockPointDeg.Statement : Prop :=
  ∀ (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ'] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (k₀ : K), (∀ k, k = k₀) →
    ∀ (w : (Σ k, ι k) → Φ') (c : ∀ k, ι k), w ⟨k₀, c k₀⟩ ≠ 0 →
      Module.Finite Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) →
      Transcendental (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) (w ⟨k₀, c k₀⟩) →
      IsProjVarF (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) 0 ∧
        IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c ∧
        ptDeg (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c =
          Module.finrank Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩))

def DualStdFibreRatios.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b)))),
    1 ≤ i → ∃ c : T,
      G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K ∧
      Transcendental (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdImageBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualImageBottom

open DualArithmeticVariety

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

def genPt (K : Type) [Field K] (i : ℕ) : (Σ _ : Unit, Fin i) → ProjField K i :=
  fun q => algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X q.2)


omit [Fintype T] in
theorem aeval_eq_zero_of_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    {f : MRing (dualBlocks T)} (hf : f ∈ dualIdeal b) : aeval (dualLatticeCoord b) f = 0 := by
  have h : ∀ g : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField K i)) (mConeMap (dualLatticeCoord b) g) =
        aeval (dualLatticeCoord b) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap]
  rw [← h f, show mConeMap (dualLatticeCoord b) f = 0 from hf, map_zero]

def evalQ (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* ProjField K i :=
  eval₂Hom (Ideal.Quotient.lift _ (aeval (dualLatticeCoord b)).toRingHom
    fun _ hf => aeval_eq_zero_of_mem b hf) fun _ => 1

theorem aeval_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (q : Σ _ : Unit, Fin i) :
    aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) = genPt K i q := by
  obtain ⟨⟨⟩, j⟩ := q
  have hs := congrArg (evalForm (K := K) i) (dualStdCoordMat_sum b j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, evalForm, Fintype.linearCombination_apply_single, one_smul, ← evalForm] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [genPt, ← hs, linForm, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, aeval_C, aeval_X, map_zsmul, ← dualLatticeCoord_eq, zsmul_eq_mul, eq_intCast]

theorem evalQ_graphMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (PBlk i)) :
    evalQ b (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f)) = aeval (genPt K i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, evalQ]
  | add p q hp hq =>
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul, aeval_X, rename_X, ← aeval_linForm b q]
    simp [graphMap, inrV, evalQ]

theorem aeval_genPt_injective : Function.Injective (aeval (R := ℤ) (genPt K i)) := by
  have hK : AlgebraicIndependent ℤ fun j : Fin i =>
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) :=
    (algebraicIndependent_gen i).restrictScalars (algebraMap ℤ K).injective_int
  have h := hK.comp (fun q : Σ _ : Unit, Fin i => q.2) (by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, c⟩ h
    cases h
    rfl)
  exact algebraicIndependent_iff_injective_aeval.mp h

end StandardDualImageBottom


open StandardDualImageBottom in
theorem DualStdImageBot.proof : DualStdImageBot.Statement := by
  intro K _ _ i T _ _ b
  refine eq_bot_iff.mpr fun f hf => (Ideal.mem_bot).mpr (aeval_genPt_injective (K := K) (i := i) ?_)
  have h0 : graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f) = 0 := hf
  rw [map_zero, ← evalQ_graphMap b, h0, map_zero]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEnergyCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualEnergyChartsAlt

open StandardDualMassAtPoint DualGeometricDegreeCharts

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

def chartMat (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ :=
  LinearMap.toMatrix' (LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)).symm.toLinearMap

theorem atProj (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartEnergyIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    (∀ σ, Function.Bijective (chartMat hOf b hb hΨ σ).mulVec) ∧ ∀ k : ℕ,
      ptsIntegralAt (e := D) (dualIdeal b) Ψ
          (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
        ∑ σ : K →+* ℂ, chartMixedEnergy ((chartMat hOf b hb hΨ σ)ᴴ * F.metric σ * chartMat hOf b hb hΨ σ)
          ((chartMat hOf b hb hΨ σ)ᴴ * chartMat hOf b hb hΨ σ) k := by
  set A := chartMat hOf b hb hΨ with hAdef
  let E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ) := fun σ =>
    LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)
  have hAv : ∀ σ v, A σ *ᵥ v = (E σ).symm v := fun σ v => LinearMap.toMatrix'_mulVec _ v
  have hAbij : ∀ σ, Function.Bijective (A σ).mulVec := fun σ => by
    have : (A σ).mulVec = (E σ).symm := funext (hAv σ)
    rw [this]
    exact (E σ).symm.bijective
  have hΨA : ∀ σ v, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ v))) = v := fun σ v => by
    rw [hAv]
    exact (E σ).apply_symm_apply v
  have huniq : ∀ σ v c, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) = c → v = A σ *ᵥ c :=
    fun σ v c h => (E σ).injective (by
      show Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) =
        Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ c)))
      rw [h, hΨA])
  have hne : ∀ σ (y : Fin D → ℂ), A σ *ᵥ Fin.cons 1 y ≠ 0 := fun σ y h0 => by
    have h1 : Fin.cons 1 y = (0 : Fin (D + 1) → ℂ) := (hAbij σ).1 (h0.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun h1 0
  have hfib : ∀ y : Fin D → ℂ, ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) Ψ y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := by
    intro y
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hΨz⟩
      obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
      have hz' := eq_planePt b hb hσ
      have hv : recLin b hb σ z = A σ *ᵥ Fin.cons 1 y := huniq σ _ _ (by rw [← hz']; exact hΨz)
      refine ⟨σ, ?_⟩
      show segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) = segre z
      rw [← hv, ← hz']
    · rintro ⟨σ, rfl⟩
      exact ⟨_, hOf K (D + 1) F T b hb σ _ (hne σ y), rfl, hΨA σ _⟩
  have hsheet : ∀ σ (y : Fin D → ℂ), IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y')) := by
    intro σ y
    have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
      rw [differentiable_pi]
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simpa using differentiable_apply (𝕜 := ℂ) k
    refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, hOf K (D + 1) F T b hb σ _ (hne σ y'), hΨA σ _⟩⟩
    refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt, Matrix.mulVec, dotProduct]
    exact Differentiable.fun_sum fun j _ =>
      (Differentiable.fun_sum fun k _ => (differentiable_pi.mp hc k).const_mul _).const_mul _

  have hnear : ∀ σ (y : Fin D → ℂ) γ, IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ →
      ∀ᶠ y' in 𝓝 y, γ y' = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y') := by
    intro σ y γ hγ
    have hγy : γ y = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y) := by
      funext ⟨u, t⟩
      cases u
      have h1 := congrFun hγ.1 (fun _ => t)
      simpa only [segre_const] using h1
    have hcont : ContinuousAt γ y := (hγ.2.self_of_nhds).1.continuousAt
    have hR : ∀ᶠ y' in 𝓝 y, recLin b hb σ (γ y') ≠ 0 := by
      have hc : ContinuousAt (fun y' => recLin b hb σ (γ y')) y :=
        (LinearMap.continuous_of_finiteDimensional (recLin b hb σ)).continuousAt.comp hcont
      apply hc.eventually_ne
      rw [hγy, recLin_planePt]
      exact hne σ y
    filter_upwards [hγ.2, hR] with y' hy' hRy'
    obtain ⟨-, hmc, hΨy'⟩ := hy'
    obtain ⟨ρ, hρ⟩ := hOn K (D + 1) F T b hb _ hmc
    have hρσ : ρ = σ := by
      by_contra h
      apply hRy'
      funext k
      exact hρ σ (Ne.symm h) k
    subst hρσ
    have hz' := eq_planePt b hb hρ
    have hv : recLin b hb ρ (γ y') = A ρ *ᵥ Fin.cons 1 y' :=
      huniq ρ _ _ (by rw [← hz']; exact hΨy')
    rw [hz', hv]

  have hpotF : ∀ σ (y' : Fin D → ℂ), Real.log ((dualLine F b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y' := fun σ y' => by
    rw [h_planePt, hermChartPot_eq]
  have hpotS : ∀ σ (y' : Fin D → ℂ),
      Real.log ((dualLine F.withStdMetric b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * A σ) y' := fun σ y' => by
    have h1 := h_planePt (F := F.withStdMetric) b hb σ (A σ *ᵥ Fin.cons 1 y')
    have h2 := hermChartPot_eq (A σ) (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) y'
    rw [Matrix.mul_one] at h2
    rw [h2]
    exact congrArg Real.log h1
  refine ⟨hAbij, fun k => ?_⟩
  have hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) =
      (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro σ y
    have hex : ∃ γ, IsSheet (dualIdeal b) Ψ y
        (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩
    unfold sheetDensity
    rw [dite_eq_left hex]
    have hev := hnear σ y _ hex.choose_spec
    beta_reduce
    rw [hev.self_of_nhds, hpotF, hpotS]
    congr 1
    apply maDensity_congr_of_eventuallyEq
    intro j
    filter_upwards [hev] with y' hy'
    simp only [pot]
    rw [hy']
    split_ifs
    · exact hpotF σ y'
    · exact hpotS σ y'
  have hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ =>
      segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) :=
    fun y σ τ h => planePt_inj b hb (hne σ y) h
  have hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) Ψ y,
      sheetDensity (dualIdeal b) Ψ
        (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y w =
      ∑ σ : K →+* ℂ, (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro y
    rw [hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hdens σ y
  have hN : ∀ σ, ((A σ)ᴴ * A σ).PosDef := fun σ => by
    simpa using (Matrix.PosDef.one (n := Fin (D + 1)) (R := ℂ)).conjTranspose_mul_mul_same (hAbij σ).1
  unfold ptsIntegralAt
  simp only [hsum]
  rw [integral_finsetSum _ fun σ _ =>
    hInt D _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1) (hN σ) k]
  rfl

end DualEnergyChartsAlt


open DualEnergyChartsAlt DualGeometricDegreeCharts in
theorem DualEnergyCharts.proof (hInt : ChartEnergyIntegrable.Statement) : DualEnergyCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨chartMat DualPtsOfPlane.proof b hb hex.choose_spec, hA, fun k => ?_⟩
  show ptsIntegral (e := D) (dualIdeal b)
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = _
  unfold ptsIntegral
  rw [dite_eq_left hex]
  exact hE k

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointUnitSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ClosedPointUnitSection.exists_valuationSubring {K : Type*} [Field K] (A : Subring K)
    (P : Ideal A) [P.IsPrime] :
    ∃ W : ValuationSubring K, (∀ a : A, (a : K) ∈ W) ∧ (∀ a : A, a ∉ P → W.valuation (a : K) = 1) ∧
      ∀ a : A, a ∈ P → W.valuation (a : K) < 1 := by
  obtain ⟨W, h, hloc⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.ofPrime A P)
  have hA : ∀ a : A, (a : K) ∈ (LocalSubring.ofPrime A P).toSubring :=
    fun a => LocalSubring.le_ofPrime A P a.2
  have key : ∀ a : A, (IsUnit (algebraMap A (LocalSubring.ofPrime A P).toSubring a) ↔ a ∉ P) :=
    fun a => IsLocalization.AtPrime.isUnit_to_map_iff _ P a
  refine ⟨W, fun a => h (hA a), fun a ha => ?_, fun a ha => ?_⟩
  · have hu := ((key a).mpr ha).map (Subring.inclusion h)
    exact (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mp hu
  · refine lt_of_le_of_ne (W.valuation_le_one ⟨a, h (hA a)⟩) fun h1 => ?_
    have hu : IsUnit (Subring.inclusion h (algebraMap A (LocalSubring.ofPrime A P).toSubring a)) :=
      (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mpr h1
    exact (key a).mp ((isUnit_map_iff (Subring.inclusion h) _).mp hu) ha

def ClosedPointUnitSection.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        ∃ (e : ℕ) (g : K'), 1 ≤ e ∧ g ≠ 0 ∧ g ∈ chartLat y 1 e ∧
          ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
            (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) →
              ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMetricPull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField Matrix

noncomputable section

namespace StandardDualMetricPullback

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [DecidableEq T] in
theorem linApply_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) (j : Fin i) :
    linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ =
      ∑ τ : K →+* ℂ, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) := by
  classical
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hMW : dualEmbMatrix b *ᵥ W = fun t => z ⟨(), t⟩ :=
    (LinearEquiv.ofBijective _ hb).apply_symm_apply _
  have hA : ∀ p : (K →+* ℂ) × Fin i,
      ∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p = p.1 ((Pi.single j 1 : Fin i → K) p.2) := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← dualStdCoordMat_sum b j, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [dualEmbMatrix, Pi.smul_apply, zsmul_eq_mul]
  calc linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩
      = ∑ t, (dualStdCoordMat b () j t : ℂ) * ∑ p, dualEmbMatrix b t p * W p := by
        simp only [linApply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← congrFun hMW t]
        rfl
    _ = ∑ p, (∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p) * W p := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ τ : K →+* ℂ, W (τ, j) := by
        simp only [hA, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
        simp

end StandardDualMetricPullback


open StandardDualMetricPullback in
theorem DualStdMetricPull.proof : DualStdMetricPull.Statement := by
  intro K _ _ i T _ _ b hb z hz
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  obtain ⟨σ, hσ⟩ := DualPtsOnPlane.proof K i _ T b hb z hz
  have hy : ∀ j, linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ = W (σ, j) := fun j => by
    rw [linApply_eq b hb z j]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  have hterm : ∀ τ, ((star fun j => W (τ, j)) ⬝ᵥ
      ((HermLattice.standard K i).metric τ *ᵥ fun j => W (τ, j))).re = ∑ j, ‖W (τ, j)‖ ^ 2 := by
    intro τ
    simp only [HermLattice.standard, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
    norm_cast
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = _
  rw [show dualNormSq b hb (fun t => z ⟨(), t⟩) = ∑ τ, ∑ j, ‖W (τ, j)‖ ^ 2 from
    Finset.sum_congr rfl fun τ _ => hterm τ]
  simp only [fsMulti, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, fsMetric, Finset.univ_unique, Finset.prod_singleton, zpow_one,
    EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [W, hσ τ hτ]) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by rw [← hy j]

end

end GroundTheory.Heights₂.Heights
end
