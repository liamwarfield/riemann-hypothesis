module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompletedSelfDual

open GlobalTheory.AdelicU GlobalTheory.AdelicU.SelfDual GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

theorem mem_maxOrder_iff_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    z ∈ maxOrder F E v ↔ z ∈ intLoc F E v := by
  constructor
  · intro hz
    rw [mem_intLoc_iff_absFin_le_one, absFin_le_iff]
    intro τ
    obtain ⟨p, hp, hpz⟩ := (mem_maxOrder F E v z).1 hz
    let f : v.adicCompletionIntegers F →+* (valBar F v).integer :=
      ((algebraMap (Fv F v) (FvBar F v)).comp (v.adicCompletionIntegers F).subtype).codRestrict _ fun a => by
        change absBar F v (algebraMap (Fv F v) (FvBar F v) a) ≤ 1
        rw [absBar_algebraMap]
        exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 a.2
    refine (Valuation.integer.integers (valBar F v)).mem_of_integral (x := finEmb F v τ z)
      ⟨p.map f, hp.map _, ?_⟩
    have := congrArg (finEmb F v τ : Fv F v ⊗[F] E →+* FvBar F v) hpz
    rw [Polynomial.hom_eval₂, map_zero] at this
    rw [Polynomial.eval₂_map, ← this]
    congr 1
    ext a
    exact ((finEmb F v τ).commutes (a : Fv F v)).symm
  · refine intLoc_induction (p := fun z => z ∈ maxOrder F E v) (fun a ha x => ?_) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem)
    have h1 : (1 : Fv F v) ⊗ₜ[F] (x : E) ∈ maxOrder F E v := by
      letI := (intToEv F E v).toAlgebra
      exact (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
        (RingHom.ext_int _ _)
    have h2 : a ⊗ₜ[F] (1 : E) ∈ maxOrder F E v :=
      RingHom.isIntegralElem_map (intToEv F E v) (x := ⟨a, ha⟩)
    simpa using mul_mem h2 h1

theorem exists_isSelfDualLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ σ n J L hJ hL hsd v
  classical
  let Lv : Submodule (maxOrder F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := latLoc F L v
      zero_mem' := zero_mem _
      add_mem' := fun h h' => add_mem h h'
      smul_mem' := fun c _ hy =>
        (latLoc F L v).smul_mem ⟨c.1, (mem_maxOrder_iff_mem_intLoc v _).1 c.2⟩ hy }
  have hmem : ∀ y, y ∈ Lv ↔ y ∈ latLoc F L v := fun _ => Iff.rfl
  have hfull : Submodule.IsFullLattice E L := by
    refine { toIsLattice := hL, span_eq_top := eq_top_iff.mpr fun y _ => ?_ }
    obtain ⟨s, hs⟩ := hL.fg
    obtain ⟨d, hd, hden⟩ := exists_integral_multiples ℤ ℚ
      (s.image fun x => hE σ J x y)
    have hdE : (d : E) ≠ 0 := by exact_mod_cast hd
    have hy : (d : E) • y ∈ L := by
      apply (hsd _).2
      intro x hx
      rw [← hs] at hx
      have hint : IsIntegral ℤ (hE σ J x ((d : E) • y)) := by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          have hh := hden (hE σ J x y) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
          convert hh using 1 <;> simp [hE, Formalism.UG.hform, Pi.smul_apply,
            smul_eq_mul, Finset.mul_sum, Finset.sum_mul, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        | zero => simpa [hE, Formalism.UG.hform] using (isIntegral_zero : IsIntegral ℤ (0 : E))
        | add x z _ _ hx hz =>
          convert hx.add hz using 1 <;>
            simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]
        | smul a x _ hx =>
          have ha : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toRingHom.toIntAlgHom
          convert ha.mul hx using 1 <;>
            simp [hE, Formalism.UG.hform, Pi.smul_apply, ← algebraMap_smul E, smul_eq_mul, map_mul,
              Finset.mul_sum, mul_assoc]
      exact ⟨⟨_, hint⟩, rfl⟩
    have hyspan : (d : E) • y ∈ Submodule.span E (L : Set (Fin n → E)) := Submodule.subset_span hy
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (d : E)⁻¹ hyspan
    simpa [← smul_smul, hdE] using this
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := exists_frame L hfull
  have h2 := map_mul_eq_one (F := F) (Fv F v) h1
  have hcol : ∀ j, (fun i => S.map (inclR (F := F) (Fv F v)) i j) ∈ Lv := fun j =>
    tmul_mem_latLoc (one_mem _) (hS j)
  refine ⟨Lv, ⟨?_, ?_, fun y => ?_⟩, hmem⟩
  · refine ⟨Finset.univ.image fun j i => S.map (inclR (F := F) (Fv F v)) i j, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hcol j
    · rw [eq_sum_col h2 y]
      refine sum_mem fun j _ => ?_
      exact Submodule.smul_mem _ (⟨_, (mem_maxOrder_iff_mem_intLoc v _).2
        ((mem_latLoc_iff_of_frame h1 hS hΦ v y).1 hy j)⟩ : maxOrder F E v)
        (Submodule.subset_span (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩))
  · refine eq_top_iff.2 fun y _ => ?_
    rw [eq_sum_col h2 y]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hcol j))
  · have h3 : latLoc F L v = dualLoc σ J L v := (forall_isSelfDualAt_iff hJ.2 hfull).2 hsd v
    simp only [mem_maxOrder_iff_mem_intLoc]
    rw [hmem, h3]
    exact Iff.rfl

end GlobalTheory.CompletedSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrderStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLattice_completion_maxOrder : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  first | exact @GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | exact GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | (intros; apply GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCountData
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono (show I.Kg g ⊆ I.Kset from fun x hx => hx.1)).trans_lt
      (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (by exact fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (by exact fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finsetSum _ fun q _ => hi q, ?_⟩
  rw [integral_finsetSum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

end Tens

end GlobalTheory.Mem.RowsBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceNormalFiniteIndex
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem congruence_normal_finite_index : ∀ (I : AutInst), (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ IsOpen (I.Kg g) ∧ (∀ x ∈ I.Kset, ∀ y ∈ I.Kg g, x * y * x⁻¹ ∈ I.Kg g) ∧ ∃ s : Finset I.Gf, ∀ x ∈ I.Kset, ∃ t ∈ s, t⁻¹ * x ∈ I.Kg g := by
  intro I
  obtain ⟨-, -, -, hKc, -, hK, hg⟩ := GlobalTheory.CongTop.adelic_topology I
  refine ⟨hK, fun g hg1 => ?_⟩
  obtain ⟨hKgo, ⟨H, hH⟩, hnorm⟩ := hg g hg1
  refine ⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩

  have hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := fun t _ =>
    hKgo.preimage (continuous_const_mul t⁻¹)
  have hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := by
    intro x hx
    refine Set.mem_biUnion hx ?_
    show x⁻¹ * x ∈ I.Kg g
    rw [inv_mul_cancel, ← hH]
    exact H.one_mem
  obtain ⟨b, -, hb, hcov⟩ := hKc.elim_finite_subcover_image hopen hsub
  refine ⟨hb.toFinset, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨t, hb.mem_toFinset.mpr ht, hxt⟩

end GlobalTheory.CongTop
end

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_const_mul t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_const_mul x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraints
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraints
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm

theorem pairsPar : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  intro Ca Cg cb Cw cT CT C0 C' Cl D large₂ hH hK hC' hCl hCa
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩
  obtain ⟨_, _, hvI, hv1, hf, _, hfin, _, _, _, _, hg2, hT⟩ := hH D large₂ hStd
  obtain ⟨⟨hS0, _, _⟩, _⟩ := hK
  obtain ⟨_, h2, h3, _, h5, _, h7, _, _, _, h11, h12, _, _, _, _, _, _, _, _, _, _, h23, h24, h25⟩ := hS0
  have hL : 1 < large₂.sc.L := one_lt_scale_L D large₂
  have hb2 : 2 ≤ large₂.sc.b := two_le_scale_b D large₂
  have hlb : Real.log large₂.sc.b = large₂.sc.L := log_scale_eq_L D large₂
  refine ⟨by rw [hfin, hf], (two_rank_add_two_eq_m D).symm, h24, by rw [hf]; exact h3, ?_, by rw [hlb]; exact h7,
    by rw [hf]; exact h5, hb2, by rw [hvI]; exact hv1, ?_, ?_, ?_⟩
  · rw [hf]
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by positivity
    have : ((D.R.m ^ 5 * D.R.f : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc (D.R.m : ℝ) ^ 5 * D.R.f = 1 * ((D.R.m : ℝ) ^ 5 * D.R.f) * 1 := by ring
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f) * large₂.sc.L := by gcongr <;> linarith
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := h2
    exact_mod_cast this
  · rw [hvI]
    have hrd : 0 < D.host.rdE := pf_rd_pos D
    have hL0 : 0 < large₂.sc.L := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine h11.trans ?_
      rw [div_le_iff₀ h25]; nlinarith
    have h2v : 2 * D.host.v = D.host.rdE := by
      show 2 * (D.host.rdE / 2) = D.host.rdE; ring
    rw [h2v]
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.2 h1
      _ = large₂.sc.b := by rw [← hlb, Real.exp_log (by linarith)]
  · have hg1 : 1 ≤ D.host.g 1 := by
      rcases Nat.eq_zero_or_pos (D.host.g 1) with h | h
      · have : gS D = 0 := by simp [Lat.gS, h]
        omega
      · exact h
    calc ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := h12
      _ = (D.host.g 0 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by gcongr; exact_mod_cast hg1
      _ = (gS D : ℝ) := by simp [Lat.gS]
  · intro u
    refine ⟨(hT u).1.one_lt.le, ?_⟩
    have h := (h23 u).2
    calc (Tu D u : ℝ) = Tr D u := rfl
      _ ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := h
      _ ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        have : (0 : ℝ) ≤ D.R.m := by positivity
        nlinarith

end GlobalTheory.TypeAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ParameterSizeConstraintsStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_size_constraints : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.TypeAsm.pairsPar | exact GlobalTheory.TypeAsm.pairsPar | (intros; apply GlobalTheory.TypeAsm.pairsPar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeans
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeans
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsSum

theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {α β γ : Type*} (s : Finset α) (A : Finset β) (A' : Finset γ) (w : α → ℝ≥0∞)
    (T : α → β → γ → ℝ≥0∞) (c : β → γ → ℝ≥0∞) :
    ∑ a ∈ s, w a * ∑ x ∈ A, ∑ x' ∈ A', T a x x' * c x x' =
      ∑ x ∈ A, ∑ x' ∈ A', c x x' * ∑ a ∈ s, w a * T a x x' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pairs_sum_le : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  intro D large₂ X Y u hStd hCompat hPerRow hMean W HW hEmb hInv B hB hOrb j' j'' δ' δ'' S hS
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => inv_nonneg.2 (Nat.cast_nonneg _)

  have hterm : ∀ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) =
      wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) := by
    intro p hp
    have hall : p ∈ (Y.tO u u).allPairs Set.univ := by
      have h1 := (hS p hp).1
      simp only [Formalism.FourierDecayAlt.PB.Terms.allPairs, Set.mem_ofPred_eq] at h1 ⊢
      exact ⟨Set.mem_univ _, Set.mem_univ _, h1.2.2⟩
    obtain ⟨hl, hl', -⟩ := hCompat D X Y u p hall
    unfold Formalism.L2.SG.TermOp.wt
    rw [← hl, ← hl', Real.mul_self_sqrt, mul_assoc]
    exacts [rfl, mul_nonneg (hw _) (hw _)]

  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p => p.1.lam) (t := Y.what₂ u) (fun p _ => p.1.mem)]
  refine (ofReal_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun Λ _ => ?_).trans ((le_of_eq (matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero (Y.what₂ u) (Finset.Icc 1 ⌊k2Del D j' δ'⌋₊) (Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊)
    (fun Λ => ENNReal.ofReal (wRow D (X.Fu u) Λ))
    (fun Λ x x' => (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞))
    (fun x x' => ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')))).trans ?_)
  ·
    beta_reduce
    have hrw : ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam * (wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) =
        wRow D (X.Fu u) Λ * ∑ p ∈ S with p.1.lam = Λ, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.1 hp).2]
    rw [hrw, ENNReal.ofReal_mul (hw Λ)]
    refine mul_le_mul' le_rfl (hPerRow D large₂ X Y u hStd W HW hEmb Λ j' j'' δ' δ'' _ fun p hp => ?_)
    obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hpS
    exact ⟨h1, hpΛ, h2, h3, h4, h5⟩
  ·
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => mul_le_mul' le_rfl ?_
    exact hMean D large₂ X Y u hStd W HW hEmb
      (fun M => (((GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) (B x x') (hB x x')
      (fun s M => by simp only [hInv s M x x'])
      (fun Λ hΛ => hOrb Λ hΛ x x' (Finset.mem_Icc.1 hx).1 (Finset.mem_Icc.1 hx').1)

end GlobalTheory.TypeAsm.PairsSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeansStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → CompatC → PerRowC →
    RowsMeanC → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (M : Submodule (𝓞 D.host.E) W) (x x' : ℕ),
      (GlobalTheory.DegCnt.Trip HW (gS D) (s • M) D.R.rS x x').encard = (GlobalTheory.DegCnt.Trip HW (gS D) M D.R.rS x x').encard) →
    ∀ B : ℕ → ℕ → ℝ, (∀ x x', 0 ≤ B x x') →
    (∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B x x')) →
    ∀ (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ENNReal.ofReal (∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) ≤
      ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
        ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
          GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x') *
        ENNReal.ofReal (massC Y u * B x x') := by
  first | exact @GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | exact GlobalTheory.TypeAsm.PairsSum.pairs_sum_le | (intros; apply GlobalTheory.TypeAsm.PairsSum.pairs_sum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengths
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YBound

open GlobalTheory.Amp.GramFlag (eucl_eq)

theorem det_upper {r : ℕ} (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upper]
  · intro a b h
    have h' : b < a := h
    simp [upper, not_lt.2 h'.le, h'.ne']

theorem det_change {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) (U U' : Matrix (Fin j) (Fin j) ℂ)
    (hU : U.det = 1) (hU' : U'.det = 1) :
    (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)).det =
      (Matrix.of fun a b => B (y a) (y' b)).det := by
  have e : (Matrix.of fun a b => B (∑ c, U c a • y c) (∑ c, U' c b • y' c)) =
      Uᵀ * (Matrix.of fun a b => B (y a) (y' b)) * (U'ᴴ)ᵀ := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_; simp; ring)
  rw [e]
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hU, hU']

theorem prod_le_pow' {n : ℕ} (f : Fin n → ℝ) (R : ℝ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ R) :
    ∏ i, f i ≤ R ^ n := by
  calc _ ≤ ∏ _a : Fin n, R := Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => h i
    _ = _ := by simp

def formE {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip ∘ₗ Matrix.toEuclideanLin H

theorem formE_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    formE H (WithLp.toLp 2 v) (WithLp.toLp 2 w) = herm H v w := by
  show ⟪(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 (H *ᵥ v)⟫_ℂ = _
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm]

theorem formE_le {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ * H = 1) (v w : EuclideanSpace ℂ (Fin n)) :
    ‖formE H v w‖ ≤ ‖v‖ * ‖w‖ := by
  have h1 : ‖Matrix.toEuclideanLin H v‖ = ‖v‖ := by
    have : ⟪Matrix.toEuclideanLin H v, Matrix.toEuclideanLin H v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      congr 1
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hH]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), this, ← norm_eq_sqrt_re_inner]
  show ‖⟪w, Matrix.toEuclideanLin H v⟫_ℂ‖ ≤ _
  rw [mul_comm, ← h1]
  exact norm_inner_le_norm _ _

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have h : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem gramProj_le {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ)
    (U : Matrix (Fin r) (Fin r) ℂ) (hU : U.det = 1) (R : ℝ) (hR : ∀ a, eucl (∑ b, U b a • v b) ≤ R) :
    gramProj P v ≤ R ^ r := by
  have h := (Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gramHadamard (EuclideanSpace ℂ (Fin n)) r
    (fun a => ∑ b, U b a • P.starProjection (WithLp.toLp 2 (v b)))).2 R (fun a => by
      refine le_trans ?_ (hR a)
      rw [eucl_eq, WithLp.toLp_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_smul, ← map_sum, WithLp.toLp_smul]
      exact P.norm_starProjection_apply_le _)
  have e : ∀ w : Fin r → EuclideanSpace ℂ (Fin n), (Matrix.gram ℂ w).det =
      (Matrix.of fun a b => (innerₛₗ ℂ).flip (w a) (w b)).det := by
    intro w
    rw [← Matrix.det_transpose]
    rfl
  unfold gramProj
  rw [e, det_change _ _ _ U U hU hU, ← e] at h
  exact h

theorem dr_y_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  intro k r z z' γ hT x hx
  obtain ⟨hz, hz', -, -, hg, -, -⟩ := hT
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hG := uHGroup _ _ hH
  have hgx : γ * x ∈ GG k r := hG.2.1 _ hg _ hx
  obtain ⟨u', hu', -⟩ := GramFlag.gramSchmidt_lengths k r z' x hx
  obtain ⟨u, hu, -⟩ := GramFlag.gramSchmidt_lengths k r z _ hgx
  have h1 : ∀ a, eucl (∑ b, upper u b a • ((γ * x)⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z (γ * x) := fun a => by
    rw [(hu a).1]; exact (((LInv.lengths_basic k r z hz).2.2 _).2.1 _).2
  have h2 : ∀ a, eucl (∑ b, upper u' b a • (x⁻¹ *ᵥ bvec (eI k r b))) ≤ Sg k r z' x := fun a => by
    rw [(hu' a).1]; exact (((LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2
  have hD0 : 0 ≤ Dr k r z z' γ := norm_nonneg _
  refine ⟨?_, div_nonneg (Real.sqrt_nonneg _) hD0, ?_⟩
  · have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.wedgeHadamard _ _ (formE (Hpk k r))
      (formE_le _ (by rw [(hpkFacts k r).1, (hpkFacts k r).2.1])) r
      (fun a => ∑ b, upper u' b a • WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r b)))
      (fun a => ∑ b, upper u b a • WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))
    rw [det_change _ _ _ _ _ (det_upper u') (det_upper u)] at h
    have e : Dmin k r z z' γ ⟨r, by omega⟩ = (Matrix.of fun a b : Fin r => formE (Hpk k r)
        (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r a))) (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r b)))).det := by
      unfold Dmin
      rw [← Matrix.det_transpose]
      congr 1
      ext a b
      have ha := a.2
      have hb := b.2
      simp only at ha hb
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Formalism.QuantumDeterminants.Zhat, fvec, Matrix.of_apply, formE_apply]
      rw [dite_eq_left (by simpa using ha), dite_eq_left (by simpa using hb),
        ← herm_mulVec (hG.2.2 _ hgx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_mul_cancel_right _ _ (hG.2.2 _ hg).1]
      rfl
    unfold Dr
    rw [e]
    refine h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_)
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h2 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · refine prod_le_pow' _ _ (fun _ => norm_nonneg _) fun a => le_trans (le_of_eq ?_) (h1 a)
      rw [eucl_eq, WithLp.toLp_sum]; rfl
    · exact pow_nonneg (zero_le_one.trans ((LInv.lengths_basic k r z' hz').2.2 _).1) _
  · unfold Yv
    refine div_le_div_of_nonneg_right ?_ hD0
    refine gramProj_le _ _ (upper u) (det_upper u) _ fun a => ?_
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_inv_rev] using h1 a

end GlobalTheory.Amp.YBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopMinorAndGramNumberLeMajorantLengthsStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_minor_and_gram_number_le_majorant_lengths : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ → ∀ x ∈ GG k r, Dr k r z z' γ ≤ Sg k r z' x ^ r * Sg k r z (γ * x) ^ r ∧ 0 ≤ Yv k r z z' γ x ∧ Yv k r z z' γ x ≤ Sg k r z (γ * x) ^ r / Dr k r z z' γ := by
  first | exact @GlobalTheory.Amp.YBound.dr_y_le | exact GlobalTheory.Amp.YBound.dr_y_le | (intros; apply GlobalTheory.Amp.YBound.dr_y_le <;> assumption)
end
end
