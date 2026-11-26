module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverage
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBisStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.MapMulRightEqOfMemCompactSubgroup
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.Xa1

theorem map_mul_right_eq_of_mem_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ → ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, μ.map (fun x => x * k) = μ := by
  intro G _ _ _ _ _ _ _ _ μ hinv hfin K hK k hk
  let ν : Measure G := Measure.haar
  have hmeas : Measurable (fun x : G => x * k) := measurable_mul_const k
  have key : ν.map (fun x => x * k) = ν := by
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
    have hS : IsCompact (C * (K : Set G)) := hC.mul hK
    have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
    have hpos : ν (C * (K : Set G)) ≠ 0 :=
      ((Measure.measure_pos_of_mem_nhds ν hC1).trans_le (measure_mono hsub)).ne'
    have htop : ν (C * (K : Set G)) ≠ ⊤ := hS.measure_lt_top.ne
    have hpre : (fun x : G => x * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
      ext x
      constructor
      · rintro ⟨c, hc, l, hl, h⟩
        refine ⟨c, hc, l * k⁻¹, K.mul_mem hl (K.inv_mem hk), ?_⟩
        simp only at h ⊢
        rw [← mul_assoc, h, mul_inv_cancel_right]
      · rintro ⟨c, hc, l, hl, rfl⟩
        exact ⟨c, hc, l * k, K.mul_mem hl hk, (mul_assoc _ _ _).symm⟩
    haveI : IsFiniteMeasureOnCompacts (ν.map (fun x => x * k)) :=
      ⟨fun L hL => by
        rw [Measure.map_apply hmeas hL.measurableSet]
        exact ((Homeomorph.mulRight k).isCompact_preimage.2 hL).measure_lt_top⟩
    have h1 := Measure.isMulLeftInvariant_eq_smul (ν.map (fun x => x * k)) ν
    set c := Measure.haarScalarFactor (ν.map (fun x => x * k)) ν with hc
    have h2 : (ν.map (fun x => x * k)) (C * (K : Set G)) = ν (C * (K : Set G)) := by
      rw [Measure.map_apply hmeas hS.measurableSet, hpre]
    rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : (c : ℝ≥0∞) = 1 := by
      have := (ENNReal.mul_left_inj hpos htop).1 (h2.trans (one_mul _).symm)
      exact this
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h1, h4, one_smul]
  have h := Measure.isMulLeftInvariant_eq_smul μ ν
  rw [h, Measure.map_smul, key]
  exact hmeas.aemeasurable

end GlobalTheory.CompanionTheory.Xa1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStable
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscKfin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem fin_cpt_apply (u : GL (Fin M) (Af E)) (k : Kinf E M) (a : Sm E M) :
    finRep E M u (cptRep E M k a) = cptRep E M k (finRep E M u a) := by
  have h : finRep E M u * cptRep E M k = cptRep E M k * finRep E M u := by
    change rt E M (finGL E M u) * rt E M (infGL E M (Unitary.toUnits k)) =
      rt E M (infGL E M (Unitary.toUnits k)) * rt E M (finGL E M u)
    rw [← map_mul, ← map_mul, infGL_comm]
  exact LinearMap.congr_fun h a

theorem continuous_coeff (A : Submodule ℂ (Sm E M)) [FiniteDimensional ℂ A]
    (hA : ∀ k, ∀ a ∈ A, cptRep E M k a ∈ A) (ℓ : Sm E M →ₗ[ℂ] ℂ) (a : Sm E M) (ha : a ∈ A) :
    Continuous fun k => ℓ (cptRep E M k a) := by
  let ev : GA E M → Module.Dual ℂ A := fun g =>
    (LinearMap.proj g).comp ((Sm E M).subtype.comp A.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ g, v.1.1 g = 0 := fun g => hv _ (Submodule.subset_span ⟨g, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    set_option synthInstance.maxHeartbeats 400000 in
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev),
      Continuous fun k => ξ ⟨cptRep E M k a, hA k a ha⟩ := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact GlobalTheory.CompanionTheory.AdmDiscFin.continuous_slice a g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key (ℓ.comp A.subtype) (hspan ▸ Submodule.mem_top)

end GlobalTheory.CompanionTheory.FinDiscKfin

theorem GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) →
      ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧
        (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧
        ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  intro E _ _ _ N V hV L x hx hL
  haveI hfin : FiniteDimensional ℂ (GlobalTheory.AutGrowth.spanK E N x) := (hV.aut x hx).kfin
  refine ⟨GlobalTheory.AutGrowth.spanK E N x, hfin, GlobalTheory.AutGrowth.self_mem_spanK x, ?_,
    GlobalTheory.AutGrowth.spanK_stable x, fun ℓ a ha =>
      GlobalTheory.CompanionTheory.FinDiscKfin.continuous_coeff _ (GlobalTheory.AutGrowth.spanK_stable x) ℓ a ha⟩
  intro a ha
  refine ⟨?_, fun u hu => ?_⟩
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hV.stable (.cpt k) x hx
    | zero => exact V.zero_mem
    | add y z _ _ hy hz => exact V.add_mem hy hz
    | smul c y _ hy => exact V.smul_mem c hy
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      change finRep E N u (cptRep E N k x) = cptRep E N k x
      rw [GlobalTheory.CompanionTheory.FinDiscKfin.fin_cpt_apply, hL u hu]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
    | smul c y _ hy => rw [map_smul, hy]

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStableStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_dim_compact_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) → ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧ (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧ ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | exact GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | (intros; apply GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLe
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem exists_compact_open_level_le (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (S : Subgroup (GL (Fin N) (Af E))) (hS : IsOpen (S : Set (GL (Fin N) (Af E)))) :
    ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧
      IsCompact (L : Set (GL (Fin N) (Af E))) := by
  let K : Subgroup (GL (Fin N) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E N
  have hKo : IsOpen (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N
  have hKc : IsCompact (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E N
  have hSc : IsClosed (S : Set (GL (Fin N) (Af E))) := Subgroup.isClosed_of_isOpen S hS
  refine ⟨S ⊓ K, inf_le_left, ?_, ?_⟩
  · change IsOpen ((S : Set (GL (Fin N) (Af E))) ∩ (K : Set (GL (Fin N) (Af E))))
    exact hS.inter hKo
  · have : ((S ⊓ K : Subgroup _) : Set (GL (Fin N) (Af E))) =
        (K : Set (GL (Fin N) (Af E))) ∩ (S : Set (GL (Fin N) (Af E))) := by
      ext x; simp [and_comm]
    rw [this]
    exact hKc.inter_right hSc

end GlobalTheory.CompanionTheory.FinDiscOrth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLeStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_subgroup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Subgroup (GL (Fin N) (Af E))), IsOpen (S : Set (GL (Fin N) (Af E))) → ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧ IsCompact (L : Set (GL (Fin N) (Af E))) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | exact GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.exists_compact_open_level_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariant
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
open scoped RestrictedProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicUnimod

open GroundTheory.Automorphic

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem modularCharacter_eq_one_of_map (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (h : μ.map (fun x => x * z) = μ) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
  rw [h] at h1
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m C) h1
  have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
  simp only [Measure.coe_nnreal_smul_apply] at h2
  have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

theorem modularCharacter_eq_one_of_central (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (hz : ∀ h, z * h = h * z) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  refine modularCharacter_eq_one_of_map μ ?_
  rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
    Measure.IsMulLeftInvariant.map_mul_left_eq_self]

theorem modularCharacter_eq_one_of_compact (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : (Measure.modularCharacter k : ℝ≥0) = 1 :=
  modularCharacter_eq_one_of_map μ
    (GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup G μ inferInstance inferInstance K hK k hk)

theorem isMulRightInvariant_of_modularCharacter (μ : Measure G) [μ.IsHaarMeasure]
    (h : ∀ g : G, (Measure.modularCharacter g : ℝ≥0) = 1) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h g, one_smul]

end General

section Products

theorem pi_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (Δ : (∀ i, H i) →* ℝ≥0) (h : ∀ i (x : H i), Δ (Pi.mulSingle i x) = 1) (x : ∀ i, H i) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : ∀ i, H i), (∀ i, i ∉ S → x i = 1) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      rw [show x = 1 from funext fun i => hx i (by simp), map_one]
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (Pi.mulSingle a (x a))⁻¹) * Pi.mulSingle a (x a) := by simp
      rw [e, map_mul, h, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp
      · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  exact key Finset.univ x (by simp)

theorem restricted_eq_one {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    {A : ∀ i, Subgroup (H i)} (Δ : (Πʳ i, [H i, A i]) →* ℝ≥0)
    (h1 : ∀ i (x : H i), Δ (RestrictedProduct.mulSingle A i x) = 1)
    (h2 : ∀ x : Πʳ i, [H i, A i], (∀ i, x i ∈ A i) → Δ x = 1) (x : Πʳ i, [H i, A i]) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : Πʳ i, [H i, A i]), (∀ i, i ∉ S → x i ∈ A i) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun x hx => h2 x fun i => hx i (by simp)
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (RestrictedProduct.mulSingle A a (x a))⁻¹) *
          RestrictedProduct.mulSingle A a (x a) := by simp
      rw [e, map_mul, h1, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp [RestrictedProduct.mulSingle_eq_same, one_mem]
      · simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
          RestrictedProduct.mulSingle_eq_of_ne A _ hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  have hfin : {i | x i ∉ A i}.Finite := x.2
  exact key hfin.toFinset x fun i hi => by simpa using hi

def singleHom {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (A : ∀ i, Subgroup (H i)) (i : ι) : H i →* Πʳ i, [H i, A i] where
  toFun := RestrictedProduct.mulSingle A i
  map_one' := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]
  map_mul' x y := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]

end Products

section Adelic

variable (E : Type) [Field E] [NumberField E] (N : ℕ)

abbrev PInf : Type := ∀ w : InfinitePlace E, GL (Fin N) w.Completion

abbrev AInt (v : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin N) (v.adicCompletion E)) :=
  GLnLocal.integralGL (v.adicCompletion E) N

abbrev PFin : Type := Πʳ v : HeightOneSpectrum (𝓞 E), [GL (Fin N) (v.adicCompletion E), AInt E N v]


open GroundTheory.Automorphic.AdelicGLn in
def finInc : FiniteAdelicGL E N →* GA E N :=
  ((prodEquiv E N).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)

open GroundTheory.Automorphic.AdelicGLn in
theorem continuous_finInc : Continuous (finInc E N) :=
  (prodEquiv E N).symm.continuous.comp (continuous_const.prodMk continuous_id)


open GroundTheory.Automorphic.AdelicGLn in
theorem isMulRightInvariant_GA (μ : Measure (GA E N)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_modularCharacter μ fun g => ?_
  let e := restrictedProductEquiv E N
  let Δ : PInf E N × PFin E N →* ℝ≥0 := (Measure.modularCharacter : GA E N →* ℝ≥0).comp e.symm.toMulEquiv.toMonoidHom
  have hΔ : ∀ z, Δ z = Measure.modularCharacter (e.symm z) := fun _ => rfl
  have hcen : ∀ z, (∀ h, z * h = h * z) → Δ z = 1 := fun z hz => by
    rw [hΔ]
    refine modularCharacter_eq_one_of_central μ fun h => ?_
    have := hz (e h)
    apply e.injective
    simpa [map_mul] using this
  have hinf : ∀ (w : InfinitePlace E) (x : GL (Fin N) w.Completion),
      Δ (Pi.mulSingle w x, 1) = 1 := fun w x => by
    let ι : GL (Fin N) w.Completion →* PInf E N × PFin E N :=
      (MonoidHom.inl (PInf E N) (PFin E N)).comp (MonoidHom.mulSingle (fun w : InfinitePlace E => GL (Fin N) w.Completion) w)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (funext fun u => ?_) (by simp [ι])
    by_cases hu : u = w
    · subst hu
      simpa [ι] using hc (h.1 u)
    · simp [ι, Pi.mulSingle_eq_of_ne hu]
  have hfin : ∀ (v : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (v.adicCompletion E)),
      Δ (1, RestrictedProduct.mulSingle (AInt E N) v x) = 1 := fun v x => by
    let ι : GL (Fin N) (v.adicCompletion E) →* PInf E N × PFin E N :=
      (MonoidHom.inr (PInf E N) (PFin E N)).comp (singleHom (AInt E N) v)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (by simp [ι]) ?_
    ext u : 1
    by_cases hu : u = v
    · subst hu
      simpa [ι, singleHom, RestrictedProduct.mulSingle_eq_same] using hc (h.2 u)
    · simp [ι, singleHom, RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
  have hint : ∀ b : PFin E N, (∀ v, b v ∈ AInt E N v) → Δ (1, b) = 1 := fun b hb => by
    have hk : (finiteRestrictedEquiv E N).symm b ∈ integralFiniteGL E N :=
      (mem_integralFiniteGL_iff_forall E N).2 (by simpa using hb)
    have hcomp : IsCompact (((integralFiniteGL E N).map (finInc E N) : Subgroup (GA E N)) : Set (GA E N)) := by
      rw [Subgroup.coe_map]
      exact (isCompact_integralFiniteGL E N).image (continuous_finInc E N)
    have he : e.symm (1, b) = finInc E N ((finiteRestrictedEquiv E N).symm b) := by
      apply e.injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · show 1 = infiniteEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).1
        simp
      · show b = finiteRestrictedEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).2
        simp
    rw [hΔ, he]
    exact modularCharacter_eq_one_of_compact μ _ hcomp (Subgroup.mem_map_of_mem _ hk)
  have hall : ∀ z, Δ z = 1 := fun z => by
    have hz : z = (z.1, 1) * (1, z.2) := by simp
    rw [hz, map_mul]
    have a1 : Δ (z.1, 1) = 1 :=
      pi_eq_one (Δ.comp (MonoidHom.inl (PInf E N) (PFin E N))) (fun w x => hinf w x) z.1
    have a2 : Δ (1, z.2) = 1 :=
      restricted_eq_one (Δ.comp (MonoidHom.inr (PInf E N) (PFin E N))) (fun v x => hfin v x) (fun b hb => hint b hb) z.2
    rw [a1, a2, one_mul]
  have := hall (e g)
  rwa [hΔ, ContinuousMulEquiv.symm_apply_apply] at this

end Adelic

theorem isMulRightInvariant_GA_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N μ _ => isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.AdelicUnimod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | exact GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | (intros; apply GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjection
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscAvg

theorem exists_sum_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (x : W) (ho : IsOpen {k | ρ k x = x}) :
    ∃ R : Finset G, R.Nonempty ∧ ∀ u, ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ r x := by
  let K : Subgroup G :=
    { carrier := {k | ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h : ρ a⁻¹ (ρ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h }
  have hK : ∀ k, k ∈ K ↔ ρ k x = x := fun _ => Iff.rfl
  obtain ⟨R, hR, hc⟩ := GlobalTheory.compact_finite_leftCoset_reps G K ho Set.univ isCompact_univ
  have hc' : ∀ g : G, ∃ r ∈ R, r⁻¹ * g ∈ K := fun g => hc g (Set.mem_univ g)
  have hne : R.Nonempty := by
    obtain ⟨r, hr, -⟩ := hc' 1
    exact ⟨r, hr⟩
  refine ⟨R, hne, fun u => ?_⟩
  choose! σ hσR hσ using fun r : G => hc' (u * r)
  have hval : ∀ r, ρ (u * r) x = ρ (σ r) x := by
    intro r
    have h := (hK _).1 (hσ r)
    have e : u * r = σ r * ((σ r)⁻¹ * (u * r)) := by group
    rw [e, map_mul, Module.End.mul_apply, h]
  have hinj : Set.InjOn σ R := by
    intro r hr r' hr' e
    refine hR r hr r' hr' ?_
    have h1 := hσ r
    have h2 := hσ r'
    rw [show σ r = σ r' from e] at h1
    have := K.mul_mem (K.inv_mem h1) h2
    have e2 : ((σ r')⁻¹ * (u * r))⁻¹ * ((σ r')⁻¹ * (u * r')) = r⁻¹ * r' := by group
    rwa [e2] at this
  have himg : R.image σ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hσR r
    · rw [Finset.card_image_of_injOn hinj]
  calc ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ (σ r) x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hval, map_mul, Module.End.mul_apply]
    _ = ∑ s ∈ R.image σ, ρ s x := (Finset.sum_image (f := fun s => ρ s x) hinj).symm
    _ = ∑ r ∈ R, ρ r x := by rw [himg]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem l2Map_right_translate (k : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ squareIntegrableSmoothSubmoduleGL μ) (hb : finRep E N k a ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Map μ (finRep E N k a) = R (latticeGL E N) μ (finGL E N k) (l2Map μ a) := by
  rw [l2Map_apply μ ha, l2Map_apply μ hb, right_translate_toL2]
  rfl

theorem inner_R (g : GA E N) (u v : L2 (latticeGL E N) μ) :
    ⟪R (latticeGL E N) μ g u, R (latticeGL E N) μ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let T : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g : L2 (latticeGL E N) μ →L[ℂ] L2 (latticeGL E N) μ).toLinearMap, norm_R g⟩
  exact T.inner_map_map u v

theorem exists_avg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ V hV L hL x hx
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  let ρ : L →* Module.End ℂ (Sm E N) := (finRep E N).comp L.subtype
  have hρ : ∀ l : L, ρ l = finRep E N (l : GL (Fin N) (Af E)) := fun _ => rfl
  have ho : IsOpen {k : L | ρ k x = x} :=
    (hV.aut x hx).level.preimage continuous_subtype_val
  obtain ⟨S, hS, hfix⟩ := exists_sum_fixed ρ x ho
  have hn : ((S.card : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
  have hmem : ∀ l : L, ρ l x ∈ V := fun l => hV.stable (.fin _) x hx
  refine ⟨(S.card : ℂ)⁻¹ • ∑ r ∈ S, ρ r x, V.smul_mem _ (V.sum_mem fun r _ => hmem r), ?_, ?_⟩
  · intro u hu
    rw [map_smul, ← hρ ⟨u, hu⟩ , hfix]
  · intro y hy hyL
    have hl2 : ∀ z ∈ V, z ∈ squareIntegrableSmoothSubmoduleGL μ := fun z hz => mem_l2Sub_of_isAutForm μ (hV.aut z hz) (hV.sqInt z hz)
    have hxl := hl2 x hx
    have key : ∀ r : L, ⟪l2Map μ (ρ r x), l2Map μ y⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
      intro r
      have e1 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hxl (hl2 _ (hmem r))
      have e2 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hy (by rw [hyL _ r.2]; exact hy)
      rw [hyL _ r.2] at e2
      rw [hρ, e1]
      conv_lhs => rw [e2]
      exact inner_R μ _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, inner_smul_left, sum_inner, Finset.sum_congr rfl fun r _ => key r,
      Finset.sum_const, nsmul_eq_mul, map_inv₀, Complex.conj_natCast, inv_mul_cancel_left₀ hn]

end GlobalTheory.CompanionTheory.FinDiscAvg

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjectionStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | exact GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | (intros; apply GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2Inner
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2Inner
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem setIntegral_mul_conj_eq_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  intro E _ _ _ N μ _ F hF x y hx hy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, MemL2Quotient.inner_toL2_eq_theta_pairing, pet_eq hF ((mem_l2Sub μ).1 hx).1 ((mem_l2Sub μ).1 hy).1]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2InnerStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_l2_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | exact GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometry
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometry
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem rt_mem_l2Sub_and_inner_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N) (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  have key : ∀ z : Sm E N, ∀ hz : z ∈ squareIntegrableSmoothSubmoduleGL μ, ∃ h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ,
      l2Map μ (rt E N g z) = R (latticeGL E N) μ g (l2Map μ z) := by
    intro z hz
    have h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ := ((mem_l2Sub μ).1 hz).mul_right g
    refine ⟨h', ?_⟩
    rw [l2Map_apply μ h', l2Map_apply μ hz, right_translate_toL2]
    rfl
  obtain ⟨hx', ex⟩ := key x hx
  obtain ⟨hy', ey⟩ := key y hy
  refine ⟨hx', ?_⟩
  let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  rw [ex, ey]
  exact U.inner_map_map _ _

end GlobalTheory.CompanionTheory.FinDiscOrth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometryStatement
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translate_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N), x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | exact GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphic
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc.Orth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def fixS (V : Submodule ℂ (Sm E N)) (L : Subgroup (GL (Fin N) (Af E))) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ L, finRep E N u x = x}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩

theorem mem_l2_of_discrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) : x ∈ squareIntegrableSmoothSubmoduleGL μ := mem_l2Sub_of_isAutForm μ (hV.aut x hx) (hV.sqInt x hx)

theorem cont_of_mem {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N} (hx : x ∈ V) : Continuous x.1 :=
  ContAut.continuous_of_isOpen_stab E N x (hV.aut x hx).level

theorem eq_zero_of_l2Map_eq_zero_of_isDiscrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) (h0 : l2Map μ x = 0) : x = 0 := by
  by_contra hne
  have := re_l2Form_pos μ (mem_l2_of_discrete μ hV hx) (cont_of_mem hV hx) hne
  simp [l2Form, h0] at this

def stabS (x : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k x = x}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) x = x
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change finRep E N 1 x = x
    rw [map_one, Module.End.one_apply]
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ x = x
    have h : finRep E N a⁻¹ (finRep E N a x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

theorem exists_repr (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x : Sm E N} (hx : x ∈ V) :
    ∃ y ∈ V', ∀ z ∈ V', ⟪l2Map μ z, l2Map μ x⟫_ℂ = ⟪l2Map μ z, l2Map μ y⟫_ℂ := by
  obtain ⟨L, hLS, hLo, hLc⟩ := GlobalTheory.T.exists_open_compact_subgroup_le E N (stabS x) (hV.aut x hx).level
  have hunit : ∀ (k : Kinf E N) {W W' : Submodule ℂ (Sm E N)}, IsDiscrete W → IsDiscrete W' → ∀ a ∈ W, ∀ b ∈ W',
      ⟪l2Map μ (cptRep E N k a), l2Map μ (cptRep E N k b)⟫_ℂ = ⟪l2Map μ a, l2Map μ b⟫_ℂ :=
    fun k _ _ h h' a ha b hb => (GlobalTheory.T.right_translate_isometry E N μ _ a b (mem_l2_of_discrete μ h ha) (mem_l2_of_discrete μ h' hb)).2
  letI : MeasurableSpace (Kinf E N) := borel _
  haveI : BorelSpace (Kinf E N) := ⟨rfl⟩
  haveI : CompactSpace (Kinf E N) := GlobalTheory.KinfCompactness.compactSpace_Kinf E N
  have key := GlobalTheory.T.representation_unitary_average (Measure.haar : Measure (Kinf E N)) (cptRep E N) (l2Map μ) (fixS V L) (fixS V' L)
    (fun g : GA E N => (LinearMap.proj g).comp (Sm E N).subtype)
    (fun k a ha b hb => hunit k hV' hV a ha.1 b hb.1)
    (fun k a ha b hb => hunit k hV' hV' a ha.1 b hb.1)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V hV L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V' hV' L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun W hW => by
      haveI := GlobalTheory.CompanionTheory.AdmDiscFin.admissible_discrete_spaces E N L W hLo hW V' hV'
      refine Submodule.finiteDimensional_of_le (Submodule.span_mono (t := {φ | φ ∈ V' ∧ TypeB L W φ}) ?_)
      rintro a ⟨ha, hW'⟩
      exact ⟨ha.1, fun u hu g => congrFun (congrArg Subtype.val (ha.2 u hu)) g, hW'⟩)
  have hfx : ∀ u ∈ L, finRep E N u x = x := fun u hu => hLS hu
  obtain ⟨y, hy, hyz⟩ := key x ⟨hx, hfx⟩
  refine ⟨y, hy.1, fun z hz => ?_⟩
  obtain ⟨z', hz', hfix, e⟩ := GlobalTheory.T.exists_invariant_projection E N μ V' hV' L hLc z hz
  rw [e x (mem_l2_of_discrete μ hV hx) hfx, e y (mem_l2_of_discrete μ hV' hy.1) hy.2]
  exact hyz z' ⟨hz', hfix⟩

theorem exists_adj (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (o : Op E N) :
    ∃ o' : Op E N, ∀ {V W : Submodule ℂ (Sm E N)}, IsDiscrete V → IsDiscrete W → ∀ x ∈ V, ∀ y ∈ W,
      ⟪l2Map μ x, l2Map μ (act o y)⟫_ℂ = ⟪l2Map μ (act o' x), l2Map μ y⟫_ℂ := by
  cases o with
  | fin k =>
    refine ⟨.fin k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (finGL E N k) (act (.fin k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = finRep E N k (finRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | cpt k =>
    refine ⟨.cpt k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (infGL E N (Unitary.toUnits k)) (act (.cpt k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = cptRep E N k (cptRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | lie X =>
    refine ⟨.lie (-X), fun {V W} hV hW x hx y hy => ?_⟩
    have hxX := hV.stable (.lie X) x hx
    have hyX := hW.stable (.lie X) y hy
    have h := GlobalTheory.T.lie_skew_adjoint_l2' E N μ X x y (cont_of_mem hV hx) (cont_of_mem hW hy) (cont_of_mem hV hxX) (cont_of_mem hW hyX)
      (mem_l2_of_discrete μ hV hx) (mem_l2_of_discrete μ hW hy) (mem_l2_of_discrete μ hV hxX) (mem_l2_of_discrete μ hW hyX)
    have e : act (.lie (-X)) x = - lie E N X x := by
      change lie E N (-X) x = _
      rw [map_neg]; rfl
    rw [e, map_neg, inner_neg_left]
    exact h

theorem isoV_of_ne (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x₀ y₀ : Sm E N} (hx₀ : x₀ ∈ V) (hy₀ : y₀ ∈ V')
    (hne : ⟪l2Map μ y₀, l2Map μ x₀⟫_ℂ ≠ 0) : IsoV V V' := by
  have uniq : ∀ a ∈ V', ∀ b ∈ V', (∀ z ∈ V', ⟪l2Map μ z, l2Map μ a⟫_ℂ = ⟪l2Map μ z, l2Map μ b⟫_ℂ) → a = b := by
    intro a ha b hb h
    have h1 := h (a - b) (V'.sub_mem ha hb)
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero] at h1
    exact sub_eq_zero.1 (eq_zero_of_l2Map_eq_zero_of_isDiscrete μ hV' (V'.sub_mem ha hb) h1)
  choose T hTm hT using fun x : V => exists_repr μ hV hV' x.2
  let Tl : V →ₗ[ℂ] V' :=
    { toFun := fun x => ⟨T x, hTm x⟩
      map_add' := fun x y => Subtype.ext (uniq _ (hTm _) _ (V'.add_mem (hTm x) (hTm y)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_add, map_add (f := _), inner_add_right]
        rw [← hT x z hz, ← hT y z hz])
      map_smul' := fun c x => Subtype.ext (uniq _ (hTm _) _ (V'.smul_mem c (hTm x)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_smul, map_smul, inner_smul_right, RingHom.id_apply]
        rw [← hT x z hz]) }
  have hTl : ∀ x : V, (Tl x).1 = T x := fun _ => rfl
  have eqv : ∀ (o : Op E N) (x y : V), y.1 = act o x.1 → (Tl y).1 = act o (Tl x).1 := by
    intro o x y hxy
    obtain ⟨o', ho'⟩ := exists_adj μ o
    refine uniq _ (hTm y) _ (hV'.stable o _ (hTm x)) fun z hz => ?_
    rw [hTl, ← hT y z hz, hxy, ho' hV' hV z hz _ x.2, ho' hV' hV' z hz _ (hTm x),
      hT x _ (hV'.stable o' z hz)]
  have hnz : Tl ≠ 0 := by
    intro h0
    apply hne
    have h1 : T ⟨x₀, hx₀⟩ = 0 := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x₀, hx₀⟩)
    rw [hT ⟨x₀, hx₀⟩ y₀ hy₀, h1, map_zero, inner_zero_right]
  have hker : LinearMap.ker Tl = ⊥ := by
    have hst : _root_.GlobalTheory.CuspRep.IsStable ((LinearMap.ker Tl).map V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      refine ⟨⟨_, hV.stable o _ x.2⟩, ?_, rfl⟩
      refine Subtype.ext ?_
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
      rw [eqv o x _ rfl, hx]
      simp
    rcases hV.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact Submodule.map_injective_of_injective V.injective_subtype (by rwa [Submodule.map_bot])
    · exfalso
      refine hnz (LinearMap.ext fun x => ?_)
      have : x.1 ∈ (LinearMap.ker Tl).map V.subtype := by rw [h]; exact x.2
      obtain ⟨x', hx', e⟩ := this
      obtain rfl : x' = x := Subtype.ext e
      exact hx'
  have hran : LinearMap.range Tl = ⊤ := by
    have hst : _root_.GlobalTheory.CuspRep.IsStable ((LinearMap.range Tl).map V'.subtype) := by
      rintro o _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Tl ⟨_, hV.stable o _ x.2⟩, ⟨_, rfl⟩, eqv o x _ rfl⟩
    rcases hV'.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exfalso
      have h1 : LinearMap.range Tl = ⊥ :=
        Submodule.map_injective_of_injective V'.injective_subtype (by rwa [Submodule.map_bot])
      exact hnz (LinearMap.range_eq_bot.1 h1)
    · rw [eq_top_iff]
      intro y _
      have : y.1 ∈ (LinearMap.range Tl).map V'.subtype := by rw [h]; exact y.2
      obtain ⟨y', hy', e⟩ := this
      obtain rfl : y' = y := Subtype.ext e
      exact hy'
  refine ⟨LinearEquiv.ofBijective Tl ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩, ?_⟩
  intro o x y hxy
  exact eqv o x y hxy

end GlobalTheory.CompanionTheory.FinDisc.Orth


open GlobalTheory.CompanionTheory.FinDisc.Orth in
theorem GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  intro E _ _ _ N mG bG μ _ F hF V V' hV hV' hno φ hφ ψ hψ
  obtain rfl : mG = borel _ := bG.measurable_eq
  haveI := GlobalTheory.T.haar_right_invariant E N μ
  rw [GlobalTheory.T.integral_eq_l2_inner E N μ F hF φ ψ (mem_l2_of_discrete μ hV hφ) (mem_l2_of_discrete μ hV' hψ)]
  by_contra hne
  exact hno (isoV_of_ne μ hV hV' hφ hψ hne)

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphicStatement
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_of_non_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | exact GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | (intros; apply GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV <;> assumption)
end
