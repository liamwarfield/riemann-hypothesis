module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.InvU

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem ac_mul (V : HSp D) {a b : ℕ} (g h : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V (g * h) z = ac V g (ac V h z) := by
  simp only [ac, mm, mt_mul, Matrix.mul_assoc]

theorem measurable_ac (V : HSp D) {a b : ℕ} (g : GA D V) :
    Measurable (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) V.rank a b
  have o1 : OpensMeasurableSpace (Mx D V.rank a × Mx D V.rank b) := g1.opensMeasurable
  have hc : Continuous (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) :=
    (continuous_ac V).comp (continuous_const.prodMk continuous_id)
  exact hc.measurable

theorem rho_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    rho hn I μ x₀ A = Q0 I μ (zp d hn x₀ ⁻¹' A) :=
  Measure.map_apply (measurable_zp d hn x₀) hA

def sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (A : Set (Mx D B.rank W.rank × Mx D B.rank t)) (x : GA D B) : ℝ≥0∞ :=
  rho hn I μ x₀ {z | ac B x⁻¹ z ∈ A}

theorem measurable_sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) : Measurable (sA hn I μ x₀ A) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oB : OpensMeasurableSpace (GA D B) := hB.opensMeasurable
  have e1 : SecondCountableTopologyEither (GA D B) (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (GA D B × Par D n t W) := Prod.opensMeasurableSpace
  have := sigmaFinite_parameter_product_measure I μ hμ
  have hc : Continuous fun p : GA D B × Par D n t W => ac B p.1⁻¹ (zp d hn x₀ p.2) :=
    (continuous_ac B).comp ((continuous_fst.inv).prodMk ((continuous_zp d hn x₀).comp continuous_snd))
  have hS : MeasurableSet {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A} := hc.measurable hA
  have key := measurable_measure_prodMk_left (ν := Q0 I μ) hS
  have e : sA hn I μ x₀ A = fun x => Q0 I μ (Prod.mk x ⁻¹' {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A}) := by
    funext x
    exact rho_apply hn I μ x₀ (measurable_ac B x⁻¹ hA)
  rw [e]
  exact key

theorem sA_stab (hL : Law) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) (q : GlobalTheory.RegSW.stab d) (x : GA D B) :
    sA hn I μ x₀ A (q * x) = ((GlobalTheory.RegSW.absDet d q ^ (W.rank + t) : ℝ≥0) : ℝ≥0∞) * sA hn I μ x₀ A x := by
  have hA' : MeasurableSet {z | ac B x⁻¹ z ∈ A} := measurable_ac B x⁻¹ hA
  have h1 := congrArg (fun ν : Measure _ => ν {z | ac B x⁻¹ z ∈ A}) (hL D n t B W d hn I μ hμ x₀ q⁻¹)
  beta_reduce at h1
  rw [Measure.map_apply (measurable_ac B _) hA'] at h1
  have e : sA hn I μ x₀ A (q * x) = rho hn I μ x₀ (ac B ((q⁻¹ : GlobalTheory.RegSW.stab d) : GA D B) ⁻¹' {z | ac B x⁻¹ z ∈ A}) := by
    unfold sA
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, Subgroup.coe_inv]
  rw [e, h1, map_inv, inv_inv]
  rfl

theorem nuT_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    nuT hn I μ x₀ A = ∫⁻ k : I.l.K, sA hn I μ x₀ A (k : GA D B) ∂I.νK := by
  have := sigmaFinite_parameter_product_measure I μ hμ
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hA, Measure.prod_apply (measurable_pi hn I x₀ hA)]
  refine lintegral_congr fun k => ?_
  exact (rho_apply hn I μ x₀ (measurable_ac B (k : GA D B)⁻¹ hA)).symm

theorem nuT_map_ac (hQ : QK) (hL : Law) (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) (x₀) (h : GA D B) :
    (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  change (nuT hn I μ x₀).map (ac B h) = nuT hn I μ x₀
  refine Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (ac B h ⁻¹' A) := measurable_ac B h hA
  rw [Measure.map_apply (measurable_ac B h) hA, nuT_apply hn I μ hμ x₀ hA', nuT_apply hn I μ hμ x₀ hA]
  have key := hQ D t B W d I.l I.good I.νK I.haarK (sA hn I μ x₀ A) (measurable_sA hn I μ hμ x₀ hA)
    (fun q x => sA_stab hL hn I μ hμ x₀ hA q x) h⁻¹
  rw [← key]
  refine lintegral_congr fun k => ?_
  unfold sA
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, inv_inv]

end GlobalTheory.CompanionTheory.ColumnSplitting.InvU

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_unitary_group_invariant : QK → Law → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (h : GA D B), (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | exact GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolume
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib


open scoped Pointwise in
theorem map_mul_fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) (a : ℝ≥0) (ha : ‖x‖ = (a : ℝ)⁻¹) :
    lam.map (fun y => x * y) = a • lam := by
  open scoped Pointwise in
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v x hx
    have he : Units.mk0 x hx = hu.unit := by
      ext
      simp
    rw [he] at h
    simpa [ha] using congrArg (fun z : ℝ≥0 => (z : ℝ)) h
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem mass_scalT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact inv_ne_zero ha' hnorm.symm
  have hs := map_mul_fv v lam t ht a hnorm
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => c
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact hcu
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]
    rw [Subsingleton.elim p 0, mul_comm]
  obtain ⟨-, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g :=
    fun S => rfl
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    rw [hτ, hts]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g,
      Matrix.of_apply]
    ring
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    have h1 : Continuous τ :=
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
    exact h1.measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    apply Subtype.ext
    rw [hτ]
    simp
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : a ^ M = a * a ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have key3 := (ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2
  have hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    rfl
  rw [hset, ← key3]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolumeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rank_one_zero_fibre_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibility
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibility
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv

variable {l : ℕ} [Fact l.Prime]

theorem continuous_omC : Continuous (omC (l := l)) :=
  (AddMonoidHomClass.isometry_of_norm (omC (l := l)) norm_omC).continuous

theorem tail_le (K : FinExt l) (c : ℕ → ↥(OL K)) (y x : Om l) (hy : ‖omC y‖ ≤ 1)
    (hs : HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * y ^ k) x) (D : ℕ) :
    ‖omC x - ∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i‖ ≤ ‖omC y‖ ^ D := by
  have ht : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, oc K (c i) * omC y ^ i)
      Filter.atTop (nhds (omC x)) := by
    have h1 := (continuous_omC (l := l)).continuousAt.tendsto.comp hs.tendsto_sum_nat
    refine h1.congr fun N => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Function.comp, map_sum, map_mul, map_pow]
    rfl
  have h2 := (ht.sub_const (∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i)).norm
  refine le_of_tendsto h2 ?_
  filter_upwards [Filter.eventually_ge_atTop D] with N hN
  rw [← Finset.sum_Ico_eq_sub _ hN]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (norm_oc_le_one K _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hy (Finset.mem_Ico.1 hk).1)

theorem norm_read {ρ : ℝ} (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) (a y : Tl l) (b : ℕ → Tl l)
    (A Y : ℂ_[l]) (B : ℕ → ℂ_[l]) (D : ℕ) (hY : ‖Y‖ ≤ 1) (hA : ‖sh a - A‖ ≤ ρ)
    (hy : ‖sh y - Y‖ ≤ ρ) (hb : ∀ i, ‖sh (b i) - B i‖ ≤ ρ) :
    ‖a - ∑ i ∈ Finset.range D, b i * y ^ i‖ ≤
      max ρ ‖A - ∑ i ∈ Finset.range D, B i * Y ^ i‖ := by
  have h1 : ‖sh (∑ i ∈ Finset.range D, b i * y ^ i) - ∑ i ∈ Finset.range D, B i * Y ^ i‖ ≤ ρ :=
    near_sum hρ _ fun i _ => near_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hY)
      (hb i) (near_pow hρ hY hy i)
  have h2 := near_sub hρ hA h1
  rw [norm_eq_norm_sh]
  set x := a - ∑ i ∈ Finset.range D, b i * y ^ i
  set W := A - ∑ i ∈ Finset.range D, B i * Y ^ i
  have e : sh x = (sh x - W) + W := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h2 le_rfl)

theorem pow_read (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem pow_compat {f : ℕ} {u : ℕ → Tl l} (hu : ∀ n, u (n + 1) ^ l ^ f = u n) (n m : ℕ) :
    u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hu, ih]

theorem pow_fixed {f : ℕ} {x : Tl l} (hx : x ^ l ^ f = x) (m : ℕ) : x ^ l ^ (f * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hx, ih]

theorem exists_pow_le {f : ℕ} (hf : 0 < f) {ρ ε : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ m, 2 ≤ m ∧ ρ ^ l ^ (f * m) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨N + 2, by omega, (pow_le_pow_of_le_one h0 h1.le ?_).trans hN.le⟩
  have h2 : N + 2 < l ^ (N + 2) := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
  have h3 : l ^ (N + 2) ≤ l ^ (f * (N + 2)) :=
    Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left _ hf)
  omega

theorem galdiv : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  intro l _ K π z f hf hl hπ hz1 hz2 u hu hun r₀ hr hrn hu0 g c hs n D
  rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, norm_pow]
  set ρ := ‖oc K π‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hε : 0 < ‖u n‖ ^ D := pow_pos (norm_pos_iff.2 (hu0 n)) D
  obtain ⟨m, hm, hmρ⟩ := exists_pow_le (l := l) hf hρ0 hπ hε
  set k := n + m with hk
  have hk2 : 2 ≤ k := by omega
  have hzk : ‖omC (z k)‖ ≤ 1 := (hz1 k).le
  have hnorm : ‖omC (z k)‖ ≤ ‖u k‖ := by
    by_contra hlt
    push_neg at hlt
    have e : omC (z k) = sh (u k) - (sh (u k) - omC (z k)) := by ring
    have h3 : ‖omC (z k)‖ ≤ max ‖sh (u k)‖ ρ := by
      conv_lhs => rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max le_rfl (by rw [norm_neg]; exact hun k))
    rcases le_max_iff.1 h3 with h4 | h4
    · rw [← norm_eq_norm_sh] at h4; linarith
    · linarith [hz2 k hk2]
  have hA : ‖sh (actT g (u k)) - omC (g (z k))‖ ≤ ρ := by
    rw [sh_actT, ← galCp_omC, ← map_sub, norm_galCp]
    exact hun k
  have hread := norm_read hl (actT g (u k)) (u k) (fun i => r₀ (c i)) (omC (g (z k))) (omC (z k))
    (fun i => oc K (c i)) D hzk hA (hun k) (fun i => hrn _)
  have htail := tail_le K c (z k) (g (z k)) hzk (hs k) D
  have hx : ‖actT g (u k) - ∑ i ∈ Finset.range D, r₀ (c i) * u k ^ i‖ ≤ max ρ (‖u k‖ ^ D) :=
    hread.trans (max_le_max le_rfl (htail.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm D)))
  have hpow := pow_read (f * m) (actT g (u k)) (u k) (fun i => r₀ (c i)) D
  have hc : u k ^ l ^ (f * m) = u n := pow_compat hu n m
  have ha : actT g (u k) ^ l ^ (f * m) = actT g (u n) := by rw [← map_pow, hc]
  simp only [pow_fixed (hr _) m, hc, ha] at hpow
  rw [← hpow, norm_pow]
  have hun' : ‖u k‖ ^ l ^ (f * m) = ‖u n‖ := by rw [← norm_pow, hc]
  refine (pow_le_pow_left₀ (norm_nonneg _) hx _).trans ?_
  rcases le_total ρ (‖u k‖ ^ D) with h | h
  · rw [max_eq_right h, ← pow_mul, mul_comm, pow_mul, hun']
  · rw [max_eq_left h]; exact hmρ

end GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibilityStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | exact GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv.galdiv <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

variable {E : Type} [Field E] [NumberField E]

def kcSub {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : Submodule (𝓞 E) (Fin m → 𝓞 E) where
  carrier := (Kc c : Set (Fin m → 𝓞 E))
  add_mem' := fun hx hy => (Kc c).add_mem hx hy
  zero_mem' := (Kc c).zero_mem
  smul_mem' := by
    intro r y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨r * o, ?_⟩
    have h : (fun j => algebraMap (𝓞 E) E ((r • y) j)) =
        (algebraMap (𝓞 E) E r) • fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, ← ho, map_mul, smul_eq_mul]

def pair {m : ℕ} (w : Fin m → E) : (Fin m → 𝓞 E) →ₗ[𝓞 E] E where
  toFun y := ∑ j, w j * (y j : E)
  map_add' := by
    intro y z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change w j * ((r * y j : 𝓞 E) : E) = r • (w j * (y j : E))
    rw [Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring

def bMod {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : Submodule (𝓞 E) E :=
  1 ⊔ (kcSub c).map (pair w)

theorem bMod_fg {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : (bMod c w).FG := by
  refine Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))
  rw [Submodule.one_eq_span]
  exact Submodule.fg_span_singleton _

variable {F : Type} [Field F] [Algebra F E]

theorem sO_mem_tor (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (hsO : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E)) {m : ℕ}
    (c : Matrix (Fin m) (Fin m) E) (hc : ∀ a b, σ (c b a) = c a b) (u : Fin m → E) (a : 𝓞 E)
    (ha : ∀ y ∈ Kc c, (a : E) * ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E)) :
    sO σ a ∈ tor c u := by
  have hmem : (sO σ a) • u ∈ lam c := by
    refine GlobalTheory.T.mem_lattice_of_dual_pairing E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) _ ?_
    intro a' hL

    have hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m := by
      intro j i
      by_cases h : i = j
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, h]⟩
    have hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j := by
      intro j
      have h1 := hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)
      rw [Submodule.mem_one] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, by rw [ho]; simp⟩
    choose o ho using hent
    have hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i := by
      intro i
      have hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c :=
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))
      have h1 := hL _ hx
      rw [Submodule.mem_one] at h1
      obtain ⟨p, hp⟩ := h1
      refine ⟨p, ?_⟩
      rw [hp]
      simp [dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
    have hy : (fun j => sO σ (o j)) ∈ Kc c := by
      intro i
      obtain ⟨p, hp⟩ := hcol i
      refine ⟨sO σ p, ?_⟩
      have e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p) := hsO p
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, hp, map_sum]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j) := by
        rw [← ho j]; exact hsO (o j)
      rw [e2, map_mul, hc i j, mul_comm]
    have h2 := ha _ hy
    rw [Submodule.mem_one] at h2 ⊢
    obtain ⟨q, hq⟩ := h2
    refine ⟨sO σ q, ?_⟩
    have e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q) := hsO q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, hq, map_mul, map_sum]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j) := by
      rw [hsO, ← ho j]
    simp only [e3, map_mul, hinv, Algebra.smul_def]
    have e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E) := hsO a
    rw [e4]
    ring
  rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover


open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
  intro F E _ _ _ _ _ σ hcm m c hc u b hb
  obtain ⟨hinv, -, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  set w : Fin m → E := fun j => σ (u j) with hw
  let B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    ⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩
  have hB1 : (1 : E) ∈ B := by
    change (1 : E) ∈ bMod c w
    exact Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hB1
    exact one_ne_zero hB1
  have hBi : B⁻¹ ≠ 0 := inv_ne_zero hB0
  have hbB : b ∈ B := by
    have hbi : b ∈ (B⁻¹)⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hBi]
      intro x hx
      rw [FractionalIdeal.mem_inv_iff hB0] at hx
      have hx1 := hx 1 hB1
      rw [mul_one, FractionalIdeal.mem_one_iff] at hx1
      obtain ⟨a, rfl⟩ := hx1
      have ht : sO σ a ∈ tor c u := by
        refine sO_mem_tor σ hinv hsO c hc u a ?_
        intro y hy
        have hyB : ∑ j, σ (u j) * (y j : E) ∈ B := by
          change _ ∈ bMod c w
          exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))
        have := hx _ hyB
        rw [FractionalIdeal.mem_one_iff] at this
        obtain ⟨q, hq⟩ := this
        rw [Submodule.mem_one]
        exact ⟨q, hq⟩
      have h := hb _ ht
      rw [hsO, hinv] at h
      rw [Submodule.mem_one] at h
      obtain ⟨q, hq⟩ := h
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨q, ?_⟩
      rw [mul_comm]
      exact hq
    rwa [inv_inv] at hbi
  have hbB' : b ∈ bMod c w := hbB
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hbB'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨y, hy, ?_⟩
  have : b - ∑ j, σ (u j) * (y j : E) = p := by
    rw [← hpz]
    change p + ∑ j, σ (u j) * (y j : E) - _ = p
    ring
  rw [this]
  exact hp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolutionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_orthogonality_integral_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingHomMulSubEqZero
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SmallRatCell

open RestrictedProduct InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem exists_nat_mem (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.prod_pos fun v _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  refine ⟨2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal, by omega, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ : Ideal.absNorm v.asIdeal ∣ 2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    (Finset.dvd_prod_of_mem _ hv).mul_left 2
  rw [hc]
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

def tau (N k : ℕ) : ℚ := (N : ℚ) ^ k / (1 + ((N : ℚ) ^ k) ^ 2)

theorem tau_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : 0 < tau N k := by
  have : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold tau
  positivity

theorem tendsto_tau_fin (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Tendsto (fun k => algebraMap F (v.adicCompletion F) ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  have hv : Valued.v (N : v.adicCompletion F) < 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) :=
      (map_natCast _ N).symm
    rw [e]
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
    have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (N : 𝓞 F)).2 hN
    exact h1 ▸ h2
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have h2 : Tendsto (fun k : ℕ => 1 + ((N : v.adicCompletion F) ^ k) ^ 2) atTop (𝓝 1) := by
    simpa using (ht.pow 2).const_add 1
  have h3 := ht.div h2 one_ne_zero
  rw [zero_div] at h3
  refine h3.congr fun k => ?_
  simp [tau, map_div₀, map_add (f := _), map_pow, map_natCast]

theorem tendsto_tau_inf (w : InfinitePlace F) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun k => algebraMap F w.Completion ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ k, ‖algebraMap F w.Completion ((tau N k : ℚ) : F)‖ = (tau N k : ℝ) := fun k => by
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    have h := map_ratCast ((extensionEmbedding w).comp (algebraMap F w.Completion)) (tau N k)
    rw [RingHom.comp_apply] at h
    rw [h, Complex.norm_ratCast, abs_of_pos (by exact_mod_cast tau_pos hN k)]
  simp only [hnorm]
  have hb : ∀ k, (tau N k : ℝ) ≤ (1 / 2 : ℝ) ^ k := fun k => by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : (2 : ℝ) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hxp : (0 : ℝ) < (N : ℝ) ^ k := by linarith
    simp only [tau]
    push_cast
    rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ 1 + ((N : ℝ) ^ k) ^ 2 := by nlinarith
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith
  refine squeeze_zero (fun k => by exact_mod_cast (tau_pos hN k).le) hb ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)


open Classical in
def finS (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) q else 0, by
    rw [Filter.eventually_principal]
    intro v hv
    have hv' : v ∉ S := by simpa using hv
    simp only [if_neg hv']
    exact zero_mem _⟩

theorem cofinite_le (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

def sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) : AF F :=
  (fun w => algebraMap F w.Completion q,
    RestrictedProduct.inclusion _ _ (cofinite_le S) (finS S q))

theorem tendsto_sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : ℕ → F)
    (hi : ∀ w : InfinitePlace F, Tendsto (fun k => algebraMap F w.Completion (q k)) atTop (𝓝 0))
    (hf : ∀ v ∈ S, Tendsto (fun k => algebraMap F (v.adicCompletion F) (q k)) atTop (𝓝 0)) :
    Tendsto (fun k => sAd S (q k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => finS S (q k)) atTop (𝓝 0) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    by_cases hv : v ∈ S
    · refine (hf v hv).congr fun k => ?_
      exact (if_pos hv).symm
    · refine tendsto_const_nhds.congr fun k => ?_
      show (0 : v.adicCompletion F) = _
      exact (if_neg hv).symm
  have h2 := ((RestrictedProduct.continuous_inclusion (cofinite_le S)).tendsto 0).comp h1
  refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hi) h2

theorem one_tmul_algebraMap {A E : Type} [CommRing A] [Algebra F A] [Field E] [Algebra F E] (q : F) :
    (1 : A) ⊗ₜ[F] algebraMap F E q = algebraMap F A q ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem ring_hom_mul_sub_eq_zero {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x e y : A) (c : B)
    (hc : f e = c) (h : f x * c = f y) : f (x * e - y) = 0 := by
  rw [map_sub, map_mul, hc, h, sub_self]


open Classical in
theorem tensor_key {E : Type} [Field E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : AF F ⊗[F] E) (hi : ∀ w, compInf F E w e = 1)
    (hf : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) (q : F) :
    ((1 : AF F) ⊗ₜ[F] algebraMap F E q) * e = sAd S q ⊗ₜ[F] (1 : E) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.CompanionTheory.AdeleComp.tensor_eq_zero _ (fun w => ?_) (fun v => ?_)
  · refine ring_hom_mul_sub_eq_zero (compInf F E w) _ _ _ _ (hi w) ?_
    rw [mul_one]
    exact one_tmul_algebraMap (A := w.Completion) _
  · refine ring_hom_mul_sub_eq_zero (compFin F E v) _ _ _ _ (hf v) ?_
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_one]
      have h : evFin F v (sAd S q) = algebraMap F (v.adicCompletion F) q := if_pos hv
      show (1 : v.adicCompletion F) ⊗ₜ[F] _ = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h]
      exact one_tmul_algebraMap _
    · rw [if_neg hv, mul_zero]
      have h : evFin F v (sAd S q) = 0 := if_neg hv
      show 0 = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h, TensorProduct.zero_tmul]

theorem incA_mul_idem (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) (q : ℚ) :
    incA D ((q : ℚ) : D.host.E) * e = sAd S ((q : ℚ) : D.host.F) • (1 : AE D) := by
  have hq : ((q : ℚ) : D.host.E) = algebraMap D.host.F D.host.E ((q : ℚ) : D.host.F) :=
    (map_ratCast (algebraMap D.host.F D.host.E) q).symm
  have hs : sAd S ((q : ℚ) : D.host.F) • (1 : AE D) =
      sAd S ((q : ℚ) : D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show _ • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, hq]
  exact tensor_key S e he.1 he.2 _

theorem smallRat : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.SmallRat := by
  intro _ D S e he V hV M
  obtain ⟨N, hN, hmem⟩ := exists_nat_mem S
  have ht : Tendsto (fun k => sAd S ((tau N k : ℚ) : D.host.F)) atTop (𝓝 0) :=
    tendsto_sAd S _ (fun w => tendsto_tau_inf w hN) (fun v hv => tendsto_tau_fin v (hmem v hv))
  have hz : Tendsto (fun k => incA D ((tau N k : ℚ) : D.host.E) * e) atTop (𝓝 0) := by
    have h := ht.smul_const (1 : AE D)
    rw [zero_smul] at h
    exact h.congr fun k => (incA_mul_idem D S e he _).symm
  have hall : ∀ᶠ k in atTop, ∀ j : Fin M,
      ((j.1 + 1 : ℕ) : AE D) * (incA D ((tau N k : ℚ) : D.host.E) * e) ∈ V := by
    rw [Filter.eventually_all]
    intro j
    have h := hz.const_mul ((j.1 + 1 : ℕ) : AE D)
    rw [mul_zero] at h
    exact h hV
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨fun j => ((j.1 + 1 : ℕ) : ℚ) * tau N k, fun i j hij => ?_, fun j => ?_⟩
  · have h := mul_right_cancel₀ (tau_pos hN k).ne' hij
    have h2 : i.1 + 1 = j.1 + 1 := by exact_mod_cast h
    exact Fin.ext (by omega)
  · have h := hk j
    have e1 : incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) =
        ((j.1 + 1 : ℕ) : AE D) * incA D ((tau N k : ℚ) : D.host.E) := by
      rw [Rat.cast_mul, map_mul, Rat.cast_natCast, map_natCast]
    show incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) * e ∈ V
    rw [e1, mul_assoc]
    exact h

end GlobalTheory.CompanionTheory.SmallRatCell

end
end
