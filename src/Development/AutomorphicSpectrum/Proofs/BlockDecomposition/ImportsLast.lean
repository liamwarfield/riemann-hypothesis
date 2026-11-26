module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasure
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem isCompact_mt_preimage (V : HSp D) {T : Set (Mx D V.rank V.rank)} (hT : IsCompact T) :
    IsCompact {g : GA D V | mt V g ∈ T} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, i4, -⟩ := top_mx (D := D) V.rank V.rank
  have i1 : T1Space (Mx D V.rank V.rank) := @T2Space.t1Space _ _ i4
  have he : Topology.IsClosedEmbedding (fun g : GA D V =>
      Units.embedProduct (Mx D V.rank V.rank) (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g)) :=
    Units.isClosedEmbedding_embedProduct.comp (isClosedEmbedding_matHom_GAd D.sp.cm.sig V.gram)
  have hc : Continuous fun X : Mx D V.rank V.rank => giA V * (adj X * gA V) :=
    continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)
  have hK := he.isCompact_preimage (hT.prod ((hT.image hc).image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (hT.isClosed.preimage (continuous_mt V)) fun g hg => ?_
  refine ⟨hg, _, ⟨mt V g, hg, rfl⟩, ?_⟩
  simp only [Units.embedProduct_apply]
  rw [← GlobalTheory.MixModel.mt_inv]; rfl

theorem det_ne_zero {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} {b : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hb : b.det ≠ 0) (h : gramQ W x₀ = b) : x₀.det ≠ 0 := by
  intro h0
  apply hb
  rw [← h, gramQ]
  simp [Matrix.det_mul, h0]

theorem rat_inv_mul {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀⁻¹) (rat x₀) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem rat_mul_inv {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (h : x₀.det ≠ 0) :
    mm (rat x₀) (rat x₀⁻¹) = (1 : Mx D W.rank W.rank) := by
  rw [mm, ← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem join_first_second_columns_eq (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with s | s <;> simp [jn, c1, c2]

theorem continuous_jn (hn : W.rank + t = n) {a : ℕ} :
    Continuous fun p : Mx D a W.rank × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
  · exact (continuous_fst.matrix_elem i s)
  · exact (continuous_snd.matrix_elem i s)

theorem box_rec (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    mm d.p0 (mm d.jX u + mm d.j0 w) = w ∧ mm d.pX (mm d.jX u + mm d.j0 w) = u := by
  constructor
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.p0_j0,
      Matrix.zero_mul, Matrix.one_mul, zero_add]
  · rw [mm, Matrix.mul_add, mm, mm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.pX_jX, d.pX_j0,
      Matrix.zero_mul, Matrix.one_mul, add_zero]

theorem zp_rec (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (p : Par D n t W) :
    mm d.p0 (zp d hn x₀ p).1 = ww W x₀ p.1 ∧ mm d.pX (zp d hn x₀ p).1 = c1 hn p.2.1 ∧
      mm d.p0 (zp d hn x₀ p).2 = mm (ww W x₀ p.1) p.2.2 ∧
      mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2) = c2 hn p.2.1 := by
  obtain ⟨h1, h2⟩ := box_rec (a := W.rank) d (c1 hn p.2.1) (ww W x₀ p.1)
  refine ⟨h1, h2, ?_, ?_⟩
  · change mm d.p0 (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1)) = _
    simp only [mm] at h1 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc d.p0 _ p.2.2, h1, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  · change mm d.pX (mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 hn p.2.1) -
      mm (mm d.jX (c1 hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2) = _
    rw [add_sub_cancel_left, mm, mm, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]

theorem ac_ac (V : HSp D) {a b : ℕ} (g : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V g (ac V g⁻¹ z) = z := by
  have e : ∀ {c : ℕ} (x : Mx D V.rank c), mm (mt V g) (mm (mt V g⁻¹) x) = x := fun x => by
    rw [mm, mm, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul]
  exact Prod.ext (e z.1) (e z.2)

theorem exists_box (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    {x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E} (hx : x₀.det ≠ 0)
    {C : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hC : IsCompact C) :
    ∃ (Ah : Set (GA D W)) (AU : Set (Mx D t n)) (Ay : Set (Mx D W.rank t)),
      IsCompact Ah ∧ IsCompact AU ∧ IsCompact Ay ∧ ∀ (k : I.l.K) (p : Par D n t W),
        ac B ((k : GA D B)⁻¹) (zp d hn x₀ p) ∈ C → p.1 ∈ Ah ∧ p.2.1 ∈ AU ∧ p.2.2 ∈ Ay := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨t1, -, -, -, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨t2, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨t3, -, -, -, -⟩ := top_mx (D := D) t W.rank
  obtain ⟨t4, -, -, -, -⟩ := top_mx (D := D) t t
  set C' : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    (fun u : GA D B × (Mx D B.rank W.rank × Mx D B.rank t) => ac B u.1 u.2) '' ((I.l.K : Set (GA D B)) ×ˢ C) with hC'
  have cC' : IsCompact C' := (I.good.isCompact_K.prod hC).image (continuous_ac B)
  set Aw : Set (Mx D W.rank W.rank) := (fun z : Mx D B.rank W.rank × Mx D B.rank t => mm d.p0 z.1) '' C' with hAw
  have cAw : IsCompact Aw := cC'.image (continuous_const.matrix_mul continuous_fst)
  set T : Set (Mx D W.rank W.rank) := (fun X : Mx D W.rank W.rank => mm X (rat x₀⁻¹)) '' Aw with hT
  have cT : IsCompact T := cAw.image (continuous_id.matrix_mul continuous_const)
  set Ah : Set (GA D W) := (fun g : GA D W => g⁻¹) '' {g : GA D W | mt W g ∈ T} with hAh
  have cAh : IsCompact Ah := (isCompact_mt_preimage W cT).image continuous_inv
  set Ay : Set (Mx D W.rank t) :=
    (fun u : GA D W × (Mx D B.rank W.rank × Mx D B.rank t) => mm (rat x₀⁻¹) (mm (mt W u.1) (mm d.p0 u.2.2))) ''
      (Ah ×ˢ C') with hAy
  have cAy : IsCompact Ay := (cAh.prod cC').image (continuous_const.matrix_mul
    (((continuous_mt W).comp continuous_fst).matrix_mul
      (continuous_const.matrix_mul (continuous_snd.comp continuous_snd))))
  set AU : Set (Mx D t n) :=
    (fun u : (Mx D B.rank W.rank × Mx D B.rank t) × Mx D W.rank t =>
      jn hn (mm d.pX u.1.1) (mm d.pX (u.1.2 - mm u.1.1 u.2))) '' (C' ×ˢ Ay) with hAU
  have s2 : ContinuousSub (Mx D B.rank t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ t2
  have cAU : IsCompact AU := (cC'.prod cAy).image ((continuous_jn (W := W) hn).comp
    ((continuous_const.matrix_mul (continuous_fst.comp continuous_fst)).prodMk
      (continuous_const.matrix_mul ((continuous_snd.comp continuous_fst).sub
        ((continuous_fst.comp continuous_fst).matrix_mul continuous_snd)))))
  refine ⟨Ah, AU, Ay, cAh, cAU, cAy, fun k p hp => ?_⟩
  have e1 := rat_mul_inv hx
  have e2 := rat_inv_mul hx
  simp only [mm] at e1 e2
  have hz : zp d hn x₀ p ∈ C' := ⟨((k : GA D B), ac B ((k : GA D B)⁻¹) (zp d hn x₀ p)), ⟨k.2, hp⟩, ac_ac B _ _⟩
  obtain ⟨r1, r2, r3, r4⟩ := zp_rec d hn x₀ p
  have hw : ww W x₀ p.1 ∈ Aw := ⟨_, hz, r1⟩
  have hg : mt W p.1⁻¹ ∈ T := ⟨_, hw, by
    change mm (mm (mt W p.1⁻¹) (rat x₀)) (rat x₀⁻¹) = _
    simp only [mm]
    rw [Matrix.mul_assoc, e1, Matrix.mul_one]⟩
  have hh : p.1 ∈ Ah := ⟨p.1⁻¹, hg, inv_inv _⟩
  have hy : p.2.2 ∈ Ay := ⟨(p.1, zp d hn x₀ p), ⟨hh, hz⟩, by
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm d.p0 (zp d hn x₀ p).2)) = _
    rw [r3]
    change mm (rat x₀⁻¹) (mm (mt W p.1) (mm (mm (mt W p.1⁻¹) (rat x₀)) p.2.2)) = _
    simp only [mm]
    rw [← Matrix.mul_assoc (mt W p.1), ← Matrix.mul_assoc (mt W p.1),
      GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, ← Matrix.mul_assoc, e2, Matrix.one_mul]⟩
  have hU : p.2.1 ∈ AU := ⟨(zp d hn x₀ p, p.2.2), ⟨hz, hy⟩, by
    change jn hn (mm d.pX (zp d hn x₀ p).1) (mm d.pX ((zp d hn x₀ p).2 - mm (zp d hn x₀ p).1 p.2.2)) = _
    rw [r2, r4, join_first_second_columns_eq]⟩
  exact ⟨hh, hU, hy⟩

end GlobalTheory.CompanionTheory.ColumnSplitting.Cpt

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem isFiniteMeasureOnCompacts_nuT : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  intro D n t B W d hn I μ hμ b₀ hb x₀ hx
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, -, k4, -⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, -, l4, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := 𝓕
  have := I.haar
  have := I.probK
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have := sigmaFinite_parameter_product_measure I μ hμ
  refine ⟨fun C hC => ?_⟩
  obtain ⟨Ah, AU, Ay, cAh, cAU, cAy, h⟩ := Cpt.exists_box d hn I (Cpt.det_ne_zero hb hx) hC
  rw [nuT, Measure.map_apply (measurable_pi hn I x₀) hC.measurableSet]
  have hsub : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹' C ⊆
      Set.univ ×ˢ (Ah ×ˢ (AU ×ˢ Ay)) := fun p hp => by
    obtain ⟨a, b, c⟩ := h p.1 p.2 hp
    exact ⟨trivial, a, b, c⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Q0, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (ENNReal.mul_lt_top cAh.measure_lt_top
    (ENNReal.mul_lt_top cAU.measure_lt_top cAy.measure_lt_top))

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasureStatement
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
theorem _root_.GlobalTheory.T.finite_on_compacts_orbit_measure : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → IsFiniteMeasureOnCompacts (nuT hn I μ x₀) := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT | exact GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.isFiniteMeasureOnCompacts_nuT <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormula
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
noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting.JnM

variable {D : D7} {a b r t n : ℕ}

theorem fromCols_mul_shear {R : Type} [Ring R] (w : Matrix (Fin a) (Fin r) R) (v : Matrix (Fin a) (Fin t) R)
    (y : Matrix (Fin r) (Fin t) R) :
    (Matrix.fromCols w v : Matrix (Fin a) (Fin r ⊕ Fin t) R) *
        (Matrix.fromBlocks 1 y 0 1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) =
      Matrix.fromCols w (w * y + v) := by
  ext i (k | k) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mm_jn (hn : r + t = n) (A : Mx D b a) (x : Mx D a r) (v : Mx D a t) :
    mm A (jn hn x v) = jn hn (mm A x) (mm A v) := by
  ext i j
  simp only [jn, mm, Matrix.submatrix_apply, id, Matrix.mul_apply]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;>
    simp [Matrix.mul_apply]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) :
    jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  simp only [jn, Matrix.add_apply, Matrix.submatrix_apply, id]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;> simp

theorem jn_c {W : HSp D} (hn : W.rank + t = n) (U : Mx D a n) :
    jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with k | k <;> simp [jn, c1, c2]

theorem shear_gen {R : Type} [Ring R] (hn : r + t = n) (w : Matrix (Fin a) (Fin r) R)
    (v : Matrix (Fin a) (Fin t) R) (y : Matrix (Fin r) (Fin t) R) :
    ((Matrix.fromCols w v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin a) (Fin n) R) *
        ((Matrix.fromBlocks 1 y 0 1).submatrix (finSumFinEquiv.trans (finCongr hn)).symm
          (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin n) (Fin n) R) =
      (Matrix.fromCols w (w * y + v)).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm := by
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_shear]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t) :
    mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v) :=
  shear_gen hn w v y

end GlobalTheory.CompanionTheory.ColumnSplitting.JnM

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnPi_holds : JnPi := by
  intro D n t B W d hn x₀ g p
  obtain ⟨h, U, y⟩ := p
  have hX : XU d hn x₀ h U =
      jn hn (mm d.jX (c1 hn U) + mm d.j0 (ww W x₀ h)) (mm d.jX (c2 hn U)) := by
    unfold XU
    conv_lhs => rw [← JnM.jn_c (W := W) hn U]
    have h0 : mm d.j0 (0 : Mx D W.rank t) = 0 := Matrix.mul_zero _
    rw [JnM.mm_jn, JnM.mm_jn, JnM.jn_add, h0, add_zero]
  simp only [hX, JnM.jn_bl, JnM.mm_jn]
  rfl

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormulaStatement
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
theorem _root_.GlobalTheory.T.joined_projection_formula : JnPi := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.jnPi_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Frame

theorem det_ne_zero_of_gramQ : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  intro D W b₀ hb x₀ hx h0
  apply hb
  rw [← hx]
  unfold gramQ
  simp [Matrix.det_mul, h0]

end GlobalTheory.CompanionTheory.ColumnSplitting.Frame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerateStatement
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
theorem _root_.GlobalTheory.T.det_ne_zero_of_gram_nondegenerate : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | exact GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainProperty
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.DomProof

section Maj

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sc (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) : E →L[ℝ] E :=
  ((2 : ℝ) ^ k)⁻¹ • ContinuousLinearMap.id ℝ E

theorem sc_apply (k : ℕ) (u : E) : sc E k u = ((2 : ℝ) ^ k)⁻¹ • u := rfl

theorem norm_sc_apply (k : ℕ) (u : E) : ‖sc E k u‖ = ((2 : ℝ) ^ k)⁻¹ * ‖u‖ := by
  rw [sc_apply, norm_smul, norm_inv, norm_pow, Real.norm_ofNat]

theorem norm_sc_le (k : ℕ) : ‖sc E k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [norm_sc_apply, one_mul]
  have h : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  exact mul_le_of_le_one_left (norm_nonneg _) h

theorem iter_term (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (z : ℂ) (k n : ℕ) (u : E) :
    iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u =
      z • (iteratedFDeriv ℝ n b (sc E k u)).compContinuousLinearMap fun _ => sc E k := by
  have h1 : ContDiff ℝ ∞ (b ∘ sc E k) := hb.comp (sc E k).contDiff
  have e : (fun v => z * b (sc E k v)) = z • (b ∘ sc E k) := rfl
  rw [e, iteratedFDeriv_const_smul_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top)),
    (sc E k).iteratedFDeriv_comp_right hb u (by exact_mod_cast le_top)]

theorem term_bound (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (A : ℕ → ℝ) (hA : ∀ n x, ‖iteratedFDeriv ℝ n b x‖ ≤ A n)
    (z : ℂ) (k n : ℕ) (u : E) : ‖iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u‖ ≤ ‖z‖ * A n := by
  rw [iter_term b hb, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h : ∏ _i : Fin n, ‖sc E k‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_sc_le k
  exact (mul_le_of_le_one_right (norm_nonneg _) h).trans (hA n _)

theorem term_zero (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0)
    (z : ℂ) (k n : ℕ) (u : E) (hu : (2 : ℝ) ^ (k + 1) < ‖u‖) :
    iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u = 0 := by
  rw [iter_term b hb, hs n _ ?_]
  · ext m
    simp
  · rw [norm_sc_apply, pow_succ] at *
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [inv_mul_eq_div, lt_div_iff₀ h2]
    linarith

theorem term_decay (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (A : ℕ → ℝ) (hA : ∀ n x, ‖iteratedFDeriv ℝ n b x‖ ≤ A n)
    (hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0) (z : ℂ) (k n p : ℕ) (u : E) :
    ‖u‖ ^ p * ‖iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u‖ ≤ ((2 : ℝ) ^ (k + 1)) ^ p * (‖z‖ * A n) := by
  by_cases hu : (2 : ℝ) ^ (k + 1) < ‖u‖
  · rw [term_zero b hb hs z k n u hu, norm_zero, mul_zero]
    have : 0 ≤ A n := (norm_nonneg _).trans (hA n 0)
    positivity
  · have h1 := term_bound b hb A hA z k n u
    have h2 : ‖u‖ ^ p ≤ ((2 : ℝ) ^ (k + 1)) ^ p := pow_le_pow_left₀ (norm_nonneg _) (not_lt.1 hu) p
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)

def cf (C : ℕ → ℝ) (k : ℕ) : ℝ := ⨅ N : ℕ, C N * (2 / (2 : ℝ) ^ k) ^ N

theorem cf_nonneg {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (k : ℕ) : 0 ≤ cf C k :=
  le_ciInf fun N => mul_nonneg (hC N) (by positivity)

theorem cf_le {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (k N : ℕ) : cf C k ≤ C N * (2 / (2 : ℝ) ^ k) ^ N :=
  ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact mul_nonneg (hC M) (by positivity)⟩ N

theorem le_cf {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) {r y : ℝ} (hr : 0 ≤ r) (h : ∀ N : ℕ, (1 + r) ^ N * y ≤ C N) {k : ℕ}
    (hk : (2 : ℝ) ^ k ≤ 2 * (1 + r)) : y ≤ cf C k := by
  refine le_ciInf fun N => ?_
  have h1 : (0 : ℝ) < 1 + r := by linarith
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h3 : 1 / (1 + r) ≤ 2 / (2 : ℝ) ^ k := by
    rw [div_le_div_iff₀ h1 h2]
    linarith
  have h4 : y ≤ C N * (1 / (1 + r)) ^ N := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h N
  exact h4.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 N) (hC N))

theorem summable_weighted {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (p : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Summable fun k => ((2 : ℝ) ^ (k + 1)) ^ p * (‖(cf C k : ℂ)‖ * a) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_two.mul_left (2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * a))
  rw [Complex.norm_real, Real.norm_of_nonneg (cf_nonneg hC k)]
  have h1 := cf_le hC k (p + 1)
  have h2 : ((2 : ℝ) ^ (k + 1)) ^ p * (C (p + 1) * (2 / (2 : ℝ) ^ k) ^ (p + 1)) =
      2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * (1 / 2) ^ k := by
    have h0 : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [div_pow, one_div, inv_pow, pow_succ (2 : ℝ) k, mul_pow, pow_succ ((2 : ℝ) ^ k) p]
    field_simp
  calc ((2 : ℝ) ^ (k + 1)) ^ p * (cf C k * a)
      ≤ ((2 : ℝ) ^ (k + 1)) ^ p * ((C (p + 1) * (2 / (2 : ℝ) ^ k) ^ (p + 1)) * a) := by gcongr
    _ = 2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * a * (1 / 2) ^ k := by
        rw [← mul_assoc, h2]
        ring

end Maj

section MajMain

open scoped ContDiff

theorem real_maj (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : X → E) (w : X → ℝ) (h : ∀ N : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖P x‖) ^ N * w x ≤ C) :
    ∃ F : SchwartzMap E ℂ, (∀ u, 0 ≤ (F u).re ∧ (F u).im = 0) ∧ ∀ x, w x ≤ (F (P x)).re := by
  choose C₀ hC₀ using h
  set C : ℕ → ℝ := fun N => max (C₀ N) 0 with hCd
  have hC : ∀ N, 0 ≤ C N := fun N => le_max_right _ _
  have hw : ∀ x N, (1 + ‖P x‖) ^ N * w x ≤ C N := fun x N => (hC₀ N x).trans (le_max_left _ _)
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set b : E → ℂ := fun u => ((φ u : ℝ) : ℂ) with hbd
  have hb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hsupp : tsupport b ⊆ Metric.closedBall (0 : E) 2 := by
    have : tsupport b ⊆ tsupport φ := closure_mono fun x hx h0 => hx (by simp [hbd, h0])
    rwa [φ.tsupport_eq] at this
  have hbs : HasCompactSupport b :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset (isClosed_tsupport b) hsupp
  have hA : ∀ n : ℕ, ∃ A : ℝ, ∀ x, ‖iteratedFDeriv ℝ n b x‖ ≤ A := fun n =>
    (hb.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support (hbs.iteratedFDeriv n)
  choose A hA using hA
  have hA0 : ∀ n, 0 ≤ A n := fun n => (norm_nonneg _).trans (hA n 0)
  have hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0 := by
    intro n x hx
    by_contra hne
    have h1 : x ∈ tsupport b := support_iteratedFDeriv_subset n hne
    have h2 := hsupp h1
    rw [mem_closedBall_zero_iff] at h2
    linarith
  set f : ℕ → E → ℂ := fun k v => (cf C k : ℂ) * b (sc E k v) with hfd
  have hf : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k => contDiff_const.mul (hb.comp (sc E k).contDiff)
  set v : ℕ → ℕ → ℝ := fun n k => ‖(cf C k : ℂ)‖ * A n with hvd
  have hsum : ∀ n, Summable (v n) := fun n => by
    have h0 := summable_weighted hC 0 (A n) (hA0 n)
    simp only [pow_zero, one_mul] at h0
    exact h0
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ ⊤ → Summable (v k) := fun k _ => hsum k
  have hd : ∀ (k i : ℕ) (x : E), (k : ℕ∞) ≤ ⊤ → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i :=
    fun k i x _ => term_bound b hb A hA _ i k x
  let F : SchwartzMap E ℂ :=
    { toFun := fun x => ∑' k, f k x
      smooth' := contDiff_tsum hf hv hd
      decay' := fun p n => ⟨∑' k, ((2 : ℝ) ^ (k + 1)) ^ p * (‖(cf C k : ℂ)‖ * A n), fun x => by
        rw [iteratedFDeriv_tsum_apply hf hv hd (le_top) x]
        have hn : Summable fun k => ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hd n k x le_top) (hsum n)
        calc ‖x‖ ^ p * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ p * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hn
          _ = ∑' k, ‖x‖ ^ p * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ _ := (hn.mul_left _).tsum_le_tsum (fun k => term_decay b hb A hA hs _ k n p x)
              (summable_weighted hC p (A n) (hA0 n))⟩ }
  have hcf : Summable fun k => cf C k := by
    have := summable_weighted hC 0 1 zero_le_one
    simpa [Complex.norm_real, Real.norm_of_nonneg (cf_nonneg hC _), abs_of_nonneg (cf_nonneg hC _)] using this
  have hr : ∀ u, Summable fun k => cf C k * φ (sc E k u) := fun u =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (cf_nonneg hC k) φ.nonneg)
      (fun k => mul_le_of_le_one_right (cf_nonneg hC k) φ.le_one) hcf
  have hF : ∀ u, F u = ((∑' k, cf C k * φ (sc E k u) : ℝ) : ℂ) := fun u => by
    rw [Complex.ofReal_tsum]
    show ∑' k, f k u = _
    simp [hfd, hbd]
  refine ⟨F, fun u => ?_, fun x => ?_⟩
  · rw [hF, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨tsum_nonneg fun k => mul_nonneg (cf_nonneg hC k) φ.nonneg, rfl⟩
  · rw [hF, Complex.ofReal_re]
    obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := 1 + ‖P x‖) (y := (2 : ℝ))
      (by linarith [norm_nonneg (P x)]) one_lt_two
    have hk : (2 : ℝ) ^ (n + 1) ≤ 2 * (1 + ‖P x‖) := by
      rw [pow_succ]
      linarith
    have hone : φ (sc E (n + 1) (P x)) = 1 := by
      refine φ.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff, norm_sc_apply, inv_mul_eq_div]
      have h2' : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      rw [div_le_iff₀ h2']
      show ‖P x‖ ≤ 1 * 2 ^ (n + 1)
      linarith
    have h3 := le_cf hC (norm_nonneg (P x)) (hw x) hk
    have h4 := (hr (P x)).le_tsum (n + 1) (fun k _ => mul_nonneg (cf_nonneg hC k) φ.nonneg)
    rw [hone, mul_one] at h4
    exact h3.trans h4

end MajMain

theorem fin_gen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y]
    (Pr : X → Y) (hPc : Continuous Pr) (U : Set Y) (hUc : IsClopen U) (hUk : IsCompact U) (h0 : (0 : Y) ∈ U)
    (g : X → ℂ) (hg : g ∈ WeilM.SB X) :
    ∃ G ∈ WeilM.SB Y, (∀ y, 0 ≤ (G y).re ∧ (G y).im = 0) ∧ ∀ x, ‖g x‖ ≤ (G (Pr x)).re := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hc
  have hK : IsCompact (Pr '' tsupport g) := hc.isCompact.image hPc
  have hHom : ∀ y : Y, IsClopen ((fun z => y + z) '' U) ∧ IsCompact ((fun z => y + z) '' U) := fun y =>
    ⟨⟨(Homeomorph.addLeft y).isClosed_image.2 hUc.1, (Homeomorph.addLeft y).isOpen_image.2 hUc.2⟩, hUk.image (continuous_const.add continuous_id)⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun y => (fun z => y + z) '' U) fun y _ =>
    (hHom y).1.2.mem_nhds ⟨0, h0, add_zero y⟩
  set K : Set Y := ⋃ y ∈ t, (fun z => y + z) '' U with hKd
  have hKc : IsClopen K := t.finite_toSet.isClopen_biUnion fun y _ => (hHom y).1
  have hKk : IsCompact K := t.finite_toSet.isCompact_biUnion fun y _ => (hHom y).2
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hnn : ∀ y, 0 ≤ (K.indicator (fun _ => ((C' : ℝ) : ℂ)) y).re ∧ (K.indicator (fun _ => ((C' : ℝ) : ℂ)) y).im = 0 := by
    intro y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy, hC0]
    · simp [Set.indicator_of_notMem hy]
  refine ⟨K.indicator fun _ => ((C' : ℝ) : ℂ), ⟨?_, ?_⟩, hnn, fun x => ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const Y ((C' : ℝ) : ℂ)) hKc).isLocallyConstant
  · refine hKk.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (fun y hy => by
      by_contra h
      exact hy (Set.indicator_of_notMem h _)) hKc.1
  · by_cases hx : g x = 0
    · simpa [hx] using (hnn (Pr x)).1
    · have hm : Pr x ∈ K := ht ⟨x, subset_tsupport g hx, rfl⟩
      rw [Set.indicator_of_mem hm, Complex.ofReal_re]
      exact (hC x).trans (le_max_left _ _)

theorem fin_dom (D : D7) (a b c : ℕ) (ι : Fin c → Fin b)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ G ∈ WeilM.SB (Fin a → Fin c → Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ y, 0 ≤ (G y).re ∧ (G y).im = 0) ∧ ∀ x, ‖g x‖ ≤ (G fun i j => x i (ι j)).re := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI h1 : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.topologicalAddGroup (Af D.host.F) _
  haveI h2 : IsTopologicalAddGroup (Fin c → Af D.host.F ⊗[D.host.F] D.host.E) := Pi.topologicalAddGroup
  haveI h3 : IsTopologicalAddGroup (Fin a → Fin c → Af D.host.F ⊗[D.host.F] D.host.E) := Pi.topologicalAddGroup
  obtain ⟨U, hUc, hUk, h0⟩ := GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero D a c
  exact fin_gen (fun x i j => x i (ι j))
    (continuous_pi fun i => continuous_pi fun j => (continuous_apply (ι j)).comp (continuous_apply i))
    U hUc hUk h0 g hg

theorem real_dom {T : Type} [Fintype T] (a b c : ℕ) (ι : Fin c → Fin b) (f : SchwartzMap (T → Fin a → Fin b → ℂ) ℂ) :
    ∃ F : SchwartzMap (T → Fin a → Fin c → ℂ) ℂ, (∀ u, 0 ≤ (F u).re ∧ (F u).im = 0) ∧
      ∀ v, ‖f v‖ ≤ (F fun τ i j => v τ i (ι j)).re := by
  refine real_maj (T → Fin a → Fin c → ℂ) (T → Fin a → Fin b → ℂ) (fun v τ i j => v τ i (ι j)) (fun v => ‖f v‖) fun N => ?_
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun v => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f v
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  have hP : ‖(fun τ i j => v τ i (ι j) : T → Fin a → Fin c → ℂ)‖ ≤ ‖v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
          (norm_le_pi_norm (v τ i) (ι j)).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
  gcongr

theorem pure_dom (D : D7) (θ : InfFam D) (a b c : ℕ) (ι : Fin c → Fin b)
    (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ M ∈ schwartzA θ a c, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
      ∀ x : Mx D a b, ‖f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))‖ ≤
        (M (x.submatrix id ι)).re := by
  obtain ⟨F, hF, hFd⟩ := real_dom a b c ι f
  obtain ⟨G, hG, hG0, hGd⟩ := fin_dom D a b c ι g hg
  refine ⟨fun y => F (fun τ i j => compAt θ τ y i j) * G (fun i j => finPart D (y i j)),
    Submodule.subset_span ⟨F, G, hG, rfl⟩, fun y => ?_, fun x => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (fun τ i j => compAt θ τ y i j)
    obtain ⟨h3, h4⟩ := hG0 (fun i j => finPart D (y i j))
    simp only [Complex.mul_re, Complex.mul_im, h2, h4, mul_zero, zero_mul, add_zero, sub_zero, and_true]
    exact mul_nonneg h1 h3
  · have h1 := hFd (fun τ i j => compAt θ τ x i j)
    have h2 := hGd (fun i j => finPart D (x i j))
    have e1 : (fun τ i j => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin a → Fin b → ℂ) τ i (ι j)) =
        (fun τ i j => compAt θ τ (x.submatrix id ι) i j) := rfl
    have e2 : (fun i j => (fun i j => finPart D (x i j) : Fin a → Fin b → _) i (ι j)) =
        (fun i j => finPart D ((x.submatrix id ι) i j)) := rfl
    rw [e1] at h1
    rw [e2] at h2
    obtain ⟨-, h4⟩ := hF (fun τ i j => compAt θ τ (x.submatrix id ι) i j)
    simp only [norm_mul, Complex.mul_re, h4, zero_mul, sub_zero]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

end GlobalTheory.CompanionTheory.ColumnSplitting.DomProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem dom : Dom := by
  intro D θ _ a b c ι _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact DomProof.pure_dom D θ a b c ι f g hg
  | zero => exact ⟨0, zero_mem _, fun _ => by simp, fun _ => by simp⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨M₁, m₁, p₁, d₁⟩ := h1
    obtain ⟨M₂, m₂, p₂, d₂⟩ := h2
    refine ⟨M₁ + M₂, add_mem m₁ m₂, fun y => ?_, fun x => ?_⟩
    · simp only [Pi.add_apply, Complex.add_re, Complex.add_im, (p₁ y).2, (p₂ y).2, add_zero, and_true]
      exact add_nonneg (p₁ y).1 (p₂ y).1
    · simp only [Pi.add_apply, Complex.add_re]
      exact (norm_add_le _ _).trans (add_le_add (d₁ x) (d₂ x))
  | smul k φ _ h =>
    obtain ⟨M, m, p, d⟩ := h
    refine ⟨((‖k‖ : ℝ) : ℂ) • M, Submodule.smul_mem _ _ m, fun y => ?_, fun x => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        (p y).2, zero_mul, mul_zero, sub_zero, add_zero, and_true]
      exact mul_nonneg (norm_nonneg _) (p y).1
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left (d x) (norm_nonneg _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainPropertyStatement
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
theorem _root_.GlobalTheory.T.fundamental_domain_property : Dom := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.dom | exact GlobalTheory.CompanionTheory.ColumnSplitting.dom | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.dom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
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

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

section Fub4Proof

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem integral_prod_three (b : Measure β) (c : Measure γ) (a : Measure α) [SFinite a] [SFinite b] [SFinite c]
    (g : β × γ × α → ℂ) (hg : Integrable g (b.prod (c.prod a))) :
    ∫ q, g q ∂(b.prod (c.prod a)) = ∫ h, ∫ u, ∫ k, g (h, u, k) ∂a ∂c ∂b := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with h hh
  exact integral_prod _ hh

theorem integral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℂ) (hg : Integrable g (e.prod (b.prod (c.prod a)))) :
    ∫ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫ y, ∫ h, ∫ u, ∫ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with y hy
  exact integral_prod_three b c a _ hy

theorem lintegral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun y => ?_
  have h1 : Measurable fun q : β × γ × α => g (y, q) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ h1.aemeasurable]
  refine lintegral_congr fun h => ?_
  have h2 : Measurable fun q : γ × α => g (y, h, q) := h1.comp measurable_prodMk_left
  exact lintegral_prod _ h2.aemeasurable

def swapFour (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    (α × β × γ × δ) ≃ᵐ (δ × β × γ × α) where
  toFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  invFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    dsimp only [Equiv.coe_fn_mk]
    fun_prop
  measurable_invFun := by
    dsimp only [Equiv.coe_fn_symm_mk]
    fun_prop

theorem measurePreserving_swapFour (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e] :
    MeasurePreserving (swapFour α β γ δ) (a.prod (b.prod (c.prod e))) (e.prod (b.prod (c.prod a))) := by
  have p1 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := δ)).symm)
      (a.prod (b.prod (c.prod e))) (a.prod ((b.prod c).prod e)) :=
    (MeasurePreserving.id a).prod ((measurePreserving_prodAssoc b c e).symm _)
  have p2 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := β × γ) (γ := δ)).symm
      (a.prod ((b.prod c).prod e)) ((a.prod (b.prod c)).prod e) :=
    (measurePreserving_prodAssoc a (b.prod c) e).symm _
  have p3 : MeasurePreserving Prod.swap ((a.prod (b.prod c)).prod e) (e.prod (a.prod (b.prod c))) :=
    Measure.measurePreserving_swap
  have p4 : MeasurePreserving (Prod.map id Prod.swap) (e.prod (a.prod (b.prod c))) (e.prod ((b.prod c).prod a)) :=
    (MeasurePreserving.id e).prod Measure.measurePreserving_swap
  have p5 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := α)))
      (e.prod ((b.prod c).prod a)) (e.prod (b.prod (c.prod a))) :=
    (MeasurePreserving.id e).prod (measurePreserving_prodAssoc b c a)
  exact (((p5.comp p4).comp p3).comp p2).comp p1

end Fub4Proof

theorem iterated_integrals_four_factors_holds : Fub4 := by
  intro α β γ δ _ _ _ _ a b c e _ _ _ _
  have hm := measurePreserving_swapFour a b c e
  constructor
  · intro f hf
    let g : δ × β × γ × α → ℂ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hfg : g ∘ swapFour α β γ δ = f := rfl
    have hg : Integrable g (e.prod (b.prod (c.prod a))) :=
      (hm.integrable_comp_emb (swapFour α β γ δ).measurableEmbedding).1 (by rwa [hfg])
    calc ∫ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫ q, g q ∂(e.prod (b.prod (c.prod a))) :=
          hm.integral_comp (swapFour α β γ δ).measurableEmbedding g
      _ = _ := integral_prod_four e b c a g hg
  · intro f hf
    let g : δ × β × γ × α → ℝ≥0∞ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hg : Measurable g := hf.comp (swapFour α β γ δ).symm.measurable
    calc ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫⁻ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) := hm.lintegral_comp hg
      _ = _ := lintegral_prod_four e b c a g hg

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactorsStatement
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
theorem _root_.GlobalTheory.T.iterated_integrals_four_factors : Fub4 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds <;> assumption)
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
