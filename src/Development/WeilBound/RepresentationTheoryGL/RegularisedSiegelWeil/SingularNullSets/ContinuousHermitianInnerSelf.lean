module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c : ℕ}

scoped instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩
scoped instance scMx (m n : ℕ) : SecondCountableTopology (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.1
scoped instance t2Mx (m n : ℕ) : T2Space (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.2.1

theorem continuous_ci (w : InfinitePlace D.host.F) : Continuous (compInf D.host.F D.host.E w) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (evInf D.host.F w).toLinearMap (map_mul (evInf D.host.F w))
    ((continuous_apply w).comp continuous_fst)

theorem continuous_cv (v : Pl D) : Continuous (cv D v) := GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v

theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem box₁ {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (AE D)} (hK : IsCompact K) :
    ∃ K' : Set (AE D), IsCompact K' ∧
      ∀ x, (∀ v ∉ S, cv D v x ∈ intLoc D.host.F D.host.E v) → e * x ∈ K → x ∈ K' := by
  classical
  obtain ⟨K', hK', hmem⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box D.host.F D.host.E
    (fun w => compInf D.host.F D.host.E w '' K)
    (fun v => if v ∈ S then cv D v '' K else (intLoc D.host.F D.host.E v : Set _))
    (fun w => hK.image (continuous_ci w))
    (fun v => by
      split_ifs
      · exact hK.image (continuous_cv v)
      · exact (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1)
    (Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => Finset.mem_coe.2 (by
      by_contra h
      exact hv (by simp [h]))))
  refine ⟨K', hK', fun x hx hex => hmem x (fun w => ⟨e * x, hex, ?_⟩) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · by_cases hv : v ∈ S
    · simp only [if_pos hv]
      exact ⟨e * x, hex, by rw [map_mul, he.2 v, if_pos hv, one_mul]⟩
    · simp only [if_neg hv]
      exact hx v hv

theorem boxM {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (Mx D a b)} (hK : IsCompact K) :
    ∃ K' : Set (Mx D a b), IsCompact K' ∧ ∀ x, IntOff S x → e • x ∈ K → x ∈ K' := by
  choose C hC hCm using fun i j => box₁ he (hK.image (continuous_id.matrix_elem i j))
  refine ⟨{x | ∀ i j, x i j ∈ C i j}, ?_, fun x hx hex i j => hCm i j (x i j) (fun v hv => hx v hv i j) ⟨e • x, hex, rfl⟩⟩
  exact isCompact_pi_infinite fun i => isCompact_pi_infinite fun j => hC i j

theorem boxP {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {K : Set (Mx D a b × Mx D a c)} (hK : IsCompact K) :
    ∃ K' : Set (Mx D a b × Mx D a c), IsCompact K' ∧
      ∀ z : Mx D a b × Mx D a c, IntOff S z.1 → IntOff S z.2 → (e • z.1, e • z.2) ∈ K → z ∈ K' := by
  obtain ⟨K1, h1, m1⟩ := boxM he (hK.image continuous_fst)
  obtain ⟨K2, h2, m2⟩ := boxM he (hK.image continuous_snd)
  exact ⟨K1 ×ˢ K2, h1.prod h2, fun z hz1 hz2 hz => ⟨m1 _ hz1 ⟨_, hz, rfl⟩, m2 _ hz2 ⟨_, hz, rfl⟩⟩⟩

theorem cv_eq_zero {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {N : Mx D a b} (hN : e • N = N) {v : Pl D}
    (hv : v ∉ S) (i : Fin a) (j : Fin b) : cv D v (N i j) = 0 := by
  rw [← hN, Matrix.smul_apply, smul_eq_mul, map_mul, he.2 v, if_neg hv, zero_mul]

theorem intOff_iff {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {x x' : Mx D a b} (h : e • (x' - x) = x' - x) :
    IntOff S x' ↔ IntOff S x := by
  have key : ∀ v ∉ S, ∀ i j, cv D v (x' i j) = cv D v (x i j) := fun v hv i j => by
    have := cv_eq_zero he h hv i j
    rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  refine ⟨fun hx v hv i j => ?_, fun hx v hv i j => ?_⟩
  · rw [← key v hv i j]; exact hx v hv i j
  · rw [key v hv i j]; exact hx v hv i j

theorem isClosed_intOff (S : Finset (Pl D)) : IsClosed {x : Mx D a b | IntOff S x} := by
  have hc : ∀ v : Pl D, IsClosed (intLoc D.host.F D.host.E v : Set (Fv D.host.F v ⊗[D.host.F] D.host.E)) := fun v => by
    have := AddSubgroup.isClosed_of_isOpen (intLoc D.host.F D.host.E v).toAddSubgroup (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
    exact this
  simp only [IntOff, Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => isClosed_iInter fun j =>
    (hc v).preimage ((continuous_cv v).comp (continuous_id.matrix_elem i j))

theorem intOff_mul {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := fun v hv i j => by
  show cv D v ((x * y) i j) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  exact Subring.sum_mem _ fun k _ => by rw [map_mul]; exact Subring.mul_mem _ (hx v hv i k) (hy v hv k j)

theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := fun v hv i j => by
  show cv D v (cA D (x j i)) ∈ _
  rw [cv_cA]
  exact GlobalTheory.AdelicU.sigR_mem_intLoc _ (hx v hv j i)

theorem exists_intOff (M : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S M := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele (M i j)
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun S hS v hv i j => ?_⟩
  by_contra hn
  exact hv (hS ((Filter.eventually_cofinite.1 h).mem_toFinset.2 fun h' => hn (h' i j)))

end PositivityTheory.Rg.Rsw.L.LToS

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem adj_smul (e : AE D) (x : Mx D a b) : adj (e • x) = cA D e • adj x := by
  ext i j
  show cA D (e * x j i) = cA D e * cA D (x j i)
  exact map_mul _ _ _

theorem ip_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem yv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem qv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, yv_smul he, ip_smul he, pr_smul he, smul_sub]

theorem continuous_ip (V : HSp D) : Continuous fun p : Mx D V.rank a × Mx D V.rank b => ip V p.1 p.2 := by
  show Continuous fun p : Mx D V.rank a × Mx D V.rank b => adj p.1 * (gA V * p.2)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd)

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) :
    Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => rat b₀.1⁻¹ * ip V z.1 z.2
  exact continuous_const.matrix_mul (continuous_ip V)

theorem isClosed_qv (V : HSp D) (b₀ : HermE D r) :
    IsClosed {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} := by
  have hy := continuous_yv (t := t) V b₀
  have h1 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.2 * (gA V * z.2)
    exact (continuous_adj.comp continuous_snd).matrix_mul (continuous_const.matrix_mul continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj (yv V b₀ z) * ((b₀.1.map (incA D)) * yv V b₀ z)
    exact (continuous_adj.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have e : {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} =
      {z | ip V z.2 z.2 = pr b₀ (yv V b₀ z) (yv V b₀ z)} := Set.ext fun z => sub_eq_zero
  rw [e]
  exact isClosed_eq h1 h2

theorem map_transport {X : Type*} [MeasurableSpace X] {ν : Measure X} {A : Set X} (hA : MeasurableSet A)
    {f φ ψ : X → X} (hf : Measurable f) (hφ : Measurable φ) (hψ : Measurable ψ) (hA' : φ ⁻¹' A = A)
    (hc : ∀ z, ψ (f z) = f (φ z)) {κ : ℝ≥0} (hν : ν.map φ = κ • ν) :
    ((ν.restrict A).map f).map ψ = κ • (ν.restrict A).map f := by
  have h1 : (ν.restrict A).map φ = κ • ν.restrict A := by
    conv_lhs => rw [← hA']
    rw [← Measure.restrict_map hφ hA, hν, Measure.restrict_smul]
  rw [Measure.map_map hψ hf, show ψ ∘ f = f ∘ φ from funext hc, ← Measure.map_map hf hφ, h1, Measure.map_smul]
  exact hf.aemeasurable

end PositivityTheory.Rg.Rsw.L.LToS

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw.L.LToS

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem fix_mul_left {e : AE D} {M : Mx D a a} (hM : e • (M - 1) = M - 1) (x : Mx D a b) :
    e • (mm M x - x) = mm M x - x := by
  have h : mm M x - x = (M - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul]
  rw [h, ← Matrix.smul_mul, hM]

theorem fix_add_mul {e : AE D} {y : Mx D b c} (hy : e • y = y) (x : Mx D a b) (z : Mx D a c) :
    e • (z + mm x y - z) = z + mm x y - z := by
  rw [add_sub_cancel_left]
  show e • (x * y) = x * y
  rw [← Matrix.mul_smul, hy]

theorem fix_mul_right {e : AE D} {g : Mx D b b} (hg : e • (g - 1) = g - 1) (x : Mx D a b) :
    e • (mm x g - x) = mm x g - x := by
  have h : mm x g - x = x * (g - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
  rw [h, ← Matrix.mul_smul, hg]

theorem hc_U (e : AE D) (M : Mx D a a) (z : Mx D a b × Mx D a c) :
    (mm M (e • z.1), mm M (e • z.2)) = (e • mm M z.1, e • mm M z.2) := by
  simp only [mm, Matrix.mul_smul]

theorem hc_S (e : AE D) (y : Mx D b c) (z : Mx D a b × Mx D a c) :
    (e • z.1, e • z.2 + mm (e • z.1) y) = (e • z.1, e • (z.2 + mm z.1 y)) := by
  simp only [mm, Matrix.smul_mul, smul_add]

theorem hc_C (e : AE D) (g : Mx D c c) (z : Mx D a b × Mx D a c) :
    (e • z.1, mm (e • z.2) g) = (e • z.1, e • mm z.2 g) := by
  simp only [mm, Matrix.smul_mul]

theorem continuous_addMul (y : Mx D b c) : Continuous fun z : Mx D a b × Mx D a c => z.2 + mm z.1 y :=
  continuous_snd.add (continuous_fst.matrix_mul continuous_const)

theorem measurable_S (y : Mx D b c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, z.2 + mm z.1 y) :=
  (continuous_fst.prodMk (continuous_addMul y)).measurable

theorem continuous_mulR (M : Mx D c c) : Continuous fun z : Mx D a b × Mx D a c => mm z.2 M :=
  continuous_snd.matrix_mul continuous_const

theorem measurable_C (M : Mx D c c) : Measurable fun z : Mx D a b × Mx D a c => (z.1, mm z.2 M) :=
  (continuous_fst.prodMk (continuous_mulR M)).measurable

theorem continuous_hermitian_inner_self (V : HSp D) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1 := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.1 * (gA V * z.1)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem isOrb_e {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (hee : e * e = e ∧ cA D e = e) {ν : Measure (Mx D V.rank r × Mx D V.rank t)} (hν : IsOrb V b₀ 1 ν) :
    IsOrb V b₀ e ((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map fun z => (e • z.1, e • z.2)) := by
  have hA : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t | IntOff S z.1 ∧ IntOff S z.2} :=
    (((isClosed_intOff S).preimage continuous_fst).inter ((isClosed_intOff S).preimage continuous_snd)).measurableSet
  have hf : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_fst.const_smul e).prodMk (continuous_snd.const_smul e)).measurable
  have := hν.fin
  refine ⟨⟨fun K hK => ?_⟩, ?_, fun h hh => ?_, fun y hy => ?_, fun g hg => ?_⟩
  · obtain ⟨K', hK', hmem⟩ := boxP he hK
    rw [Measure.map_apply hf hK.measurableSet, Measure.restrict_apply (hf hK.measurableSet)]
    exact lt_of_le_of_lt (measure_mono fun z hz => hmem z hz.2.1 hz.2.2 hz.1) hK'.measure_lt_top
  · have hG : IsClosed {z : Mx D V.rank r × Mx D V.rank t |
        e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0} :=
      (isClosed_eq (continuous_fst.const_smul e) continuous_fst).inter
        ((isClosed_eq (continuous_snd.const_smul e) continuous_snd).inter
          ((isClosed_eq (continuous_hermitian_inner_self V) continuous_const).inter (isClosed_qv V b₀)))
    have hm : MeasurableSet {z : Mx D V.rank r × Mx D V.rank t |
        ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} := hG.isOpen_compl.measurableSet
    rw [Measure.map_apply hf hm]
    refine nonpos_iff_eq_zero.1 ?_
    refine (Measure.restrict_apply_le _ _).trans (le_of_eq (measure_mono_null (fun z hz => ?_) hν.supp))
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
    intro hg
    apply hz
    obtain ⟨-, -, h3, h4⟩ := hg
    refine ⟨by rw [smul_smul, hee.1], by rw [smul_smul, hee.1], ?_, ?_⟩
    · rw [ip_smul hee, h3, one_smul]
    · rw [qv_smul hee, h4, smul_zero]
  · have hφ : Measurable fun z : Mx D V.rank r × Mx D V.rank t => (mm (mt V h) z.1, mm (mt V h) z.2) :=
      ((continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)).measurable
    have key := map_transport (κ := 1) hA hf hφ hφ ?_ (fun z => hc_U e (mt V h) z)
      (by rw [one_smul]; exact hν.invU h (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_mul_left hh z.1), intOff_iff he (fix_mul_left hh z.2)]
  · have key := map_transport (κ := 1) hA hf (measurable_S y) (measurable_S y) ?_
      (fun z => hc_S e y z)
      (by rw [one_smul]; exact hν.invS y (one_smul _ _))
    · rwa [one_smul] at key
    · ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [intOff_iff he (fix_add_mul hy z.1 z.2)]
  · exact map_transport hA hf (measurable_C (a := V.rank) (b := r) g.1) (measurable_C (a := V.rank) (b := r) g.1)
      (by
        ext z
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [intOff_iff he (fix_mul_right hg z.2)])
      (fun z => hc_C e g.1 z) (hν.cov g (one_smul _ _))

theorem toS_of (hI : IdemEx) : ToS := by
  classical
  intro D r t V b₀ _
  obtain ⟨S₁, h₁⟩ := exists_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS e he ν hν => ⟨isOrb_e he ((hI D S).2 e he) hν, fun z hz1 hz2 =>
    ⟨?_, yv_smul ((hI D S).2 e he) V b₀ z⟩⟩⟩
  show IntOff S (mm (rat b₀.1⁻¹) (mm (adj z.1) (mm (gA V) z.2)))
  exact intOff_mul (h₁ S (Finset.union_subset_left hS))
    (intOff_mul (intOff_adj hz1) (intOff_mul (h₂ S (Finset.union_subset_right hS)) hz2))

end PositivityTheory.Rg.Rsw.L.LToS

namespace PositivityTheory.Rg.Rsw.L

theorem toS : IdemEx → ToS := LToS.toS_of

end PositivityTheory.Rg.Rsw.L

end
