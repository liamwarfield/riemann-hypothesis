module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.ContinuousAtInvOfUh
open Matrix MeasureTheory Measure Topology
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem det_ne_of_uh {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) :
    a.det ≠ 0 := by
  exact (Matrix.isUnit_det_of_left_inverse (uh_left ha)).ne_zero

theorem continuousAt_inv_of_uh {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : ContinuousAt (Inv.inv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → _) a := by
  refine continuousAt_matrix_inv a ?_
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (det_ne_of_uh ha)

def RS (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ RStab k r g}

theorem isClosed_RS (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : IsClosed (RS k r g) := IsClosed.preimage (f := fun x : Mt k r => Matrix.of x) continuous_id (isClosed_RStab g)

abbrev RT (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Type := RS k r g

section Grp

variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} [hg : Fact (g ∈ UH (Hpk k r))]

def toM (x : RT k r g) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of x.1

theorem toM_mem (x : RT k r g) : toM x ∈ RStab k r g := x.2

theorem toM_inj {x y : RT k r g} (h : toM x = toM y) : x = y := Subtype.ext (Matrix.of.injective h)

instance : Mul (RT k r g) := ⟨fun x y => ⟨fun i j => (toM x * toM y) i j, rstab_mul hg.out x.2 y.2⟩⟩
instance : One (RT k r g) := ⟨⟨fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j, rstab_one hg.out⟩⟩
instance : Inv (RT k r g) := ⟨fun x => ⟨fun i j => (toM x)⁻¹ i j, rstab_inv hg.out x.2⟩⟩

theorem toM_mul (x y : RT k r g) : toM (x * y) = toM x * toM y := rfl
theorem toM_one : toM (1 : RT k r g) = 1 := rfl
theorem toM_inv (x : RT k r g) : toM x⁻¹ = (toM x)⁻¹ := rfl

instance instGroupRT : Group (RT k r g) where
  mul_assoc x y z := toM_inj (by rw [toM_mul, toM_mul, toM_mul, toM_mul, Matrix.mul_assoc])
  one_mul x := toM_inj (by rw [toM_mul, toM_one, Matrix.one_mul])
  mul_one x := toM_inj (by rw [toM_mul, toM_one, Matrix.mul_one])
  inv_mul_cancel x := toM_inj (by rw [toM_mul, toM_inv, toM_one, uh_inv_mul (toM_mem x).1.1])

theorem continuous_toM : Continuous (toM : RT k r g → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_subtype_val

instance : IsTopologicalGroup (RT k r g) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_toM.comp continuous_fst).matrix_mul (continuous_toM.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (continuousAt_inv_of_uh (toM_mem x).1.1).comp continuous_toM.continuousAt

instance : LocallyCompactSpace (RT k r g) := (isClosed_RS g).locallyCompactSpace

end Grp

section Meas

variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)}

theorem rs_emb (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    MeasurableEmbedding (Subtype.val : RT k r g → Mt k r) := MeasurableEmbedding.subtype_coe (isClosed_RS g).measurableSet

theorem rs_back (hc : μR {x | Matrix.of x ∉ RStab k r g} = 0) :
    (μR.comap (Subtype.val : RT k r g → Mt k r)).map Subtype.val = μR := by
  rw [(rs_emb g).map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)

theorem measurable_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have : Continuous (fun x : Mt k r => (a * Matrix.of x) i j) := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finsetSum _ fun l _ =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply l))
  exact this.measurable

theorem rs_val_mul [Fact (g ∈ UH (Hpk k r))] (a : RT k r g) :
    (Subtype.val : RT k r g → Mt k r) ∘ (fun x => a * x) = lmulM (toM a) ∘ Subtype.val := by
  funext x
  rfl

theorem rs_inv [Fact (g ∈ UH (Hpk k r))] (hc : μR {x | Matrix.of x ∉ RStab k r g} = 0)
    (hinv : ∀ s ∈ RStab k r g, μR.map (lmulM s) = μR) :
    IsMulLeftInvariant (μR.comap (Subtype.val : RT k r g → Mt k r)) := by
  constructor
  intro a
  have hf : Measurable (fun x : RT k r g => a * x) := by
    rw [← (rs_emb g).measurable_comp_iff, rs_val_mul a]
    exact (measurable_lmulM _).comp measurable_subtype_coe
  rw [← (rs_emb g).comap_map (Measure.map (fun x => a * x) (μR.comap Subtype.val)),
    Measure.map_map (rs_emb g).measurable hf, rs_val_mul a,
    ← Measure.map_map (measurable_lmulM _) (rs_emb g).measurable, rs_back hc, hinv _ (toM_mem a)]

theorem rs_smul [Fact (g ∈ UH (Hpk k r))] (hμ : IsHaarOn (RStab k r g) μR) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μR.comap (Subtype.val : RT k r g → Mt k r) = c • (haar : Measure (RT k r g)) := by
  obtain ⟨hσ, h0, hc, hinv⟩ := hμ
  have hback := rs_back hc
  haveI : SigmaFinite (μR.comap (Subtype.val : RT k r g → Mt k r)) :=
    SigmaFinite.of_map _ (rs_emb g).measurable.aemeasurable (by rw [hback]; exact hσ)
  haveI : IsMulLeftInvariant (μR.comap (Subtype.val : RT k r g → Mt k r)) := rs_inv hc hinv
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : RT k r g)
  have hK0 : (haar : Measure (RT k r g)) K ≠ 0 := (measure_pos_of_mem_nhds haar hK1).ne'
  have hKt : (haar : Measure (RT k r g)) K ≠ ⊤ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul (μ' := μR.comap (Subtype.val : RT k r g → Mt k r))
    (ν' := (haar : Measure (RT k r g))) hK0 hKt
  refine ⟨_, ?_, ?_, heq⟩
  · intro hz
    rw [hz, zero_smul] at heq
    apply h0
    rw [← hback, heq, Measure.map_zero]
  · intro ht
    rw [ht] at heq
    set ν := μR.comap (Subtype.val : RT k r g → Mt k r) with hνdef
    obtain ⟨n, hn⟩ : ∃ n, (haar : Measure (RT k r g)) (spanningSets ν n) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hU : (haar : Measure (RT k r g)) (⋃ n, spanningSets ν n) = 0 := measure_iUnion_null hcon
      rw [iUnion_spanningSets] at hU
      exact isOpen_univ.measure_ne_zero haar Set.univ_nonempty hU
    have h2 : ν (spanningSets ν n) = ((⊤ : ℝ≥0∞) • (haar : Measure (RT k r g))) (spanningSets ν n) := by
      rw [← heq]
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at h2
    exact (measure_spanningSets_lt_top ν n).ne h2

theorem rhaar_props (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) :
    (∀ C : Set (Mt k r), IsCompact C → μR C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (U ∩ RS k r g).Nonempty → μR U ≠ 0) := by
  haveI : Fact (g ∈ UH (Hpk k r)) := ⟨hg⟩
  obtain ⟨c, hc1, hc2, hν⟩ := rs_smul hμ
  have hback := rs_back hμ.2.2.1
  refine ⟨?_, ?_⟩
  · intro C hC
    have hpc : IsCompact ((Subtype.val : RT k r g → Mt k r) ⁻¹' C) := by
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe]
      exact hC.inter_right (isClosed_RS g)
    rw [← hback, Measure.map_apply (rs_emb g).measurable hC.measurableSet, hν, Measure.smul_apply,
      smul_eq_mul]
    exact ENNReal.mul_lt_top hc2.lt_top hpc.measure_lt_top
  · rintro U hU ⟨x, hxU, hxR⟩
    rw [← hback, Measure.map_apply (rs_emb g).measurable hU.measurableSet, hν, Measure.smul_apply,
      smul_eq_mul]
    exact mul_ne_zero hc1 ((hU.preimage continuous_subtype_val).measure_ne_zero haar ⟨⟨x, hxR⟩, hxU⟩)

end Meas

end PI.AmpOrbQuot
end
end

open Matrix MeasureTheory Measure Topology
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem continuous_ofM {X : Type*} [TopologicalSpace X] {f : X → Mt k r} (hf : Continuous f) :
    Continuous (fun x => Matrix.of (f x)) := hf

theorem continuous_toMt {X : Type*} [TopologicalSpace X]
    {M : X → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : Continuous M) :
    Continuous (fun x => (fun i j => M x i j : Mt k r)) := hM

instance instBorelMt2 : BorelSpace (Mt k r × Mt k r) := Prod.borelSpace
instance instBorelPair : BorelSpace (PairSp k r) := Prod.borelSpace
instance instBorelMtPair : BorelSpace (Mt k r × PairSp k r) := Prod.borelSpace

def minv (x : Mt k r) : Mt k r := fun i j => (Matrix.of x)⁻¹ i j

theorem measurable_minv : Measurable (minv (k := k) (r := r)) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hdet : Continuous (fun x : Mt k r => (Matrix.of x).det) := hof.matrix_det
  rw [measurable_pi_iff]; intro i
  rw [measurable_pi_iff]; intro j
  have hadj : Continuous (fun x : Mt k r => (Matrix.of x).adjugate i j) :=
    (hof.matrix_adjugate.matrix_elem i j)
  have e : (fun x : Mt k r => minv x i j) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    funext x
    simp only [minv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [e]
  exact (measurable_inv.comp hdet.measurable).mul hadj.measurable

theorem continuous_stabAct (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1) p.2) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  unfold stabAct
  first
    | fun_prop
    | continuity

theorem measurable_stabAct (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1) p.2) := (continuous_stabAct g).measurable

theorem measurable_stabAct_inv (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun p : Mt k r × PairSp k r => stabAct g (Matrix.of p.1)⁻¹ p.2) := by
  have hf : Measurable (fun p : Mt k r × PairSp k r => (minv p.1, p.2)) := by
    first
      | exact (measurable_minv.comp measurable_fst).prodMk measurable_snd
      | exact (measurable_minv.comp measurable_fst).prod_mk measurable_snd
  exact (measurable_stabAct g).comp hf

theorem measurable_stabAct_one (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (stabAct (k := k) (r := r) g a) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hc : Continuous (stabAct (k := k) (r := r) g a) := by
    unfold stabAct
    first
      | fun_prop
      | continuity
  exact hc.measurable

private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hs : (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) < 2 * r + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single (⟨_, hs⟩ : Fin (2 * r + k + 1))]
  · by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, eq_self_iff_true, and_true]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
    · rw [if_neg hij]
      rw [Fin.ext_iff] at hij
      simp only [Hpk, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro l _ hl
    rw [Ne, Fin.ext_iff, Fin.val_mk] at hl
    simp only [Hpk, Fin.ext_iff]
    split_ifs at * <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_of_mem_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_sq_lemma k r]
  exact Matrix.isUnit_det_of_left_inverse h

theorem stabAct_comp {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : PairSp k r) :
    stabAct g b (stabAct g a x) = stabAct g (b * a) x := by
  have hd := isUnit_det_of_mem_UH' hg
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show (b * (a * Matrix.of x.1.2)) i j = (b * a * Matrix.of x.1.2) i j
    rw [Matrix.mul_assoc]
  · funext i j
    show (g⁻¹ * b * g * (g⁻¹ * a * g * Matrix.of x.2.2)) i j = (g⁻¹ * (b * a) * g * Matrix.of x.2.2) i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left g _ hd]

theorem stabAct_one {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (x : PairSp k r) : stabAct g 1 x = x := by
  have hd := isUnit_det_of_mem_UH' hg
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Matrix.of x.1.2) i j = x.1.2 i j
    rw [Matrix.one_mul]
    rfl
  · funext i j
    show (g⁻¹ * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * Matrix.of x.2.2) i j = x.2.2 i j
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul g hd, Matrix.one_mul]
    rfl

theorem stabAct_inv_cancel {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) (x : PairSp k r) :
    stabAct g a⁻¹ (stabAct g a x) = x := by
  rw [stabAct_comp hg, Matrix.nonsing_inv_mul a (isUnit_det_of_mem_UH' ha), stabAct_one hg]

theorem stabAct_eq_map (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    stabAct (k := k) (r := r) g a = Prod.map (Prod.map id (lmulM a)) (Prod.map id (lmulM (g⁻¹ * a * g))) := by
  funext p
  rfl

theorem pairMeas_inv (L : LocBessel k r) [SFinite L.μN]
    (hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN)
    {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ RStab k r g) :
    (pairMeas L).map (stabAct g a) = pairMeas L := by
  obtain ⟨⟨h1, -⟩, -⟩ := L.hμW
  obtain ⟨⟨h2, -⟩, -⟩ := L.hμW'
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hl : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (lmulM (k := k) (r := r) s) := by
    intro s
    have hc : Continuous (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      first
        | fun_prop
        | continuity
    exact hc.measurable
  have hp : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (Prod.map (id : Mt k r → Mt k r) (lmulM (k := k) (r := r) s)) := by
    intro s
    first
      | exact measurable_id.prodMap (hl s)
      | exact measurable_id.prod_map (hl s)
  rw [stabAct_eq_map, pairMeas, ← Measure.map_prod_map _ _ (hp a) (hp _),
    ← Measure.map_prod_map _ _ measurable_id (hl a), ← Measure.map_prod_map _ _ measurable_id (hl _),
    Measure.map_id, Measure.map_id, hN a ha.1, hN _ ha.2]

def NS (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ Nset k r}

theorem isClosed_NS : IsClosed (NS k r) := by
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have h1 : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), IsClosed {x : Mt k r | a.val ≤ i.val →
      x i (eI k r a) = if i = eI k r a then 1 else 0} := by
    intro a i
    by_cases h : a.val ≤ i.val
    · simp only [h, true_implies]
      exact isClosed_eq (by fun_prop) continuous_const
    · simp only [h, false_implies, Set.setOf_true]
      exact isClosed_univ
  have h3 : ∀ i j : Fin (2 * r + k + 1), IsClosed {x : Mt k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      x i j = if i = j then 1 else 0} := by
    intro i j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k ∧ r ≤ i.val
    · simp only [h.1, h.2.1, h.2.2, true_implies]
      exact isClosed_eq (by fun_prop) continuous_const
    · have e : {x : Mt k r | r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
          x i j = if i = j then 1 else 0} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2 h3
        exact absurd ⟨h1, h2, h3⟩ h
      rw [e]
      exact isClosed_univ
  have e : NS k r = {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} ∩
      ((⋂ a : Fin r, ⋂ i : Fin (2 * r + k + 1), {x : Mt k r | a.val ≤ i.val →
          x i (eI k r a) = if i = eI k r a then 1 else 0}) ∩
        (⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1), {x : Mt k r | r ≤ j.val → j.val ≤ r + k →
          r ≤ i.val → x i j = if i = j then 1 else 0})) := by
    ext x
    simp only [NS, Nset, UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [e]
  exact h1.inter ((isClosed_iInter fun a => isClosed_iInter fun i => h2 a i).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => h3 i j))

theorem pairMeas_null (L : LocBessel k r) [SFinite L.μN] (hc : L.μN (NS k r)ᶜ = 0) :
    pairMeas L {y | y.1.2 ∉ NS k r} = 0 := by
  obtain ⟨⟨h1, -⟩, -⟩ := L.hμW
  obtain ⟨⟨h2, -⟩, -⟩ := L.hμW'
  have e : {y : PairSp k r | y.1.2 ∉ NS k r} = (Set.univ ×ˢ (NS k r)ᶜ) ×ˢ Set.univ := by
    ext y; simp
  rw [e, pairMeas, Measure.prod_prod, Measure.prod_prod, hc, mul_zero, zero_mul]

end PI.AmpOrbQuot
