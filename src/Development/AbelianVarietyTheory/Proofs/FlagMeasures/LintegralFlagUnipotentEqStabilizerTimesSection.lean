module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmHalfIntegralGeneratorMemAlgebraicClosure
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Model

theorem _root_.GlobalTheory.Amp.Model.det_upper {r : ℕ} (x : _root_.GlobalTheory.Amp.UT r → ℂ) :
    (_root_.GlobalTheory.Amp.upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [_root_.GlobalTheory.Amp.upper]
  · intro i j hij
    simp only [id] at hij
    have h1 : ¬ i < j := not_lt.mpr hij.le
    simp [_root_.GlobalTheory.Amp.upper, h1, hij.ne']

theorem _root_.GlobalTheory.Amp.Model.cont_uEmb (k r : ℕ) :
    Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper x) := by
  have hup : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.upper x := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold _root_.GlobalTheory.Amp.upper
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hinv : ∀ x : _root_.GlobalTheory.Amp.UT r → ℂ,
      (_root_.GlobalTheory.Amp.upper x)⁻¹ = (_root_.GlobalTheory.Amp.upper x).adjugate := by
    intro x; rw [Matrix.inv_def, _root_.GlobalTheory.Amp.Model.det_upper]; simp
  have hc : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      (_root_.GlobalTheory.Amp.upper x)⁻¹ := by
    simp_rw [hinv]; exact hup.matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.uEmb
  split_ifs
  · exact (continuous_apply_apply _ _).comp hup
  · exact ((continuous_apply_apply _ _).comp hc).star
  · exact continuous_const
  · exact continuous_const

theorem _root_.GlobalTheory.Amp.Model.cont_pOf (k r : ℕ) :
    Continuous (_root_.GlobalTheory.Amp.pOf k r) := by
  have herm : ∀ {f g : _root_.GlobalTheory.Amp.PPar k r → Fin (k + 1) → ℂ},
      Continuous f → Continuous g → Continuous fun q => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hb k) (f q) (g q) :=
    fun hf hg => (_root_.Formalism.FourierDecayAlt.P.B2x5.continuous_herm (_root_.Formalism.QuantumDeterminants.Hb k)).comp (hf.prodMk hg)
  have hB : ∀ a, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => q.1 a :=
    fun a => (continuous_apply a).comp continuous_fst
  have hS : ∀ a b, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r =>
      _root_.GlobalTheory.Amp.skewM q.2.1 q.2.2 a b := by
    intro a b
    unfold _root_.GlobalTheory.Amp.skewM
    split_ifs
    · exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)
    · exact ((continuous_apply _).comp (continuous_fst.comp continuous_snd)).star.neg
    · exact (Complex.continuous_ofReal.comp
        ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).mul continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.pOf _root_.GlobalTheory.Amp.pEl
  split_ifs
  · exact continuous_const
  · exact (herm continuous_const (hB _)).neg
  · exact (continuous_apply _).comp (hB _)
  · exact (hS _ _).sub ((herm (hB _) (hB _)).div_const _)
  · exact continuous_const

theorem _root_.GlobalTheory.Amp.Model.cont_lebN_map (k r : ℕ) :
    Continuous fun q : (_root_.GlobalTheory.Amp.UT r → ℂ) × _root_.GlobalTheory.Amp.PPar k r =>
      (Matrix.of.symm (_root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper q.1) *
        _root_.GlobalTheory.Amp.pOf k r q.2) : _root_.Formalism.QuantumDeterminants.Mt k r) := by
  exact ((_root_.GlobalTheory.Amp.Model.cont_uEmb k r).comp continuous_fst).matrix_mul
    ((_root_.GlobalTheory.Amp.Model.cont_pOf k r).comp continuous_snd)

end GlobalTheory.Amp.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplit
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PSplit

theorem mp_merge {ι α : Type} [Fintype ι] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (p q : ι → Prop) [DecidablePred p] [Fintype {i // p i}] [Fintype {i // q i}]
    (hq : ∀ i, q i ↔ ¬ p i) :
    MeasurePreserving (fun x : ({i // p i} → α) × ({i // q i} → α) =>
      fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, (hq i).2 h⟩) volume volume := by
  obtain rfl : q = fun i => ¬ p i := funext fun i => propext (hq i)
  have := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => α) p).symm
  convert this using 1
  all_goals first | rfl | (congr <;> exact Subsingleton.elim _ _)

theorem mp_comm {A B C D : Type} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [MeasureSpace D] [SFinite (volume : Measure A)] [SFinite (volume : Measure B)]
    [SFinite (volume : Measure C)] [SFinite (volume : Measure D)] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure A) (volume : Measure B)
    (volume : Measure (C × D))
  have h2 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure B) (volume : Measure C)
      (volume : Measure D)).symm
  have h3 := (MeasurePreserving.id (volume : Measure A)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure B)) (ν := (volume : Measure C))).prod
      (MeasurePreserving.id (volume : Measure D)))
  have h4 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure C) (volume : Measure B)
      (volume : Measure D))
  have h5 := (measurePreserving_prodAssoc (volume : Measure A) (volume : Measure C)
    (volume : Measure (B × D))).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem lintegral_shift {A C T : Type} [MeasureSpace A] [MeasureSpace C] [MeasureSpace T]
    [SFinite (volume : Measure A)] [SFinite (volume : Measure C)] [SFinite (volume : Measure T)]
    [AddGroup C] [MeasurableAdd₂ C] [Measure.IsAddRightInvariant (volume : Measure C)]
    (F : (A × C) × T → ℝ≥0∞) (hF : Measurable F) (c : A × T → C) (hc : Measurable c) :
    ∫⁻ x, F x = ∫⁻ y : A × C, ∫⁻ t : T, F ((y.1, y.2 + c (y.1, t)), t) := by
  have hG : Measurable (fun x : (A × C) × T => F ((x.1.1, x.1.2 + c (x.1.1, x.2)), x.2)) := by
    apply hF.comp
    fun_prop
  rw [lintegral_lintegral_swap (f := fun (y : A × C) (t : T) => F ((y.1, y.2 + c (y.1, t)), t))
    hG.aemeasurable, Measure.volume_eq_prod, lintegral_prod_symm _ hF.aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [Measure.volume_eq_prod, lintegral_prod _ (Measurable.aemeasurable (by fun_prop)),
    lintegral_prod (fun y : A × C => F ((y.1, y.2 + c (y.1, t)), t))
      (Measurable.aemeasurable (hG.comp (f := fun y : A × C => (y, t)) (by fun_prop)))]
  refine lintegral_congr fun a => ?_
  exact (lintegral_add_right_eq_self (fun s => F ((a, s), t)) (c (a, t))).symm

theorem sf_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure ((ι → ℂ) × (κ → ℝ))) := inferInstance

theorem sf_rows (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure (ι → κ → ℂ)) := inferInstance

theorem sf_triple (ι ι' κ κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    SFinite (volume : Measure ((ι → ι' → ℂ) × (κ → ℂ) × (κ' → ℝ))) := by
  have := sf_pair κ κ'
  have := sf_rows ι ι'
  exact Measure.prod.instSFinite

theorem inv_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    Measure.IsAddRightInvariant (volume : Measure ((ι → ℂ) × (κ → ℝ))) :=
  Measure.prod.instIsAddRightInvariant

def merge (k r j : ℕ) (x : PSec k r j × PTop k r j) : PPar k r :=
  (fun a => if h : (a : ℕ) < j then x.1.1 ⟨a, h⟩ else x.2.1 ⟨a, not_lt.1 h⟩,
   fun p => if h : (p.1.1 : ℕ) < j then x.1.2.1 ⟨p, h⟩ else x.2.2.1 ⟨p, not_lt.1 h⟩,
   fun a => if h : (a : ℕ) < j then x.1.2.2 ⟨a, h⟩ else x.2.2.2 ⟨a, not_lt.1 h⟩)

theorem mp_mergeP (k r j : ℕ) : MeasurePreserving (merge k r j) volume volume := by
  have h1 := mp_merge (α := Fin (k + 1) → ℂ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have h2 := mp_merge (α := ℂ) (fun p : UT r => (p.1.1 : ℕ) < j)
    (fun p : UT r => j ≤ (p.1.1 : ℕ)) (fun _ => not_lt.symm)
  have h3 := mp_merge (α := ℝ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_pair {p : UT r // j ≤ (p.1.1 : ℕ)} {a : Fin r // j ≤ (a : ℕ)}
  have := sf_pair (UT r) (Fin r)
  have h4 := (h2.prod h3).comp mp_comm
  have h5 := @MeasurePreserving.prod _ _ _ _ _ _ _ _ _ _ _ _ Measure.prod.instSFinite
    Measure.prod.instSFinite _ _ h1 h4
  exact h5.comp mp_comm

theorem cont_pOf (k r : ℕ) : Continuous (fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  simp only [pOf, pEl, skewM, Rad.herm_Hb]
  split_ifs <;> fun_prop

noncomputable def shift (k r j : ℕ)
    (x : ({a : Fin r // (a : ℕ) < j} → Fin (k + 1) → ℂ) × PTop k r j) :
    ({p : UT r // (p.1.1 : ℕ) < j} → ℂ) × ({a : Fin r // (a : ℕ) < j} → ℝ) :=
  (fun p => if h : j ≤ (p.1.1.2 : ℕ) then
      herm (Hb k) (x.2.1 ⟨p.1.1.2, h⟩) (x.1 ⟨p.1.1.1, p.2⟩) / 2 else 0, 0)

theorem meas_shift (k r j : ℕ) : Measurable (shift k r j) := by
  refine Measurable.prodMk (Measurable.of_eval fun p => ?_) measurable_const
  simp only [Rad.herm_Hb]
  split_ifs <;> fun_prop

theorem herm_zero_left {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) 0 w = 0 := by
  simp [Rad.herm_Hb]

theorem herm_zero_right {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) w 0 = 0 := by
  simp [Rad.herm_Hb]

theorem mul_eq (k r j : ℕ) (q' : PSec k r j) (q : PTop k r j) :
    pTop k r j q * pSec k r j q' =
      pOf k r (merge k r j ((q'.1, q'.2 + shift k r j (q'.1, q)), q)) := by
  simp only [pTop, pSec, pOf, Rad.pEl_mul, merge]
  congr 1
  · funext a
    by_cases h : (a : ℕ) < j
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  · ext a b
    simp only [Matrix.add_apply, Matrix.of_apply, skewM, shift]
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · have ha' := not_le.2 ha
      have hb' := not_le.2 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]
    · have ha' := not_le.2 ha
      have hb' := not_lt.1 hb
      have hab : a < b := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, herm_zero_left]
    · have ha' := not_lt.1 ha
      have hb' := not_le.2 hb
      have hab : b < a := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, hab.not_gt, herm_zero_left]
      rw [← Rad.herm_star]
      simp only [Complex.star_def]
      ring
    · have ha' := not_lt.1 ha
      have hb' := not_lt.1 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]

theorem lintegral_split (k r j : ℕ) (f : Mat k r → ℝ≥0∞)
    (hf : Measurable (fun x : Mt k r => f (Matrix.of x))) :
    ∫⁻ q : PPar k r, f (pOf k r q) =
      ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  have hg : Measurable (fun q : PPar k r => f (pOf k r q)) :=
    hf.comp (f := fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r))
      (cont_pOf k r).measurable
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_triple {a : Fin r // j ≤ (a : ℕ)} (Fin (k + 1)) {p : UT r // j ≤ (p.1.1 : ℕ)}
    {a : Fin r // j ≤ (a : ℕ)}
  have := inv_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  rw [← (mp_mergeP k r j).lintegral_comp hg,
    lintegral_shift (fun x => f (pOf k r (merge k r j x))) (hg.comp (mp_mergeP k r j).measurable) _ (meas_shift k r j)]
  simp only [mul_eq]

end GlobalTheory.Amp.PSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplitStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_radical_eq_top_section_split : ∀ (k r j : ℕ) (f : Mat k r → ℝ≥0∞), Measurable (fun x : Mt k r => f (Matrix.of x)) → ∫⁻ q : PPar k r, f (pOf k r q) = ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  first | exact @GlobalTheory.Amp.PSplit.lintegral_split | exact GlobalTheory.Amp.PSplit.lintegral_split | (intros; apply GlobalTheory.Amp.PSplit.lintegral_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RadConj

theorem det_eq_one_of_isNilpotent {W : Type} [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {L : W →ₗ[ℝ] W} (hK : IsNilpotent (L - 1)) : LinearMap.det L = 1 := by
  have h := (hK.neg).charpoly_eq_X_pow_finrank
  have h2 := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [h] at h2
  simpa using h2.symm

theorem isNilpotent_of_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (L : V →ₗ[ℝ] V) (A : W →ₗ[ℝ] W) (h : ∀ v, ι (L v) = A (ι v))
    (hA : IsNilpotent (A - 1)) : IsNilpotent (L - 1) := by
  obtain ⟨n, hn⟩ := hA
  have key : ∀ (m : ℕ) (v : V), ι (((L - 1) ^ m) v) = ((A - 1) ^ m) (ι v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih => intro v; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; simp [h]
  refine ⟨n, LinearMap.ext fun v => hι ?_⟩
  rw [key, hn]; simp

theorem isNilpotent_upper_sub_one {r : ℕ} (x : UT r → ℂ) : IsNilpotent (upper x - 1) := by
  have ht : (upper x - 1).BlockTriangular id := by
    intro i j h
    have h' : j < i := h
    simp [upper, not_lt.2 h'.le, h'.ne', Matrix.one_apply]
  have h := Matrix.aeval_self_charpoly (upper x - 1)
  rw [Matrix.charpoly_of_isUpperTriangular _ ht] at h
  refine ⟨r, ?_⟩
  simpa [upper] using h

def skewL (r : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun p := skewM p.1 p.2
  map_add' p q := by
    ext a b; simp only [skewM, Matrix.add_apply]; split_ifs <;> simp <;> ring
  map_smul' c p := by
    ext a b; simp only [skewM, Matrix.smul_apply]; split_ifs <;> simp <;> ring

def skewR (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun S := (fun p => S p.1.1 p.1.2, fun a => (S a a).im)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

theorem skewR_skewL {r : ℕ} (p : (UT r → ℂ) × (Fin r → ℝ)) : skewR r (skewL r p) = p := by
  ext a
  · simp [skewR, skewL, skewM, a.2]
  · simp [skewR, skewL, skewM]

theorem skewL_skewR {r : ℕ} (S : Matrix (Fin r) (Fin r) ℂ) (h : Sᴴ = -S) : skewL r (skewR r S) = S := by
  obtain ⟨p, hp, -⟩ := (GlobalTheory.Amp.Rad.radical 0 r).2.2.1 S h
  have : S = skewL r p := hp
  rw [this, skewR_skewL]

def conjA {r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ :=
  LinearMap.mulLeft ℝ u * LinearMap.mulRight ℝ uᴴ

theorem conjA_apply {r : ℕ} (u S : Matrix (Fin r) (Fin r) ℂ) : conjA u S = u * S * uᴴ := by
  simp [conjA, Matrix.mul_assoc]

theorem isNilpotent_conjA {r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) (h : IsNilpotent (u - 1)) :
    IsNilpotent (conjA u - 1) := by
  have h' : IsNilpotent (u - 1)ᴴ := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by rw [← Matrix.conjTranspose_pow, hn, Matrix.conjTranspose_zero]⟩
  have ha : IsNilpotent (LinearMap.mulLeft ℝ (u - 1)) := (LinearMap.isNilpotent_mulLeft_iff ℝ _).2 h
  have hb : IsNilpotent (LinearMap.mulRight ℝ (u - 1)ᴴ) := (LinearMap.isNilpotent_mulRight_iff ℝ _).2 h'
  have hc : Commute (LinearMap.mulLeft ℝ (u - 1)) (LinearMap.mulRight ℝ (u - 1)ᴴ) :=
    LinearMap.commute_mulLeft_right _ _
  have e : conjA u - 1 = LinearMap.mulLeft ℝ (u - 1) * (1 + LinearMap.mulRight ℝ (u - 1)ᴴ) +
      LinearMap.mulRight ℝ (u - 1)ᴴ := by
    ext1 S
    simp [conjA_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [e]
  have hc2 : Commute (LinearMap.mulLeft ℝ (u - 1)) (1 + LinearMap.mulRight ℝ (u - 1)ᴴ) :=
    (Commute.one_right _).add_right hc
  refine Commute.isNilpotent_add ?_ (hc2.isNilpotent_mul_right ha) hb
  exact hc.mul_left ((Commute.one_left _).add_left (Commute.refl _))

def rowL {r m : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) : (Fin r → Fin m → ℂ) →ₗ[ℝ] (Fin r → Fin m → ℂ) where
  toFun B := fun a => ∑ c, star (u a c) • B c
  map_add' p q := by ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c p := by ext; simp [Finset.mul_sum, mul_left_comm]

theorem rowL_apply {r m : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin m → ℂ) (a : Fin r) :
    rowL u B a = ∑ c, star (u a c) • B c := rfl

theorem rowL_mul {r m : ℕ} (u v : Matrix (Fin r) (Fin r) ℂ) : (rowL (u * v) : (Fin r → Fin m → ℂ) →ₗ[ℝ] _) = rowL u * rowL v := by
  refine LinearMap.ext fun B => funext fun a => funext fun j => ?_
  simp only [Module.End.mul_apply, rowL_apply, Matrix.mul_apply, star_sum, star_mul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem rowL_one {r m : ℕ} : (rowL (1 : Matrix (Fin r) (Fin r) ℂ) : (Fin r → Fin m → ℂ) →ₗ[ℝ] _) = 1 := by
  refine LinearMap.ext fun B => funext fun a => funext fun j => ?_
  simp [rowL_apply, Matrix.one_apply, ite_apply]

theorem isNilpotent_rowL {r m : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) (h : IsNilpotent (u - 1)) :
    IsNilpotent ((rowL u : (Fin r → Fin m → ℂ) →ₗ[ℝ] _) - 1) := by
  have e : (rowL u : (Fin r → Fin m → ℂ) →ₗ[ℝ] _) - 1 = rowL (u - 1) := by
    rw [← rowL_one]; refine LinearMap.ext fun B => funext fun a => funext fun j => ?_
    simp [rowL_apply, sub_mul, Finset.sum_sub_distrib]
  have key : ∀ n : ℕ, (rowL (u - 1) : (Fin r → Fin m → ℂ) →ₗ[ℝ] _) ^ n = rowL ((u - 1) ^ n) := by
    intro n
    induction n with
    | zero => simp [rowL_one]
    | succ n ih => rw [pow_succ, pow_succ, rowL_mul, ih]
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [e, key, hn]; refine LinearMap.ext fun B => funext fun a => funext fun j => ?_
  simp [rowL_apply]

def conjL (k : ℕ) {r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) : PPar k r →ₗ[ℝ] PPar k r :=
  LinearMap.prodMap (rowL u) (skewR r ∘ₗ conjA u ∘ₗ skewL r)

theorem skewL_conj {r : ℕ} (u : Matrix (Fin r) (Fin r) ℂ) (p : (UT r → ℂ) × (Fin r → ℝ)) :
    skewL r ((skewR r ∘ₗ conjA u ∘ₗ skewL r) p) = conjA u (skewL r p) := by
  apply skewL_skewR
  have : (skewL r p)ᴴ = -skewL r p := (GlobalTheory.Amp.Rad.radical 0 r).2.1 p.1 p.2
  simp [conjA_apply, this, Matrix.mul_assoc]

theorem det_conjL (k : ℕ) {r : ℕ} (x : UT r → ℂ) : LinearMap.det (conjL k (upper x)) = 1 := by
  have h := isNilpotent_upper_sub_one x
  rw [conjL, LinearMap.det_prodMap, det_eq_one_of_isNilpotent (isNilpotent_rowL _ h),
    det_eq_one_of_isNilpotent (isNilpotent_of_intertwine (skewL r) (Function.LeftInverse.injective skewR_skewL) _ _
      (skewL_conj _) (isNilpotent_conjA _ h)), one_mul]

theorem map_conjL (k : ℕ) {r : ℕ} (x : UT r → ℂ) : (volume : Measure (PPar k r)).map (conjL k (upper x)) = volume := by
  haveI h1 : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI h0 : (volume : Measure (Fin (k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h0' : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI s1 : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := Measure.prod.instSFinite
  haveI h2 : (volume : Measure (PPar k r)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [det_conjL]; exact one_ne_zero), det_conjL]
  simp

theorem ext_cols {k r : ℕ} {M M' : Mat k r} (h1 : ∀ a, M *ᵥ bvec (eI k r a) = M' *ᵥ bvec (eI k r a))
    (h2 : ∀ a, M *ᵥ bvec (wI k r a) = M' *ᵥ bvec (wI k r a))
    (h3 : ∀ a, M *ᵥ bvec (esI k r a) = M' *ᵥ bvec (esI k r a)) : M = M' := by
  have h : ∀ j, M *ᵥ bvec j = M' *ᵥ bvec j := by
    intro j
    by_cases a : j.val < r
    · exact h1 ⟨j.val, a⟩
    by_cases b : j.val ≤ r + k
    · have : j = wI k r ⟨j.val - r, by omega⟩ := Fin.ext (by simp only [wI]; omega)
      rw [this]; exact h2 _
    · have : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
      rw [this]; exact h3 _
  ext i j
  simpa [bvec] using congrFun (h j) i

theorem herm_rowL_right {r m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin m → ℂ)
    (v : Fin m → ℂ) (a : Fin r) : herm H v (rowL u B a) = ∑ c, u a c * herm H v (B c) := by
  simp [herm, rowL_apply, star_sum, sum_dotProduct]

theorem herm_rowL_left {r m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin m → ℂ)
    (v : Fin m → ℂ) (a : Fin r) : herm H (rowL u B a) v = ∑ c, star (u a c) * herm H (B c) v := by
  simp [herm, rowL_apply, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul]

theorem uEmb_mul_pEl (k r : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) : uEmb k r u * pEl k r B S = pEl k r (rowL u B) (u * S * uᴴ) * uEmb k r u := by
  obtain ⟨-, -, he, hes, hw⟩ := (GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu
  have hw' : ∀ j, uEmb k r u *ᵥ bvec (wI k r j) = bvec (wI k r j) := fun j => hw _ (by
    intro i hi
    have : i ≠ wI k r j := fun h => by
      have := congrArg Fin.val h
      simp only [wI] at this; omega
    simp [bvec, this])
  obtain ⟨pe, pw, pes, -⟩ := (GlobalTheory.Amp.Rad.radical k r).1 B S
  obtain ⟨pe', pw', pes', -⟩ := (GlobalTheory.Amp.Rad.radical k r).1 (rowL u B) (u * S * uᴴ)
  apply ext_cols
  · intro a
    simp only [← Matrix.mulVec_mulVec, pe, he, Matrix.mulVec_sum, Matrix.mulVec_smul, pe']
  · intro j
    simp only [← Matrix.mulVec_mulVec, pw, he, hw', Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, pw',
      herm_rowL_right, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · intro b
    set C : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => S a b - herm (Hb k) (B b) (B a) / 2 with hC
    have hC' : ∀ a b, (u * S * uᴴ) a b - herm (Hb k) (rowL u B b) (rowL u B a) / 2 = (u * C * uᴴ) a b := by
      intro a b
      simp only [herm_rowL_right, herm_rowL_left, Matrix.mul_apply, hC, Matrix.of_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      rw [Finset.sum_comm (f := fun c i => u a c * (star (u b i) * herm (Hb k) (B i) (B c)) / 2)]
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hC0 : ∀ a b, S a b - herm (Hb k) (B b) (B a) / 2 = C a b := fun _ _ => rfl
    have e1 : ∀ j, ∑ a, star (u⁻¹ b a) * rowL u B a j = B b j := by
      intro j
      have : rowL u⁻¹ (rowL u B) = B := by
        rw [← Module.End.mul_apply, ← rowL_mul, Matrix.nonsing_inv_mul _ hu, rowL_one]; rfl
      have := congrFun (congrFun this b) j
      simpa [rowL_apply u⁻¹] using this
    have e2 : ∀ d, ∑ a, star (u⁻¹ b a) * (u * C * uᴴ) d a = ∑ a, C a b * u d a := by
      intro d
      have : u * C * uᴴ * (u⁻¹)ᴴ = u * C := by
        rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hu]; simp
      have := congrFun (congrFun this d) b
      rw [Matrix.mul_apply, Matrix.mul_apply (M := u)] at this
      simpa [mul_comm] using this
    simp only [← Matrix.mulVec_mulVec, pes, he, hes, hw', Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, pes',
      hC', hC0, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a j => (star (u⁻¹ b a) * rowL u B a j) • bvec (wI k r j)),
      Finset.sum_comm (f := fun a d => (star (u⁻¹ b a) * (u * C * uᴴ) d a) • bvec (eI k r d)),
      Finset.sum_comm (f := fun a d => (C a b * u d a) • bvec (eI k r d))]
    simp only [← Finset.sum_smul, e1, e2]

theorem uEmb_mul_pOf (k r : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (q : PPar k r) :
    uEmb k r u * pOf k r q = pOf k r (conjL k u q) * uEmb k r u := by
  rw [pOf, uEmb_mul_pEl k r u hu, ← conjA_apply]
  have := skewL_conj u q.2
  exact congrArg (fun S => pEl k r (rowL u q.1) S * uEmb k r u) this.symm

theorem lintegral_swap (k r : ℕ) (x : UT r → ℂ) (f : Mat k r → ℝ≥0∞) (hf : Measurable fun y : Mt k r => f (Matrix.of y)) :
    ∫⁻ q : PPar k r, f (uEmb k r (upper x) * pOf k r q) = ∫⁻ q : PPar k r, f (pOf k r q * uEmb k r (upper x)) := by
  have hc : Continuous fun q : PPar k r => (Matrix.of.symm (pOf k r q * uEmb k r (upper x)) : Mt k r) :=
    (Model.cont_pOf k r).matrix_mul continuous_const
  have hm : Measurable fun q : PPar k r => f (pOf k r q * uEmb k r (upper x)) := hf.comp hc.measurable
  conv_rhs => rw [← map_conjL k x]
  rw [lintegral_map hm (conjL k (upper x)).continuous_of_finiteDimensional.measurable]
  simp only [uEmb_mul_pOf k r (upper x) (by rw [Model.det_upper]; exact isUnit_one)]

theorem measurable_uEmb (k r : ℕ) :
    Measurable fun M : Fin r → Fin r → ℂ => (Matrix.of.symm (uEmb k r (Matrix.of M)) : Mt k r) := by
  have hd : Continuous fun M : Fin r → Fin r → ℂ => (Matrix.of M).det := Continuous.matrix_det continuous_id
  have ha : Continuous fun M : Fin r → Fin r → ℂ => (Matrix.of M).adjugate := Continuous.matrix_adjugate continuous_id
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.of_symm_apply, uEmb]
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact continuous_star.measurable.comp (hd.measurable.inv.mul (ha.matrix_elem _ _).measurable)
  all_goals exact measurable_const

theorem measurable_mul {X : Type} [MeasurableSpace X] {k r : ℕ} {a b : X → Mat k r}
    (ha : Measurable fun x => (Matrix.of.symm (a x) : Mt k r)) (hb : Measurable fun x => (Matrix.of.symm (b x) : Mt k r)) :
    Measurable fun x => (Matrix.of.symm (a x * b x) : Mt k r) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp ha)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hb))

theorem cont_in (k r : ℕ) (β : Fin r → ℕ) : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
  refine (Model.cont_uEmb k r).comp (continuous_pi fun p => ?_)
  split_ifs <;> fun_prop

theorem cont_off (k r : ℕ) (β : Fin r → ℕ) : Continuous fun x : UToff β → ℂ => uEmb k r (upperOff β x) := by
  refine (Model.cont_uEmb k r).comp (continuous_pi fun p => ?_)
  split_ifs <;> fun_prop

theorem cont_pTop (k r j : ℕ) : Continuous (pTop k r j) := by
  refine (Model.cont_pOf k r).comp (Continuous.prodMk (continuous_pi fun p => ?_)
    (Continuous.prodMk (continuous_pi fun p => ?_) (continuous_pi fun p => ?_))) <;>
  split_ifs <;> fun_prop

theorem cont_pSec (k r j : ℕ) : Continuous (pSec k r j) := by
  refine (Model.cont_pOf k r).comp (Continuous.prodMk (continuous_pi fun p => ?_)
    (Continuous.prodMk (continuous_pi fun p => ?_) (continuous_pi fun p => ?_))) <;>
  split_ifs <;> fun_prop

theorem meas_in (k r : ℕ) (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) :=
  (show Continuous (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) from cont_in k r β).measurable

theorem meas_off (k r : ℕ) (β : Fin r → ℕ) :
    Measurable fun x : UToff β → ℂ => (Matrix.of.symm (uEmb k r (upperOff β x)) : Mt k r) :=
  (show Continuous (fun x : UToff β → ℂ => (Matrix.of.symm (uEmb k r (upperOff β x)) : Mt k r)) from cont_off k r β).measurable

theorem meas_pTop (k r j : ℕ) : Measurable fun x : PTop k r j => (Matrix.of.symm (pTop k r j x) : Mt k r) :=
  (show Continuous (fun x : PTop k r j => (Matrix.of.symm (pTop k r j x) : Mt k r)) from cont_pTop k r j).measurable

theorem meas_pSec (k r j : ℕ) : Measurable fun x : PSec k r j => (Matrix.of.symm (pSec k r j x) : Mt k r) :=
  (show Continuous (fun x : PSec k r j => (Matrix.of.symm (pSec k r j x) : Mt k r)) from cont_pSec k r j).measurable

theorem meas_pOf (k r : ℕ) : Measurable fun x : PPar k r => (Matrix.of.symm (pOf k r x) : Mt k r) :=
  (show Continuous (fun x : PPar k r => (Matrix.of.symm (pOf k r x) : Mt k r)) from Model.cont_pOf k r).measurable

theorem tonelli4 {Y X Q P : Type} [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace P]
    (μY : Measure Y) (μX : Measure X) (μQ : Measure Q) (μP : Measure P) [SFinite μY] [SFinite μX] [SFinite μQ] [SFinite μP]
    (G : Y → X → Q → P → ℝ≥0∞) (hG : Measurable fun t : (Y × X) × Q × P => G t.1.1 t.1.2 t.2.1 t.2.2) :
    ∫⁻ y, ∫⁻ x, ∫⁻ q, ∫⁻ p, G y x q p ∂μP ∂μQ ∂μX ∂μY = ∫⁻ t, ∫⁻ x, ∫⁻ p, G t.2 x t.1 p ∂μP ∂μX ∂(μQ.prod μY) := by
  have hG2 : Measurable fun t : (Y × X) × Q => ∫⁻ p, G t.1.1 t.1.2 t.2 p ∂μP :=
    Measurable.lintegral_prod_right' (f := fun t : ((Y × X) × Q) × P =>
      G t.1.1.1 t.1.1.2 t.1.2 t.2) (hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hG3 : Measurable fun t : Q × Y => ∫⁻ x, ∫⁻ p, G t.2 x t.1 p ∂μP ∂μX :=
    Measurable.lintegral_prod_right' (f := fun t : (Q × Y) × X =>
      ∫⁻ p, G t.1.2 t.2 t.1.1 p ∂μP) (hG2.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst))
  rw [lintegral_prod_symm _ hG3.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact lintegral_lintegral_swap (f := fun x q => ∫⁻ p, G y x q p ∂μP)
    (hG2.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable

theorem sfinite_PPar (k r : ℕ) : SFinite (volume : Measure (PPar k r)) :=
  haveI : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := Measure.prod.instSFinite
  Measure.prod.instSFinite

theorem sfinite_PTop (k r j : ℕ) : SFinite (volume : Measure (PTop k r j)) :=
  haveI : SFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) :=
    Measure.prod.instSFinite
  Measure.prod.instSFinite

theorem sfinite_PSec (k r j : ℕ) : SFinite (volume : Measure (PSec k r j)) :=
  haveI : SFinite (volume : Measure (({p : UT r // p.1.1.val < j} → ℂ) × ({a : Fin r // a.val < j} → ℝ))) :=
    Measure.prod.instSFinite
  Measure.prod.instSFinite

theorem lintegral_lebN (k r j : ℕ) (β : Fin r → ℕ) (hβ : Monotone β) (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ n, f n ∂(lebN k r) = ∫⁻ y : UToff β → ℂ, ∫⁻ x : UTin β → ℂ, ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j,
      f (Matrix.of.symm (uEmb k r (upperIn β x) * (pTop k r j q * pSec k r j q') * uEmb k r (upperOff β y))) := by
  have := sfinite_PPar k r
  have hright : ∀ a b : Mat k r, Measurable fun y : Mt k r => f (Matrix.of.symm (a * Matrix.of y * b)) := fun a b =>
    hf.comp (measurable_mul (measurable_mul measurable_const measurable_id) measurable_const)
  have h0 : Measurable fun q : (UT r → ℂ) × PPar k r => f (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2)) :=
    hf.comp (Model.cont_lebN_map k r).measurable
  rw [lebN, lintegral_map hf (Model.cont_lebN_map k r).measurable, Measure.volume_eq_prod,
    lintegral_prod _ h0.aemeasurable]
  have e1 : ∀ u : UT r → ℂ, ∫⁻ p : PPar k r, f (Matrix.of.symm (uEmb k r (upper u) * pOf k r p)) =
      ∫⁻ p : PPar k r, f (Matrix.of.symm (pOf k r p * uEmb k r (upper u))) := fun u =>
    lintegral_swap k r u (fun M => f (Matrix.of.symm M)) hf
  simp only [e1]
  have hF : Measurable fun M : Fin r → Fin r → ℂ =>
      ∫⁻ p : PPar k r, f (Matrix.of.symm (pOf k r p * uEmb k r (Matrix.of M))) :=
    Measurable.lintegral_prod_right' (f := fun t : (Fin r → Fin r → ℂ) × PPar k r =>
      f (Matrix.of.symm (pOf k r t.2 * uEmb k r (Matrix.of t.1))))
      (hf.comp (measurable_mul ((meas_pOf k r).comp measurable_snd) ((measurable_uEmb k r).comp measurable_fst)))
  refine ((GlobalTheory.Amp.USplit.lebesgue_split r β hβ).2 _ hF).trans ?_
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  have d1 : IsUnit (upperIn β x).det := by rw [upperIn, Model.det_upper]; exact isUnit_one
  have d2 : IsUnit (upperOff β y).det := by rw [upperOff, Model.det_upper]; exact isUnit_one
  have e2 := lintegral_swap k r (fun p => if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0)
    (fun M => f (Matrix.of.symm (1 * M * uEmb k r (upperOff β y)))) (hright _ _)
  simp only [Matrix.one_mul] at e2
  refine Eq.trans ?_ (e2.symm.trans (GlobalTheory.T.lintegral_radical_eq_top_section_split k r j
    (fun M => f (Matrix.of.symm (uEmb k r (upperIn β x) * M * uEmb k r (upperOff β y)))) (hright _ _)))
  refine lintegral_congr fun p => ?_
  rw [Equiv.apply_symm_apply, (GlobalTheory.Amp.UEmb.uEmb_hom k r).1 _ _ d1 d2, ← Matrix.mul_assoc]
  rfl

theorem lintegral_commonStabilizerNormalForm_rightMul_section (k r j : ℕ) (β : Fin r → ℕ) (f : Mt k r → ℝ≥0∞) (hf : Measurable f)
    (q : PSec k r j × (UToff β → ℂ)) : ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) =
      ∫⁻ x : UTin β → ℂ, ∫⁻ p : PTop k r j,
        f (Matrix.of.symm (uEmb k r (upperIn β x) * (pTop k r j p * pSec k r j q.1) * uEmb k r (upperOff β q.2))) := by
  have := sfinite_PTop k r j
  have hc : Measurable fun t : (UTin β → ℂ) × PTop k r j => (Matrix.of.symm (rEl k r j β t) : Mt k r) :=
    measurable_mul ((meas_in k r β).comp measurable_fst) ((meas_pTop k r j).comp measurable_snd)
  have hm : Measurable fun ρ => f (rmulM (sEl k r j β q) ρ) :=
    hf.comp (measurable_mul (a := fun ρ => Matrix.of ρ) measurable_id measurable_const)
  have hmc : Measurable fun t : (UTin β → ℂ) × PTop k r j => f (rmulM (sEl k r j β q) (Matrix.of.symm (rEl k r j β t))) :=
    hm.comp hc
  rw [lebR0, lintegral_map hm hc, Measure.volume_eq_prod, lintegral_prod _ hmc.aemeasurable]
  refine lintegral_congr fun x => lintegral_congr fun p => ?_
  simp only [rmulM, rEl, sEl, Equiv.apply_symm_apply, Matrix.mul_assoc]
  rfl

theorem lebN_split : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) →
    ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ n, f n ∂(lebN k r) =
      ∫⁻ q : PSec k r j × (UToff β → ℂ), ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) := by
  intro k r j β hβ _ f hf
  have := sfinite_PTop k r j
  have := sfinite_PSec k r j
  rw [lintegral_lebN k r j β hβ f hf]
  simp only [lintegral_commonStabilizerNormalForm_rightMul_section k r j β f hf]
  exact tonelli4 volume volume volume volume (fun (y : UToff β → ℂ) (x : UTin β → ℂ) (q' : PSec k r j) (q : PTop k r j) =>
    f (Matrix.of.symm (uEmb k r (upperIn β x) * (pTop k r j q * pSec k r j q') * uEmb k r (upperOff β y))))
    (hf.comp (measurable_mul (measurable_mul ((meas_in k r β).comp measurable_fst.snd)
      (measurable_mul ((meas_pTop k r j).comp measurable_snd.snd) ((meas_pSec k r j).comp measurable_snd.fst)))
      ((meas_off k r β).comp measurable_fst.fst)))

end GlobalTheory.Amp.RadConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSectionStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ n, f n ∂(lebN k r) = ∫⁻ q : PSec k r j × (UToff β → ℂ), ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) := by
  first | exact @GlobalTheory.Amp.RadConj.lebN_split | exact GlobalTheory.Amp.RadConj.lebN_split | (intros; apply GlobalTheory.Amp.RadConj.lebN_split <;> assumption)
end
