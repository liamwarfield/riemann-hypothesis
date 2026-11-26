module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.CoefficientSpans
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Plane
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureCancel
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

theorem int_fin {α Y : Type} [MeasurableSpace α] (μ : Measure α) (G : α → Y → ℂ) (w : α → ℂ) (hf : (Set.range G).Finite)
    (hm : ∀ g, MeasurableSet {a | G a = g}) (D : Set α) (hD : ∀ a ∉ D, G a = 0) (hw : IntegrableOn w D μ)
    (S : Submodule ℂ (Y → ℂ)) (hS : ∀ a, G a ∈ S) :
    (∀ y, Integrable (fun a => G a y * w a) μ) ∧ (fun y => ∫ a, G a y * w a ∂μ) ∈ S := by
  let s := hf.toFinset.erase 0
  have e : ∀ y a, G a y * w a = ∑ g ∈ s, g y * ({a | G a = g} : Set α).indicator w a := fun y a => by
    by_cases h0 : G a = 0
    · rw [h0, Pi.zero_apply, zero_mul, Finset.sum_eq_zero]
      intro g hg
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h => (Finset.mem_erase.1 hg).1 (h.symm.trans h0)
    · rw [Finset.sum_eq_single (G a), Set.indicator_of_mem (by rfl)]
      · intro g _ hne
        rw [Set.indicator_of_notMem (s := {a | G a = g}) (fun h => hne (Eq.symm h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨h0, hf.mem_toFinset.2 ⟨a, rfl⟩⟩) h
  have hi : ∀ g ∈ s, Integrable (({a | G a = g} : Set α).indicator w) μ := fun g hg =>
    (integrable_indicator_iff (hm g)).2 (hw.mono_set fun a ha => by
      by_contra hn
      exact (Finset.mem_erase.1 hg).1 (Eq.trans (Eq.symm ha) (hD a hn)))
  refine ⟨fun y => ?_, ?_⟩
  · simp only [e y]
    exact integrable_finsetSum _ fun g hg => (hi g hg).const_mul _
  · have : (fun y => ∫ a, G a y * w a ∂μ) = ∑ g ∈ s, (∫ a, ({a | G a = g} : Set α).indicator w a ∂μ) • g := by
      funext y
      simp only [e y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum _ fun g hg => (hi g hg).const_mul _]
      exact Finset.sum_congr rfl fun g _ => by rw [integral_const_mul, mul_comm]
    rw [this]
    refine S.sum_mem fun g hg => S.smul_mem _ ?_
    obtain ⟨a, rfl⟩ := hf.mem_toFinset.1 (Finset.mem_erase.1 hg).2
    exact hS a

section Schr
variable {k κ : Type} [CommRing k] [Invertible (2 : k)] [TopologicalSpace k] [IsTopologicalRing k] [Fintype κ]
  {ψ : AddChar k ℂ}

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_mul (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * this

theorem schr_fix (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ x ∈ tsupport φ,
      ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 ∧ φ (x + w.1) = φ x ∧ φ (x - w.1) = φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
    have c1 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 ⬝ᵥ z.1.2 + ⅟(2 : k) * (z.1.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    have c2 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 + z.1.1 := by fun_prop
    have c3 : Continuous fun z : ((κ → k) × (κ → k)) × (κ → k) => z.2 - z.1.1 := by fun_prop
    have e1 := (hψ.comp_continuous c1).eventually_eq (0, x)
    have e2 := (hφ.1.comp_continuous c2).eventually_eq (0, x)
    have e3 := (hφ.1.comp_continuous c3).eventually_eq (0, x)
    have e4 := (hφ.1.comp_continuous (continuous_snd (X := (κ → k) × (κ → k)))).eventually_eq (0, x)
    filter_upwards [e1, e2, e3, e4] with z a b c d
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, mul_zero, add_zero, sub_zero,
      AddChar.map_zero_eq_one] at a b c d
    exact ⟨a, b.trans d.symm, c.trans d.symm⟩
  filter_upwards [h] with w hw
  funext x
  by_cases hx : x ∈ tsupport φ
  · rw [schr, (hw x hx).1, (hw x hx).2.1, one_mul]
  · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [schr, h0]
    by_cases h1 : x + w.1 ∈ tsupport φ
    · have := (hw _ h1).2.2
      rw [add_sub_cancel_right, h0] at this
      rw [← this, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

theorem schr_lc (hψ : IsLocallyConstant ψ) {φ : (κ → k) → ℂ} (hs : ∀ w, schr ψ w φ ∈ SB (κ → k)) :
    IsLocallyConstant fun w => schr ψ w φ := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun w₀ => ?_
  have c : Continuous fun w : (κ → k) × (κ → k) => ⅟(2 : k) * (w.1 ⬝ᵥ w₀.2 - w₀.1 ⬝ᵥ w.2) := by
    unfold dotProduct; fun_prop
  have h : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ (w + w₀) φ = schr ψ w₀ φ := by
    filter_upwards [schr_fix hψ (hs w₀), (hψ.comp_continuous c).eventually_eq 0] with w a b
    simp only [Function.comp_apply, Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero, mul_zero,
      AddChar.map_zero_eq_one] at b
    rw [schr_mul, b, one_smul] at a
    exact a
  have t : Tendsto (fun w : (κ → k) × (κ → k) => w - w₀) (𝓝 w₀) (𝓝 0) := by
    have := (continuous_sub_right w₀).tendsto w₀
    rwa [sub_self] at this
  filter_upwards [t.eventually h] with w hw
  rwa [sub_add_cancel] at hw

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_comm (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  rw [schr_mul, schr_mul, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  have := invOf_two_add_invOf_two (R := k)
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * this

omit [TopologicalSpace k] [IsTopologicalRing k] in
theorem schr_lin (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ) (c : ℂ) :
    schr ψ w (φ + c • φ') = schr ψ w φ + c • schr ψ w φ' := by
  funext x; simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end Schr

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_uniq {v : Pl F} {T} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ φ₂ hφ fun r hr => (h₁ r hr).symm.trans (h₂ r hr)

theorem opF_eq {v : Pl F} {T} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : φ₁ ∈ SB _) (h : Acts (evFin F v) T φ φ₁) :
    opF v T φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := ⟨φ₁, h₁, h⟩
  rw [opF, dite_eq_left ex]
  exact acts_uniq hφ ex.choose_spec.2 h

theorem acts_comp {v : Pl F} {S T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) :
    Acts (evFin F v) (fun Φ => S (T Φ)) φ φ₂ := fun r hr => by
  show S (T _) = _
  rw [h₁ r hr]
  exact h₂ r ⟨hr.1, h₁ r hr ▸ hT _ hr.2⟩

theorem pure_cancel {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, w v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) {g : SInf F κ}
    (hg : g ≠ 0) {a b : (κ → Fv F v) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v a) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v b)) : a = b := by
  have := PositivityTheory.ThKF.tensInj F κ w hne hstd {v} 2 ![1, -1] ![g, g] ![Function.update w v a, Function.update w v b]
    (fun i u hu => by
      have : u ≠ v := fun e => hu (Finset.mem_singleton.2 e)
      fin_cases i <;> simp [Function.update_of_ne this]) (by simp [Fin.sum_univ_two, h])
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  funext y
  let y' : ∀ u : ({v} : Finset (Pl F)), κ → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ y
  let m : MultilinearMap (RingHom.id ℂ) (fun u : ({v} : Finset (Pl F)) => (κ → Fv F u) → ℂ) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ _ ℂ).compLinearMap fun u => LinearMap.proj (y' u)
  let ez : SInf F κ →ₗ[ℂ] ℂ := ⟨⟨fun f => f z, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ez (PiTensorProduct.lift m))) this
  have hm : ∀ c : (κ → Fv F v) → ℂ, m (fun u => Function.update w v c u) = c y := fun c => by
    simp only [m, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
    rw [Fintype.prod_eq_single (⟨v, Finset.mem_singleton_self v⟩ : ({v} : Finset (Pl F)))
      fun u hu => absurd (Subtype.ext (Finset.mem_singleton.1 u.2)) hu]
    simp [y']
  simp only [Fin.sum_univ_two, map_add (f := _), map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, PiTensorProduct.lift.tprod,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, LinearMap.mul_apply', hm] at h2
  have h3 : g z * (a y - b y) = 0 := by
    change (1 : ℂ) • (g z * a y) + (-1 : ℂ) • (g z * b y) = 0 at h2
    simp only [smul_eq_mul] at h2
    linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hz)

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}


variable (F) in
def rk (p : Fin n → E) (q : Fin d → E) : Matrix (Fin n) (Fin d) (AE F E) := Matrix.vecMulVec (GlobalTheory.ThK.incV F p) (GlobalTheory.ThK.incV F q)


variable (σ) in
abbrev hh (X : Spc F E n) (W : Spc F E d) (x y : Matrix (Fin n) (Fin d) (AE F E)) : AE F E :=
  hTens (cA σ) (incM F X.J) (incM F W.J) x y

variable {X : Spc F E n} {W : Spc F E d}

theorem hh_add (x x' y : Matrix (Fin n) (Fin d) (AE F E)) : hh σ X W (x + x') y = hh σ X W x y + hh σ X W x' y := by
  simp only [hh, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hh_smul (a b : AE F E) (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    hh σ X W (a • x) (b • y) = a * cA σ b * hh σ X W x y := by
  simp only [hh, hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem hh_rk (p p' : Fin n → E) (q q' : Fin d → E) :
    hh σ X W (rk F p q) (rk F p' q') = inclR (F := F) (AF F) (form σ X.J p p' * form σ W.J q q') := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
  have f1 : form σ X.J p p' = ∑ i, ∑ k, p i * (X.J i k * σ (p' k)) := by
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  have f2 : form σ W.J q q' = ∑ i, ∑ k, q i * (W.J i k * σ (q' k)) := by
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [f1, f2, Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul_sum, map_sum, hh, hTens, rk, Matrix.vecMulVec_apply, GlobalTheory.ThK.incV, incM, Matrix.map_apply, map_mul, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem incM_rk (p : Fin n → E) (q : Fin d → E) : incM F (Matrix.vecMulVec p q) = rk F p q := by
  ext i j; simp [incM, rk, GlobalTheory.ThK.incV, Matrix.vecMulVec_apply]

theorem rk_smul (s t : E) (p : Fin n → E) (q : Fin d → E) :
    rk F (s • p) (t • q) = inclR (F := F) (AF F) (s * t) • rk F p q := by
  ext i j
  simp only [rk, GlobalTheory.ThK.incV, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply]
  ring

theorem comp_lat {p p' : Fin n → E} {q q' : Fin d → E}
    (hp : ∀ x ∈ X.L, ∃ s : E, s • p' ∈ X.L ∧ form σ X.J x p = s * form σ X.J p' p)
    (hq : ∀ y ∈ W.L, ∃ t : E, t • q' ∈ W.L ∧ form σ W.J y q = t * form σ W.J q' q) (v : Pl F) {γ} (hγ : γ ∈ latAtV X W v) :
    ∃ t : AE F E, t • rk F p' q' ∈ latAtV X W v ∧ hh σ X W γ (rk F p q) = t * hh σ X W (rk F p' q') (rk F p q) := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨s, hs, hs'⟩ := hp x hx
    obtain ⟨t, ht, ht'⟩ := hq y hy
    refine ⟨algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) (s * t), AddSubgroup.subset_closure
      ⟨a, ha, hav, _, hs, _, ht, by rw [incM_rk, rk_smul, mul_smul, algebraMap_smul]⟩, ?_⟩
    have := hh_smul (σ := σ) (X := X) (W := W) (algebraMap (AF F) (AE F E) a) 1 (rk F x y) (rk F p q)
    rw [one_smul, algebraMap_smul, map_one, mul_one] at this
    rw [incM_rk, this, hh_rk, hh_rk, hs', ht']
    simp only [map_mul]; ring
  | zero => exact ⟨0, by rw [zero_smul]; exact zero_mem _, by simp [hh, hTens]⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, h1, h2⟩ := hy
    obtain ⟨t', h1', h2'⟩ := hz
    exact ⟨t + t', by rw [add_smul]; exact add_mem h1 h1', by rw [hh_add, h2, h2', add_mul]⟩
  | neg y _ hy =>
    obtain ⟨t, h1, h2⟩ := hy
    refine ⟨-t, by rw [neg_smul]; exact neg_mem h1, ?_⟩
    have := hh_smul (σ := σ) (X := X) (W := W) (-1) 1 y (rk F p q)
    rw [one_smul, neg_one_smul, map_one, mul_one] at this
    rw [this, h2]; ring

theorem form_lin (J : Matrix (Fin n) (Fin n) E) (s t : E) (x u y z : Fin n → E) :
    form σ J (s • x + u + t • y) z = s * form σ J x z + form σ J u z + t * form σ J y z := by
  simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem exists_smul_y_mem_and_form_eq_of_isAdapted {B : Base F E} {m : ℕ} {Y₁ : Spc F E m} {H : Plane E n m} {i j : ℕ} (h : H.IsAdapted σ B X Y₁ i j) :
    ∀ z ∈ X.L, ∃ s : E, s • H.y ∈ X.L ∧ form σ X.J z H.x = s * form σ X.J H.y H.x := fun z hz => by
  obtain ⟨s, t, u, -, ht, -, rfl⟩ := h.split z hz
  exact ⟨t, ht, by rw [form_lin, h.xx, (h.orth u).1]; ring⟩

theorem plane_y {B : Base F E} {m : ℕ} {Y₁ : Spc F E m} {H : Plane E n m} {i j : ℕ} (h : H.IsAdapted σ B X Y₁ i j) :
    ∀ z ∈ X.L, ∃ s : E, s • H.x ∈ X.L ∧ form σ X.J z H.y = s * form σ X.J H.x H.y := fun z hz => by
  obtain ⟨s, t, u, hs, -, -, rfl⟩ := h.split z hz
  exact ⟨s, hs, by rw [form_lin, h.yy, (h.orth u).2]; ring⟩

variable {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem dirs {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e u}
    (h : Cfg B M M₁ H H' e u) : ∃ (V₀ V₁ : Matrix (Fin n) (Fin d) (AE F E)) (c : AE F E →ₐ[AF F] AE F E),
      (∀ l, u l = c l.1 • V₀) ∧ hh σ X W V₀ V₀ = 0 ∧ hh σ X W V₁ V₁ = 0 ∧
      (∀ t : AE F E, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (t • V₁) Φ) = e Φ) ∧
      ∀ v, ∀ γ ∈ latAtV X W v, ∃ t : AE F E, t • V₁ ∈ latAtV X W v ∧ hh σ X W γ V₀ = t * hh σ X W V₁ V₀ := by
  obtain ⟨i, j, hH⟩ := h.hH
  obtain ⟨i', j', hH'⟩ := h.hH'
  rcases h.ev with ⟨he, rfl⟩ | ⟨he, rfl⟩
  · refine ⟨rk F H.x H'.y, rk F H.y H'.x, AlgHom.id _ _, fun _ => rfl, by rw [hh_rk, hH.xx, zero_mul, map_zero],
      by rw [hh_rk, hH.yy, zero_mul, map_zero], fun t => he.inv _ (Or.inl ⟨t • GlobalTheory.ThK.incV F H.y, ?_⟩),
      fun v γ hγ => comp_lat (exists_smul_y_mem_and_form_eq_of_isAdapted hH) (plane_y hH') v hγ⟩
    ext a b; simp [rk, Matrix.vecMulVec_apply, mul_assoc]
  · refine ⟨rk F H.y H'.x, rk F H.x H'.y, cA σ, fun _ => rfl, by rw [hh_rk, hH.yy, zero_mul, map_zero],
      by rw [hh_rk, hH.xx, zero_mul, map_zero], fun t => he.inv _ (Or.inl ⟨t • GlobalTheory.ThK.incV F H'.y, ?_⟩),
      fun v γ hγ => comp_lat (plane_y hH) (exists_smul_y_mem_and_form_eq_of_isAdapted hH') v hγ⟩
    ext a b; simp [rk, Matrix.vecMulVec_apply, mul_left_comm]

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

abbrev rv (B : Base F E) (M : Model σ X W) (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)) (φ : Fl F v n d) : Fl F v n d :=
  schr (psiAt B.ψ v) (locCo M.co v w) φ

theorem rv_sb {B : Base F E} (hB : B.IsGood σ) (M : Model σ X W) (v : Pl F) (w) {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    schr (psiAt B.ψ v) w φ ∈ SB _ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v w φ hφ

theorem rv_acts (B : Base F E) (M : Model σ X W) {v : Pl F} {w} (hw : At (evFin F v) w) (φ : Fl F v n d) :
    Acts (evFin F v) (M.co.rho B.ψ w) φ (rv B M v w φ) := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v w hw φ

theorem evFin_idem (v : Pl F) : evFin F v (idem F v) = 1 := evFin_liftV v 1

theorem at_idem {N : Type} [AddCommGroup N] [Module (AF F) N] (v : Pl F) (z : N) : At (evFin F v) (idem F v • z) := fun u hu => by
  rw [smul_smul, show u * idem F v = 0 from at_liftV v 1 u hu, zero_smul]

theorem at_smul {N : Type} [AddCommGroup N] [Module (AF F) N] {v : Pl F} (a : AF F) {z : N} (hz : At (evFin F v) z) :
    At (evFin F v) (a • z) := fun u hu => by rw [smul_comm, hz u hu, smul_zero]

theorem locCo_smul (M : Model σ X W) (v : Pl F) (a : AF F) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    locCo M.co v (a • w) = evFin F v a • locCo M.co v w := by
  ext i <;> simp [locCo]

theorem ev_inv {B : Base F E} (hB : B.IsGood σ) {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e ei ev} (h : IsEvLoc M M₁ e ei ev) {v : Pl F} {i} (hi : At (evFin F v) i)
    (he : ∀ Φ ∈ schA F _, e (M.co.rho B.ψ i Φ) = e Φ) {φ : Fl F v n d} (hφ : φ ∈ SB _) : ev v (rv B M v i φ) = ev v φ := by
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h.ne (ContinuousLinearMap.ext hn)
  have sb : ∀ a : Fl F v n d, a ∈ SB _ → ∀ u, Function.update M.vac v a u ∈ SB _ := fun a ha u => by
    by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact (hM.vac u).1
  have cf : ∀ a : Fl F v n d, ∀ᶠ u in cofinite, Function.update M.vac v a u = M.vac u := fun a => by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu using Function.update_of_ne hu _ _
  have st : ∀ a : Fl F v n d, ∀ᶠ u in cofinite, Function.update M.vac v a u =
      Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := fun a => by
    filter_upwards [cf a, hM.std] with u a b using a.trans b
  have up : ∀ a : Fl F v n d, (fun u => ev u (Function.update M.vac v a u)) = Function.update M₁.vac v (ev v a) := fun a =>
    funext fun u => by
      by_cases e : u = v
      · subst e; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e, Function.update_of_ne e, (h.vac u).1]
  have h1 := (PositivityTheory.ThKF.pureAct F _ v (M.co.rho B.ψ i) f _ (sb φ hφ) (st φ)).2.2 (rv B M v i φ)
    (by rw [Function.update_self]; exact rv_acts B M hi φ)
  have h2 := he _ (GlobalTheory.TensUniq.pure_mem_schA f _ (sb φ hφ) (st φ))
  rw [h1, Function.update_idem, h.pure f _ (sb _ (rv_sb hB M v _ hφ)) (cf _), h.pure f _ (sb _ hφ) (cf _), up, up] at h2
  exact pure_cancel (fun u => (hM₁.vac u).2.1) hM₁.std v hf h2

theorem vac_fix {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) {v : Pl F} {γ} (hγ : γ ∈ latAtV X W v)
    (h0 : hh σ X W γ γ = 0) : Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v) (M.vac v) := by
  obtain ⟨-, -, θ, -, hθ⟩ := hM.vac v
  have := hθ γ hγ
  rwa [symp, show hTens (cA σ) (incM F X.J) (incM F W.J) γ γ = 0 from h0, mul_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul] at this

theorem key {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e u ei ev}
    (hc : Cfg B M M₁ H H' e u) (h : IsEvLoc M M₁ e ei ev) {V₀ V₁ : Matrix (Fin n) (Fin d) (AE F E)}
    (hinv : ∀ t : AE F E, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (t • V₁) Φ) = e Φ) {v : Pl F}
    (hcomp : ∀ γ ∈ latAtV X W v, ∃ t : AE F E, t • V₁ ∈ latAtV X W v ∧ hh σ X W γ V₀ = t * hh σ X W V₁ V₀)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (a : AF F) (ha : ∀ t : AE F E, t • V₁ ∈ latAtV X W v → rv B M v (a • t • V₁) φ = φ)
    (b : AE F E) (hb : At (evFin F v) (b • V₀)) (hne : ev v (rv B M v (b • V₀) φ) ≠ 0) : a • b • V₀ ∈ latAtV X W v := by
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  refine PositivityTheory.ThK.Vac.mem_latAtV hc.base hX hW v (at_smul a hb) fun γ hγ => ?_
  obtain ⟨t, ht, e1⟩ := hcomp γ hγ
  have hi : At (evFin F v) (a • t • V₁) := at_smul a ((latAtV_at_stable X W v).1 _ ht)
  have e2 : a • t • V₁ = (algebraMap (AF F) (AE F E) a * t) • V₁ := by rw [mul_smul, algebraMap_smul]
  have h1 := ev_inv hc.base hc.good hc.good₁ h hi (by rw [e2]; exact hinv _) (rv_sb hc.base M v (locCo M.co v (b • V₀)) hφ)
  rw [rv, schr_comm, ← GlobalTheory.LatVac.DualLoc.psi_form M.co v B.ψ hi, show schr _ (locCo M.co v (a • t • V₁)) φ = φ from ha t ht,
    map_smul] at h1
  have h2 : B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (a • t • V₁) (b • V₀)) = 1 :=
    smul_left_injective ℂ hne (h1.trans (one_smul _ _).symm)
  rw [← h2, symp, symp]
  congr 3
  have e3 : a • b • V₀ = (algebraMap (AF F) (AE F E) a * b) • V₀ := by rw [mul_smul, algebraMap_smul]
  have e4 := hh_smul (σ := σ) (X := X) (W := W) 1 (algebraMap (AF F) (AE F E) a * b) γ V₀
  rw [one_smul] at e4
  change hh σ X W _ _ = hh σ X W _ _
  rw [e2, e3, e4, hh_smul, e1, map_mul, AlgHom.commutes]
  ring

theorem lat_compact {B : Base F E} {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W) (v : Pl F) :
    ∃ C, IsCompact C ∧ ∀ γ ∈ latAtV X W v, locCo M.co v γ ∈ C := by
  obtain ⟨I, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X W hX.lat.toIsLattice hW.lat.toIsLattice v
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  refine ⟨Set.range fun a : I → v.adicCompletionIntegers F => ∑ m, (a m : Fv F v) • locCo M.co v (incM F (g m)),
    isCompact_range (continuous_finsetSum _ fun m _ => (show Continuous fun a : I → v.adicCompletionIntegers F => (a m : Fv F v) from
      continuous_subtype_val.comp (continuous_apply m)).smul continuous_const),
    fun γ hγ => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ
  refine ⟨a, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [locCo_smul, GlobalTheory.EmbChart.evFin_atPlace]

theorem exists_nat (v : Pl F) {U : Set (Fv F v)} (hU : U ∈ 𝓝 0) : ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) ∈ U := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : ‖((Ideal.absNorm v.asIdeal : ℕ) : Fv F v)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
    simpa using this
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).eventually hU).exists
  exact ⟨Ideal.absNorm v.asIdeal ^ m, pow_ne_zero _ h0, by rw [Nat.cast_pow]; exact hm⟩

theorem psi_lc {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : IsLocallyConstant (psiAt B.ψ v) :=
  GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt B.ψ hB.std.1 v)

theorem exists_level {B : Base F E} (hB : B.IsGood σ) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ γ ∈ latAtV X W v, rv B M v ((N : AF F) • γ) φ = φ := by
  obtain ⟨C, hC, h⟩ := lat_compact hX hW M v
  have h1 : ∀ᶠ x in 𝓝 (0 : Fv F v), ∀ w ∈ C, schr (psiAt B.ψ v) (x • w) φ = φ := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have t : Tendsto (fun z : Fv F v × _ => z.1 • z.2) (𝓝 (0, w)) (𝓝 0) := by
      have := (continuous_smul (M := Fv F v)).tendsto (0, w)
      rwa [zero_smul] at this
    exact t.eventually (schr_fix (psi_lc hB v) hφ)
  obtain ⟨N, hN, h2⟩ := exists_nat v h1
  exact ⟨N, hN, fun γ hγ => by rw [rv, locCo_smul, map_natCast]; exact h2 _ (h γ hγ)⟩

theorem cont_loc (M : Model σ X W) (v : Pl F) (c : AE F E →ₐ[AF F] AE F E) (V : Matrix (Fin n) (Fin d) (AE F E)) :
    Continuous fun x : AE F E => locCo M.co v (c x • V) := by
  let L : AE F E →ₗ[AF F] _ := M.co.e.toLinearMap ∘ₗ ((LinearMap.toSpanSingleton (AE F E) _ V).restrictScalars (AF F)) ∘ₗ c.toLinearMap
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have he : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact (continuous_pi fun i => he.comp ((continuous_apply i).comp hL.fst)).prodMk
    (continuous_pi fun i => he.comp ((continuous_apply i).comp hL.snd))

end PositivityTheory.ThKG.Loc.Cone.Fin

end
end

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.FinStmt
noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


open Classical in
def FinCone2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F, (∀ l, ev v (opF v (M.co.rho B.ψ (idem F v • u l)) (M.vac v)) = if idem F v • u l ∈ latAtV X W v then M₁.vac v else 0) ∧
    (∀ l, idem F v • u l ∈ latAtV X W v → Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (M.vac v) (M.vac v)) ∧
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 2 ≤ z →
    ∃ Λ : Fl F v _ _ →ₗ[ℂ] Fl F v _ _, ∀ φ ∈ SB _, Λ φ = coneF B M om m v (ev v) u ν z φ ∧ Λ φ ∈ SB _ ∧ ∀ y,
      (∀ k : kAt K (evFin F v), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.xf v)) ∧
        Integrable (fun k : kAt K (evFin F v) => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.kf v)

end PositivityTheory.ThKG.Loc.Cone

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

theorem idem_sq (v : Pl F) : idem F v * idem F v = idem F v := by
  have := PositivityTheory.ThK.Vac.liftV_mul v 1 (idem F v)
  rwa [evFin_idem, mul_one] at this

theorem norm_wt (ν : Chr F E) (z : ℕ) (l : (AE F E)ˣ) : ‖wt ν z l‖ = (absE F E l : ℝ) ^ z := by
  rw [wt, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg NNReal.zero_le_coe]

theorem cont_wt {ν : Chr F E} (hν : Continuous ν) (z : ℕ) : Continuous (wt ν z) :=
  (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)


variable (σ X) in
def uSub (v : Pl F) : Subgroup (UA σ X.J) where
  carrier := UAt σ X (evFin F v)
  one_mem' := fun u _ => by rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  mul_mem' := fun {a b} ha hb u hu => by
    have e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1) := by
      rw [show mat (a * b) = mat a * mat b from rfl, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, ha u hu, hb u hu, Matrix.zero_mul, add_zero]
  inv_mem' := fun {a} ha u hu => by
    have h1 : mat a⁻¹ * mat a = 1 := a.1.inv_mul
    have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, neg_zero]

theorem kAt_eq (K : Subgroup (UA σ X.J)) (v : Pl F) : kAt K (evFin F v) = K ⊓ uSub σ X v :=
  congrArg (K ⊓ ·) (Subgroup.closure_eq (uSub σ X v))

theorem kAt_mem {K : Subgroup (UA σ X.J)} {v : Pl F} (k : kAt K (evFin F v)) : k.1 ∈ UAt σ X (evFin F v) :=
  ((kAt_eq K v).le k.2).2

theorem kAt_compact {K : Subgroup (UA σ X.J)} (hK : IsCompact (K : Set (UA σ X.J))) (v : Pl F) : CompactSpace (kAt K (evFin F v)) := by
  refine isCompact_iff_compactSpace.1 ?_
  rw [kAt_eq, Subgroup.coe_inf]
  refine hK.inter_right ?_
  have : (uSub σ X v : Set (UA σ X.J)) = ⋂ u : AF F, ⋂ _ : evFin F v u = 0, {g | u • (mat g - 1) = 0} := by
    ext g; simp only [Set.mem_iInter]; rfl
  rw [this]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq (((PositivityTheory.ThK.kc_cont_mat X.J).sub continuous_const).const_smul u) continuous_const

theorem tate (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {e u ei ev} (hc : Cfg B M M₁ H H' e u) (h : IsEvLoc M M₁ e ei ev) (v : Pl F)
    {K : Subgroup (UA σ X.J)} (m : LocMeas K) (hm : m.Is) {ν : Chr F E} (hν : Continuous ν) {z : ℕ} (hz : 2 ≤ z)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    (∀ y, @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1) (m.xf v)) ∧
      (fun y => @integral _ _ _ _ (borel _) (m.xf v) fun l => ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1) ∈ SB _ := by
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  haveI := (hm.xf v).1
  obtain ⟨V₀, V₁, c, hu, -, -, hinv, hcomp⟩ := dirs hc
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨i, j, hH⟩ := hc.hH
  obtain ⟨i', j', hH'⟩ := hc.hH'
  obtain ⟨𝔞, h𝔞, hin⟩ := hJ F E σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hc.base hX hW hH hH' u
    (hc.ev.imp And.right And.right)
  obtain ⟨-, -, μ, -, -, -, hμ⟩ := hS F E σ B n X r s hc.base hX
  obtain ⟨πi, π, κ, -, hπ, hF⟩ := hI F E σ B n X K m μ hc.base hm hμ 𝔞 z h𝔞 hz
  have hint := ((hF 1 ∅ ∅ continuous_const (Finset.Subset.refl _) (fun w _ x _ => map_one Circle.toUnits)
    (fun w hw => absurd hw (Finset.notMem_empty _))).1 v (Finset.notMem_empty v)).2
  obtain ⟨N, hN, hfix⟩ := exists_level hc.base hX hW M v hφ
  obtain ⟨C, hC, hCΓ⟩ := lat_compact hX hW M v
  let g : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → Fl F v n₁ d₁ := fun w => ev v (schr (psiAt B.ψ v) w φ)
  have hg : IsLocallyConstant g := (schr_lc (psi_lc hc.base v) fun w => rv_sb hc.base M v w hφ).comp (ev v)
  have e1 : ∀ l : (AE F E)ˣ, locCo M.co v (idem F v • u l) = locCo M.co v (c l.1 • V₀) := fun l => by
    rw [locCo_smul, evFin_idem, one_smul, hu]
  have hG : IsLocallyConstant fun l : idAt E (evFin F v) => ev v (rv B M v (idem F v • u l.1) φ) := by
    simp only [rv, e1]
    exact hg.comp_continuous ((cont_loc M v c V₀).comp (Units.continuous_val.comp continuous_subtype_val))
  have hk : ∀ l : (AE F E)ˣ, ev v (rv B M v (idem F v • u l) φ) ≠ 0 → (N : AF F) • idem F v • u l ∈ latAtV X W v := fun l hl => by
    have e2 : idem F v • u l = (idem F v • c l.1) • V₀ := by rw [hu, smul_assoc]
    rw [e2] at hl ⊢
    exact key hc h hinv (hcomp v) hφ N (fun t ht => hfix _ ht) _ (e2 ▸ at_idem v _) hl
  have hN' : (N : Fv F v) ≠ 0 := by
    haveI : CharZero (Fv F v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN
  refine int_fin (m.xf v) (fun l => ev v (rv B M v (idem F v • u l.1) φ)) (fun l => wt ν z l.1) ?_
    (fun a => (hG.isOpen_fiber a).measurableSet) {l | ev v (rv B M v (idem F v • u l.1) φ) ≠ 0} (fun a ha => not_not.1 ha) ?_ _
    fun l => (h.vac v).2 ▸ Submodule.mem_map_of_mem (rv_sb hc.base M v _ hφ)
  · haveI := isCompact_iff_compactSpace.1 hC
    have hf := (hg.comp_continuous ((continuous_subtype_val (p := (· ∈ C))).const_smul (N : Fv F v)⁻¹)).range_finite
    refine (hf.insert 0).subset ?_
    rintro _ ⟨l, rfl⟩
    by_cases h0 : ev v (rv B M v (idem F v • u l.1) φ) = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨_, hCΓ _ (hk _ h0)⟩, ?_⟩
      change g ((N : Fv F v)⁻¹ • locCo M.co v ((N : AF F) • idem F v • u l.1)) = _
      rw [locCo_smul M v (N : AF F), map_natCast, inv_smul_smul₀ hN']
  · have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN
    let lN : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (N : E) hNE)
    let l₀ := π v lN
    have hl₀ : (l₀.1 : AE F E) = idem F v • (N : AE F E) + (1 - idem F v) • (1 : AE F E) := by
      have := (hπ lN).2 v
      rw [IsPart, show (lN : AE F E) = (N : AE F E) from map_natCast (inclR (F := F) (AF F)) N] at this
      exact this
    have e3 : ∀ l : idAt E (evFin F v), idem F v • u (l₀ * l).1 = (N : AF F) • idem F v • u l.1 := fun l => by
      rw [hu, hu, ← smul_assoc, ← smul_assoc, ← smul_assoc]
      congr 1
      have q : algebraMap (AF F) (AE F E) (idem F v) * algebraMap (AF F) (AE F E) (idem F v) =
          algebraMap (AF F) (AE F E) (idem F v) := by rw [← map_mul, idem_sq]
      rw [Subgroup.coe_mul, Units.val_mul, map_mul, hl₀, map_add (f := _), map_smul, map_smul, map_natCast, map_one]
      simp only [Algebra.smul_def, smul_eq_mul, map_mul, map_sub, map_one, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
      linear_combination ((N : AE F E) * c l.1.1 - c l.1.1) * q
    have h0 : (0 : ℝ) < absE F E l₀.1 := by
      refine lt_of_le_of_ne NNReal.zero_le_coe fun e => ?_
      have : absE F E l₀.1 * absE F E l₀.1⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [show absE F E l₀.1 = 0 from NNReal.coe_eq_zero.1 e.symm, zero_mul] at this
      exact zero_ne_one this
    refine Integrable.mono' (((hint.comp_mul_left l₀).norm.const_mul (((absE F E l₀.1 : ℝ) ^ z)⁻¹)).integrableOn)
      ((cont_wt hν z).comp continuous_subtype_val).aestronglyMeasurable
      (ae_restrict_of_forall_mem (hG.isClosed_fiber 0).measurableSet.compl fun l hl => ?_)
    have := (hin v (l₀ * l).1).1 (e3 l ▸ hk _ hl)
    rw [if_pos this, one_mul, norm_wt, norm_wt, Subgroup.coe_mul, map_mul, NNReal.coe_mul, mul_pow,
      inv_mul_cancel_left₀ (pow_pos h0 z).ne']

theorem finCone2_of (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) : FinCone2 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc h v
  obtain ⟨V₀, V₁, c, hu, h00, h11, hinv, hcomp⟩ := dirs hc
  have hv := (hc.good.vac v).1
  have e2 : ∀ l, idem F v • u l = (idem F v • c l.1) • V₀ := fun l => by rw [hu, smul_assoc]
  have c2 : ∀ l, idem F v • u l ∈ latAtV X W v → Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (M.vac v) (M.vac v) :=
    fun l hl => vac_fix hc.good hl (by rw [e2, hh_smul, h00, mul_zero])
  refine ⟨fun l => ?_, c2, fun K m hK hm χX χW om r s r' s' hP ν z hν hz => ?_⟩
  · split_ifs with hl
    · rw [opF_eq hv hv (c2 l hl), (h.vac v).1]
    · rw [opF_eq hv (rv_sb hc.base M v _ hv) (rv_acts B M (at_idem v _) _)]
      by_contra hne
      rw [e2] at hne hl
      have := key hc h hinv (hcomp v) hv 1 (fun t ht => by
        rw [one_smul]
        exact acts_uniq hv (rv_acts B M ((latAtV_at_stable X W v).1 _ ht) _)
          (vac_fix hc.good ht (by rw [hh_smul, h11, mul_zero]))) _ (e2 l ▸ at_idem v _) hne
      rw [one_smul] at this
      exact hl this
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  obtain ⟨K', -, -, hK', hKc, -⟩ := hS F E σ B n X r s hP.base hP.herm
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI := kAt_compact hKc v
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (m.kf v) := ⟨(hm.kf v).2⟩
  have o1 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (uSub σ W v).one_mem
  have sb : ∀ k : kAt K (evFin F v), ∀ φ ∈ SB _, ω (k.1, 1) φ ∈ SB _ := fun k φ hφ => L.pres _ (kAt_mem k) _ o1 φ hφ
  have op : ∀ (k : kAt K (evFin F v)) (l : (AE F E)ˣ), ∀ φ ∈ SB _,
      opF v (fun Φ => M.co.rho B.ψ (idem F v • u l) (om (k.1, 1) Φ)) φ = rv B M v (idem F v • u l) (ω (k.1, 1) φ) :=
    fun k l φ hφ => opF_eq hφ (rv_sb hc.base M v _ (sb k φ hφ)) (acts_comp ((IsUWeilPair.isUSplitting hP.weil).pres _)
      ((L.acts _ (kAt_mem k) _ o1 φ hφ _).2 rfl) (rv_acts B M (at_idem v _) _))
  let A : Fl F v n d → Fl F v n₁ d₁ := fun φ y => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
    ev v (rv B M v (idem F v • u l.1) φ) y * wt ν z l.1
  have hA := fun φ (hφ : φ ∈ SB _) => tate hI hJ hS hc h v m hm hν hz (φ := φ) hφ
  have lc : ∀ φ ∈ SB _, IsLocallyConstant fun k : kAt K (evFin F v) => ω (k.1, 1) φ := fun φ hφ => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun k₀ => ?_
    obtain ⟨U, hU, hU'⟩ := (PositivityTheory.ThKF0.actsEx F E σ B n d X W M χX χW om r s r' s' hP v).2.2 _ (sb k₀ φ hφ)
    have t : Tendsto (fun k : kAt K (evFin F v) => (((k * k₀⁻¹).1, 1) : UA σ X.J × UA σ W.J)) (𝓝 k₀) (𝓝 1) := by
      have : Continuous fun k : kAt K (evFin F v) => (((k * k₀⁻¹).1, 1) : UA σ X.J × UA σ W.J) :=
        (continuous_subtype_val.comp (continuous_mul_const k₀⁻¹)).prodMk continuous_const
      have := this.tendsto k₀
      rwa [mul_inv_cancel] at this
    filter_upwards [t.eventually hU] with k hk
    have h1 := (L.acts _ (kAt_mem (k * k₀⁻¹)) _ o1 _ (sb k₀ φ hφ) _).1 (hU' _ hk (kAt_mem (k * k₀⁻¹)) o1)
    rw [← L.mul _ (kAt_mem (k * k₀⁻¹)) _ o1 _ (kAt_mem k₀) _ o1 φ hφ, mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right] at h1
    exact h1.symm
  have hk : ∀ φ ∈ SB _, (∀ y, Integrable (fun k : kAt K (evFin F v) => A (ω (k.1, 1) φ) y * 1) (m.kf v)) ∧
      (fun y => ∫ k : kAt K (evFin F v), A (ω (k.1, 1) φ) y * 1 ∂(m.kf v)) ∈ SB _ := fun φ hφ =>
    int_fin (m.kf v) (fun k => A (ω (k.1, 1) φ)) (fun _ => 1) ((lc φ hφ).comp A).range_finite
      (fun a => (((lc φ hφ).comp A).isOpen_fiber a).measurableSet) Set.univ (fun a ha => absurd trivial ha)
      (integrable_const _).integrableOn _ fun k => (hA _ (sb k φ hφ)).2
  simp only [mul_one] at hk
  have ce : ∀ φ ∈ SB _, coneF B M om m v (ev v) u ν z φ = fun y => ∫ k : kAt K (evFin F v), A (ω (k.1, 1) φ) y ∂(m.kf v) :=
    fun φ hφ => funext fun y => by
      simp only [coneF, op _ _ φ hφ, A, wt, mul_assoc]
  have Al : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ (a : ℂ) y, A (φ + a • φ') y = A φ y + a * A φ' y := fun φ hφ φ' hφ' a y => by
    letI : MeasurableSpace (idAt E (evFin F v)) := borel _
    simp only [A, rv, schr_lin, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add ((hA φ hφ).1 y) (((hA φ' hφ').1 y).const_mul a), integral_const_mul]
  have cl : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ a : ℂ, coneF B M om m v (ev v) u ν z (φ + a • φ') =
      coneF B M om m v (ev v) u ν z φ + a • coneF B M om m v (ev v) u ν z φ' := fun φ hφ φ' hφ' a => by
    rw [ce _ hφ, ce _ hφ', ce _ (add_mem hφ (Submodule.smul_mem _ a hφ'))]
    funext y
    simp only [map_add (f := _), map_smul, Al _ (sb _ φ hφ) _ (sb _ φ' hφ'), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add ((hk φ hφ).1 y) (((hk φ' hφ').1 y).const_mul a), integral_const_mul]
  have c0 : coneF B M om m v (ev v) u ν z 0 = 0 := by
    have := cl 0 (zero_mem _) 0 (zero_mem _) 1
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let Λ₀ : SB (Fin n × Fin d → Fv F v) →ₗ[ℂ] Fl F v n₁ d₁ :=
    { toFun := fun φ => coneF B M om m v (ev v) u ν z φ.1
      map_add' := fun φ φ' => by simpa using cl _ φ.2 _ φ'.2 1
      map_smul' := fun a φ => by simpa [c0] using cl 0 (zero_mem _) _ φ.2 a }
  obtain ⟨Λ, hΛ⟩ := Λ₀.exists_extend
  refine ⟨Λ, fun φ hφ => ?_⟩
  have eΛ : Λ φ = coneF B M om m v (ev v) u ν z φ := LinearMap.congr_fun hΛ ⟨φ, hφ⟩
  refine ⟨eΛ, by rw [eΛ, ce φ hφ]; exact (hk φ hφ).2, fun y => ⟨fun k => ?_, ?_⟩⟩
  · simp only [op _ _ φ hφ]
    exact (hA _ (sb k φ hφ)).1 y
  · simp only [op _ _ φ hφ]
    exact (hk φ hφ).1 y

end PositivityTheory.ThKG.Loc.Cone.Fin

end
