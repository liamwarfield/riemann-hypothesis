module

public import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstMatch
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_ext {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)] {S T : Finset ι} (h : S ⊆ T)
    (z : ∀ v, M v) : ∃ e : (PiTensorProduct ℂ fun v : S => M v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => M v,
      ∀ u : ∀ v, M v, (∀ v ∉ S, u v = z v) → e (PiTensorProduct.tprod ℂ fun v : S => u v) = PiTensorProduct.tprod ℂ fun v : T => u v := by
  let c : (∀ v : S, M v) → ∀ v : T, M v := fun x v => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v
  have key : ∀ [DecidableEq S] x (i : S) w, c (Function.update x i w) = Function.update (c x) ⟨i, h i.2⟩ w := fun x i w => by
    funext v
    by_cases hvi : v = ⟨i, h i.2⟩
    · subst hvi
      simp [c]
    · rw [Function.update_of_ne hvi]
      by_cases hv : (v : ι) ∈ S
      · simp only [c, dif_pos hv]
        exact Function.update_of_ne (fun e => hvi (Subtype.ext (by rw [← e]))) _ _
      · simp only [c, dif_neg hv]
  refine ⟨PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℂ (c x)
      map_update_add' := fun x i y y' => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i a y => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun v => ?_)
  by_cases hv : (v : ι) ∈ S
  · simp only [c, dif_pos hv]
  · simp only [c, dif_neg hv, hu v hv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}


variable (B G R Rf) in
def On (T : Finset (Pl F)) (Φ : Fn F a (a + a')) (Φ' : Fn F a' (a + a')) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem On.mono (hm : IsMatched B G X om om' R Rf) {S T : Finset (Pl F)} (h0 : X.T ⊆ S) (h : S ⊆ T) {Φ Φ'}
    (H : On B G R Rf S Φ Φ') : On B G R Rf T Φ Φ' := by
  obtain ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩ := H
  obtain ⟨e, he⟩ := exists_ext Rf.Pi h fun v => Rf.p v (G.M.vac v)
  refine ⟨m, m', f, φ, f', φ', fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (h k)⟩,
    fun i => ⟨(h2 i).1, (h2 i).2.1, fun v hv => (h2 i).2.2 v fun k => hv (h k)⟩, e1, e2, ?_⟩
  have := congrArg (e.lTensor R.Pi) e3
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
  · rw [he (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
  · rw [he (fun v => Rf.p' v (φ' i v)) fun v hv => by rw [(h2 i).2.2 v hv, (hm.fin.sph v fun k => hv (h0 k)).1]]

theorem pm_zero : PolMatch B G X R Rf 0 0 :=
  ⟨_, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp, by simp, by simp⟩

theorem pm_add (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (c : ℂ) (h1 : PolMatch B G X R Rf Φ Φ')
    (h2 : PolMatch B G X R Rf Ψ Ψ') : PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  obtain ⟨T₁, hT₁, H₁⟩ := h1
  obtain ⟨T₂, hT₂, H₂⟩ := h2
  obtain ⟨m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := On.mono hm hT₁ (Finset.subset_union_left (s₂ := T₂)) H₁
  obtain ⟨k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := On.mono hm hT₂ (Finset.subset_union_right (s₁ := T₁)) H₂
  refine ⟨T₁ ∪ T₂, hT₁.trans Finset.subset_union_left, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', fun i => ?_, fun i => ?_, funext fun x => ?_, funext fun x => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩
    · simp only [Fin.append_right]
      exact hg i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2⟩
    · simp only [Fin.append_right]
      exact hg' i
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, e1, e2]

theorem loc_op (hS : SplitModel) {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} {r s r' s' : ℕ}
    (p : IsPair B M χ χ' o r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ O : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), (∀ φ ∈ SB _, O φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (O φ)) ∧
      ∀ f (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) → (∀ᶠ u in cofinite, φ u = M.vac u) →
        o (1, h) (pure f φ) = pure f (Function.update φ v (O (φ v))) := by
  obtain ⟨-, ι, b, -, r1⟩ := hS F E σ B n d Y W M _ _ o _ _ _ _ p v t
  obtain ⟨j, -, j2⟩ := exists_inv' b
  let h₀ := Matrix.GeneralLinearGroup.map (piW t) h.1
  have k := fun φ hφ => acts_of_reads (r1 h hh h₀ rfl) j2 (φ := φ) hφ
  refine ⟨j ∘ₗ GlobalTheory.SplitFlip.repB (chrW χ' t) (chrW χ t) (1, h₀) ∘ₗ ι, k, fun f φ p1 p2 => ?_⟩
  obtain ⟨T, t1, -, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and p.good.std).mono fun _ h => h.1.trans h.2)
  have := t3 _ _ (p1 v) _ (k _ (p1 v)).2
  rwa [t1, t1, Function.update_eq_self] at this

theorem pm_fin (hS : SplitModel) (hm : IsMatched B G X om om' R Rf) {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') :
    PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  obtain ⟨T, hT, H⟩ := H
  obtain ⟨m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := On.mono hm hT (Finset.subset_insert v T) H
  obtain ⟨O, o1, o2⟩ := loc_op hS (pairV hm.triple) t hh
  obtain ⟨O', o1', o2'⟩ := loc_op hS (pairV' hm.triple) t hh
  obtain ⟨s, hs⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective
    ((LinearMap.range_domRestrict _ _).trans (hm.fin.onto v))
  let A : Module.End ℂ (Rf.Pi v) := Rf.p v ∘ₗ O ∘ₗ (SB _).subtype ∘ₗ s
  have q : ∀ x ∈ SB _, ∀ x' ∈ SB _, Rf.p v x = Rf.p' v x' → Rf.p v (O x) = Rf.p' v (O' x') := fun x hx x' hx' =>
    hm.fin.equiv v h hh x hx x' hx' _ (o1 x hx).1 _ (o1' x' hx').1 (o1 x hx).2 (o1' x' hx').2
  have A' : ∀ x' ∈ SB _, A (Rf.p' v x') = Rf.p' v (O' x') := fun x' hx' =>
    q _ (s _).2 x' hx' (LinearMap.congr_fun hs _)
  have A1 : ∀ x ∈ SB _, A (Rf.p v x) = Rf.p v (O x) := fun x hx => by
    obtain ⟨x', hx', k⟩ : Rf.p v x ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
    rw [q x hx x' hx' k.symm, ← k, A' x' hx']
  have up : ∀ {P : ∀ u : Pl F, Type} (Q : ∀ u, P u → Prop) (x : ∀ u, P u) (y : P v), Q v y → (∀ u ≠ v, Q u (x u)) →
      ∀ u, Q u (Function.update x v y u) := fun Q x y a b u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact b u hu
  have ne : ∀ u ∉ insert v T, u ≠ v := fun u hu k => hu (k ▸ Finset.mem_insert_self _ _)
  refine ⟨_, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (O (φ i v)), f',
    fun i => Function.update (φ' i) v (O' (φ' i v)), fun i => ⟨(h1 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1 _ ((h1 i).2.1 v)).1 fun u _ => (h1 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h1 i).2.2 u hu)⟩, fun i => ⟨(h2 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1' _ ((h2 i).2.1 v)).1 fun u _ => (h2 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h2 i).2.2 u hu)⟩, ?_, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => o2 _ _ (h1 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h1 i).2.2)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => o2' _ _ (h2 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h2 i).2.2)
  let D : ∀ u, Module.End ℂ (Rf.Pi u) := Function.update (fun _ => LinearMap.id) v A
  have := congrArg ((PiTensorProduct.map fun u : (insert v T : Finset _) => D u).lTensor R.Pi) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_)) <;> congr 2 <;> funext ⟨u, _⟩ <;>
    by_cases hu : u = v
  · subst hu; simp only [D, Function.update_self, A1 _ ((h1 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]
  · subst hu; simp only [D, Function.update_self, A' _ ((h2 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]

end GlobalTheory.ThK.Dbl.TC

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstAn
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

local instance borelU {J : Matrix (Fin n) (Fin n) E} : BorelSpace (UA σ J) := ⟨rfl⟩

local instance topU {J : Matrix (Fin n) (Fin n) E} : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

def Ker (θ : UA σ X.J → UA σ W.J → ℂ) : Prop :=
  Continuous (fun x : UA σ X.J × UA σ W.J => θ x.1 x.2) ∧
    (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, θ (γ * g) (γ' * h) = θ g h) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖θ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k

variable {θ : UA σ X.J → UA σ W.J → ℂ} {φ : UA σ W.J → ℂ} {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}

theorem Ker.bd (hθ : Ker θ) (hφ : IsRapid φ) : ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ g h, ‖φ h * star (θ g h)‖ ≤ K * (ht g : ℝ) ^ k := by
  obtain ⟨-, hi, C, k, hC⟩ := hθ
  obtain ⟨C', hC'⟩ := hφ.2.2 k
  have h0 : 0 ≤ C' := le_trans (by positivity) (hC' 1)
  refine ⟨|C| * C', k, by positivity, fun g h => ?_⟩
  have h1 : ‖θ g h‖ ≤ |C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
    have := Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => |C| * (ht g : ℝ) ^ k * (x : ℝ) ^ k)
      (g := fun γ : ratU σ W.J => ht (γ.1 * h)) (by fun_prop) (fun x y hxy => by
        have : (x : ℝ) ≤ y := hxy
        dsimp only; gcongr) (OrderBot.bddBelow _)
    refine le_of_le_of_eq (le_ciInf fun γ => ?_) this.symm
    rw [← hi 1 (one_mem _) γ.1 γ.2, one_mul, mul_assoc, ← mul_pow]
    exact (hC _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [norm_mul, norm_star]
  calc _ ≤ ‖φ h‖ * (|C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = |C| * (ht g : ℝ) ^ k * (‖φ h‖ * (qht h : ℝ) ^ k) := by ring
    _ ≤ |C| * (ht g : ℝ) ^ k * C' := mul_le_mul_of_nonneg_left (hC' h) (by positivity)
    _ = _ := by ring

theorem Ker.meas (hθ : Ker θ) (hφ : IsRapid φ) (g) : AEStronglyMeasurable (fun h => φ h * star (θ g h)) (μ.restrict D) :=
  (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable

theorem Ker.int (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) (g) : IntegrableOn (fun h => φ h * star (θ g h)) D μ := by
  obtain ⟨K, k, -, hK⟩ := hθ.bd hφ
  exact Measure.integrableOn_of_bounded hD.ne (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable
    (Eventually.of_forall (hK g))

theorem Ker.cont [LocallyCompactSpace (UA σ X.J)] [FirstCountableTopology (UA σ X.J)]
    (hb : ∀ Ω : Set (UA σ X.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C) (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) :
    Continuous fun g => pet μ D φ (θ g) := by
  obtain ⟨K, k, h0, hK⟩ := hθ.bd hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨C, hC⟩ := hb Ω hΩ
  refine continuousAt_of_dominated (bound := fun _ => K * (C : ℝ) ^ k) (Eventually.of_forall (hθ.meas hφ)) ?_
    (integrableOn_const hD.ne) (Eventually.of_forall fun h => ?_)
  · filter_upwards [hg] with x hx
    refine Eventually.of_forall fun h => (hK x h).trans ?_
    have : (ht x : ℝ) ≤ C := hC x hx
    gcongr
  · exact (continuous_const.mul (hθ.1.comp (Continuous.prodMk_left h)).star).continuousAt

theorem theta_act (om : Rep σ X W) (Ψ : Fn F n d) (u g : UA σ X.J) (h x : UA σ W.J) :
    theta om (om (u, h) Ψ) g x = theta om Ψ (g * u) (x * h) := by
  rw [theta, theta, ← Module.End.mul_apply, ← map_mul]; rfl

theorem theta_add {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (g h) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add (f := _)]
  exact thetaSum_add F (hp _ _ hΦ) (hp _ _ hΨ)

theorem theta_smul (om : Rep σ X W) (c : ℂ) (Φ : Fn F n d) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul, thetaSum_smul]

theorem exists_form {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _)
    (hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ)) (hD : μ D < ⊤) {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (P : Submodule ℂ Q) (C : Q →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ P, IsRapid (C Φ)) (g : UA σ X.J) :
    ∃ L : Q →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ, ∀ Φ ∈ P, ∀ Ψ ∈ schA F _, L Φ Ψ = th om μ D (C Φ) Ψ g := by
  obtain ⟨q, hq⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
  obtain ⟨q', hq'⟩ := (schA F (Fin n × Fin d)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have i := fun (a : Q) (b : Fn F n d) => (hk _ (q' b).2).int (hr _ (q a).2) hD g
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => th om μ D (C (q a)) (q' b) g) (fun a a' b => ?_)
    (fun c a b => ?_) (fun a b b' => ?_) fun c a b => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (i a b) (i a' b)
  · simp only [th, pet, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]
  · simp only [th, pet, map_add (f := _), Submodule.coe_add, theta_add hp (q' b).2 (q' b').2, star_add, mul_add]
    exact integral_add (i a b) (i a b')
  · simp only [th, pet, map_smul, Submodule.coe_smul, theta_smul, star_mul', smul_eq_mul, mul_left_comm _ (star c),
      integral_const_mul]
    rfl
  · have e : q Φ = ⟨Φ, hΦ⟩ := LinearMap.congr_fun hq ⟨Φ, hΦ⟩
    have e' : q' Ψ = ⟨Ψ, hΨ⟩ := LinearMap.congr_fun hq' ⟨Ψ, hΨ⟩
    change th om μ D (C (q Φ)) (q' Ψ) g = _
    rw [e, e']

theorem th_right [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable (ratU σ W.J)] (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    {om : Rep σ X W} {Ψ : Fn F n d} (hθ : Ker (theta om Ψ)) (hφ : IsRapid φ) (g h) :
    th om μ D (fun x => φ (x * h)) (om (1, h) Ψ) g = th om μ D φ Ψ g := by
  simp only [th, pet, theta_act, mul_one]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => φ x * star (theta om Ψ g x)) (fun γ hγ x => by
    rw [hφ.2.1 γ hγ, ← hθ.2.1 1 (one_mem _) γ hγ g x, one_mul]) h

theorem exists_fac {P A Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (f : P →ₗ[ℂ] A) (g : P →ₗ[ℂ] Z) (h : ∀ x, f x = 0 → g x = 0) : ∃ C : A →ₗ[ℂ] Z, ∀ x, C (f x) = g x := by
  obtain ⟨C, hC⟩ := ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨C, fun x => (LinearMap.congr_fun hC ⟨f x, x, rfl⟩).trans ?_⟩
  exact congrArg ((LinearMap.ker f).liftQ g h) (f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)

end GlobalTheory.ThK.Dbl.TC

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open PositivityTheory.ThKEst (GrpTop EpsOf FinVolU)
open PositivityTheory.ThKF (Unimod)
open PositivityTheory.KCo (SoSt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}

namespace TC

theorem chrW_div {v : Pl F} (χ χ' : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x :=
  map_div Circle.toUnits _ _

theorem chrW_norm {v : Pl F} (χ : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : ‖(chrW χ t x : ℂ)‖ = 1 := Circle.norm_coe _

theorem const_of (hL : LocDist) (hC : ConstOfGood) (hT : ThetaBasic) (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod)
    (hS : SplitModel) {B : Base F E} {X : Spc F E n} {X' : Spc F E n'} {W : Spc F E d} {M : Model σ X W} {M' : Model σ X' W}
    {om : Rep σ X W} {om' : Rep σ X' W} {χ χ' χ₂ : Chr F E} {r s r₁ s₁ r' s' : ℕ} (p : IsPair B M χ (χ / χ') om r s r' s')
    (p' : IsPair B M' χ' χ₂ om' r₁ s₁ r' s') (e : Fin n ⊕ Fin n' ≃ Fin d) (hn : 2 ≤ n) (T : Finset (Pl F))
    (hne : ∀ v ∉ T, SplitsFully E v → ∃ t : E →ₐ[F] Fv F v, chrW (χ / χ') t (unifAt v) ≠ 1)
    (C : Fn F n' d →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ PolData B M', IsRapid (C Φ))
    (he : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M', om' (1, h) Φ ∈ PolData B M' ∧ C (om' (1, h) Φ) = fun x => C Φ (x * h))
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) :
    ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, ∀ g, th om μ D (C Φ) Ψ g = th om μ D (C Φ) Ψ 1 := by
  classical
  letI := GlobalTheory.LocalData.complRel (F := F)
  letI := GlobalTheory.LocalData.isLocalField (F := F)
  have inv_loc (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) (hM' : M'.IsGood B.ψ) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
      {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
      {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
      (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
      (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
      {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
      (hne : ν (unifAt v) ≠ 1) (L : Fn F n' d →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
      (hh : ∀ h₀, ∃ h, PositivityTheory.KCo.Reads v ι (om (1, h)) (GlobalTheory.SplitFlip.omB ν α 1 h₀) ∧ PositivityTheory.KCo.Reads v ι' (om' (1, h)) (GlobalTheory.SplitFlip.omB ν' α' 1 h₀) ∧
        ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L (om' (1, h) Φ) (om (1, h) Ψ) = L Φ Ψ)
      {u g₀} (hu : PositivityTheory.KCo.Reads v ι (om (u, 1)) (GlobalTheory.SplitFlip.omB ν α g₀ 1)) : ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L Φ (om (u, 1) Ψ) = L Φ Ψ := by
    obtain ⟨j, j1, j2⟩ := exists_inv' b
    obtain ⟨j', j1', j2'⟩ := exists_inv' b'
    intro Φ hΦ Ψ hΨ
    refine LinearMap.eqOn_span' (f := L.flip (om (u, 1) Ψ)) (g := L.flip Ψ) ?_ hΦ
    rintro _ ⟨f', hf', φ', p1', p2', rfl⟩
    refine PositivityTheory.KCo.schA_le (LinearMap.eqLocus (L (pure f' φ') ∘ₛₗ om (u, 1)) (L (pure f' φ'))) (fun f φ p1 p2 => ?_) hΨ
    obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
    obtain ⟨T', t1', -, t3'⟩ := intersection_update_fsHerm_neg_one v f' p1' ((p2'.and hM'.std).mono fun _ h => h.1.trans h.2)
    have t2' : ∀ ψ ∈ SB _, T' ψ ∈ PolData B M' := fun ψ hψ => Submodule.subset_span ⟨f', hf', _, fun w => by
      by_cases hw : w = v
      · subst hw; rwa [Function.update_self]
      · rw [Function.update_of_ne hw]; exact p1' w, by
        filter_upwards [p2', eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h, t1' ψ⟩
    let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2), GlobalTheory.SplitFlip.apow_one _⟩, fun x y => GlobalTheory.SplitFlip.apow_mul x y _⟩
    have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (GlobalTheory.SplitFlip.apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
    have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
    have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (GlobalTheory.SplitFlip.apow x ((m : ℂ) / 2)) = GlobalTheory.SplitFlip.apow x ((m : ℂ) / 2) := fun x m => by
      obtain ⟨r, -, h⟩ := apow_real x m
      rw [h, Complex.conj_ofReal]
    let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun a b => L (T' (j' b.1)) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
        (fun _ _ _ => by simp) fun _ _ _ => by simp
    let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
    have key := locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
      ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 (p1' v)⟩ g₁
    · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
      rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
      change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
      rw [star_star, j2 _ (p1 v), j2' _ (p1' v), t1', t1 (φ v), Function.update_eq_self, Function.update_eq_self, hN,
        show Matrix.GeneralLinearGroup.det g₁ = GlobalTheory.SplitFlip.gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
      change L _ (om (u, 1) _) = _
      rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet g₀) ((d : ℂ) / 2)
      field_simp
    · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
      rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
      have := n1 (unifAt v)
      rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
      rw [h, this]; rfl
    · obtain ⟨h, r1, r2, r3⟩ := hh h₀
      have a1 := j1 _ (sb_star a.2)
      have b1 := j1' _ b.2
      have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
      have k2 := t3' _ _ b1.1 _ (acts_of_reads r2 j2' b1.1).2
      have k3 := r3 _ (t2' _ b1.1) _ (t2 _ a1.1)
      rw [k1, k2, a1.2, b1.2, omB_right, omB_right] at k3
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
      have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
        have := Fintype.card_congr e
        simp only [Fintype.card_sum, Fintype.card_fin] at this
        rw [← this]; push_cast; ring
      change L (T' (j' fun y => b.1 (y * h₀.1))) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (T' (j' b.1)) (T (j (star a.1)))
      rw [← k3, hN, hν, hd, GlobalTheory.SplitFlip.apow_add]
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet h₀) ((n : ℂ) / 2)
      have := GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet h₀) ((n' : ℂ) / 2)
      simp only [Units.val_div_eq_div_val]
      field_simp
  intro Φ hΦ Ψ hΨ
  have hB := p.base
  have eW := (h2 F E σ B hB d W r' s' (.inr p.skew)).1
  obtain ⟨a1, a2, -, -, -, -, -, a5⟩ := h1 F E σ hB.cm n X.J (h2 F E σ B hB n X r s (.inl p.herm)).1
  obtain ⟨u0, -, u2⟩ := h4 F E σ hB.cm d W.J (-1) (fun i j => by simp [p.skew.skew]) eW.2
  have := u2 μ hμ
  have : FirstCountableTopology (UA σ X.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have fin := h3 F E σ hB.cm d W.J eW μ D hμ hD
  have hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ) := (hT F E σ B n d X W M _ _ om _ _ _ _ p).1
  have hp := p.weil.isUSplitting.pres
  refine hC F E σ B n X r s hB p.herm hn T _ ((hk Ψ hΨ).cont a5 (hr Φ hΦ) fin) (fun γ hγ g => ?_) fun v hv hs u hu g => ?_
  · have : theta om Ψ (γ * g) = theta om Ψ g := funext fun h => by
      rw [← (hk Ψ hΨ).2.1 γ hγ 1 (one_mem _) g h, one_mul]
    rw [th, th, this]
  obtain ⟨t, ht⟩ := hne v hv hs
  obtain ⟨s1, ι, b, l1, r1⟩ := hS F E σ B n d X W M _ _ om _ _ _ _ p v t
  obtain ⟨-, ι', b', -, r2⟩ := hS F E σ B n' d X' W M' _ _ om' _ _ _ _ p' v t
  obtain ⟨L, hl⟩ := exists_form hp hk fin (PolData B M') C hr g
  obtain ⟨g₀, hg⟩ := l1 u hu
  have key := inv_loc hL e p'.good b b' (chrW_norm _ t) (chrW_norm _ t) (chrW_div χ χ' t) ht L (fun h₀ => by
    obtain ⟨h, hh, e0⟩ := s1 h₀
    refine ⟨h, r1 h hh h₀ e0, r2 h hh h₀ e0, fun Φ hΦ Ψ hΨ => ?_⟩
    rw [hl _ (he v t h hh Φ hΦ).1 _ (hp _ _ hΨ), hl _ hΦ _ hΨ, (he v t h hh Φ hΦ).2, th_right hD (hk Ψ hΨ) (hr Φ hΦ)]) hg Φ hΦ Ψ hΨ
  rw [hl _ hΦ _ (hp _ _ hΨ), hl _ hΦ _ hΨ] at key
  rw [← key, th, th]
  congr 1
  funext x
  rw [theta_act, mul_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem pol_mem {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', h1, h2, rfl, rfl, -⟩ := h
  exact ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f i, (h1 i).1, φ i, (h1 i).2.1, T.eventually_cofinite_notMem.mono (h1 i).2.2, rfl⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f' i, (h2 i).1, φ' i, (h2 i).2.1, T.eventually_cofinite_notMem.mono (h2 i).2.2, rfl⟩⟩

theorem pol_le {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact PositivityTheory.KCo.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem I_add {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W}
    (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), o x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (c1 : M.Conv o Φ) (c2 : M.Conv o Ψ) : M.I o (Φ + Ψ) = M.I o Φ + M.I o Ψ := funext fun h => by
  simp only [Model.I, theta_add hp hΦ hΨ]
  exact integral_add (c1 h) (c2 h)

theorem I_smul {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) :
    M.I o (c • Φ) = c • M.I o Φ := funext fun h => by
  simp only [Model.I, theta_smul, integral_const_mul, Pi.smul_apply, smul_eq_mul]

theorem I_zero {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) : M.I o 0 = 0 := by
  simpa using I_smul M o 0 0

def matched (hm : IsMatched B G X om om' R Rf) : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) where
  carrier := {y | PolMatch B G X R Rf y.1 y.2}
  zero_mem' := pm_zero
  add_mem' h h' := by simpa using pm_add hm 1 h h'
  smul_mem' c _ h := by simpa using pm_add hm c h pm_zero

theorem exists_maps (hD : KDecay) (hF : Factor) (hm : IsMatched B G X om om' R Rf) (s t : ℂ) :
    ∃ (C : Fn F a (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)) (C' : Fn F a' (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)),
      (∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y) ∧ ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → C' Φ' = C Φ := by
  obtain ⟨d1, d2⟩ := hD F E σ B a a' G X om om' hm.triple
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf hm
  let P := (G.M'.So B.ψ B.τ₁).comap (LinearMap.snd ℂ _ _) ⊓ matched hm
  have m1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM (pol_mem y.2.2).1
  have m2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM' (pol_mem y.2.2).2
  let c : P →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun y => comb G om om' s t y.1
      map_add' := fun y z => by
        simp only [comb, Submodule.coe_add, Prod.fst_add, Prod.snd_add]
        rw [I_add hm.triple.weil.isUSplitting.pres (m1 y) (m1 z) (d1 _ (m1 y)) (d1 _ (m1 z)),
          I_add hm.triple.weil'.isUSplitting.pres (m2 y) (m2 z) (d2 _ y.2.1).2.1 (d2 _ z.2.1).2.1]
        module
      map_smul' := fun x y => by
        simp only [comb, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, I_smul, RingHom.id_apply]
        module }
  obtain ⟨C, hC⟩ := exists_fac (LinearMap.fst ℂ _ _ ∘ₗ P.subtype) c fun y h => by
    have h0 : y.1.1 = 0 := h
    have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2.2
    change comb G om om' s t y.1 = 0
    rw [comb, f2 y.1.2 y.2.1 (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  have k : ∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y := fun y hy => hC ⟨y, hy⟩
  obtain ⟨C', hC'⟩ := exists_fac (LinearMap.snd ℂ _ _ ∘ₗ (matched hm).subtype) (C ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ (matched hm).subtype)
    fun y h => by
      have h0 : y.1.2 = 0 := h
      have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2
      change C y.1.1 = 0
      rw [k y.1 ⟨h0 ▸ zero_mem _, h1⟩, comb, f1 _ (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  exact ⟨C, C', k, fun Φ Φ' h => hC' ⟨(Φ, Φ'), h⟩⟩

end TC

open TC in
theorem thConst_of (hL : LocDist) (hG : GoodNe) (hC : ConstOfGood) (hF : Factor) (hM : MatchEx) (hT : ThetaBasic) (hD : KDecay)
    (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod) (hS : TC.SplitModel) (hO : SoSt) : ThConst := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm s t hr μ D hμ hD' y hy
  obtain ⟨C, C', c1, c2⟩ := exists_maps hD hF hm s t
  obtain ⟨m1, m2, -⟩ := hM F E σ B a a' G X om om' R Rf hm
  have hg := hG F E σ B a a' G X om om' hm.triple
  have r1 : ∀ Φ ∈ PolData B G.M, IsRapid (C Φ) := fun Φ hΦ => by
    obtain ⟨Φ', h, h'⟩ := m1 Φ hΦ
    exact c1 (Φ, Φ') ⟨h, h'⟩ ▸ hr (Φ, Φ') ⟨h, h'⟩
  have e1 : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ PolData B G.M,
      om (1, h) Φ ∈ PolData B G.M ∧ C (om (1, h) Φ) = fun x => C Φ (x * h) := fun v w h hh Φ hΦ => by
    obtain ⟨Φ', k, k'⟩ := m1 Φ hΦ
    have k2 := pm_fin hS hm w hh k'
    refine ⟨(pol_mem k2).1, ?_⟩
    rw [c1 (_, _) ⟨hO F E σ B a a' G X om om' hm.triple _ _ k, k2⟩, c1 (Φ, Φ') ⟨k, k'⟩]
    funext x
    simp only [comb, Model.I, Pi.add_apply, Pi.smul_apply, theta_act, mul_one]
  have l1 := hm.triple.geo.lt
  have l2 := hm.triple.geo.aBig
  rw [← c1 y hy]
  refine ⟨c2 _ _ hy.2 ▸ const_of hL hC hT h1 h2 h3 h4 hS (pairV hm.triple) (pairV' hm.triple) finSumFinEquiv (by omega) X.T
    (fun v hv hs => ?_) C' (fun Φ' h => ?_) (fun v w h hh Φ' hΦ => ?_) hμ hD' _ (pol_mem hy.2).2,
    const_of hL hC hT h1 h2 h3 h4 hS (pairV' hm.triple) (pairV hm.triple) ((Equiv.sumComm _ _).trans finSumFinEquiv) (by omega) X.T
    (fun v hv hs => ?_) C r1 e1 hμ hD' _ (pol_mem hy.2).1⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    refine ⟨t, fun h' => h t ?_⟩
    rw [chrW_div, div_eq_one] at h'
    rw [Chars.ν, chrW_div, h', div_self']
  · obtain ⟨Φ, k⟩ := m2 Φ' h
    exact c2 _ _ k ▸ r1 Φ (pol_mem k).1
  · obtain ⟨Φ, k⟩ := m2 Φ' hΦ
    have k2 := pm_fin hS hm w hh k
    exact ⟨(pol_mem k2).2, by rw [c2 _ _ k2, c2 _ _ k, (e1 v w h hh Φ (pol_mem k).1).2]⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    exact ⟨t, h t⟩

end GlobalTheory.ThK.Dbl

end
