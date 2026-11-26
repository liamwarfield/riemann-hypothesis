module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
public import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem exists_section {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] (p : A →ₗ[ℂ] P)
    (S : Submodule ℂ A) : ∃ s : P →ₗ[ℂ] A, (∀ y, s y ∈ S) ∧ ∀ x ∈ S, p (s (p x)) = p x := by
  let g := p.domRestrict S
  obtain ⟨t, ht⟩ := g.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict g)
  obtain ⟨q, hq⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨S.subtype ∘ₗ t ∘ₗ q, fun y => (t (q y)).2, fun x hx => ?_⟩
  have e : q (p x) = ⟨p x, ⟨x, hx⟩, rfl⟩ := LinearMap.congr_fun hq ⟨p x, ⟨x, hx⟩, rfl⟩
  have := congrArg Subtype.val (LinearMap.congr_fun ht ⟨p x, ⟨x, hx⟩, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, e]
  exact this

theorem ml_congr {ι : Type} [Fintype ι] {Y : ι → Type} [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] (l : MultilinearMap (RingHom.id ℂ) Y Z) (S K : ∀ v, Submodule ℂ (Y v))
    (h : ∀ ψ, (∀ v, ψ v ∈ S v) → (∃ v, ψ v ∈ K v) → l ψ = 0) (ψ ψ' : ∀ v, Y v) (hψ : ∀ v, ψ v ∈ S v) (hψ' : ∀ v, ψ' v ∈ S v)
    (hk : ∀ v, ψ v - ψ' v ∈ K v) : l ψ = l ψ' := by
  have e : ψ = (ψ - ψ') + ψ' := (sub_add_cancel _ _).symm
  rw [e, l.map_add_univ, Finset.sum_eq_single ∅, Finset.piecewise_empty]
  · intro s _ hs
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine h _ (fun u => ?_) ⟨v, by rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hk v⟩
    by_cases hu : u ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hu]; exact sub_mem (hψ u) (hψ' u)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hu]; exact hψ' u
  · exact fun h => absurd (Finset.mem_univ _) h

theorem desc {ι : Type} [Fintype ι] {A P Z : Type} {Y Q : ι → Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Z] [Module ℂ Z] [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (l : A →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) Y Z) (p : A →ₗ[ℂ] P) (q : ∀ v, Y v →ₗ[ℂ] Q v) (S₀ : Submodule ℂ A)
    (S : ∀ v, Submodule ℂ (Y v)) (h : ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) → (p f = 0 ∨ ∃ v, q v (ψ v) = 0) → l f ψ = 0) :
    ∃ L : P ⊗[ℂ] (PiTensorProduct ℂ Q) →ₗ[ℂ] Z, ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) →
      L (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v => q v (ψ v)) = l f ψ := by
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_section p S₀
  choose s hs hs' using fun v => exists_section (q v) (S v)
  refine ⟨TensorProduct.lift ((PiTensorProduct.lift (R := ℂ) (s := Q) (E := Z)).toLinearMap ∘ₗ
    (MultilinearMap.compLinearMapₗ s) ∘ₗ l ∘ₗ s₀), fun f hf ψ hψ => ?_⟩
  simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [ml_congr (l (s₀ (p f))) S (fun v => LinearMap.ker (q v)) (fun ψ h1 h2 => h _ (hs₀ _) ψ h1 (Or.inr h2)) _ ψ
    (fun v => hs v _) hψ (fun v => by rw [LinearMap.mem_ker, map_sub, hs' v _ (hψ v), sub_self])]
  have := h (s₀ (p f) - f) (sub_mem (hs₀ _) hf) ψ hψ (Or.inl (by rw [map_sub, hs₀' f hf, sub_self]))
  rwa [map_sub, MultilinearMap.sub_apply, sub_eq_zero] at this

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Std (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

theorem Std.congr {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (h : ∀ᶠ v in cofinite, φ v = w v) : Std φ := by
  filter_upwards [hw, h] with v h1 h2 using h2.trans h1

theorem ev_of_off {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ∀ᶠ v in cofinite, φ v = w v := by
  filter_upwards [T.eventually_cofinite_notMem] with v hv using h v hv

theorem tens_eq {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) :
    ∑ i, f i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ i v) =
      ∑ i, f' i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ' i v) := by
  let E := (Fintype.equivFin (ι ⊕ ι')).symm
  let c : ι ⊕ ι' → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  have := tensInj F κ w hne hw T _ (fun i => c (E i)) (fun i => Sum.elim f f' (E i)) (fun i => Sum.elim φ φ' (E i))
    (fun i => by rcases E i with j | j; exacts [h j, h' j])
    (by rw [E.sum_comp (fun j => c j • pure (Sum.elim f f' j) (Sum.elim φ φ' j)), Fintype.sum_sum_type]
        simp [c, e])
  rw [E.sum_comp (fun j => c j • Sum.elim f f' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Sum.elim φ φ' j v)),
    Fintype.sum_sum_type] at this
  simpa [c, ← sub_eq_add_neg, sub_eq_zero] using this

theorem tens_eq_map {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (p : SInf F κ →ₗ[ℂ] P) (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) :
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) =
      ∑ i, p (f' i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ' i v)) := by
  have := congrArg (TensorProduct.map p (PiTensorProduct.map fun v : T => q v)) (tens_eq hne hw T f φ f' φ' h h' e)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] using this

def ext (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ : ∀ v : T, (κ → Fv F v) → ℂ) (v : Pl F) :
    (κ → Fv F v) → ℂ := if h : v ∈ T then ψ ⟨v, h⟩ else w v

theorem ext_of {w φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ext w T (fun v => φ v) = φ := funext fun v => by
  unfold ext; split_ifs with hv
  exacts [rfl, (h v hv).symm]

theorem ext_off (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ) : ∀ v ∉ T, ext w T ψ v = w v :=
  fun _ hv => dif_neg hv

theorem pure_ext {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (f : SInf F κ) (ψ) (x : κ → AF F) :
    pure f (ext w T ψ) x = f (fun i => evI F (x i)) * ((∏ v : T, ψ v fun i => evFin F v (x i)) *
      ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  have hf := GlobalTheory.PureFactor.mulSupport_finite _ (hw.congr (ev_of_off (ext_off w T ψ))) x
  rw [← finprod_mem_univ, ← Set.union_compl_self (T : Set (Pl F)),
    finprod_mem_union' disjoint_compl_right (hf.inter_of_right _) (hf.inter_of_right _), finprod_mem_coe_finset,
    ← Finset.prod_coe_sort T]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by unfold ext; rw [dite_eq_left v.2]
  · exact finprod_congr fun v => finprod_congr fun hv => by rw [ext_off w T ψ v hv]

theorem exists_pureML {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) :
    ∃ l : SInf F κ →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) (fun v : T => (κ → Fv F v) → ℂ) ((κ → AF F) → ℂ),
      ∀ f ψ, l f ψ = pure f (ext w T ψ) := by
  let m : (κ → AF F) → MultilinearMap (RingHom.id ℂ) (fun v : T => (κ → Fv F v) → ℂ) ℂ := fun x =>
    (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v => LinearMap.proj fun i => evFin F v (x i)
  refine ⟨{ toFun := fun f => MultilinearMap.pi fun x =>
              (f (fun i => evI F (x i)) * ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) • m x
            map_add' := fun f g => ?_, map_smul' := fun a f => ?_ }, fun f ψ => ?_⟩
  · ext ψ x; simp [add_mul]
  · ext ψ x; simp [mul_assoc]
  · funext x
    rw [pure_ext hw]
    simp [m]; ring

theorem exists_factorOp (v : Pl F) (π : Module.End ℂ ((κ → Fv F v) → ℂ)) :
    ∃ O : Module.End ℂ ((κ → AF F) → ℂ), ∀ (f : SInf F κ) φ, Std φ → O (pure f φ) = pure f (Function.update φ v (π (φ v))) := by
  let sh : (κ → AF F) → (κ → Fv F v) → κ → AF F := fun x y i => x i + GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))
  refine ⟨{ toFun := fun Φ x => π (fun y => Φ (sh x y)) fun i => evFin F v (x i)
            map_add' := fun Φ Ψ => funext fun x => ?_, map_smul' := fun a Φ => funext fun x => ?_ }, fun f φ hφ => ?_⟩
  · exact congrFun (π.map_add (fun y => Φ (sh x y)) fun y => Ψ (sh x y)) _
  · exact congrFun (π.map_smul a fun y => Φ (sh x y)) _
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  have e : pure f φ = tens (evFin F v) (φ v) r := by rw [hr', Function.update_eq_self]
  rw [← hr', e]
  funext x
  have e2 : (fun y => tens (evFin F v) (φ v) r (sh x y)) = r x • φ v := by
    funext y
    have h1 : (fun i => evFin F v (sh x y i)) = y := funext fun i => by
      simp only [sh, map_add (f := _), GlobalTheory.EmbChart.evFin_atPlace, add_sub_cancel]
    have h2 : r (sh x y) = r x := hr x (fun i => GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))) fun u hu => by
      funext i
      show u * GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i)) = 0
      refine Prod.ext (mul_zero u.1) (af_ext fun w => ?_)
      show evalV F w (u.2 * singleFin v (y i - evFin F v (x i))) = evalV F w 0
      rw [map_mul, map_zero]
      by_cases h : w = v
      · subst h; rw [show evalV F w u.2 = 0 from hu, zero_mul]
      · rw [evalV_singleFin_ne h, mul_zero]
    simp only [tens, h1, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  change π (fun y => tens (evFin F v) (φ v) r (sh x y)) _ = _
  rw [e2, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_comm]

end PositivityTheory.ThKF

end
end

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.UpdSelf
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))

end PositivityTheory.ThKF

end
end

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem so_leK {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : M.So B.ψ B.τ₁ ≤ schA F _ :=
  Submodule.span_le.2 (by
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    rw [e]
    exact PositivityTheory.ThKG.pureA_mem f hg)

theorem clsV (hW : WeilConv) (hC : ICont) (hS : SqInt) (t : IsTriple B G X om om') : Cls B G.M om (schA F _) :=
  have p : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) := ⟨t.base, t.geo.hV, t.geo.hW, t.geo.hM, t.chars.heckeβ, PositivityTheory.ThKG.isHecke_div t.chars.heckeβ t.chars.heckeα, t.chars.resβ, PositivityTheory.ThKG.resEtaPow_div t.chars.resβ t.chars.resα, t.weil⟩
  have wc : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have := t.geo.eBig
    left
    omega
  have w := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p wc
  ⟨le_rfl, fun Φ h => (w.1 Φ h).1, (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 wc, fun ψ hψ _ => w.2 ψ hψ,
    fun μ 𝓕 h1 h2 Φ _ h => (hS F E σ B a a' G X om om' t μ 𝓕 h1 h2).1 Φ h⟩

theorem clsV' (hD : KDecay) (hK : KCoinv) (hc : SoCont) (hC : ICont) (hS : SqInt) (m : IsMatched B G X om om' R Rf) :
    Cls B G.M' om' (G.M'.So B.ψ B.τ₁) := by
  have p : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
    let t := m.triple
    exact ⟨t.base, t.geo.hV', t.geo.hW, t.geo.hM', t.chars.heckeα, PositivityTheory.ThKG.isHecke_div t.chars.heckeα t.chars.heckeβ, t.chars.resα, by rw [add_comm a a']; exact PositivityTheory.ThKG.resEtaPow_div t.chars.resα t.chars.resβ, t.weil'⟩
  refine ⟨so_leK p.good, fun Φ h => ((hD F E σ B a a' G X om om' m.triple).2 Φ h).2.1,
    (hC F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).2 (hK F E σ B a a' G X om om' R Rf m).2, fun ψ hψ hf h => ?_,
    fun μ 𝓕 h1 h2 Φ h' h => (hS F E σ B a a' G X om om' m.triple μ 𝓕 h1 h2).2 Φ ⟨h, h'⟩⟩
  refine SeqContinuous.continuous fun u f hu => ?_
  have := hc F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p 1 (fun _ => ψ) (fun _ => f) (fun k _ => u k) (fun _ => ⟨hψ, hu⟩)
    (fun k => by simpa using hf (u k)) (by simpa using hf f) h
  simp only [Finset.univ_unique, Finset.sum_singleton] at this
  exact this

theorem pure_soK (m : IsTriple B G X om om') (f : SInf F _) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = G.M'.vac u)
    {x} (hx : x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁)) : pure f (upd φ B.v₁ x) ∈ G.M'.So B.ψ B.τ₁ := by
  have p : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
    let t := m
    exact ⟨t.base, t.geo.hV', t.geo.hW, t.geo.hM', t.chars.heckeα, PositivityTheory.ThKG.isHecke_div t.chars.heckeα t.chars.heckeβ, t.chars.resα, by rw [add_comm a a']; exact PositivityTheory.ThKG.resEtaPow_div t.chars.resα t.chars.resβ, t.weil'⟩
  obtain ⟨j, hj, -⟩ := intersection_update_fsHerm_neg_one pureAct p f h1 h2 B.v₁
  rw [← hj]
  refine (Submodule.span_le (p := (G.M'.So B.ψ B.τ₁).comap j)).2 (fun y hy => ?_) hx
  show j y ∈ G.M'.So B.ψ B.τ₁
  rw [hj]
  exact Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 _ _, by rwa [upd_self], rfl⟩

theorem kills0_of (hT : ThetaBasic) (hW : WeilConv) (hK : KCoinv) (h : Kills) : PositivityTheory.ThKG.Loc.Kills0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m q0 f hf φ h1 h2 h3
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
    let t := m.triple
    exact ⟨t.base, t.geo.hV', t.geo.hW, t.geo.hM', t.chars.heckeα, PositivityTheory.ThKG.isHecke_div t.chars.heckeα t.chars.heckeβ, t.chars.resα, by rw [add_comm a a']; exact PositivityTheory.ThKG.resEtaPow_div t.chars.resα t.chars.resβ, t.weil'⟩
  have cv := fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p2 (Or.inr (by simp [q0]))).1 Φ hΦ).1
  obtain ⟨-, k2, k3, -⟩ := (hK F E σ B a a' G X om om' R Rf m).1 _ m.triple.chars.good
  obtain ⟨x, hx, e⟩ := k3 B.τ₁ (Rf.p' _ (φ B.v₁))
  have ha : φ B.v₁ - x ∈ augAt om' B.v₁ := (k2 _ (sub_mem (h1 _) hx.1)).1 (by rw [map_sub, e, sub_self])
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one pureAct p2 f h1 h2 B.v₁
  have js : ∀ y ∈ SB _, j y ∈ schA F _ := fun y hy => by
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA p2.good _ (upd_sb h1 hy) (upd_cof h2 B.v₁ y)
    rw [hj, e]
    exact PositivityTheory.ThKG.pureA_mem f hg
  have add : ∀ y ∈ SB _, ∀ z ∈ SB _, G.M'.I om' (j (y + z)) = G.M'.I om' (j y) + G.M'.I om' (j z) := fun y hy z hz =>
    funext fun g => by rw [map_add (f := _)]; exact PositivityTheory.ThKG.I_add p2.weil cv (js y hy) (js z hz) g
  have key : ∀ z ∈ augAt om' B.v₁, G.M'.I om' (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e2 := add _ (sub_mem hy hx) _ hx
      rw [sub_add_cancel, ← hjS _ x hx y hxy, I_left unimodularity_holds hT p2 (js x hx)] at e2
      exact left_eq_add.1 (e2.trans (add_comm _ _))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero _ _
    | add a b ha hb iha ihb => rw [add a (augAt_le _ ha) b (augAt_le _ hb), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  have e3 := add _ (augAt_le _ ha) x hx.1
  rw [sub_add_cancel, key _ ha, zero_add, hj, hj, upd_eq] at e3
  rw [e3]
  refine (h F E σ B a a' G X om om' R Rf m).2 f hf _ (upd_sb h1 hx.1) (upd_cof h2 _ _)
    (by rw [upd_self]; exact Submodule.subset_span hx) (h3.imp id fun ⟨v, hv⟩ => ⟨v, ?_⟩)
  by_cases ev : v = B.v₁
  · subst ev; rw [upd_self, e, hv]
  · rwa [upd_ne _ _ _ ev]

end PositivityTheory.ThKF

end
end
