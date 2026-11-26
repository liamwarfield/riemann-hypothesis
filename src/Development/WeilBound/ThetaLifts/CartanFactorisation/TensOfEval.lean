module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem eval_basis {Y : Type} [Nonempty Y] {m : ℕ} (φ : Fin m → Y → ℂ) :
    ∃ (s : Finset Y) (e : Y → Y → ℂ), ∀ i, φ i = ∑ j ∈ s, φ i j • e j := by
  let w : Y → Fin m → ℂ := fun y i => φ i y
  have hfg : (Submodule.span ℂ (Set.range w)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hs'' : ∀ x, x ∈ s' → ∃ y, w y = x := fun x hx => hs' (Finset.mem_coe.2 hx)
  choose! p hp using hs''
  have h : ∀ y, ∃ c : (Fin m → ℂ) → ℂ, ∑ x ∈ s', c x • x = w y := fun y => by
    have : w y ∈ Submodule.span ℂ (s' : Set (Fin m → ℂ)) := hsp ▸ Submodule.subset_span ⟨y, rfl⟩
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 this
    exact ⟨c, hc⟩
  choose c hc using h
  refine ⟨s'.image p, fun j y => c y (w j), fun i => ?_⟩
  funext y
  rw [Finset.sum_image (fun a ha b hb hab => by rw [← hp a ha, ← hp b hb, hab])]
  have := congrFun (hc y) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  change w y i = _
  rw [← this]
  refine Finset.sum_congr rfl fun x hx => ?_
  change _ = w (p x) i * _
  rw [hp x hx, mul_comm]

theorem tens_of_eval {ι : Type} [Fintype ι] {Y : ι → Type} [∀ v, Nonempty (Y v)] {A : Type} [AddCommGroup A] [Module ℂ A] {m : ℕ}
    (c : Fin m → ℂ) (a : Fin m → A) (φ : Fin m → ∀ v, Y v → ℂ)
    (h : ∀ y : ∀ v, Y v, ∑ i, (c i * ∏ v, φ i v (y v)) • a i = 0) :
    ∑ i, c i • a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v => φ i v) = 0 := by
  choose s e he using fun v => eval_basis (fun i => φ i v)
  have h1 : ∀ i, (PiTensorProduct.tprod ℂ fun v => φ i v) =
      ∑ J ∈ Fintype.piFinset s, (∏ v, φ i v (J v)) • PiTensorProduct.tprod ℂ fun v => e v (J v) := fun i => by
    conv_lhs => rw [show (fun v => φ i v) = fun v => ∑ j ∈ s v, φ i v j • e v j from funext fun v => he v i]
    rw [MultilinearMap.map_sum_finset]
    exact Finset.sum_congr rfl fun J _ => MultilinearMap.map_smul_univ _ _ _
  simp only [h1, TensorProduct.tmul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun J _ => ?_
  have := congrArg (· ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v => e v (J v))) (h J)
  simp only [TensorProduct.sum_tmul, TensorProduct.zero_tmul] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_smul, smul_smul, TensorProduct.smul_tmul']

theorem tensInj : TensInj := by
  intro F _ _ κ _ vac hne hstd T m c f φ hφ hsum
  choose b hb using fun v => Function.ne_iff.1 (hne v)
  let s : Finset (Pl F) := (Filter.eventually_cofinite.1 hstd).toFinset \ T
  refine tens_of_eval c f (fun i (v : T) => φ i v) fun y => ?_
  ext z
  let pt : ∀ v : Pl F, κ → Fv F v := fun v => if h : v ∈ T then y ⟨v, h⟩ else b v
  let x : κ → AF F := fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z k), ∑ v ∈ T ∪ s, singleFin v (pt v k))
  have hx : ∀ u k, evFin F u (x k) = if u ∈ T ∪ s then pt u k else 0 := fun u k => by
    change evalV F u (∑ v ∈ T ∪ s, singleFin v (pt v k)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
        evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun h : u = v => hu (h ▸ hv)) _
  have hI : (fun k => evI F (x k)) = z := funext fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have hd : Disjoint T s := Finset.disjoint_sdiff
  have hp : ∀ i, (∏ᶠ v, φ i v fun k => evFin F v (x k)) = (∏ v : T, φ i v (y v)) * ∏ v ∈ s, vac v (b v) := fun i => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := T ∪ s), Finset.prod_union hd, ← Finset.prod_coe_sort T]
    · congr 1
      · refine Finset.prod_congr rfl fun v _ => ?_
        congr 1; funext k
        rw [hx, if_pos (Finset.mem_union_left _ v.2)]
        simp only [pt, dif_pos v.2]
      · refine Finset.prod_congr rfl fun v hv => ?_
        have hT : v ∉ T := (Finset.mem_sdiff.1 hv).2
        rw [hφ i v hT]
        congr 1; funext k
        rw [hx, if_pos (Finset.mem_union_right _ hv)]
        simp only [pt, dif_neg hT]
    · intro v hv
      by_contra hn
      have hn' : v ∉ T ∪ s := fun h => hn (Finset.mem_coe.2 h)
      have hT : v ∉ T := fun h => hn' (Finset.mem_union_left _ h)
      have hs : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hn' (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Set.Finite.mem_toFinset _).2 h, hT⟩))
      apply hv
      simp only [hφ i v hT, hs, hx, if_neg hn']
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  have h0 := congrFun hsum x
  have hC : ∏ v ∈ s, vac v (b v) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hb v
  simp only [Finset.sum_apply, Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI, hp, smul_eq_mul, Pi.zero_apply] at h0
  have e : (∑ i, (c i * ∏ v : T, φ i v (y v)) • f i) z = ∑ i, (c i * ∏ v : T, φ i v (y v)) * f i z := by
    rw [SchwartzMap.sum_apply]; rfl
  rw [e]
  apply mul_right_cancel₀ hC
  rw [Finset.sum_mul, SchwartzMap.zero_apply, zero_mul, ← h0]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem pureAct : PureAct := by
  intro F _ _ κ _ v S f φ hSB hstd
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  refine ⟨⟨fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩,
    fun _ => rfl⟩, fun φ₁ φ₂ a => ?_, fun φ₁ h => ?_⟩
  · rw [← hr', ← hr', ← hr']
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e : tens (evFin F v) (φ v) r = pure f φ := by rw [hr', Function.update_eq_self]
    rw [← hr', ← e]
    exact h r ⟨hr, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩

end PositivityTheory.ThKF

end
end

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.RinfZero
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem absMax {Q Q' P ι : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup P] [Module ℂ P]
    {p : Q →ₗ[ℂ] P} {p' : Q' →ₗ[ℂ] P} {S : Submodule ℂ Q} {S' : Submodule ℂ Q'} {R : ι → Q → Q → Prop} {R' : ι → Q' → Q' → Prop}
    (on : S.map p = ⊤) (on' : S'.map p' = ⊤) (ex : ∀ i, ∀ x ∈ S, ∃ y, R i x y) (ex' : ∀ i, ∀ x ∈ S', ∃ y, R' i x y)
    (z : ∀ i, R i 0 0) (z' : ∀ i, R' i 0 0)
    (eqv : ∀ i, ∀ x ∈ S, ∀ x' ∈ S', ∀ y y', R i x y → R' i x' y' → p x = p' x' → p y = p' y')
    (irr : ∀ N : Submodule ℂ P, (∀ i, ∀ x ∈ S, ∀ y, R i x y → p x ∈ N → p y ∈ N) → N = ⊥ ∨ N = ⊤) :
    ((∀ i, ∀ x ∈ S, ∀ y, R i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ S, (∀ i, ∀ x ∈ N, ∀ y, R i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) ∧
    (∀ i, ∀ x ∈ S', ∀ y, R' i x y → p' x = 0 → p' y = 0) ∧
      ∀ N ≤ S', (∀ i, ∀ x ∈ N, ∀ y, R' i x y → y ∈ N) → N.map p' = ⊥ ∨ N.map p' = ⊤ := by
  refine ⟨⟨fun i x hx y h h0 => by simpa using eqv i x hx 0 S'.zero_mem y 0 h (z' i) (by simpa using h0), fun N hN hs => irr _ ?_⟩,
    fun i x hx y h h0 => by simpa using (eqv i 0 S.zero_mem x hx 0 y (z i) h (by simpa using h0.symm)).symm,
    fun N hN hs => irr _ ?_⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨x', hx', e'⟩ : p x ∈ S'.map p' := on' ▸ Submodule.mem_top
    obtain ⟨y', hy'⟩ := ex' i x' hx'
    obtain ⟨w₁, hw₁⟩ := ex i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁,
      (eqv i w (hN hw) x' hx' w₁ y' hw₁ hy' (e.trans e'.symm)).trans (eqv i x hx x' hx' y y' h hy' e'.symm).symm⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨w₁, hw₁⟩ := ex' i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁, (eqv i x hx w (hN hw) y w₁ h hw₁ e.symm).symm⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem acts_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 :=
  fun r _ => by
    have : tens ev 0 r = 0 := funext fun x => by simp [tens]
    rw [this, map_zero]

theorem actsD_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD ev (fun t => T t) 0 0 := fun r _ x => by
  have : tens ev 0 r = 0 := funext fun x => by simp [tens]
  simp only [this, map_zero]
  exact hasDerivAt_const _ _

theorem augAt_le (v : Pl F) : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, x, hx, y, hy, -, rfl⟩
  exact sub_mem hy hx)

theorem one_at' {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev :=
  fun u _ => by simp [mat]

theorem ex_fin (hp : IsPair B M χX χW om r s r' s') (v : Pl F) (h : UAt σ W (evFin F v)) :
    ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∃ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, h.1)) x y := fun x hx => by
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  exact ⟨_, hω.pres 1 (one_at' _) h h.2 x hx, (hω.acts 1 (one_at' _) h h.2 x hx _).2 rfl⟩

def RInf (B : Base F E) (om : Rep σ X W) : Lines σ W ⊕ KInf σ W B.emb → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d) → Prop
  | .inl γ, f, g => ActsD (evI F) (fun t => om (1, γ.1 (Multiplicative.ofAdd t))) f g
  | .inr k, f, g => Acts (evI F) (om (1, k.1)) f g

theorem kinf_one {m : ℕ} {Y : Spc F E m} (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ :=
  ⟨one_at' _, fun w => by
    have : (mat (1 : UA σ Y.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _⟩

theorem pol_lie (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {γ δ} (hγ : γ ∈ Lines σ X)
    (hδ : δ ∈ Lines σ W) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) f g' ↔ g' = g := by
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨g, h1, h2, -⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ (fun t => op _ (hγ.2 _) _ (hδ.2 _))
    (fun t => hop _ _ _ _) f hf
  exact ⟨g, h1, fun g' => ⟨fun h => (hQ F _ f g' g).2 _ h h2, fun h => h ▸ h2⟩⟩

theorem pol_k (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {k k'} (hk : k ∈ KInf σ X B.emb)
    (hk' : k' ∈ KInf σ W B.emb) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _, Acts (evI F) (om (k, k')) f g' ↔ g' = g := by
  obtain ⟨T, h1, h2⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp k hk.1 k' hk'.1
  exact ⟨T f, h2 hk hk' f hf, fun g' => ⟨fun h => (hQ F _ f g' _).1 _ h (h1.2 f), fun h => h ▸ h1.2 f⟩⟩

theorem rinf_ex (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) {f}
    (hf : f ∈ M.Pol B.ψ B.emb) : ∃ g ∈ M.Pol B.ψ B.emb, ∀ g', RInf B om i f g' ↔ g' = g := by
  rcases i with γ | k
  · exact pol_lie hO hL hQ hp (γ := 1) ⟨continuous_const, fun _ => one_at' _⟩ γ.2 hf
  · exact pol_k hO hQ hp (kinf_one _) k.2 hf

theorem rinf_zero (i) : RInf B om i 0 0 := by
  rcases i with γ | k
  · exact actsD_zero _ fun t => om (1, γ.1 (Multiplicative.ofAdd t))
  · exact acts_zero _ _

theorem max_fin {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P] {v : Pl F} {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P}
    (on : (SB _).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (h : (∀ i : UAt σ W (evFin F v), ∀ x ∈ SB _, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ SB _, (∀ i : UAt σ W (evFin F v), ∀ x ∈ N, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → y ∈ N) →
        N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker p ⊓ SB _) :=
  maximal_of p _ _ on (fun _ h => h.2.1)
    ⟨le_inf inv (augAt_le v), inf_le_right, fun g hg x hx y hy e => ⟨h.1 ⟨g, hg⟩ x hx.2 y ⟨hy, e⟩ hx.1, hy⟩⟩
    fun N hN => h.2 N hN.2.1 fun i x hx y hy => hN.2.2 i i.2 x hx y hy.1 hy.2

theorem max_inf (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {P : Type} [AddCommGroup P]
    [Module ℂ P] [Nontrivial P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p)
    (h : (∀ i, ∀ x ∈ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ M.Pol B.ψ B.emb, (∀ i, ∀ x ∈ N, ∀ y, RInf B om i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P ∧ P ≠ M.Pol B.ψ B.emb) (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  have st : ∀ i, ∀ x ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
    fun i x hx y hy => by
      obtain ⟨g, hg, e⟩ := rinf_ex hO hL hQ hp i hx.2
      exact ⟨h.1 i x hx.2 y hy hx.1, (e y).1 hy ▸ hg⟩
  refine maximal_of p _ _ q.onto (fun _ h => h.1) ⟨inf_le_right, fun γ hγ f hf y hy => ⟨q.lie γ hγ f hf y hy, ?_⟩,
    fun k hk f hf y hy => ⟨show p (y - f) = 0 by rw [map_sub, q.cpt k hk f hf y hy, sub_self], ?_⟩,
    fun γ hγ f hf y hy => st (.inl ⟨γ, hγ⟩) f hf y hy, fun k hk f hf y hy => st (.inr ⟨k, hk⟩) f hf y hy⟩
    fun N hN => h.2 N hN.1 ?_
  · obtain ⟨g, hg, e⟩ := pol_lie hO hL hQ hp hγ (δ := 1) ⟨continuous_const, fun _ => one_at' _⟩ hf
    exact (e y).1 hy ▸ hg
  · obtain ⟨g, hg, e⟩ := pol_k hO hQ hp hk (kinf_one _) hf
    exact sub_mem ((e y).1 hy ▸ hg) hf
  · rintro (γ | k) x hx y hy
    exacts [hN.2.2.2.1 γ γ.2 x hx y hy, hN.2.2.2.2 k k.2 x hx y hy]

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem maxFinP (m : IsMatched B G X om om' R Rf) (v : Pl F) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p v) ⊓ SB _) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p' v) ⊓ SB _) := by
  haveI := m.fin.nontriv v
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n k l : ℕ}
      (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' k) (e : l = n + k) : ResEtaPow K (χ / χ') l := by
    intro x
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have p1 : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV, m.triple.geo.hW, m.triple.geo.hM, m.triple.chars.heckeβ,
      hecke_div m.triple.chars.heckeβ m.triple.chars.heckeα, m.triple.chars.resβ,
      res_div m.triple.chars.resβ m.triple.chars.resα rfl, m.triple.weil⟩
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV', m.triple.geo.hW, m.triple.geo.hM', m.triple.chars.heckeα,
      hecke_div m.triple.chars.heckeα m.triple.chars.heckeβ, m.triple.chars.resα,
      res_div m.triple.chars.resα m.triple.chars.resβ (add_comm _ _), m.triple.weil'⟩
  have := absMax (R := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y)
    (R' := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om' (1, i.1)) x y) (m.fin.onto v) (m.fin.onto' v)
    (ex_fin p1 v) (ex_fin p2 v)
    (fun _ => ⟨zero_mem _, acts_zero _ _⟩) (fun _ => ⟨zero_mem _, acts_zero _ _⟩)
    (fun i x hx x' hx' y y' h h' => m.fin.equiv v i i.2 x hx x' hx' y h.1 y' h'.1 h.2 h'.2)
    fun N hN => m.fin.irred v N fun h hh x hx y hy e => hN ⟨h, hh⟩ x hx y ⟨hy, e⟩
  exact ⟨max_fin (m.fin.onto v) (m.fin.inv v) this.1, max_fin (m.fin.onto' v) (m.fin.inv' v) this.2⟩

theorem maxInfP (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (m : IsMatched B G X om om' R Rf) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P ∧ P ≠ G.M.Pol B.ψ B.emb)
        (LinearMap.ker R.p ⊓ G.M.Pol B.ψ B.emb) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' P ∧ P ≠ G.M'.Pol B.ψ B.emb)
        (LinearMap.ker R.p' ⊓ G.M'.Pol B.ψ B.emb) := by
  haveI := m.real.nontriv
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n k l : ℕ}
      (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' k) (e : l = n + k) : ResEtaPow K (χ / χ') l := by
    intro x
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have p1 : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV, m.triple.geo.hW, m.triple.geo.hM, m.triple.chars.heckeβ,
      hecke_div m.triple.chars.heckeβ m.triple.chars.heckeα, m.triple.chars.resβ,
      res_div m.triple.chars.resβ m.triple.chars.resα rfl, m.triple.weil⟩
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV', m.triple.geo.hW, m.triple.geo.hM', m.triple.chars.heckeα,
      hecke_div m.triple.chars.heckeα m.triple.chars.heckeβ, m.triple.chars.resα,
      res_div m.triple.chars.resα m.triple.chars.resβ (add_comm _ _), m.triple.weil'⟩
  have := absMax (R := RInf B om) (R' := RInf B om') m.real.quot.onto m.real.quot'.onto
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p1 i hx; ⟨g, (e g).2 rfl⟩)
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p2 i hx; ⟨g, (e g).2 rfl⟩) rinf_zero rinf_zero
    (by
      rintro (γ | k) x hx x' hx' y y' h h'
      exacts [m.real.lie γ γ.2 x hx x' hx' y y' h h', m.real.cpt k k.2 x hx x' hx' y y' h h'])
    fun N hN => m.real.irred N (fun γ hγ => hN (.inl ⟨γ, hγ⟩)) fun k hk => hN (.inr ⟨k, hk⟩)
  exact ⟨max_inf hO hL hQ p1 m.real.quot this.1, max_inf hO hL hQ p2 m.real.quot' this.2⟩

end PositivityTheory.ThKF

end
end
