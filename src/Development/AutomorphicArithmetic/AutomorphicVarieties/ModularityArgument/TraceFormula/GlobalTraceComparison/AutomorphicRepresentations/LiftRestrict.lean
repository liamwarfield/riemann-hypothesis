module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LiftRestrict
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F

private theorem lift_lift {J₀ J A : Type} [Ring A] [Algebra ℂ A] (v : J₀ → J) (e : J → A)
    (p : FreeAlgebra ℂ J₀) :
    FreeAlgebra.lift ℂ e (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j)) p) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) p := by
  have h : (FreeAlgebra.lift ℂ e).comp (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j))) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) := by
    apply FreeAlgebra.hom_ext
    funext j
    simp
  exact DFunLike.congr_fun h p

private theorem lift_restrict {V J : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : J → Module.End ℂ V) (r : J → Module.End ℂ P) (h : ∀ j (x : P), ((r j x : P) : V) = e j x)
    (p : FreeAlgebra ℂ J) : ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x := by
  refine FreeAlgebra.induction ℂ J (motive := fun p => ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x)
    ?_ ?_ ?_ ?_ p
  · intro c x
    simp [AlgHom.commutes, Module.algebraMap_end_apply]
  · intro j x
    simpa using h j x
  · intro a b ha hb x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  · intro a b ha hb x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]

private theorem list_restrict {V ι : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : ι → Module.End ℂ V) (r : ι → Module.End ℂ P) (h : ∀ i (x : P), ((r i x : P) : V) = e i x)
    (l : List ι) : ∀ x : P, (((l.map r).prod x : P) : V) = (l.map e).prod x := by
  induction l with
  | nil => intro x; rfl
  | cons a l ih =>
    intro x
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

private theorem simple_of {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (W : Submodule ℂ P)
    (h : W.map P.subtype = ⊥ ∨ W.map P.subtype = P) : W = ⊥ ∨ W = ⊤ := by
  have inj := Submodule.map_injective_of_injective P.injective_subtype
  rcases h with h | h
  · left
    exact inj (by rw [h, Submodule.map_bot])
  · right
    exact inj (by rw [h, Submodule.map_subtype_top])

private theorem comm_res {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (u v : Module.End ℂ P)
    (u' v' : Module.End ℂ V) (hu : ∀ x : P, ((u x : P) : V) = u' x) (hv : ∀ x : P, ((v x : P) : V) = v' x)
    (h : Commute u' v') : Commute u v := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((u (v x) : P) : V) = ((v (u x) : P) : V)
  rw [hu, hv, hv, hu]
  exact LinearMap.congr_fun h.eq (x : V)

private theorem prod_reorder {ι A : Type} [Monoid A] (Z : Finset ι) (c : ι × Bool → A)
    (hc : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k → Commute (c i) (c k)) :
    ((Z ×ˢ (Finset.univ : Finset Bool)).toList.map c).prod =
      ((Finset.univ : Finset Z).toList.map fun w => c (w.1, false) * c (w.1, true)).prod := by
  classical
  have step : ∀ l : List Z, ((l.flatMap fun w => [(w.1, false), (w.1, true)]).map c).prod =
      (l.map fun w => c (w.1, false) * c (w.1, true)).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons, List.prod_cons, mul_assoc]
      rw [ih]
  have hnd : ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]).Nodup := by
    refine List.nodup_flatMap.2 ⟨fun w _ => by simp, ?_⟩
    refine (Finset.nodup_toList _).imp_of_mem ?_
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_left]
    intro x hx hx'
    apply hab
    apply Subtype.ext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simpa using h
  have hperm : (Z ×ˢ (Finset.univ : Finset Bool)).toList.Perm
      ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnd).2 ?_
    rintro ⟨w, b⟩
    simp only [Finset.mem_toList, Finset.mem_product, Finset.mem_univ, and_true, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro hw
      refine ⟨⟨w, hw⟩, trivial, ?_⟩
      cases b <;> simp
    · rintro ⟨a, -, h⟩
      have hw : w = a.1 := by
        rcases h with h | h <;> exact (Prod.ext_iff.1 h).1
      rw [hw]
      exact a.2
  rw [← step]
  refine List.Perm.prod_eq' (hperm.map c) ?_
  rw [List.pairwise_map]
  refine (Finset.nodup_toList _).imp_of_mem ?_
  intro a b ha hb hab
  exact hc a (Finset.mem_toList.1 ha) b (Finset.mem_toList.1 hb) hab

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → PfHecke → ProdOp → LocComm → YLoc → ZSimple → YSwap → Isot → SimpleFix → AbsCore → ZTr := by
  intro hAdm hPf hPO hLC hYL hZS hYS hIs hSF hAC E _ _ _ n S Z N hS hZ hG π y τ hτ
  have hNo : ∀ w, IsOpen (N w : Set (GLw n w)) := fun w => (hG w).1
  have hNl : ∀ w, N w ≤ KGL w (n := n) := fun w => (hG w).2.1
  have hSl : ∀ w ∈ Z, ∀ b, Sl S (w, b) := fun w hw b => ⟨(hZ w hw).1, fun _ => (hZ w hw).2⟩
  have hZero : ∀ w, IsHecke (N w) (0 : GLw n w → ℂ) := fun w => ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hLoc := hLC E n S Z N hS hZ hG
  have hfixY : ∀ w ∈ Z, ∀ b, ∀ x ∈ y.Y, x ∈ fixed (rw' n w b) (N w) := fun w hw b x hx =>
    ((hLoc (w, b) (hSl w hw b) 0 (hZero w)).1 x (y.fix hx)).1
  have part1 : ∀ w ∈ Z, fixed (τ w).ρ (N w) ≠ ⊥ := by
    intro w hw hbot
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot y.ne
    apply hx0
    have := hIs E n π w (τ w) (hτ w hw) (N w) (hNo w) (hNl w) 1 (fun v hv => by
      rw [hbot, Submodule.mem_bot] at hv
      simp [hv]) x (y.le hx) (hfixY w hw false x hx)
    simpa using this
  haveI : FiniteDimensional ℂ y.Y := y.fd
  haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
  haveI : ∀ w : ↥Z, FiniteDimensional ℂ (fixed (τ w.1).ρ (N w.1)) := fun w =>
    hAdm E n w.1 (τ w.1) (N w.1) (hNo _)
  have hαinv : ∀ (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ fixed (τ w.1).ρ (N w.1),
      Lv (τ w.1).ρ (N w.1) f.1 x ∈ fixed (τ w.1).ρ (N w.1) := fun w f x hx =>
    (hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).1 f.1 f.2 x hx
  have hYinv : ∀ (b : Bool) (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ y.Y,
      Lw N w.1 b f.1 x ∈ y.Y := fun b w f x hx =>
    hYL E n S Z N hS hZ hG π y (w.1, b) (hSl w.1 w.2 b) f.1 f.2 x hx
  let α : ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ (fixed (τ w.1).ρ (N w.1)) :=
    fun w f => (Lv (τ w.1).ρ (N w.1) f.1).restrict (hαinv w f)
  let c : Bool → ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ y.Y :=
    fun b w f => (Lw N w.1 b f.1).restrict (hYinv b w f)
  have h1 : ∀ (i : ↥Z) (W : Submodule ℂ (fixed (τ i.1).ρ (N i.1))), (∀ f, ∀ x ∈ W, α i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro w W hW
    refine simple_of _ W ((hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).2 (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    exact Submodule.mem_map.2 ⟨α w ⟨f, hf⟩ x0, hW ⟨f, hf⟩ x0 hx0, rfl⟩
  have h2 : ∀ (i : ↥Z) (p : FreeAlgebra ℂ {f : GLw n i.1 → ℂ // IsHecke (N i.1) f}),
      FreeAlgebra.lift ℂ (α i) p = 0 → FreeAlgebra.lift ℂ (c false i) p = 0 := by
    intro i p hp
    have hz : ∀ x ∈ fixed (τ i.1).ρ (N i.1), FreeAlgebra.lift ℂ (Lv (τ i.1).ρ (N i.1))
        (FreeAlgebra.lift ℂ (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => FreeAlgebra.ι ℂ j.1) p) x = 0 := by
      intro x hx
      rw [lift_lift Subtype.val, ← lift_restrict (fixed (τ i.1).ρ (N i.1)) _ (α i) (fun _ _ => rfl) p ⟨x, hx⟩, hp]
      rfl
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h3 := hIs E n π i.1 (τ i.1) (hτ i.1 i.2) (N i.1) (hNo _) (hNl _) _ hz x.1 (y.le x.2)
      (hfixY i.1 i.2 false x.1 x.2)
    rw [lift_lift Subtype.val] at h3
    have h4 := lift_restrict y.Y (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => Lv (rw' n i.1 false) (N i.1) j.1)
      (c false i) (fun _ _ => rfl) p x
    rw [h3] at h4
    simpa using h4
  have h3 : ∀ (i k : ↥Z), i ≠ k → ∀ f g, Commute (c false i f) (c false k g) := by
    intro i k hik f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, false) (hSl _ k.2 _) ?_ g.1 g.2)
    intro h
    exact hik (Subtype.ext (Prod.ext_iff.1 h).1)
  have h4 : ∀ (i k : ↥Z) f g, Commute (c false i f) (c true k g) := by
    intro i k f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, true) (hSl _ k.2 _) (by simp) g.1 g.2)
  have h5 : ∀ (i : ↥Z) f, y.A * c false i f = c true i f * y.A := by
    intro i f
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hYS E n S Z N hS hZ hG π y i.1 i.2 f.1 f.2 x (c false i f x) rfl
  have h6 : ∀ W : Submodule ℂ y.Y, (∀ (i : ↥Z) f, ∀ x ∈ W, c false i f x ∈ W ∧ c true i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine simple_of _ W (hZS E n S Z N hS hZ hG π y (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro w hw b f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    have := hW ⟨w, hw⟩ ⟨f, hf⟩ x0 hx0
    cases b
    · exact Submodule.mem_map.2 ⟨_, this.1, rfl⟩
    · exact Submodule.mem_map.2 ⟨_, this.2, rfl⟩
  obtain ⟨d, hd, key⟩ := hAC ↥Z (fun w : ↥Z => {f : GLw n w.1 → ℂ // IsHecke (N w.1) f})
    (fun w : ↥Z => ↥(fixed (τ w.1).ρ (N w.1))) y.Y α (c false) (c true) y.A h1 h2 h3 h4 y.sq h5 h6
  refine ⟨part1, d, hd, fun F hF => ?_⟩
  have hFh : ∀ w (_ : w ∈ Z) b, IsHecke (N w) (F w b) := fun w hw b =>
    (hF.1 (w, b) (by simp [hw])).2
  have hpf := hPf E n S Z N hS hZ hG _ F hF
  have hcomm : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k →
      Commute (Lw N i.1 i.2 (F i.1 i.2)) (Lw N k.1 k.2 (F k.1 k.2)) := by
    intro i hi k hk hik
    exact (hLoc i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have e1 : y.r (pf S F) = (((Finset.univ : Finset ↥Z).toList.map fun i =>
      c false i ⟨F i.1 false, hFh _ i.2 _⟩ * c true i ⟨F i.1 true, hFh _ i.2 _⟩).prod) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [y.act _ hpf x, hPO E n S Z N hS hZ hG _ F hF x (y.fix x.2),
      prod_reorder Z (fun i => Lw N i.1 i.2 (F i.1 i.2)) hcomm]
    exact (list_restrict y.Y _ _ (fun _ _ => rfl) _ x).symm
  rw [e1, key (fun i => ⟨F i.1 false, hFh _ i.2 _⟩) (fun i => ⟨F i.1 true, hFh _ i.2 _⟩)]
  congr 1
  rw [← Finset.prod_coe_sort Z]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hinv : ∀ v ∈ fixed (τ w.1).ρ (N w.1), (Lv (τ w.1).ρ (N w.1) (F w.1 false) * Lv (τ w.1).ρ (N w.1) (F w.1 true)) v ∈
      fixed (τ w.1).ρ (N w.1) := fun v hv =>
    hαinv w ⟨_, hFh _ w.2 _⟩ _ (hαinv w ⟨_, hFh _ w.2 _⟩ v hv)
  rw [GlobalTheory.BCT.trOn, dite_eq_left hinv]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLevFix
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem core_exists {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K O : Subgroup G) (hK : IsCompact (K : Set G)) (hO : IsOpen (O : Set G)) :
    ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ O ∧ ∀ k ∈ K, ∀ x ∈ M, k * x * k⁻¹ ∈ M := by
  have hU : ∀ k : G, IsOpen {y : G | k⁻¹ * y ∈ O} := fun k => hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨T, hTK, hT⟩ := hK.elim_nhds_subcover (fun k => {y : G | k⁻¹ * y ∈ O})
    (fun k _ => (hU k).mem_nhds (by simpa using O.one_mem))
  have hT' : ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ O := fun k hk => by
    simpa using hT hk
  let M : Subgroup G :=
    { carrier := {x | ∀ t ∈ T, t⁻¹ * x * t ∈ O}
      one_mem' := fun t _ => by simpa using O.one_mem
      mul_mem' := fun {a b} ha hb t ht => by
        have := O.mul_mem (ha t ht) (hb t ht)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha t ht => by
        have := O.inv_mem (ha t ht)
        simpa [mul_assoc] using this }
  refine ⟨M, ?_, ?_, ?_⟩
  · have e : (M : Set G) = ⋂ t ∈ T, (fun x => t⁻¹ * x * t) ⁻¹' (O : Set G) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_biInter_finset fun t _ =>
      hO.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · intro x hx
    obtain ⟨t, ht, h⟩ := hT' 1 K.one_mem
    have h1 : t⁻¹ ∈ O := by simpa using h
    have h2 := O.mul_mem (O.mul_mem (O.inv_mem h1) (hx t ht)) h1
    have e : t⁻¹⁻¹ * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h2
  · intro k hk x hx t ht
    obtain ⟨t', ht', h⟩ := hT' (k⁻¹ * t) (K.mul_mem (K.inv_mem hk) (hTK t ht))
    have h2 := O.mul_mem (O.mul_mem (O.inv_mem h) (hx t' ht')) h
    have e : (t'⁻¹ * (k⁻¹ * t))⁻¹ * (t'⁻¹ * x * t') * (t'⁻¹ * (k⁻¹ * t)) = t⁻¹ * (k * x * k⁻¹) * t := by group
    rwa [e] at h2

private theorem fin_reduce {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)] (q : ∀ i, G →* A i)
    (Kg H : Subgroup G) (Y : Finset ι) (base : ∀ k ∈ Kg, (∀ v ∈ Y, q v k = 1) → k ∈ H) (T : Finset ι) :
    ∀ k ∈ Kg, (∀ v ∈ Y, v ∉ T → q v k = 1) →
      (∀ v ∈ T, ∃ e ∈ H, e ∈ Kg ∧ q v e = q v k ∧ ∀ u, u ≠ v → q u e = 1) → k ∈ H := by
  induction T using Finset.induction_on with
  | empty => exact fun k hk h0 _ => base k hk fun v hv => h0 v hv (by simp)
  | insert v T hv ih =>
    intro k hk h0 h1
    obtain ⟨e, heH, heK, hev, heu⟩ := h1 v (Finset.mem_insert_self _ _)
    have hk1 : k * e⁻¹ ∈ H := by
      refine ih _ (Kg.mul_mem hk (Kg.inv_mem heK)) (fun u hu huT => ?_) (fun u huT => ?_)
      · by_cases huv : u = v
        · subst huv
          simp [hev]
        · rw [map_mul, map_inv, heu u huv, inv_one, mul_one]
          exact h0 u hu (by simp [huv, huT])
      · have huv : u ≠ v := fun h => hv (h ▸ huT)
        obtain ⟨e', h1', h2', h3', h4'⟩ := h1 u (Finset.mem_insert_of_mem huT)
        refine ⟨e', h1', h2', ?_, h4'⟩
        rw [h3', map_mul, map_inv, heu u huv, inv_one, mul_one]
    simpa using H.mul_mem hk1 heH

private def stb {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : Sm E n) : Subgroup (GF E n) where
  carrier := {k | finRep E n k φ = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem exists_fin {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (hq : ∀ w : Pl E, Continuous (qw n w false)) (H : Subgroup (GF E n)) (hH : IsOpen (H : Set (GF E n))) :
    ∃ Y : Finset (Pl E), ∀ k ∈ Kf E n, (∀ v ∈ Y, qw n v false k = 1) → k ∈ H := by
  have hC : IsCompact ((Kf E n : Set (GF E n)) ∩ (H : Set (GF E n))ᶜ) :=
    GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.inter_right hH.isClosed_compl
  obtain ⟨Y, hY⟩ := hC.elim_finite_subcover (fun v : Pl E => {g : GF E n | qw n v false g ≠ 1})
    (fun v => (isClosed_singleton.preimage (hq v)).isOpen_compl) (fun x hx => by
      by_contra hc
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hc
      have : x = 1 := GlobalTheory.LocFactor.glAf_ext fun v => by
        rw [map_one]
        exact hc v
      exact hx.2 (this ▸ H.one_mem))
  refine ⟨Y, fun k hk h1 => by_contra fun hkH => ?_⟩
  have := hY ⟨hk, hkH⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨v, hv, hne⟩ := this
  exact hne (h1 v hv)

theorem levFix_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → SlotBasic → JointFix → LevFix := by
  intro hP hS hJ E _ _ _ n π S Z hSec hZ hOff
  obtain ⟨hinv, -, hloc, -, -, -, hK⟩ := hS E n S hSec
  obtain ⟨-, hcP, -, hSP⟩ := hP E
  have hcc : ∀ w : Pl E, cPl (cPl w) = w := fun w => (hcP w).1
  have mem : ∀ (M : ∀ w : Pl E, Subgroup (GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have memK : ∀ x : GF E n, x ∈ Kf E n ↔ ∀ u : Pl E, qw n u false x ∈ KGL u (n := n) := by
    intro x
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
    rfl
  have hq : ∀ w : Pl E, Continuous (qw n w false) := fun w => (hloc w false).2.1

  have hth : ∀ (u : Pl E) (g : GF E n), qw n (cPl u) false g = 1 → qw n u true g = 1 := by
    intro u g h
    have := GlobalTheory.EulerTw.IntRead.map_thF (n := n) u g
    change qw n u true g = _ at this
    rw [this]
    have h' : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E u)) g = 1 := h
    rw [h', map_one]
  have hC : ∀ (w : Pl E) (g : GF E n), qw n w true g = 1 → qw n (cPl w) false g = 1 := by
    intro w g h
    have := hth (cPl w) (thF E n g) (by rw [hcc]; exact h)
    change qw n (cPl w) false (thF E n (thF E n g)) = 1 at this
    rwa [hinv] at this

  obtain ⟨ψ₀, hψ₀, hψ₀0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨Y₀, hY₀⟩ := exists_fin n hq (stb n ψ₀) (π.cusp ψ₀ hψ₀).1.level
  set Z2 : Finset (Pl E) := Z ∪ Z.image cPl with hZ2
  set Y : Finset (Pl E) := Y₀ ∪ Z2 with hY
  set U : Subgroup (GF E n) := Kf E n ⊓ ⨅ v ∈ Y, (qw n v false).ker with hU
  have memU : ∀ k, k ∈ U ↔ k ∈ Kf E n ∧ ∀ v ∈ Y, qw n v false k = 1 := by
    intro k
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  obtain ⟨ψ, hψ, hψ0, hψU, hψP⟩ := hJ E n π (Y \ Z2)
    (fun w hw => hOff w ⟨fun h => (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_left _ h), fun h =>
      (Finset.mem_sdiff.1 hw).2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hcc w⟩))⟩)
    U (fun k hk w hw => ((memU k).1 hk).2 w (Finset.mem_sdiff.1 hw).1)
    ⟨ψ₀, hψ₀, hψ₀0, fun k hk => hY₀ k ((memU k).1 hk).1 fun v hv =>
      ((memU k).1 hk).2 v (Finset.mem_union_left _ hv)⟩

  have hHo : IsOpen (stb n ψ : Set (GF E n)) := (π.cusp ψ hψ).1.level
  have hcore : ∀ w : Pl E, ∃ M : Subgroup (GLw n w), IsOpen (M : Set (GLw n w)) ∧
      M ≤ KGL w (n := n) ⊓ (stb n ψ).comap (jw n w false) ⊓ (stb n ψ).comap (jw n w true) ∧
      ∀ k ∈ KGL w (n := n), ∀ x ∈ M, k * x * k⁻¹ ∈ M := fun w =>
    core_exists _ _ (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
      (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.inter (hHo.preimage (hloc w false).1)).inter
        (hHo.preimage (hloc w true).1))
  choose M hMo hMle hMn using hcore
  refine ⟨fun w => if w ∈ Z then M w else KGL w (n := n), fun w => ?_, ψ, hψ, hψ0, fun k hk => ?_⟩
  · by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact ⟨hMo w, fun x hx => (hMle w hx).1.1, hMn w, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl,
        fun k hk x hx => (KGL w (n := n)).mul_mem ((KGL w (n := n)).mul_mem hk hx) ((KGL w (n := n)).inv_mem hk), fun _ => trivial⟩
  have hkN := (mem _ k).1 hk
  have hkK : k ∈ Kf E n := (hK k).1 ((mem _ k).2 fun i hi => by
    have := hkN i hi
    by_cases hz : i.1 ∈ Z
    · simp only [if_pos hz] at this
      exact (hMle _ this).1.1
    · simpa only [if_neg hz] using this)
  have hkv := (memK k).1 hkK
  have hlocal : ∀ v : Pl E, jw n v false (qw n v false k) ∈ Kf E n ∧
      qw n v false (jw n v false (qw n v false k)) = qw n v false k ∧
      ∀ u, u ≠ v → qw n u false (jw n v false (qw n v false k)) = 1 := by
    intro v
    have h1 : qw n v false (jw n v false (qw n v false k)) = qw n v false k := (hloc v false).2.2.1 _
    have h2 : ∀ u, u ≠ v → qw n u false (jw n v false (qw n v false k)) = 1 := fun u hu =>
      pLoc_locGL_of_ne hu _
    refine ⟨(memK _).2 fun u => ?_, h1, h2⟩
    by_cases hu : u = v
    · subst hu
      rw [h1]
      exact hkv u
    · rw [h2 u hu]
      exact one_mem _
  refine fin_reduce (fun v => qw n v false) (Kf E n) (stb n ψ) Y
    (fun k' hk' h' => hψU k' ((memU k').2 ⟨hk', h'⟩)) Y k hkK (fun v hv h => absurd hv h) (fun v hv => ?_)
  by_cases hvZ : v ∈ Z
  · have h0 := hkN (v, false) ⟨(hZ v hvZ).1, by simp⟩
    simp only [if_pos hvZ] at h0
    exact ⟨_, (hMle v h0).1.2, hlocal v⟩
  by_cases hvZ2 : v ∈ Z2
  · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Z, cPl w = v := by
      rcases Finset.mem_union.1 hvZ2 with h | h
      · exact absurd h hvZ
      · exact Finset.mem_image.1 h
    have hsp := (hZ w hw).2
    have h0 := hkN (w, true) ⟨(hZ w hw).1, fun _ => hsp⟩
    simp only [if_pos hw] at h0
    set b := qw n w true k with hb
    set e := jw n w true b with he
    have heH : e ∈ stb n ψ := (hMle w h0).2
    have hew : qw n w true e = b := (hloc w true).2.2.1 b
    have hev : qw n (cPl w) false e = qw n (cPl w) false k := by
      have : qw n (cPl w) false (k * e⁻¹) = 1 := hC w _ (by
        rw [map_mul, map_inv, hew, ← hb, mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this.symm
    have heu : ∀ u, u ≠ cPl w → qw n u false e = 1 := by
      intro u hu
      have hne : cPl u ≠ w := fun h => hu (by rw [← h, hcc])
      have := GlobalTheory.EulerTw.IntRead.map_thF (n := n) u (locGL E n w b)
      refine this.trans ?_
      have h1 : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E u)) (locGL E n w b) = 1 :=
        pLoc_locGL_of_ne hne b
      rw [h1, map_one]
    refine ⟨e, heH, (memK _).2 fun u => ?_, hev, heu⟩
    by_cases hu : u = cPl w
    · subst hu
      rw [hev]
      exact hkv _
    · rw [heu u hu]
      exact one_mem _
  · have hvP : v ∈ Y \ Z2 := Finset.mem_sdiff.2 ⟨hv, hvZ2⟩
    exact ⟨_, GlobalTheory.LGrp.mem_fixed.1 (hψP v hvP) _ (hkv v), hlocal v⟩

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPfHecke
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open scoped Pointwise

section Abs

variable {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)]

private def boxes (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) : List ι → Set G
  | [] => {1}
  | i :: l => (j i '' C i) * boxes j C l

private def pr (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (x : G) (l : List ι) : G :=
  (l.map fun i => j i (q i x)).prod

private theorem boxes_compact [TopologicalSpace G] [ContinuousMul G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) (hj : ∀ i, Continuous (j i)) (l : List ι)
    (h : ∀ i ∈ l, IsCompact (C i)) : IsCompact (boxes j C l) := by
  induction l with
  | nil => exact isCompact_singleton
  | cons i l ih =>
    exact ((h i (by simp)).image (hj i)).mul (ih fun k hk => h k (by simp [hk]))

private theorem pr_mem (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (C : ∀ i, Set (A i)) (x : G) (l : List ι)
    (h : ∀ i ∈ l, q i x ∈ C i) : pr j q x l ∈ boxes j C l := by
  induction l with
  | nil => simp [pr, boxes]
  | cons i l ih =>
    have h1 : j i (q i x) ∈ j i '' C i := ⟨_, h i (by simp), rfl⟩
    have h2 := ih fun k hk => h k (by simp [hk])
    simpa [pr, boxes] using Set.mul_mem_mul h1 h2

private theorem q_pr_out (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (hk : P k) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hkl : k ∉ l) : q k (pr j q x l) = 1 := by
  induction l with
  | nil => simp [pr]
  | cons i l ih =>
    have hne : i ≠ k := fun e => hkl (by simp [e])
    have h2 : q k (pr j q x l) = 1 :=
      ih (fun m hm => hl m (by simp [hm])) (fun hm => hkl (by simp [hm]))
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    rw [h3, map_mul, h2, hind i k (hl i (by simp)) hk hne, one_mul]

private theorem q_pr_in (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hnd : l.Nodup) (hkl : k ∈ l) : q k (pr j q x l) = q k x := by
  induction l with
  | nil => simp at hkl
  | cons i l ih =>
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    have hl' : ∀ m ∈ l, P m := fun m hm => hl m (by simp [hm])
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases e : k = i
    · subst e
      rw [h3, map_mul, hjq, q_pr_out j q P hind x k (hl k (by simp)) l hl' hi, mul_one]
    · have hk' : k ∈ l := by simpa [e] using hkl
      rw [h3, map_mul, ih hl' hnd' hk', hind i k (hl i (by simp)) (hl k (by simp [hk'])) (Ne.symm e), one_mul]

private theorem abs_support [TopologicalSpace G] [IsTopologicalGroup G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (hj : ∀ i, Continuous (j i)) (P : ι → Prop)
    (N : ∀ i, Subgroup (A i)) (L : Subgroup G) (hL : ∀ x, x ∈ L ↔ ∀ i, P i → q i x ∈ N i)
    (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (I : Finset ι) (hI : ∀ i ∈ I, P i)
    (C : ∀ i, Set (A i)) (hC : ∀ i ∈ I, IsCompact (C i)) (f : G → ℂ)
    (hinv : ∀ k ∈ L, ∀ x, f (x * k) = f x)
    (hs : ∀ x, f x ≠ 0 → (∀ i ∈ I, q i x ∈ C i) ∧ ∀ i, P i → i ∉ I → q i x ∈ N i) :
    HasCompactSupport f := by
  classical
  have hcl : IsClosed (Function.support f) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : f x = 0 := by simpa using hx
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (L : Set G)) :=
      hLo.preimage (continuous_const.mul continuous_id)
    have hmem : x ∈ (fun y => x⁻¹ * y) ⁻¹' (L : Set G) := by simp [L.one_mem]
    refine Filter.mem_of_superset (hop.mem_nhds hmem) ?_
    intro y hy
    have : f (x * (x⁻¹ * y)) = f x := hinv _ hy x
    simpa [hx0] using this
  have hl : ∀ i ∈ I.toList, P i := fun i hi => hI i (by simpa using hi)
  have hK : IsCompact (boxes j C I.toList * (L : Set G)) :=
    (boxes_compact j C hj _ fun i hi => hC i (by simpa using hi)).mul hLc
  have hsub : Function.support f ⊆ boxes j C I.toList * (L : Set G) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hs x hx
    have hb := pr_mem j q C x I.toList fun i hi => h1 i (by simpa using hi)
    have hy : (pr j q x I.toList)⁻¹ * x ∈ L := by
      refine (hL _).2 fun k hk => ?_
      by_cases hkI : k ∈ I
      · rw [map_mul, map_inv, q_pr_in j q P hjq hind x k _ hl I.nodup_toList (by simpa using hkI)]
        simp [(N k).one_mem]
      · rw [map_mul, map_inv, q_pr_out j q P hind x k hk _ hl (by simpa using hkI)]
        simpa using h2 k hk hkI
    have := Set.mul_mem_mul hb hy
    simpa using this
  show IsCompact (closure (Function.support f))
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hsub

end Abs

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun in
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH in
open scoped Classical in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pfHecke_pf :
    SlotBasic → LevTop → PfHecke := by
  intro hSF hLT E _ _ _ n S Z N hS hZ hN I F hF
  obtain ⟨-, -, hloc, hind, hfinK, -, -⟩ := hSF E n S hS
  obtain ⟨hLo, hLc, -, -⟩ := hLT E n S Z N hS hZ hN
  have hLev : ∀ x, x ∈ Lev S N ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ N i.1 := by
    intro x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]

  have hposition : ∀ i : Pl E × Bool, Sl S i → ∀ a ∈ N i.1, ∀ x,
      F i.1 i.2 (a * x) = F i.1 i.2 x ∧ F i.1 i.2 (x * a) = F i.1 i.2 x := by
    intro i hi a ha x
    by_cases hiI : i ∈ I
    · exact (hF.1 i hiI).2.2 a ha x
    · rw [hF.2 i hi hiI]
      constructor
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show a * x ∈ (N i.1 : Set _) from (N i.1).mul_mem ha hx),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show a * x ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_left _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show x * a ∈ (N i.1 : Set _) from (N i.1).mul_mem hx ha),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show x * a ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_right _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]

  have hfalse : ∀ w, w ∈ S → Sl S (w, false) := fun w hw => ⟨hw, by simp⟩
  have htrue : ∀ w, w ∈ S → IsSplitAt w → Sl S (w, true) := fun w hw hs => ⟨hw, fun _ => hs⟩
  have hinvL : ∀ k ∈ Lev S N, ∀ x, pf S F (k * x) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).1
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).1
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]
  have hinvR : ∀ k ∈ Lev S N, ∀ x, pf S F (x * k) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).2
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).2
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]

  have hfac : ∀ x : GF E n, pf S F x ≠ 0 → ∀ w ∈ S,
      (F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1) ≠ 0 := by
    intro x hx w hw h0
    apply hx
    classical
    set fac : Pl E → ℂ := fun w =>
      F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1 with hfacdef
    have hbad := hfinK x
    have hfin : (S ∩ Function.mulSupport fac).Finite := by
      refine ((Z.finite_toSet.union (I.image Prod.fst).finite_toSet).union
        (hbad.image Prod.fst)).subset ?_
      rintro u ⟨hu, hne⟩
      by_contra hout
      simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image, Set.mem_image, Set.mem_setOf_eq,
        not_or, not_exists, not_and] at hout
      obtain ⟨⟨huZ, huI⟩, hub⟩ := hout
      have hNu : N u = KGL u n := (hN u).2.2.2 huZ
      have hone : ∀ b, Sl S (u, b) → F u b (qw n u b x) = 1 := by
        intro b hb
        have hnotI : (u, b) ∉ I := fun h => huI (u, b) h rfl
        have hq : qw n u b x ∈ KGL u n := by
          by_contra hq
          exact hub (u, b) hq rfl
        rw [hF.2 (u, b) hb hnotI]
        simp only
        rw [hNu, Set.indicator_of_mem (show qw n u b x ∈ (KGL u n : Set _) from hq)]
        rfl
      apply hne
      simp only [hfacdef]
      rw [hone false (hfalse u hu)]
      by_cases hs : IsSplitAt u
      · simp only [if_pos hs]
        rw [hone true (htrue u hu hs), one_mul]
      · simp only [if_neg hs, one_mul]
    have hwm : w ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hw, ?_⟩
      show fac w ≠ 1
      rw [show fac w = 0 from h0]
      exact zero_ne_one
    show (∏ᶠ w ∈ S, fac w) = 0
    rw [finprod_mem_eq_prod fac hfin]
    exact Finset.prod_eq_zero hwm h0

  have hval : ∀ x : GF E n, pf S F x ≠ 0 → ∀ i : Pl E × Bool, Sl S i → F i.1 i.2 (qw n i.1 i.2 x) ≠ 0 := by
    rintro x hx ⟨w, b⟩ ⟨hw, hb⟩
    have h := hfac x hx w hw
    cases b with
    | false => exact left_ne_zero_of_mul h
    | true =>
      have hs := hb rfl
      have h2 := right_ne_zero_of_mul h
      rwa [if_pos hs] at h2
  refine ⟨?_, fun k hk x => ⟨hinvL k hk x, hinvR k hk x⟩⟩
  refine abs_support (ι := Pl E × Bool) (A := fun i => GLw n i.1)
    (fun i => jw n i.1 i.2) (fun i => qw n i.1 i.2) (fun i => (hloc i.1 i.2).1) (Sl S)
    (fun i => N i.1) (Lev S N) hLev hLo hLc (fun i a => (hloc i.1 i.2).2.2.1 a)
    (fun i k hi hk hne a => hind i k hi hk hne a) I (fun i hi => (hF.1 i hi).1)
    (fun i => tsupport (F i.1 i.2)) (fun i hi => (hF.1 i hi).2.1) (pf S F) hinvR ?_
  intro x hx
  refine ⟨fun i hi => subset_tsupport _ (hval x hx i (hF.1 i hi).1), fun i hi hiI => ?_⟩
  have h := hval x hx i hi
  rw [hF.2 i hi hiI] at h
  by_contra hq
  exact h (Set.indicator_of_notMem hq _)
end
