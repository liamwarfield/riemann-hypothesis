module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CtEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.ExistsUnitOrdLEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.GeneralLocalHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RCountAt
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.rCountAt :
    UpperTheory.V.Z.Mult.RCountAt := by
  classical
  intro hC hEv hCp hP E _ _ _ hU n hn1 hn4 π hreg hd S hS lam Z hZ B τ hB hτ K' hK' hKZ ι _ σ hdec
  obtain ⟨t, Bi, hi, hev⟩ := hEv E hU n hn1 S hS lam Z hZ K' hK' hKZ ι σ hdec
  obtain ⟨-, hc, -, hSec⟩ := hP E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hsat : ∀ w, Off Z w → ∃ τ₀ : SmIrr (GLw n w), π.IsLocComp w τ₀ ∧ HasSatGL w τ₀.ρ (B w) := fun w hw => by
    obtain ⟨τ₀, h₀⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
    exact ⟨τ₀, h₀.1, ((GlobalTheory.Cong.satake_locComp E n π w τ₀ h₀.1).1 _).1 (hB w hw)⟩
  have hAt : ∀ i, (∀ w, Off Z w → IsSplitAt w → Bi i w = B w) → At π (σ i) := fun i h => by
    filter_upwards [off_cofinite hP Z] with w hw hs
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    exact ⟨τ', B w, h1, h w hw hs ▸ h2, hB w hw⟩
  have hCo : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → ∀ τ₀, π.IsLocComp w τ₀ → Cp (σ i) w τ₀ := fun i h =>
    hC E hU n hn1 hn4 π hreg hd (σ i) (hdec.1 i).1 (hi i).1 h
  have hEq : ∀ i, At π (σ i) → ∀ w, Off Z w → IsSplitAt w → Bi i w = B w := fun i h w hw hs => by
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    obtain ⟨τ₀, h₀, s₀⟩ := hsat w hw
    exact HasSatGL.unique h2 ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w hs τ₀ τ' (hCo i h w hs τ₀ h₀) h1).1 _ s₀)
  refine ⟨{i // ¬ At π (σ i)}, inferInstance, fun j => Bi j.1, fun j => ?_, ?_⟩
  · by_contra hno
    refine j.2 (hAt j.1 fun w hw hs => ?_)
    by_contra hne
    obtain ⟨τ', -, h2⟩ := (hi j.1).2.2 w hw hs
    obtain ⟨τ₀, -, s₀⟩ := hsat w hw
    exact hno ⟨w, hw, hs, HasSatGL.card s₀, HasSatGL.card h2, hne⟩
  · intro f hf T hT hTZ e₁ e₂ h1 h0 k
    obtain ⟨htest, htr⟩ := hev f hf T hT hTZ e₁ e₂ k
    refine ⟨htest, fun hk => ?_⟩
    have hoffT : ∀ w ∈ T, Off Z w ∧ IsSplitAt w := fun w hw => by
      have hnZ : ∀ {u}, u ∈ T → u ∉ Z := fun hu hu' => Finset.disjoint_left.1 hTZ hu hu'
      refine ⟨⟨hnZ hw, fun h => ?_⟩, (hT w hw).2⟩
      exact ((hc w).2.1 (hT w hw).2) ((hSec S hS w).2 (hT w hw).1 (hZ _ h).1)
    have hval : ∀ i, At π (σ i) → val1 T e₁ e₂ (Bi i) = 1 := fun i h => by
      rw [← h1]
      refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨⟨ha, hb⟩, hs⟩ := hoffT w hw
      have hcs : IsSplitAt (cPl w) := (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hs).symm)
      have ho : Off Z (cPl w) := ⟨hb, by rwa [(hc w).1]⟩
      rw [hEq i h w ⟨ha, hb⟩ hs, hEq i h _ ho hcs]
    have hterm : ∀ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w (n := n)) (f w)) * val1 T e₁ e₂ (Bi i) ^ k =
        (if At π (σ i) then 1 else 0) * ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) (f w) := fun i => by
      by_cases h : At π (σ i)
      · rw [if_pos h, hval i h, one_pow, mul_one, one_mul]
        refine Finset.prod_congr rfl fun w hw => ?_
        exact ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w (hZ w hw).2 (τ w) (t i w)
          (hCo i h w (hZ w hw).2 _ (hτ w hw)) ((hi i).2.1 w hw)).2 (f w)).symm
      · rw [if_neg h, h0 ⟨i, h⟩, zero_pow (by omega), mul_zero, zero_mul]
    rw [htr, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LevInd
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Mult

section Generic

variable {G V : Type} [Group G]

private abbrev ind (H : Subgroup G) : G → ℂ := (H : Set G).indicator 1

private theorem ind_mem {H : Subgroup G} {x : G} (hx : x ∈ H) : ind H x = 1 :=
  Set.indicator_of_mem (show x ∈ (H : Set G) from hx) _

private theorem ind_notMem {H : Subgroup G} {x : G} (hx : x ∉ H) : ind H x = 0 :=
  Set.indicator_of_notMem (show x ∉ (H : Set G) from hx) _

private theorem ind_mul_left (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (k * x) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hk hx), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_left hk).1 h)), ind_notMem hx]

private theorem ind_mul_right (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    ind H (x * k) = ind H x := by
  by_cases hx : x ∈ H
  · rw [ind_mem (H.mul_mem hx hk), ind_mem hx]
  · rw [ind_notMem (fun h => hx ((H.mul_mem_cancel_right hk).1 h)), ind_notMem hx]

private theorem rStab_ind (H : Subgroup G) : rStab (ind H) = H := by
  ext k
  constructor
  · intro hk
    by_contra hn
    have h := hk 1
    rw [one_mul, ind_notMem hn, ind_mem H.one_mem] at h
    exact zero_ne_one h
  · intro hk x
    exact ind_mul_right H hk x

private theorem ind_inv (H : Subgroup G) : (fun y : G => ind H y⁻¹) = ind H := by
  funext y
  by_cases hy : y ∈ H
  · rw [ind_mem (H.inv_mem hy), ind_mem hy]
  · rw [ind_notMem (fun h => hy (by simpa using H.inv_mem h)), ind_notMem hy]

variable [AddCommGroup V] [Module ℂ V]

private theorem levOp_ind (ρ : Representation ℂ G V) (K H : Subgroup G) (x : V) (hx : x ∈ fixed ρ H) :
    levOp ρ K H (ind H) LinearMap.id x = ((H.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  have hfx : ∀ h ∈ H, ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ H, q.out ∈ H ↔ q = (QuotientGroup.mk 1 : G ⧸ H) := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ H) = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using H.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : G)
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ H)]
  · rw [ind_mem ((hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [ind_notMem (fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K H : Subgroup G) (hle : H ≤ K) (hi : H.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ H)) (hne : fixed ρ H ≠ ⊥) : trc ρ K (ind H) ≠ 0 := by
  have hlev : K ⊓ rStab (ind H) ⊓ rStab (fun y : G => ind H y⁻¹) = H := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ H, levOp ρ K H (ind H) LinearMap.id v ∈ fixed ρ H := by
    intro v hv
    rw [levOp_ind ρ K H v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K H (ind H) LinearMap.id).restrict hc = ((H.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K H v v.2]
  unfold twTr
  rw [dite_eq_left hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ H) ≠ 0 := fun h0 => hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

private theorem fixed_map_ne (ρ : Representation ℂ G V) (U : Subgroup G) (K : Subgroup U)
    (h : fixed (ρ.comp U.subtype) K ≠ ⊥) : fixed ρ (K.map U.subtype) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨x, ?_, hx0⟩
  rintro ⟨_, u, hu, rfl⟩
  simpa using hx ⟨u, hu⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem map_top_open (U : Subgroup G) (hU : U = ⊤) (K : Subgroup U) (ho : IsOpen (K : Set U)) :
    IsOpen ((K.map U.subtype : Subgroup G) : Set G) := by
  subst hU
  rw [Subgroup.coe_map]
  exact (IsOpen.isOpenMap_subtype_val (by simp)) _ ho

private theorem compact_of_map (U : Subgroup G) (K : Subgroup U)
    (hc : IsCompact ((K.map U.subtype : Subgroup G) : Set G)) : IsCompact (K : Set U) := by
  rw [Subgroup.coe_map] at hc
  exact Topology.IsInducing.subtypeVal.isCompact_iff.2 hc

end Generic

end UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.levInd :
    UpperTheory.V.Z.Mult.LevInd := by
  intro E _ _ _ n w hw K hKo hKle
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hU : UL n w = ⊤ := if_pos hw
  let H : Subgroup (GLw n w) := K.map (UL n w).subtype
  have hHo : IsOpen (H : Set (GLw n w)) := map_top_open _ hU K hKo
  have hle : H ≤ GlobalTheory.LFun.KGL w (n := n) := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hKle hu)
  have hHc : IsCompact (H : Set (GLw n w)) := hc.of_isClosed_subset (H.isClosed_of_isOpen hHo) hle
  have hKc : IsCompact (K : Set (UL n w)) := compact_of_map _ K hHc
  have hmem : ∀ x : UL n w, x.1 ∈ H ↔ x ∈ K := fun x => by
    constructor
    · rintro ⟨u, hu, hux⟩
      have : u = x := Subtype.ext hux
      exact this ▸ hu
    · exact fun hx => ⟨x, hx, rfl⟩
  have hi : H.relIndex (GlobalTheory.LFun.KGL w (n := n)) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w (n := n)) ⧸ H.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
      Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := H.subgroupOf (GlobalTheory.LFun.KGL w (n := n)))).index_ne_zero
  refine ⟨ind H, ⟨H, hHo, hle, ?_, ?_⟩, ?_, ?_⟩
  · exact HasCompactSupport.intro' hHc (H.isClosed_of_isOpen hHo) fun x hx => ind_notMem hx
  · exact fun k hk x => ⟨ind_mul_left H hk x, ind_mul_right H hk x⟩
  · intro K₁ hK₁
    refine ⟨HasCompactSupport.intro' hKc (K.isClosed_of_isOpen hKo) fun x hx => ind_notMem fun h => hx ((hmem x).1 h), ?_⟩
    intro k hk x
    have hkH : k.1 ∈ H := (hmem k).2 (hK₁ hk)
    exact ⟨ind_mul_left H hkH x.1, ind_mul_right H hkH x.1⟩
  · intro τ hτ
    exact trc_ind_ne τ.ρ _ H hle hi (finiteDimensional_fixed_openSubgroup_GLw E n w τ H hHo) (fixed_map_ne τ.ρ _ K hτ)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.IsDecOfGlobLev
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Mult

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem isDec_of_globLev {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n}
    {K₁ K₂ : ∀ w : Pl E, Subgroup (UL n w)} (h : globLev S K₁ = globLev S K₂) {ι : Type}
    {σ : ι → Submodule ℂ (UA E n → ℂ)} (hd : IsDec S lam K₁ σ) : IsDec S lam K₂ σ := by
  have hf : forms S lam K₁ = forms S lam K₂ := by
    unfold forms
    rw [h]
  unfold IsDec at hd ⊢
  rw [← hf, ← h]
  exact hd

private theorem isHecke_mono {G : Type} [Group G] [TopologicalSpace G] {K₁ K₂ : Subgroup G} (hle : K₁ ≤ K₂) {f : G → ℂ}
    (h : IsHecke K₂ f) : IsHecke K₁ f :=
  ⟨h.1, fun k hk x => h.2 k (hle hk) x⟩

private theorem fixed_equiv {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (φ : H →* G) (K : Subgroup H)
    (h : fixed (ρ.comp φ) K ≠ ⊥) : fixed (ρ'.comp φ) K ≠ ⊥ := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h1 => h0 ?_⟩
  · have h2 := GlobalTheory.LGrp.mem_fixed.1 hx k hk
    have h3 : e (ρ (φ k) x) = ρ' (φ k) (e x) := LinearMap.congr_fun (e.isIntertwining' (φ k)) x
    have h2' : ρ (φ k) x = x := h2
    change ρ' (φ k) (e x) = e x
    rw [← h3, h2']
  · exact e.toLinearEquiv.map_eq_zero_iff.1 h1

end UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.rMult :
    UpperTheory.V.Z.Mult.RMult := by
  intro hId hCA hLT hGT hLI hLc hCh hOS hMu E _ _ _ hU n hn hn4 lam
  obtain ⟨a, ha, hA⟩ := hId E hU n hn hn4 lam
  obtain ⟨μ, e, hμ⟩ := hMu E hU
  have key : ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
      ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
      IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
      (∀ w ∈ S, IsSplitAt w → ∃ τ, π.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
      ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
      (Nat.card {i // At π (σ i)} : ℝ) = a := by
    intro π hreg hdual hinf hunr S hS K' hK' hKn hfix ι _ σ hDec
    obtain ⟨Z, B, τ, w₀, f₀, hZ, hZK, hoff, hτ, hw₀, hf₀, htr₀, hsep⟩ := hCh E n hn π hunr μ e hμ S hS K' hK' hKn
    have hKLo : ∀ w, IsOpen (KL n w : Set (UL n w)) := fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1
    obtain ⟨K₀, hK₀o, hK₀le, hK₀⟩ := hLc E n w₀ (hZ w₀ hw₀).2 f₀ hf₀
    obtain ⟨K₁, hK₁Z, hK₁o⟩ : ∃ K₁ : ∀ w : Pl E, Subgroup (UL n w), (∀ w ∈ Z, K₁ w = K' w) ∧ ∀ w, w ∉ Z → K₁ w = KL n w :=
      ⟨fun w => if w ∈ Z then K' w else KL n w, fun w h => if_pos h, fun w h => if_neg h⟩
    have hK₁ : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₁ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w ∈ Z
        · rw [hK₁Z w h]
          exact hK'.1 w
        · rw [hK₁o w h]
          exact ⟨hKLo w, le_rfl, fun k hk => hk⟩
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₁o w h)
    obtain ⟨K₂, hK₂w, hK₂⟩ : ∃ K₂ : ∀ w : Pl E, Subgroup (UL n w), K₂ w₀ = K₁ w₀ ⊓ K₀ ∧ ∀ w, w ≠ w₀ → K₂ w = K₁ w :=
      ⟨Function.update K₁ w₀ (K₁ w₀ ⊓ K₀), Function.update_self _ _ _, fun w h => Function.update_of_ne h _ _⟩
    have hle : ∀ w, K₂ w ≤ K₁ w := fun w => by
      by_cases h : w = w₀
      · subst h
        rw [hK₂w]
        exact inf_le_left
      · rw [hK₂ w h]
    have hK₂o : ∀ w, w ∉ Z → K₂ w = KL n w := fun w h => by
      rw [hK₂ w (fun e => h (e ▸ hw₀)), hK₁o w h]
    have hK₂L : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₂ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w = w₀
        · subst h
          rw [hK₂w]
          refine ⟨?_, inf_le_left.trans (hK₁.1 w).2.1, fun k hk => hk⟩
          rw [Subgroup.coe_inf]
          exact (hK₁.1 w).1.inter hK₀o
        · rw [hK₂ w h]
          exact hK₁.1 w
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₂o w h)
    have hg1 : globLev S K' = globLev S K₁ := hOS E n S K' K₁ fun w hw => by
      by_cases h : w ∈ Z
      · exact (hK₁Z w h).symm
      · rw [hK₁o w h]
        exact hZK w hw h
    have hDec₁ : IsDec S lam K₁ σ := isDec_of_globLev hg1 hDec
    obtain ⟨-, ι₂, _, σ₂, d1, d2, d3, -⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K₂ hK₂L
    have hDec₂ : IsDec S lam K₂ σ₂ := ⟨d1, d2, d3⟩
    have hfx : ∀ w ∈ Z, fixed ((τ w).ρ.comp (UL n w).subtype) (K₁ w) ≠ ⊥ := fun w hw => by
      obtain ⟨t, ht, hne⟩ := hfix w (hZ w hw).1 (hZ w hw).2
      obtain ⟨eq⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w t (τ w) ht (hτ w hw)
      rw [hK₁Z w hw]
      exact fixed_equiv eq _ _ hne
    have hg : ∀ w : Pl E, ∃ g : GLw n w → ℂ, w ∈ Z → Lc (KGL w (n := n)) g ∧
        (∀ K ≤ K₁ w, IsHecke K fun x : UL n w => g x.1) ∧ trc (τ w).ρ (KGL w (n := n)) g ≠ 0 := fun w => by
      by_cases hw : w ∈ Z
      · obtain ⟨g, h1, h2, h3⟩ := hLI E n w (hZ w hw).2 (K₁ w) (hK₁.1 w).1 (hK₁.1 w).2.1
        exact ⟨g, fun _ => ⟨h1, h2, h3 _ (hfx w hw)⟩⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose g hg using hg
    have hc₂ : (Nat.card {i // At π (σ₂ i)} : ℝ) = a := by
      refine hA π hreg hdual hinf μ e hμ S hS Z hZ B τ (Function.update g w₀ f₀) hoff
        (fun w hw => ⟨hτ w hw, ?_⟩) ⟨w₀, hw₀, ?_⟩ K₂ hK₂L hK₂o (fun w hw => ?_) ι₂ σ₂ hDec₂
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self]
          exact ⟨hf₀, htr₀⟩
        · rw [Function.update_of_ne h]
          exact ⟨(hg w hw).1, (hg w hw).2.2⟩
      · rw [Function.update_self]
        exact hsep
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self, hK₂w]
          exact isHecke_mono inf_le_right hK₀
        · rw [Function.update_of_ne h, hK₂ w h]
          exact (hg w hw).2.1 _ le_rfl
    obtain ⟨J, _, C, hC, hF⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₁ hK₁ hK₁o ι σ hDec₁
    obtain ⟨J', _, C', hC', hF'⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₂ hK₂L hK₂o ι₂ σ₂ hDec₂
    obtain ⟨T, e₁, e₂, hT, hd, h1, h0⟩ := rSep places E n S hS Z (J ⊕ J') B (Sum.elim C C')
      (by rintro (j | j); exacts [hC j, hC' j])
    have hh₁ : ∀ w ∈ Z, IsHecke (K₁ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ le_rfl
    have hh₂ : ∀ w ∈ Z, IsHecke (K₂ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ (hle w)
    obtain ⟨t₁, r₁⟩ := hF g hh₁ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inl j)) 1
    obtain ⟨-, r₂⟩ := hF' g hh₂ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inr j)) 1
    have hlt := hLT E hU n hn S hS lam K₁ K₂ hK₁ hK₂L hle _ t₁
    have hd0 := (hGT E hU n hn S hS lam K₁ hK₁).1
    have hP : ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) (g w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hg w hw).2.2
    have heq := (r₂ le_rfl).symm.trans (hlt.trans (r₁ le_rfl))
    have hcc := mul_right_cancel₀ hP (mul_left_cancel₀ hd0 heq)
    have hc : Nat.card {i // At π (σ i)} = Nat.card {i // At π (σ₂ i)} := by exact_mod_cast hcc.symm
    rw [hc]
    exact hc₂
  by_cases hN : ∃ m : ℕ, (m : ℝ) = a
  · obtain ⟨m, rfl⟩ := hN
    refine ⟨m, by exact_mod_cast ha, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd => ?_⟩
    exact_mod_cast key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd
  · exact ⟨1, one_pos, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd =>
      absurd ⟨_, key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd⟩ hN⟩
end
