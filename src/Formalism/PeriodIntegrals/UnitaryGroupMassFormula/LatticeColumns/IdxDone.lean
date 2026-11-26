module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.PrincipalCongruenceLeLevel
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxAbs
namespace PI.MassDataKppVolLemmas

private theorem natCard_eq_of_surjective_of_same_fibres {α β γ : Type*} (q : α → γ) (f : α → β)
    (hq : Function.Surjective q) (hf : Function.Surjective f)
    (h : ∀ a b, q a = q b ↔ f a = f b) : Nat.card γ = Nat.card β := by
  refine Nat.card_congr (Equiv.ofBijective (fun c => f (Function.surjInv hq c)) ⟨?_, ?_⟩)
  · intro c c' hcc
    have h1 := (h (Function.surjInv hq c) (Function.surjInv hq c')).2 hcc
    simpa only [Function.surjInv_eq hq] using h1
  · intro b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨q a, (h _ _).1 (Function.surjInv_eq hq (q a))⟩

private theorem index_eq_prod_index_of_surjective_prod {A : Type*} [Group A] (S : Subgroup A) {ι : Type*}
    [Fintype ι] {B : ι → Type*} [∀ i, Group (B i)] (T : ∀ i, Subgroup (B i))
    (ψ : ∀ i, A →* B i) (hsurj : ∀ f : ∀ i, B i, ∃ a, ∀ i, ψ i a = f i)
    (hmem : ∀ a, a ∈ S ↔ ∀ i, ψ i a ∈ T i) :
    S.index = ∏ i, (T i).index := by
  unfold Subgroup.index
  rw [← Nat.card_pi]
  refine natCard_eq_of_surjective_of_same_fibres (fun a : A => (a : A ⧸ S))
    (fun a i => ((ψ i a : B i) : B i ⧸ T i)) QuotientGroup.mk_surjective ?_ ?_
  · intro f
    choose g hg using fun i => QuotientGroup.mk_surjective (f i)
    obtain ⟨a, ha⟩ := hsurj g
    exact ⟨a, funext fun i => by simp only [ha, hg]⟩
  · intro a b
    simp only [funext_iff, QuotientGroup.eq, hmem, map_mul, map_inv]

theorem IdxAbs_relIndex {G : Type} [Group G] (K K2 : Subgroup G) {ι : Type} [Fintype ι]
    {Gp : ι → Type} [∀ i, Group (Gp i)] (π : ∀ i, G →* Gp i) (Lp : ∀ i, Subgroup (Gp i))
    (hK : ∀ i, ∀ z ∈ K, π i z ∈ Lp i)
    (hsurj : ∀ f : ∀ i, Lp i, ∃ z ∈ K, ∀ i, π i z = f i)
    (hloc : ∀ z ∈ K, (∀ i, ∃ w ∈ K2, π i w = π i z) → z ∈ K2) :
    K2.relIndex K = ∏ i, (K2.map (π i)).relIndex (Lp i) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ i, K →* Lp i, ∀ i (a : K), ((ψ i a : Lp i) : Gp i) = π i a :=
    ⟨fun i => ((π i).comp K.subtype).codRestrict (Lp i) (fun z => hK i z z.2),
      fun _ _ => rfl⟩
  have hs : ∀ f : ∀ i, Lp i, ∃ a : K, ∀ i, ψ i a = f i := by
    intro f
    obtain ⟨z, hzK, hz⟩ := hsurj f
    exact ⟨⟨z, hzK⟩, fun i => Subtype.ext ((hψ i ⟨z, hzK⟩).trans (hz i))⟩
  have hm : ∀ a : K, a ∈ K2.subgroupOf K ↔
      ∀ i, ψ i a ∈ (K2.map (π i)).subgroupOf (Lp i) := by
    intro a
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, hψ]
    exact ⟨fun ha _ => ⟨(a : G), ha, rfl⟩, fun h => hloc a a.2 h⟩
  have key := index_eq_prod_index_of_surjective_prod (K2.subgroupOf K)
    (fun i => (K2.map (π i)).subgroupOf (Lp i)) ψ hs hm
  exact key

end PI.MassDataKppVolLemmas
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelComponentsSurjective
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxProd
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

theorem piH_mem_KvH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) (hz : z ∈ KHg X u) :
    piH X u v z ∈ KvH X u v := by
  have h : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hz
  rw [Kf, Subgroup.mem_iInf] at h
  exact h v

def SurjH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ f : ∀ p : TypX X, KvH X u p.1,
      ∃ z ∈ KHg X u, ∀ p : TypX X, piH X u p.1 z = f p

def LocH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ z ∈ KHg X u,
      (∀ p : TypX X, ∃ w ∈ unitaryLevelClosureSubgroup X hb u, piH X u p.1 w = piH X u p.1 z) → z ∈ unitaryLevelClosureSubgroup X hb u

theorem idxProdH_of (hS : SurjH) (hL : LocH) : IdxProdH := by
  intro D X hb hK u hT hLv
  exact PI.MassDataKppVolLemmas.IdxAbs_relIndex (KHg X u) (unitaryLevelClosureSubgroup X hb u) (fun p : TypX X => piH X u p.1)
    (fun p : TypX X => KvH X u p.1) (fun p z hz => piH_mem_KvH X u p.1 z hz)
    (hS X hb hK u hT hLv) (hL X hb hK u hT hLv)

end PIW.MassDataColumns
end
end

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem mem_stabT_of_comp (I : Formalism.MainNotions.S.AutInst) (h : HA (Af I.F) I.cm.sig I.J) {a : ℕ}
    (X0 : Fin a → Fin I.n → I.E)
    (hc : ∀ v, PI.MassDataKppVolLemmas.piV I v h ∈ stabT (Fv I.F v) I.cm.sig I.J X0) :
    h ∈ stabT (Af I.F) I.cm.sig I.J X0 := by
  rw [mem_stabT]
  intro b
  funext i
  rw [← sub_eq_zero]
  apply PI.MassDataKppVolLemmas.LocIdxLift_inj I
  intro v
  have hv := hc v
  rw [mem_stabT] at hv
  have e1 : ratV (F := I.F) (Fv I.F v) (X0 b) =
      (PI.MassDataKppVolLemmas.tV I v) ∘ ratV (F := I.F) (Af I.F) (X0 b) := by
    funext j
    simp [ratV, PI.MassDataKppVolLemmas.tV, tensMap_inclR]
  have h2 := congrFun (hv b) i
  rw [map_sub]
  show PI.MassDataKppVolLemmas.tV I v ((((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) *ᵥ ratV (F := I.F) (Af I.F) (X0 b)) i) -
    PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = 0
  rw [RingHom.map_mulVec, ← e1]
  have e2 : ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (PI.MassDataKppVolLemmas.tV I v) =
      ((HA.mat (Fv I.F v) I.cm.sig I.J (PI.MassDataKppVolLemmas.piV I v h) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) := rfl
  rw [e2]
  have e3 : PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = ratV (F := I.F) (Fv I.F v) (X0 b) i := by
    rw [e1]; rfl
  rw [e3, sub_eq_zero]
  exact h2

variable {D : D7}

theorem level_components_surjective : SurjH := by
  classical
  intro D X hb _hK u _hT _hL f
  have key : ∀ S : Finset (TypX X), ∃ z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
      z ∈ KHg X u ∧ ∀ p : TypX X, ((piH X u p.1 z : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        if p ∈ S then (((f p : KvH X u p.1) : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hzK, hz⟩ := ih
      set k : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J :=
        (((f q : KvH X u q.1) : Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) with hk
      have hkK : k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := (f q).2
      have hkH : k ∈ Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (f q : KvH X u q.1).1.2
      obtain ⟨h, hKf, hq1, hq2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I q.1 k hkK
      have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
        apply mem_stabT_of_comp X.B.I h
        intro v
        by_cases hv : v = q.1
        · subst hv; rw [hq1]; exact hkH
        · rw [hq2 v hv]; exact one_mem _
      refine ⟨⟨h, hH⟩ * z, ?_, fun p => ?_⟩
      · show (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
          Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
        exact mul_mem hKf hzK
      · rw [map_mul, Subgroup.coe_mul, hz p]
        show PI.MassDataKppVolLemmas.piV X.B.I p.1 h * _ = _
        by_cases hpq : p = q
        · subst hpq
          rw [if_neg hq, if_pos (Finset.mem_insert_self p S), mul_one, hq1]
        · have hp1 : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
          rw [hq2 p.1 hp1, one_mul]
          by_cases hpS : p ∈ S
          · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
          · rw [if_neg hpS, if_neg]
            intro hm
            rcases Finset.mem_insert.1 hm with e | e
            · exact hpq e
            · exact hpS e
  obtain ⟨z, hzK, hz⟩ := key Finset.univ
  refine ⟨z, hzK, fun p => Subtype.ext (Subtype.ext ?_)⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

end PIW.MassDataColumns
end
end

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) (Λ : Set (Fin n → E))

theorem kgv_conj (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (a y : HA (Fv F v) σ J) (ha : a ∈ Kv σ J Λ v)
    (hy : y ∈ Kgv σ J Λ g v) : a⁻¹ * y * a ∈ Kgv σ J Λ g v := by
  unfold Kgv Kv Kloc at *
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Set.mem_setOf_eq] at ha hy1 ⊢
  have hm : HA.mat (Fv F v) σ J (a⁻¹ * y * a) =
      (HA.mat (Fv F v) σ J a)⁻¹ * HA.mat (Fv F v) σ J y * HA.mat (Fv F v) σ J a := rfl
  rw [hm]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hy1) ha, fun y0 hy0 => ?_⟩
  set A := HA.mat (Fv F v) σ J a
  set Y := HA.mat (Fv F v) σ J y
  have ha' : ∀ x, x ∈ latLoc v Λ ↔ (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ latLoc v Λ := ha
  obtain ⟨z1, hz1, hz1e⟩ := hy2 ((A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y0) ((ha' y0).mp hy0)
  refine ⟨((A⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z1, ?_, ?_⟩
  · rw [ha', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hz1
  · have key : ((A⁻¹ * Y * A : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1 =
        ((A⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) * (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz1e, Matrix.mulVec_smul]

end Gen

theorem isUnit_natCast_of_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : (m : 𝓞 F) ∉ v.asIdeal) : IsUnit ((m : v.adicCompletionIntegers F)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← map_natCast (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) m,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v _)
    (not_lt.1 fun h => hm ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v _).1 h))

variable {D : D7}

theorem g_eq_gOf_mul_unit (X : HidaSetting D) (p : TypX X) :
    ∃ w : (p.1.adicCompletionIntegers X.B.I.F)ˣ,
      ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) =
        ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) * (w : p.1.adicCompletionIntegers X.B.I.F) := by
  have hg := X.g_eq
  have hp0 := D.host.g_prime 0
  have hp1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold Formalism.L2.SG.TypedSets.gOf
  split_ifs with h0
  · have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal := by
      intro h1
      have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) := by
        have h := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp0 hp1).2 hne)
        simpa using h.map (Int.castRingHom (𝓞 X.B.I.F))
      obtain ⟨a, b, hab⟩ := hcop
      have h1mem : (1 : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
        rw [← hab]
        exact p.1.asIdeal.add_mem (p.1.asIdeal.mul_mem_left a h0) (p.1.asIdeal.mul_mem_left b h1)
      exact p.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1mem)
    refine ⟨(isUnit_natCast_of_not_mem p.1 _ h1).unit, ?_⟩
    rw [IsUnit.unit_spec, hg, Nat.cast_mul]
  · refine ⟨(isUnit_natCast_of_not_mem p.1 _ h0).unit, ?_⟩
    rw [IsUnit.unit_spec, hg, Nat.cast_mul, mul_comm]

theorem kgv_of_gOf (X : HidaSetting D) (p : TypX X) (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
    (hy : y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1) :
    y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) X.B.g p.1 := by
  obtain ⟨w, hw⟩ := g_eq_gOf_mul_unit X p
  simp only [Formalism.L2.SG.TypedSets.Kgv, Set.mem_setOf_eq] at hy ⊢
  obtain ⟨hKv, h⟩ := hy
  refine ⟨hKv, fun y' hy' => ?_⟩
  obtain ⟨z, hz, e⟩ := h y' hy'
  refine ⟨((w⁻¹ : (p.1.adicCompletionIntegers X.B.I.F)ˣ) : p.1.adicCompletionIntegers X.B.I.F) • z,
    Submodule.smul_mem _ _ hz, ?_⟩
  rw [e, smul_smul, hw, mul_assoc, Units.mul_inv, mul_one]

theorem mem_conjugate_level_of_local (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (hz : z ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hloc : ∀ p : TypX X, ∃ k ∈ X.K2, PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb k) =
      PI.MassDataKppVolLemmas.piV X.B.I p.1 ((finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u))) :
    z ∈ K2u X hb u := by
  classical
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  obtain ⟨y, hy⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u))
  have hyK : y ∈ X.B.I.Kset := by
    rw [← PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb, hy]
    exact mul_mem (mul_mem (inv_mem ha) hz) ha
  have hgc := PI.MassDataKppVolLemmas.Cst_gc X.B.I (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
    (D.host.g_prime 1).ne_zero
  rw [← X.g_eq] at hgc
  have hy2 : y ∈ X.K2 := by
    refine PI.MassDataKppVolLemmas.LocK_mem X.B.I X.K2 hK.1 hK.2.1 X.B.g (fun x hx => (hL.1 x hx).1) Finset.univ
      (fun p : TypX X => PI.MassDataKppVolLemmas.chi X.B.I p.1) (fun p => PI.MassDataKppVolLemmas.Comp_chi_idem X.B.I p.1)
      (fun p q hpq => PI.MassDataKppVolLemmas.Comp_chi_orth X.B.I p.1 q.1 fun h => hpq (Subtype.ext h))
      (PI.MassDataKppVolLemmas.cElt X.B.I (D.host.g 0) (D.host.g 1)) (PI.MassDataKppVolLemmas.Cst_int X.B.I _ _) hgc y hyK ?_
    intro p _
    obtain ⟨k, hk, hkz⟩ := hloc p
    rw [PI.MassDataKppVolLemmas.Comp_sep X.B.I hb p.1 y k (by rw [hy]; exact hkz.symm)]
    exact PI.MassDataKppVolLemmas.LocB_K2set X.B.I _ _ _ _ _ (PI.MassDataKppVolLemmas.Comp_chi_idem X.B.I p.1)
      (PI.MassDataKppVolLemmas.Comp_chi_int X.B.I p.1) k hk
  rw [mem_conjugate_level_iff]
  refine ⟨y, hy2, ?_⟩
  have e : finHA X hb y = (finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u) := hy
  rw [e]
  group

theorem level_membership_local : LocH := by
  intro D X hb hK u hMT hL z hz hloc
  have hc := coe_K2Hg X hb hK u
  have hmem : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
    refine mem_conjugate_level_of_local X hb hK hL u z (Subgroup.mem_subgroupOf.mp hz) ?_
    intro p
    obtain ⟨w, hw, hwe⟩ := hloc p
    have hw' : (w : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
      have h2 : w ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := hw
      rw [hc] at h2
      exact h2
    obtain ⟨_, ⟨k, hk, rfl⟩, hwk⟩ := hw'
    refine ⟨k, hk, ?_⟩
    have hv : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F ↑p) (w : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F ↑p) (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
      congrArg Subtype.val hwe
    unfold PI.MassDataKppVolLemmas.piV
    simp only [map_mul, map_inv, ← hv, ← hwk]
    group
  have h3 : z ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := by
    rw [hc]
    exact hmem
  exact h3

theorem hKerIn_of_levelSubgroupCharacter_of_normalized (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) : HKerIn X hb u p := by
  intro x hx
  set y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
    with hy_def
  have hyK : y ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
  have hyg : y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1 := hx
  obtain ⟨h, hKf, h1, h2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I p.1 y hyK
  have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
    apply mem_stabT_of_comp X.B.I h
    intro v
    by_cases hv : v = p.1
    · subst hv; rw [h1]; exact (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
    · rw [h2 v hv]; exact one_mem _
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  have hK2u : h ∈ K2u X hb u := by
    apply mem_conjugate_level_of_local X hb hK hL u h hKf
    intro q
    by_cases hq : q = p
    · subst hq
      have hap : PI.MassDataKppVolLemmas.piV X.B.I q.1 (finHA X hb (X.xu u)) ∈
          Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := by
        have := ha
        rw [Kf, Subgroup.mem_iInf] at this
        exact this q.1
      have hmem : PI.MassDataKppVolLemmas.piV X.B.I q.1 ((finHA X hb (X.xu u))⁻¹ * h * finHA X hb (X.xu u)) ∈
          Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) X.B.g q.1 := by
        rw [map_mul, map_mul, map_inv, h1]
        exact kgv_of_gOf X q _ (kgv_conj X.B.I.cm.sig X.B.I.J _ q.1 (gOf q) _ _ hap hyg)
      have hg0 : X.B.g ≠ 0 := by
        rw [X.g_eq]; exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      obtain ⟨k, hk, hkc⟩ := PI.MassDataKppVolLemmas.LocIdxLift_Kg X.B.I hb q.1 X.B.g hg0 _ hmem
      exact ⟨k, (hL.1 k hk).1, hkc⟩
    · refine ⟨1, hK.1, ?_⟩
      have hq1 : q.1 ≠ p.1 := fun e => hq (Subtype.ext e)
      rw [finHA_one, map_one, map_mul, map_mul, map_inv, h2 q.1 hq1, mul_one, inv_mul_cancel]
  rw [Subgroup.mem_subgroupOf]
  refine ⟨⟨h, hH⟩, ?_, ?_⟩
  · apply Subgroup.subset_closure
    exact hK2u
  · apply Subtype.ext
    exact h1

end PIW.MassDataColumns
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxDone
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem global_index_eq_prod_local : IdxProdH := idxProdH_of level_components_surjective level_membership_local

def LocRedRest : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HImU X hb u p

theorem locRedH_of_rest (h : LocRedRest) : LocRedH :=
  locRedH_of fun X hb hK u hT hL p =>
    ⟨(h X hb hK u hT hL p).1, (h X hb hK u hT hL p).2.1, hKerIn_of_levelSubgroupCharacter_of_normalized X hb hK hL u p, (h X hb hK u hT hL p).2.2⟩

theorem idxCountStep_of_rest (h : LocRedRest) : IdxCountStep :=
  idxCountStep_of global_index_eq_prod_local (locRedH_of_rest h)

end PIW.MassDataColumns
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.MemK2HpIffCong
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

variable {D : D7}

abbrev xuP (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
  PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u))

theorem mem_K2Hp_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      (xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p ∈ MassDataIdxSteps.KppX X hb p := by
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hy' : (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
      have : y ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := hy
      rw [coe_K2Hg X hb hK u] at this
      exact this
    obtain ⟨k, hk, e⟩ := (mem_conjugate_level_iff X hb u _).1 hy'
    refine ⟨finHA X hb k, ⟨k, hk, rfl⟩, ?_⟩
    have hxy : ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        PI.MassDataKppVolLemmas.piV X.B.I p.1 (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
      rw [← hyx]
      rfl
    rw [hxy, ← e]
    show PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb k) = _
    simp only [map_mul, map_inv]
    group
  · intro hx
    obtain ⟨k', ⟨k, hk, rfl⟩, hke⟩ := hx
    set y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
      ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
      with hy_def
    have hyK : y ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
    obtain ⟨h, hKf, h1, h2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I p.1 y hyK
    have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
      apply mem_stabT_of_comp X.B.I h
      intro v
      by_cases hv : v = p.1
      · subst hv; rw [h1]; exact (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
      · rw [h2 v hv]; exact one_mem _
    have hK2u : h ∈ K2u X hb u := by
      apply mem_conjugate_level_of_local X hb hK hL u h hKf
      intro q
      by_cases hq : q = p
      · subst hq
        refine ⟨k, hk, ?_⟩
        rw [map_mul, map_mul, map_inv, h1]
        exact hke
      · refine ⟨1, hK.1, ?_⟩
        have hq1 : q.1 ≠ p.1 := fun e => hq (Subtype.ext e)
        rw [finHA_one, map_one, map_mul, map_mul, map_inv, h2 q.1 hq1, mul_one, inv_mul_cancel]
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⟨h, hH⟩, ?_, ?_⟩
    · apply Subgroup.subset_closure
      exact hK2u
    · apply Subtype.ext
      exact h1

theorem unipotent_mem_localStabilizer (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    xuP X hb u p ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := by
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  rw [Kf, Subgroup.mem_iInf] at ha
  exact ha p.1

theorem mem_K2Hp_iff_cong (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (x : KvH X u p.1) :
    x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      MassDataIdxSteps.LocCong X p ((xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p) := by
  rw [mem_K2Hp_iff X hb hK hL u p x, MassDataIdxSteps.stImAloc_holds X hb p]
  have hxK : ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
  have hA := unipotent_mem_localStabilizer X hb u p
  have hA' : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (xuP X hb u p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hA
  have hX' : HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J
      ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hxK
  have hmem : (xuP X hb u p)⁻¹ * ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
      HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) * xuP X hb u p ∈ MassDataIdxSteps.KvX X p := by
    show HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J _ ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    exact mul_mem (mul_mem (inv_mem hA') hX') hA'
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hmem, h⟩

end PIW.MassDataColumns
end
end
