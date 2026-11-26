module

public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeRhamEllipticIdentity
theorem UpperTheory.Reformulated.B.InvariantSumOfTranslates.main :
    ∀ {K S : Type} [inst : Group K] [inst_1 : TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [inst_4 : AddCommGroup S] [inst_5 : _root_.Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S),
      (∃ U ∈ nhds (1 : K), ∀ k ∈ U, ((ω : K → Module.End ℂ S) k : S → S) f₀ = f₀) →
        ∃ (m : ℕ) (k : Fin (m + (1 : ℕ)) → K),
          ∀ (g : K),
            ((ω : K → Module.End ℂ S) g : S → S) (∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀) =
              ∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀ := by
  intro K S _ _ _ _ _ _ ω f₀ h
  obtain ⟨U, hU, hfix⟩ := h
  have hmul : ∀ (a b : K) (v : S), ω (a * b) v = ω a (ω b v) := by
    intro a b v
    rw [map_mul, Module.End.mul_apply]

  let H : Subgroup K :=
    { carrier := {k | ω k f₀ = f₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ω a⁻¹ (ω a f₀) = f₀ := by
          rw [← hmul]; simp
        rwa [ha] at h1 }
  have hmem : ∀ k, k ∈ H ↔ ω k f₀ = f₀ := fun k => Iff.rfl
  have hopen : IsOpen (H : Set K) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hU (fun k hk => hfix k hk))
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _

  let F : K ⧸ H → S := fun q => ω q.out f₀
  have hF : ∀ (g : K) (q : K ⧸ H), ω g (F q) = F (g • q) := by
    intro g q
    have hq : ((g * q.out : K) : K ⧸ H) = g • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hq' : (((g • q).out : K) : K ⧸ H) = ((g * q.out : K) : K ⧸ H) := by
      rw [hq, QuotientGroup.out_eq']
    have hh : ((g • q).out)⁻¹ * (g * q.out) ∈ H := QuotientGroup.eq.mp hq'
    have h2 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    change ω g (ω q.out f₀) = ω (g • q).out f₀
    rw [← hmul, h2, hmul, (hmem _).mp hh]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (K ⧸ H) = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ K ⧸ H := (Fintype.equivFinOfCardEq hm).symm
  refine ⟨m, fun i => (e i).out, fun g => ?_⟩
  have hsum : ∑ i : Fin (m + 1), ω (e i).out f₀ = ∑ q, F q := Equiv.sum_comp e F
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  simp_rw [hF]
  exact Equiv.sum_comp (MulAction.toPerm g) F
end

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem exists_fixed_sum {K S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [AddCommGroup S] [Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S)
    (hU : ∃ U ∈ 𝓝 (1 : K), ∀ k ∈ U, ω k f₀ = f₀) :
    ∃ (m : ℕ) (k : Fin (m + 1) → K), ∀ g, ω g (∑ i, ω (k i) f₀) = ∑ i, ω (k i) f₀ :=
  _root_.UpperTheory.Reformulated.B.InvariantSumOfTranslates.main ω f₀ hU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulX (L : IsLocRep M ψ om v ω ρ) {g g' : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v))
    (hg' : g' ∈ UAt σ X (evFin F v)) {φ} (hφ : φ ∈ SB _) : ω (g * g', 1) φ = ω (g, 1) (ω (g', 1) φ) := by
  simpa using L.mul g hg 1 (one_mem_UAt W v) g' hg' 1 (one_mem_UAt W v) φ hφ

def IsLocRep.onKX (L : IsLocRep M ψ om v ω ρ) : KSub σ X v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (k.1, 1)).restrict fun φ hφ => L.pres k.1 k.2.1 1 (one_mem_UAt W v) φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext ((IsLocRep.mulX L) a.2.1 b.2.1 φ.2)

theorem IsLocRep.onKX_apply (L : IsLocRep M ψ om v ω ρ) (k : KSub σ X v) (φ : SB (Fin n × Fin d → Fv F v)) :
    ((IsLocRep.onKX L) k φ).1 = ω (k.1, 1) φ.1 := rfl

theorem IsLocRep.onK_apply (L : IsLocRep M ψ om v ω ρ) (k : KSub σ W v) (φ : SB (Fin n × Fin d → Fv F v)) :
    (L.onK k φ).1 = ω (1, k.1) φ.1 := rfl

theorem IsLocRep.sub_mem_aug (L : IsLocRep M ψ om v ω ρ) {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {φ}
    (hφ : φ ∈ SB _) : ω (g, 1) φ - φ ∈ augAt om v :=
  Submodule.subset_span ⟨g, hg, φ, hφ, _, L.pres g hg 1 (one_mem_UAt W v) φ hφ,
    (L.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl, rfl⟩

theorem IsLocRep.smoothX (L : IsLocRep M ψ om v ω ρ) {ψ' : AddChar (AF F) ℂ} {χX χW : Chr F E}
    (hw : M.IsWeil ψ' χX χW om) :
    ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ U, g ∈ UAt σ X (evFin F v) → ω (g, 1) φ = φ := by
  intro φ hφ
  have hs := IsUWeilPair.isUSplitting hw
  obtain ⟨r₀, x₀, h₀, h₁⟩ := PositivityTheory.ThKH.Locrep.exists_base (Fin n × Fin d) v
  let loc : UA σ X.J → Module.End ℂ (Fn F n d v) := fun g =>
    PositivityTheory.ThKH.Locrep.res v x₀ ∘ₗ om (g, 1) ∘ₗ PositivityTheory.ThKH.Locrep.tensL v r₀
  have key : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, loc g φ = ω (g, 1) φ := fun g hg φ hφ =>
    (PositivityTheory.ThKH.Locrep.eq_of_acts v h₁ (h₀ φ hφ) ((L.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := PositivityTheory.ThKH.Locrep.exists_small_subgroups σ X v
  obtain ⟨m, hm⟩ := PositivityTheory.ThKH.Locrep.smooth_of_weak (SB _) K hK1 hK2 loc
    (fun g hg φ hφ => by
      rw [key g (hK3 0 hg) φ hφ]; exact L.pres g (hK3 0 hg) 1 (one_mem_UAt W v) φ hφ)
    (fun φ hφ => by rw [key 1 (one_mem_UAt X v) φ hφ]; exact L.one φ hφ)
    (fun g hg g' hg' φ hφ => by
      rw [key _ (mul_mem_UAt (hK3 0 hg) (hK3 0 hg')) φ hφ, key g' (hK3 0 hg') φ hφ,
        key g (hK3 0 hg) _ (L.pres g' (hK3 0 hg') 1 (one_mem_UAt W v) φ hφ)]
      exact (IsLocRep.mulX L) (hK3 0 hg) (hK3 0 hg') hφ)
    (fun l φ hφ => (hs.cont _ (PositivityTheory.ThKH.Locrep.res_adm v x₀ l) _ (h₀ φ hφ).2).comp
      (continuous_id.prodMk continuous_const)) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  exact ⟨U, hU, fun g hg hv => by rw [← key g hv φ hφ]; exact hm g (hUK g hg hv)⟩

theorem IsLocRep.span_vac (L : IsLocRep M ψ om v ω ρ) (hs : M.vac v ∈ SB _) {z}
    (hz : z ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) :
    ∃ c : ℂ, z - c • M.vac v ∈ augAt om v := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨1, by rw [one_smul]; exact (IsLocRep.sub_mem_aug L) hg hs⟩
  | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    refine ⟨c + c', ?_⟩
    have e : y + z - (c + c') • M.vac v = (y - c • M.vac v) + (z - c' • M.vac v) := by rw [add_smul]; abel
    rw [e]
    exact add_mem hc hc'
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    refine ⟨a * c, ?_⟩
    have e : a • y - (a * c) • M.vac v = a • (y - c • M.vac v) := by rw [smul_sub, smul_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hc

theorem isVacSph_of (L : IsLocRep M ψ om v ω ρ) (H : IsHowe M v ω) (hKX : IsCompact (KAt σ X v))
    (hKW : IsCompact (KAt σ W v)) (hs : M.vac v ∈ SB _)
    (smX : ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ U, g ∈ UAt σ X (evFin F v) → ω (g, 1) φ = φ) :
    IsVacSph M om v ω := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  haveI : IsTopologicalGroup (KSub σ X v) := inferInstance
  haveI : IsTopologicalGroup (KSub σ W v) := inferInstance
  haveI : CompactSpace (KSub σ X v) := isCompact_iff_compactSpace.1 hKX
  haveI : CompactSpace (KSub σ W v) := isCompact_iff_compactSpace.1 hKW
  refine ⟨H.fixW, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨U, hU, hU'⟩ := smX φ hφ
    obtain ⟨m, k, hk⟩ := exists_fixed_sum (IsLocRep.onKX L) ⟨φ, hφ⟩
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, fun k hk => Subtype.ext (hU' k.1 hk k.2.1)⟩
    set f := ∑ i, ω ((k i).1, 1) φ with hf
    have hfS : f ∈ SB _ := sum_mem fun i _ => L.pres _ (k i).2.1 1 (one_mem_UAt W v) φ hφ
    have hfix : ∀ g ∈ KAt σ X v, ω (g, 1) f = f := fun g hg => by
      have := congrArg Subtype.val (hk ⟨g, hg⟩)
      simpa only [(IsLocRep.onKX_apply L), Submodule.coe_sum] using this
    have hgen := H.genW f hfS hfix
    have haug : ((m + 1 : ℕ) : ℂ) • φ - f ∈ augAt om v := by
      have e : ((m + 1 : ℕ) : ℂ) • φ - f = ∑ i : Fin (m + 1), -(ω ((k i).1, 1) φ - φ) := by
        rw [hf, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, neg_sub]
      rw [e]
      exact sum_mem fun i _ => neg_mem ((IsLocRep.sub_mem_aug L) (k i).2.1 hφ)
    have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    refine Submodule.mem_sup.2 ⟨_, Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) haug, _,
      Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) hgen, ?_⟩
    rw [← smul_add, sub_add_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · obtain ⟨U, hU, hU'⟩ := L.smooth φ hφ
    obtain ⟨m, k, hk⟩ := exists_fixed_sum L.onK ⟨φ, hφ⟩
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, fun k hk => Subtype.ext (hU' k.1 hk k.2.1)⟩
    set f := ∑ i, ω (1, (k i).1) φ with hf
    have hfS : f ∈ SB _ := sum_mem fun i _ => L.pres 1 (one_mem_UAt X v) _ (k i).2.1 φ hφ
    have hfix : ∀ g ∈ KAt σ W v, ω (1, g) f = f := fun g hg => by
      have := congrArg Subtype.val (hk ⟨g, hg⟩)
      simpa only [(IsLocRep.onK_apply L), Submodule.coe_sum] using this
    obtain ⟨c, hc⟩ := (IsLocRep.span_vac L) hs (H.genX f hfS hfix)
    exact ⟨m, fun i => (k i).1, c, fun i => (k i).2, hc⟩

theorem vacInert (h : HoweInert) : VacInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨p, p'⟩ := h F E σ B a a' G X om om' hT v he
  exact ⟨fun ω ρ L => isVacSph_of L (p ω ρ L) (isCompact_KAt G.V hT.geo.hV.lat v) (isCompact_KAt G.W hT.geo.hW.lat v)
      (hT.geo.hM.vac v).1 ((IsLocRep.smoothX L) hT.weil),
    fun ω ρ L => isVacSph_of L (p' ω ρ L) (isCompact_KAt G.V' hT.geo.hV'.lat v) (isCompact_KAt G.W hT.geo.hW.lat v)
      (hT.geo.hM'.vac v).1 ((IsLocRep.smoothX L) hT.weil')⟩

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

section Core

variable {V H : Type} [AddCommGroup V] [Module ℂ V]

def Stab (S A : Submodule ℂ V) (U : Set H) (T : H → Module.End ℂ V) (P : Submodule ℂ V) : Prop :=
  A ≤ P ∧ P ≤ S ∧ ∀ h ∈ U, ∀ x ∈ P, T h x ∈ P

variable {S A : Submodule ℂ V} {U : Set H} {T : H → Module.End ℂ V}

theorem Stab.sup {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') : Stab S A U T (P ⊔ P') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun i hi x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h.2.2 i hi y hy) (h'.2.2 i hi z hz)

theorem Stab.not_mem {s : V} (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s}) {P : Submodule ℂ V}
    (h : Stab S A U T P) (hP : P ≠ S) : s ∉ P := by
  intro hs
  refine hP (le_antisymm h.2.1 fun φ hφ => (sup_le h.1 (Submodule.span_le.2 ?_)) (hgen φ hφ))
  rintro _ ⟨i, hi, rfl⟩
  exact h.2.2 i hi s hs

theorem Stab.sup_ne {s : V} (hs : s ∈ S) (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s})
    (hline : ∀ φ ∈ S, ∃ (m : ℕ) (k : Fin (m + 1) → H) (w : Fin (m + 1) → ℂ) (c : ℂ),
      (∀ i, k i ∈ U ∧ w i • T (k i) s = s) ∧ ∑ i, w i • T (k i) φ - c • s ∈ A)
    {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') (hP : P ≠ S) (hP' : P' ≠ S) : P ⊔ P' ≠ S := by
  intro e
  have hs' : s ∈ P ⊔ P' := e ▸ hs
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨m, k, w, c, hw, hc⟩ := hline x (h.2.1 hx)
  have hxP : ∑ i, w i • T (k i) x ∈ P := P.sum_mem fun i _ => P.smul_mem _ (h.2.2 _ (hw i).1 x hx)
  have hyP : ∑ i, w i • T (k i) y ∈ P' := P'.sum_mem fun i _ => P'.smul_mem _ (h'.2.2 _ (hw i).1 y hy)
  have hsum : ∑ i, w i • T (k i) x + ∑ i, w i • T (k i) y = ((m + 1 : ℕ) : ℂ) • s := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, ← map_add (f := _), hxy, (hw _).2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have h1 : c • s ∈ P := by
    have := P.sub_mem hxP (h.1 hc)
    rwa [sub_sub_cancel] at this
  have h2 : (((m + 1 : ℕ) : ℂ) - c) • s ∈ P' := by
    have e2 : (((m + 1 : ℕ) : ℂ) - c) • s = ∑ i, w i • T (k i) y + (∑ i, w i • T (k i) x - c • s) := by
      rw [sub_smul, ← hsum]; abel
    rw [e2]
    exact P'.add_mem hyP (h'.1 hc)
  by_cases hc0 : c = 0
  · subst hc0
    refine Stab.not_mem hgen h' hP' ?_
    have := P'.smul_mem (((m + 1 : ℕ) : ℂ))⁻¹ h2
    rwa [sub_zero, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m), one_smul] at this
  · refine Stab.not_mem hgen h hP ?_
    have := P.smul_mem c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

end Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

omit [NumberField E] in
theorem one_uat (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]

theorem stab_of (L : IsLocRep M ψ om v ω ρ) {N} (hN : GlobalTheory.Published.ThetaSub om v N) :
    Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N :=
  ⟨hN.1, hN.2.1, fun h hh x hx => hN.2.2 h hh x hx _ (L.pres 1 (one_uat v) h hh x (hN.2.1 hx))
    ((L.acts 1 (one_uat v) h hh x (hN.2.1 hx) _).2 rfl)⟩

theorem thetaSub_of (L : IsLocRep M ψ om v ω ρ) {N}
    (hN : Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N) : GlobalTheory.Published.ThetaSub om v N :=
  ⟨hN.1, hN.2.1, fun h hh φ hφ φ₁ _ hA => by
    rw [(L.acts 1 (one_uat v) h hh φ (hN.2.1 hφ) φ₁).1 hA]
    exact hN.2.2 h hh φ hφ⟩

theorem thetaSub_sup (L : IsLocRep M ψ om v ω ρ) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') : GlobalTheory.Published.ThetaSub om v (N ⊔ N') :=
  thetaSub_of L ((stab_of L hN).sup (stab_of L hN'))

theorem sup_ne_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') (h1 : N ≠ SB _) (h2 : N' ≠ SB _) : N ⊔ N' ≠ SB _ := by
  rcases hs with hs | hs
  · obtain ⟨s, hs⟩ := hs ω ρ L
    exact Stab.sup_ne hs.mem hs.gen hs.line (stab_of L hN) (stab_of L hN') h1 h2
  · have e1 := (hs N hN).resolve_right h1
    have e2 := (hs N' hN').resolve_right h2
    rw [e1, e2, sup_idem]
    rw [e1] at h1
    exact h1

theorem maxAt_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) : PositivityTheory.HoweDualityUnitaryAlt.MaxAt om v := by
  intro N N' hN hN'
  have hq : GlobalTheory.Published.ThetaSub om v (N ⊔ N') ∧ N ⊔ N' ≠ SB _ :=
    ⟨thetaSub_sup L hN.prop.1 hN'.prop.1, sup_ne_of L hs hN.prop.1 hN'.prop.1 hN.prop.2 hN'.prop.2⟩
  exact (hN.eq_of_ge hq le_sup_left).symm.trans (hN'.eq_of_ge hq le_sup_right)

theorem locRep_tri {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G Y om om') (v : Pl F) :
    (∃ ω ρ, IsLocRep G.M B.ψ om v ω ρ) ∧ ∃ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ :=
  ⟨PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V G.W G.M om
      ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, ⟨_, _, hT.weil⟩⟩ v,
    PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V' G.W G.M' om'
      ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', ⟨_, _, hT.weil'⟩⟩ v⟩

theorem maxFinT_of (h : SphTri) : PositivityTheory.HoweDualityUnitaryAlt.MaxFinT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _
  obtain ⟨h1, h2⟩ := h F E σ B a a' G X om om' hT v
  obtain ⟨⟨ω, ρ, L⟩, ⟨ω', ρ', L'⟩⟩ := locRep_tri hT v
  exact ⟨maxAt_of L h1, maxAt_of L' h2⟩

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem relIndex_ne_zero_of_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

section Form

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

def stabK (L : IsLocRep M ψ om v ω ρ) (φ : Fn F n d v) (hφ : φ ∈ SB _) : Subgroup (UA σ W.J) where
  carrier := {k | k ∈ KAt σ W v ∧ ω (1, k) φ = φ}
  one_mem' := ⟨(KSub σ W v).one_mem, L.one φ hφ⟩
  mul_mem' := fun {a b} ha hb => ⟨(KSub σ W v).mul_mem ha.1 hb.1, by rw [L.mulW ha.1.1 hb.1.1 hφ, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨(KSub σ W v).inv_mem ha.1, by
    have e := L.mulW (inv_mem_UAt ha.1.1) ha.1.1 hφ
    rw [inv_mul_cancel, ha.2] at e
    rw [← e]
    exact L.one φ hφ⟩

theorem exists_form (hAvg : AvgSt) (L : IsLocRep M ψ om v ω ρ) (hKc : IsCompact (KAt σ W v))
    (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    (l₀ : Fn F n d v →ₗ[ℂ] ℂ) (h0 : l₀ (M.vac v) ≠ 0)
    (hX : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, l₀ (ω (g, 1) φ) = l₀ φ)
    (hfin : ∀ h ∈ UAt σ W (evFin F v), (conjInf (KSub σ W v) h).relIndex (KSub σ W v) ≠ 0) :
    ∃ l, IsSphForm M om v ω l ∧ ∀ h ∈ UAt σ W (evFin F v),
      l (ω (1, h) (M.vac v)) = avgK (KSub σ W v) (fun g => l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) h := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  have o1 := one_mem_UAt (σ := σ) X v
  have oW := one_mem_UAt (σ := σ) W v
  have stabFin : ∀ φ (hφ : φ ∈ SB _), (stabK L φ hφ).relIndex (KSub σ W v) ≠ 0 := fun φ hφ => by
    obtain ⟨U, hU, hU'⟩ := L.smooth φ hφ
    exact relIndex_ne_zero_of_nhds hKc hU fun k hk hkU => ⟨hk, hU' k hkU hk.1⟩
  obtain ⟨lam, hinv, hfor⟩ := hAvg (UA σ W.J) (Fn F n d v) (KSub σ W v) (SB _) (fun g => ω (1, g)) l₀
    (fun k hk φ hφ => L.pres 1 o1 k hk.1 φ hφ) (fun φ hφ => L.one φ hφ) (fun k hk k' hk' φ hφ => L.mulW hk.1 hk'.1 hφ)
    (fun φ hφ => ⟨stabK L φ hφ, fun k hk => hk.1, stabFin φ hφ, fun k hk => hk.2⟩)
  have haug : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, lam (ω (g, 1) φ) = lam φ := fun g hg φ hφ => by
    have hφ' := L.pres g hg 1 oW φ hφ
    have hHK : stabK L φ hφ ⊓ stabK L _ hφ' ≤ KSub σ W v := fun k hk => hk.1.1
    have hHf := Subgroup.relIndex_inf_ne_zero (stabFin φ hφ) (stabFin _ hφ')
    rw [hfor _ hφ' _ hHK hHf (fun k hk => hk.2.2), hfor _ hφ _ hHK hHf (fun k hk => hk.1.2)]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    have e : ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) (ω (g, 1) φ) =
        ω (g, 1) (ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) φ) := by
      rw [← L.mul 1 o1 _ hk g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 _ hk φ hφ, one_mul, mul_one, mul_one, one_mul]
    change l₀ (ω (1, _) (ω (g, 1) φ)) = l₀ (ω (1, _) φ)
    rw [e, hX g hg _ (L.pres 1 o1 _ hk φ hφ)]
  have hsub : Subsingleton (KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v)) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun a b => QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)⟩
  have hvac : lam (M.vac v) = l₀ (M.vac v) := by
    let q₀ : KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v) := QuotientGroup.mk 1
    rw [hfor _ hs (KSub σ W v) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hfix, Subgroup.relIndex_self,
      Nat.cast_one, inv_one, one_mul, finsum_eq_single _ q₀ fun x hx => absurd (Subsingleton.elim x q₀) hx]
    exact congrArg l₀ (hfix _ (Quotient.out q₀).2)
  refine ⟨(l₀ (M.vac v))⁻¹ • lam, ⟨Submodule.span_le.2 ?_, fun k hk φ hφ => ?_, ?_⟩, fun h hh => ?_⟩
  · rintro _ ⟨g, hg, φ, hφ, φ₁, -, ha, rfl⟩
    rw [(L.acts g hg 1 oW φ hφ φ₁).1 ha]
    change (l₀ (M.vac v))⁻¹ • lam (ω (g, 1) φ - φ) = 0
    rw [map_sub, haug g hg φ hφ, sub_self, smul_zero]
  · change (l₀ (M.vac v))⁻¹ • lam (ω (1, k) φ) = (l₀ (M.vac v))⁻¹ • lam φ
    rw [hinv k hk φ hφ]
  · change (l₀ (M.vac v))⁻¹ • lam (M.vac v) = 1
    rw [hvac, smul_eq_mul, inv_mul_cancel₀ h0]
  · have hfixh : ∀ k ∈ conjInf (KSub σ W v) h, ω (1, k) (ω (1, h) (M.vac v)) = ω (1, h) (M.vac v) := fun k hk => by
      obtain ⟨k₁, hk₁, e⟩ := Subgroup.mem_map.1 hk.2
      have e' : k = h * k₁ * h⁻¹ := by rw [← e]; rfl
      rw [← L.mulW hk.1.1 hh hs, e', show h * k₁ * h⁻¹ * h = h * k₁ by group, L.mulW hh hk₁.1 hs, hfix k₁ hk₁]
    change (l₀ (M.vac v))⁻¹ • lam (ω (1, h) (M.vac v)) = _
    rw [hfor _ (L.pres 1 o1 h hh _ hs) _ inf_le_left (hfin h hh) hfixh, avgK, smul_eq_mul, mul_left_comm, mul_finsum]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    change (l₀ (M.vac v))⁻¹ * l₀ (ω (1, _) (ω (1, h) (M.vac v))) = _
    rw [← L.mulW hk hh hs, div_eq_inv_mul]
    rfl

theorem fn_mul (L : IsLocRep M ψ om v ω ρ) (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    {l₀ : Fn F n d v →ₗ[ℂ] ℂ} {p : UA σ W.J} (hp : p ∈ UAt σ W (evFin F v)) {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) {g k : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hk : k ∈ KAt σ W v) :
    l₀ (ω (1, p * g * k) (M.vac v)) / l₀ (M.vac v) = c * (l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) := by
  rw [L.mulW (mul_mem_UAt hp hg) hk.1 hs, hfix k hk, L.mulW hp hg hs, hc _ (L.pres 1 (one_mem_UAt X v) g hg _ hs),
    mul_div_assoc]

omit [NumberField E] in
theorem fn_val {l₀ : Fn F n d v →ₗ[ℂ] ℂ} (hs : M.vac v ∈ SB _) (h0 : l₀ (M.vac v) ≠ 0) {p : UA σ W.J} {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) : l₀ (ω (1, p) (M.vac v)) / l₀ (M.vac v) = c := by
  rw [hc _ hs, mul_div_assoc, div_self h0, mul_one]

end Form

theorem sphFun_of (hCount : CountSt) (hAvg : AvgSt) (hPInv : PInvSt) (hLift : UnitLiftSt) (hChar : CharSt) (hEv : EvInvSt)
    (hSieg : SiegSt) (hMod : ModSt) (hCart : CartanSt) (hFin : FinSt) : SphFun := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' hK hK'
  haveI : LocallyCompactSpace (Fv F v) :=
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  obtain ⟨w, hw⟩ := inert_of_local F E σ B hT.base v he
  have hv : v ∉ X.T := fun h => he.false (B.τ ⟨v, hT.chars.sub h⟩)
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨m, Cy, hL, hAd, hIw, -⟩ := PositivityTheory.ThKH.Iwas.iwasawa F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩
  obtain ⟨l₀, hl, hl0⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨l₀', hl', hl0'⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨hs, -, -⟩ := hT.geo.hM.vac v
  obtain ⟨hs', -, -⟩ := hT.geo.hM'.vac v
  have hKc : IsCompact (KAt σ G.W v) := stabiliser_compact F E σ _ _ B _ _ _ _ P v
  have hch := hChar F E σ B a a' G X om om' hT v w hw hv
  have hfin := hFin F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw
  have hX := hEv F E σ _ _ B _ _ _ _ _ _ P hT.weil v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω ρ L m Cy hL hAd l₀ hl ⟨_, hs, hl0⟩
  have hX' := hEv F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω' ρ' L' m Cy hL hAd l₀' hl' ⟨_, hs', hl0'⟩
  obtain ⟨l, hlS, hlf⟩ := exists_form hAvg L hKc hK hs l₀ hl0 hX hfin
  obtain ⟨l', hlS', hlf'⟩ := exists_form hAvg L' hKc hK' hs' l₀' hl0' hX' hfin
  refine ⟨l, l', hlS, hlS', fun h hh => ?_⟩
  rw [hlf h hh, hlf' h hh]
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v

  have hval : ∀ p ∈ PSub σ G.W v Cy, ∃ (z : (AE F E)ˣ) (u : (Fv F v)ˣ),
      (∀ φ ∈ SB _, l₀ (ω (1, p) φ) = (X.β z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * l₀ φ) ∧
      (∀ φ ∈ SB _, l₀' (ω' (1, p) φ) = (X.α z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * l₀' φ) ∧
      X.α z * X.β z = 1 ∧
      ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) =
        ((sbClass (Fv F v)).modu u : ℝ) ^ m *
          ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) :=
    fun p hp => by
      have hp0 := hp
      obtain ⟨⟨hpU, t, ht⟩, -⟩ := hp0
      obtain ⟨-, hu⟩ := hPInv F E σ _ G.W v w hw m Cy hL p hp.1
      obtain ⟨z, hz, hzc⟩ := hLift F E v (hu t ht).unit
      refine ⟨z, Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (hu t ht).unit,
        hSieg F E σ _ _ B G.V G.W G.M om _ _ P hT.weil v w hw ω ρ L m Cy hL hAd l₀ hl p hpU t ht z hz hzc _ ?_,
        hSieg F E σ _ _ B G.V' G.W G.M' om' _ _ P' hT.weil' v w hw ω' ρ' L' m Cy hL hAd l₀' hl' p hpU t ht z hz hzc _ ?_,
        (hch z hz).1, hMod F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw m Cy hL hAd p hp t ht _ ?_⟩
      all_goals simp [hzc]
  refine hCount (UA σ G.W.J) (PositivityTheory.ThKH.Iwas.USub σ G.W v) (KSub σ G.W v) (PSub σ G.W v Cy) _ _ (fun k hk => hk.1)
    (fun p hp => hp.1.1) (fun g hg => ?_) (fun g hg => hCart F E σ _ B G.W _ _ hT.base hT.geo.hW hT.geo.even v w hw g hg)
    (fun g hg => hfin g hg) ?_ ?_ (fun p hp g hg k hk => ?_) (fun p hp g hg k hk => ?_) (fun p hp => ?_) h hh
  · obtain ⟨p, hp, k, hk, e⟩ := hIw g hg
    exact ⟨p, ⟨hp, (hPInv F E σ _ G.W v w hw m Cy hL p hp).1⟩, k, hk, e⟩
  · show l₀ (ω 1 (G.M.vac v)) / _ = 1
    rw [L.one _ hs, div_self hl0]
  · show l₀' (ω' 1 (G.M'.vac v)) / _ = 1
    rw [L'.one _ hs', div_self hl0']
  · obtain ⟨z, u, h1, -, -, -⟩ := hval p hp
    rw [fn_mul L hK hs hp.1.1 h1 hg hk, fn_val hs hl0 h1]
  · obtain ⟨z, u, -, h2, -, -⟩ := hval p hp
    rw [fn_mul L' hK' hs' hp.1.1 h2 hg hk, fn_val hs' hl0' h2]
  · obtain ⟨z, u, h1, h2, h3, h4⟩ := hval p hp
    rw [fn_val hs hl0 h1, fn_val hs' hl0' h2]
    have h3' : (X.α z : ℂ) * (X.β z : ℂ) = 1 := by rw [← Circle.coe_mul, h3, Circle.coe_one]
    have hR0 : 0 ≤ ((sbClass (Fv F v)).modu u : ℝ) := NNReal.coe_nonneg _
    have hm : (a : ℝ) / 2 + (a' : ℝ) / 2 = (m : ℝ) := by
      have : ((a : ℝ) + a') = 2 * m := by exact_mod_cast hL.rank
      linarith
    generalize ((sbClass (Fv F v)).modu u : ℝ) = R at hR0 h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₁ at h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₂ at h4 ⊢
    have e : R ^ ((a : ℝ) / 2) * R ^ ((a' : ℝ) / 2) = R ^ m := by
      rw [← Real.rpow_add_of_nonneg hR0 (by positivity) (by positivity), hm, Real.rpow_natCast]
    have h4' : ((n₂ : ℕ) : ℂ) = ((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul, e]
      exact_mod_cast h4
    rw [h4']
    linear_combination (((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ)) * h3'

end PositivityTheory.Sph

end
end
