module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.SharedDedup_Tr_core

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PJointFix
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open GlobalTheory.CuspRep.LocEx
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem fin_comm_loc (π : CuspSub E n) (w : Pl E) {c : GL (Fin n) (Af E)}
    (hc : GeneralLinearGroup.map (pLoc E w) c = 1) (g : GLw n w) (y : π.V) :
    π.finPart c (π.locRep w g y) = π.locRep w g (π.finPart c y) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w hc]

private theorem null_cases (π : CuspSub E n) (w : Pl E) (K : Subgroup (GLw n w)) :
    nullPart (π.locRep w) K = ⊥ ∨ nullPart (π.locRep w) K = ⊤ := by
  have inj := Submodule.map_injective_of_injective π.V.injective_subtype
  have stable : ∀ o, ∀ x ∈ nullPart (π.locRep w) K, π.op o x ∈ nullPart (π.locRep w) K := by
    intro o x hx
    cases o with
    | fin k =>
      have e := map_pLoc_inv_mul w k
      have h1 := nullPart_act (π.locRep w) K (GeneralLinearGroup.map (pLoc E w) k)
        (nullPart_comm (π.locRep w) K (π.finPart ((locGL E n w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k))
          (fun g y => fin_comm_loc π w e g y) hx)
      rwa [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
    | cpt k =>
      refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
      change (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 =
        (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      exact nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) hx
  refine (π.irred ((nullPart (π.locRep w) K).map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp
    (fun e => inj (e.trans (Submodule.map_bot _).symm)) fun e => inj (e.trans (Submodule.map_subtype_top _).symm)
  rintro o _ ⟨x, hx, rfl⟩
  exact ⟨_, stable o x hx, rfl⟩

private theorem step (π : CuspSub E n) (w : Pl E) (B : Multiset ℂˣ) (hB : HasSatGL w (π.locRep w) B)
    (U : Subgroup (GL (Fin n) (Af E))) (hU : ∀ k ∈ U, GeneralLinearGroup.map (pLoc E w) k = 1)
    (ψ : π.V) (h0 : ψ ≠ 0) (hψ : ψ ∈ fixed π.finPart U) :
    ∃ y : π.V, y ≠ 0 ∧ y ∈ fixed π.finPart U ∧ y ∈ fixed (π.locRep w) (KGL w (n := n)) := by
  by_contra hno
  have hsm : IsSmooth (π.locRep w) := fun v =>
    (π.isSmooth_finPart v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)
  have hc : IsCompact (KGL w (n := n) : Set (GLw n w)) := (Asm.unitHecke E n 0 0 w).2.2.2.1
  have hbot : fixed π.finPart U ⊓ fixed (π.locRep w) (KGL w (n := n)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
    by_contra hy0
    exact hno ⟨y, hy0, hy.1, hy.2⟩
  have hst : ∀ g, ∀ v ∈ fixed π.finPart U, π.locRep w g v ∈ fixed π.finPart U := fun g v hv =>
    mem_fix.2 fun k hk => by rw [fin_comm_loc π w (hU k hk), mem_fix.1 hv k hk]
  have hle := le_nullPart hsm hc _ hst hbot
  rcases null_cases π w (KGL w (n := n)) with h | h
  · exact h0 (by simpa [h] using hle hψ)
  · obtain ⟨x, hx0, hxK, -⟩ := hB.exists_vec
    exact hx0 (eq_zero_of_mem_nullPart hsm hc hxK (h ▸ Submodule.mem_top))

private theorem finPart_val (π : CuspSub E n) (g : GL (Fin n) (Af E)) (y : π.V) :
    (π.finPart g y : Sm E n) = finRep E n g y.1 := rfl

private theorem locRep_val (π : CuspSub E n) (w : Pl E) (a : GLw n w) (y : π.V) :
    (π.locRep w a y : Sm E n) = finRep E n (locGL E n w a) y.1 := rfl

private def fixer (y : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {g | finRep E n g y = y}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    rw [Set.mem_setOf_eq] at ha ⊢
    have h : finRep E n a⁻¹ (finRep E n a y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

end SlopeTestRemainingChoices

theorem jointFix_pf : SlotBasic → JointFix := by
  intro _ E _ _ _ n π P
  classical
  induction P using Finset.induction_on with
  | empty =>
    rintro - U - ⟨ψ, h1, h2, h3⟩
    exact ⟨ψ, h1, h2, h3, by simp⟩
  | insert w P hw ih =>
    rintro hsat U hU ⟨ψ, hψ, h0, hfix⟩
    obtain ⟨B, hB⟩ := hsat w (Finset.mem_insert_self _ _)
    obtain ⟨y, hy0, hyU, hyK⟩ := step π w B hB U (fun k hk => hU k hk w (Finset.mem_insert_self _ _)) ⟨ψ, hψ⟩
      (fun e => h0 (congrArg Subtype.val e))
      (mem_fix.2 fun k hk => Subtype.ext ((finPart_val π k ⟨ψ, hψ⟩).trans (hfix k hk)))
    have hU' : ∀ k ∈ U ⊔ (KGL w (n := n)).map (locGL E n w), ∀ v ∈ P, qw n v false k = 1 := by
      intro k hk v hv
      have hvw : v ≠ w := fun e => hw (e ▸ hv)
      have hle : U ⊔ (KGL w (n := n)).map (locGL E n w) ≤ (qw (E := E) n v false).ker := by
        refine sup_le (fun c hc => MonoidHom.mem_ker.2 (hU c hc v (Finset.mem_insert_of_mem hv))) ?_
        rintro _ ⟨a, -, rfl⟩
        exact MonoidHom.mem_ker.2 (pLoc_locGL_of_ne hvw a)
      exact MonoidHom.mem_ker.1 (hle hk)
    have hy' : ∀ k ∈ U ⊔ (KGL w (n := n)).map (locGL E n w), finRep E n k y.1 = y.1 := by
      intro k hk
      have hle : U ⊔ (KGL w (n := n)).map (locGL E n w) ≤ fixer y.1 := by
        refine sup_le (fun c hc => ?_) ?_
        · exact (finPart_val π c y).symm.trans (congrArg Subtype.val (mem_fix.1 hyU c hc))
        · rintro _ ⟨a, ha, rfl⟩
          exact (locRep_val π w a y).symm.trans (congrArg Subtype.val (mem_fix.1 hyK a ha))
      exact hle hk
    obtain ⟨φ, hφ, hφ0, hφU, hφP⟩ := ih (fun v hv => hsat v (Finset.mem_insert_of_mem hv)) _ hU'
      ⟨y.1, y.2, fun e => hy0 (Subtype.ext e), hy'⟩
    refine ⟨φ, hφ, hφ0, fun k hk => hφU k (Subgroup.mem_sup_left hk), fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact mem_fix.2 fun a ha => hφU _ (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)
    · exact hφP v hv

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSeenTr
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

private theorem hint_fst {G P : Type} [Group G] [Group P] [Subsingleton P] (K N : Subgroup G) (K' : Subgroup P)
    (u : G × P → ℂ) (hNK : N ≤ K) (hu : ∀ k ∈ N, ∀ x, u (x * k, 1) = u (x, 1)) (hi : N.relIndex K ≠ 0) :
    hint (K.prod K') u = ((N.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ N, u (q.out, 1) := by
  have hp : ∀ z : G × P, z = (z.1, 1) := fun z => Prod.ext rfl (Subsingleton.elim _ _)
  set L : Subgroup (G × P) := N.comap (MonoidHom.fst G P) with hL
  have hmap : (K.prod K').map (MonoidHom.fst G P) = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      exact ⟨(x, 1), ⟨hx, K'.one_mem⟩, rfl⟩
  have hrel : L.relIndex (K.prod K') = N.relIndex K := by
    rw [hL, Subgroup.relIndex_comap, hmap]
  have hLK : L ≤ K.prod K' := fun z hz => by
    rw [hp z]
    exact ⟨hNK hz, K'.one_mem⟩
  have hLu : L ≤ rStab u := fun k hk x => by
    have h1 : x * k = (x.1 * k.1, 1) := Prod.ext rfl (Subsingleton.elim _ _)
    rw [h1, hu k.1 hk x.1, ← hp x]
  rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ _ L u hLK hLu (by rwa [hrel]), hrel]
  congr 1
  have hval : ∀ q : G ⧸ N, u (Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) = u (q.out, 1) := by
    intro q
    have hm : ((q.out, (1 : P)))⁻¹ * Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) ∈ L :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    obtain ⟨k, hk⟩ : ∃ k : G × P, k ∈ L ∧ Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) = (q.out, 1) * k :=
      ⟨_, hm, (mul_inv_cancel_left _ _).symm⟩
    rw [hk.2]
    exact hLu hk.1 _
  have hbij : Function.Bijective (fun q : G ⧸ N => (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) := by
    constructor
    · intro a b hab
      have h := QuotientGroup.eq.mp hab
      have h2 : (a.out)⁻¹ * b.out ∈ N := by simpa [hL] using h
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      exact QuotientGroup.eq.mpr h2
    · intro c
      induction c using QuotientGroup.induction_on with
      | H z =>
        refine ⟨QuotientGroup.mk z.1, QuotientGroup.eq.mpr ?_⟩
        have h3 : ((QuotientGroup.mk z.1 : G ⧸ N).out)⁻¹ * z.1 ∈ N :=
          QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
        simpa [hL] using h3
  rw [← finsum_comp _ hbij]
  exact finsum_congr hval

private theorem tr_core (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := _root_.DedupShared.dedup_tr_core_6 (G := G) (V := V) hTr hCv ρ K N hKo hKc hNo hNc hNK hi hfd f₁ f₂ F h₁ h₂ hFeq

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.seenTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SeenTr := by
  intro hTr hAdm hCv E _ _ _ n w hw τ N hNo hNK
  obtain ⟨-, -, hKo, hKc, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w
  have hNc : IsCompact (N : Set (GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  haveI : Finite ((KGL w (n := n) : Subgroup (GLw n w)) ⧸ N.subgroupOf (KGL w (n := n))) :=
    GlobalTheory.TwTrLevel.finite_quot (KGL w (n := n)) (KGL w (n := n)) N hKc hKo hNo le_rfl
  have hi : N.relIndex (KGL w (n := n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiC : ((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  refine ⟨((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2, pow_ne_zero _ hiC, ?_⟩
  intro φ₁ φ₂ hb
  refine tr_core hTr hCv τ.ρ (KGL w (n := n)) N hKo hKc hNo hNc hNK hiC (hAdm E n w τ N hNo) _ _ _ (hb false) (hb true) ?_
  funext g
  have h₁ := hb false
  have h₂ := hb true
  have hr : ∀ k ∈ N, ∀ x : GLw n w, two φ₁ φ₂ w false (x * k) * two φ₁ φ₂ w true ((x * k)⁻¹ * g) =
      two φ₁ φ₂ w false x * two φ₁ φ₂ w true (x⁻¹ * g) := by
    intro k hk x
    have e : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    rw [e, (h₁.2 k hk x).2, (h₂.2 k⁻¹ (N.inv_mem hk) _).1]
  have hcv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N (two φ₁ φ₂ w false) (two φ₁ φ₂ w true) g =
      ∑ᶠ q : GLw n w ⧸ N, two φ₁ φ₂ w false q.out * two φ₁ φ₂ w true (q.out⁻¹ * g) := by
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
    rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ N N _ le_rfl (fun k hk x => hr k hk x) (by simp)]
    simp
  have hpr : ∀ x : GLw n w, ((x, 1) : GLw n w × GLw 0 w)⁻¹ * (g, 1) = (x⁻¹ * g, 1) := fun x =>
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [hcv]
  unfold PositivityTheory.Rg.BcB.G8.seen
  rw [if_pos hw]
  rw [hint_fst (KGL w (n := n)) N (KGL w (n := 0)) _ hNK ?_ hi]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [hpr]
    rfl
  · intro k hk x
    rw [hpr, hpr]
    exact hr k hk x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ExistsOpen
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt

section Abs

variable {G W V : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]

private theorem rep_ne [Nontrivial V] (ρ : Representation ℂ G V) (g : G) : ρ g ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h1 : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  exact hx (by rw [← h1, h]; simp)

private theorem supp_eq [Nontrivial V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) :
    Function.support (fun q : G ⧸ K => f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) =
      Function.support fun q : G ⧸ K => f q.out := by
  ext q
  have := rep_ne ρ q.out
  simp only [Function.mem_support, LinearMap.comp_id, ne_eq, smul_eq_zero, this, or_false]

private theorem lv_inter [Nontrivial W] [Nontrivial V] (σ : Representation ℂ G W) (ρ : Representation ℂ G V)
    (T : W →ₗ[ℂ] V) (hT : ∀ g v, T (σ g v) = ρ g (T v)) (K : Subgroup G) (f : G → ℂ) (x : W) :
    T (Lv σ K f x) = Lv ρ K f (T x) := by
  unfold Lv GlobalTheory.BCT.levOp
  simp only [LinearMap.smul_apply, map_smul]
  congr 1
  by_cases hfin : (Function.support fun q : G ⧸ K => f q.out).Finite
  · rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp),
      finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [supp_eq]; simp)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [LinearMap.sum_apply, map_sum, hT]
  · rw [finsum_of_infinite_support (by rwa [supp_eq]), finsum_of_infinite_support (by rwa [supp_eq])]
    simp

private theorem lift_inter [Nontrivial W] [Nontrivial V] (σ : Representation ℂ G W) (ρ : Representation ℂ G V)
    (T : W →ₗ[ℂ] V) (hT : ∀ g v, T (σ g v) = ρ g (T v)) (K : Subgroup G) (p : FreeAlgebra ℂ (G → ℂ)) :
    ∀ x : W, T (FreeAlgebra.lift ℂ (Lv σ K) p x) = FreeAlgebra.lift ℂ (Lv ρ K) p (T x) := by
  induction p using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Algebra.algebraMap_eq_smul_one]
  | grade1 f => intro x; simp [lv_inter σ ρ T hT]
  | mul a b ha hb => intro x; simp [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp [map_add (f := _), LinearMap.add_apply, ha, hb]

private def isoM (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (H : Subgroup G) : Submodule ℂ V :=
  ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, (fixed σ H).map f.1

private theorem isoM_mono (σ : Representation ℂ G W) (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H' ≤ H) :
    isoM σ ρ H ≤ isoM σ ρ H' :=
  iSup_mono fun _ => Submodule.map_mono fun _ hx => LocEx.mem_fix.2 fun k hk => LocEx.mem_fix.1 hx k (h hk)

private theorem exists_open [TopologicalSpace G] [IsTopologicalGroup G] (σ : Representation ℂ G W)
    (ρ : Representation ℂ G V) (hσ : IsSmooth σ) {y : V}
    (hy : y ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ∃ H : Subgroup G, IsOpen (H : Set G) ∧ y ∈ isoM σ ρ H := by
  induction hy using Submodule.iSup_induction' with
  | mem f y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine ⟨LocEx.stab σ v, hσ v, Submodule.mem_iSup_of_mem f ⟨v, LocEx.mem_fix.2 fun k hk => hk, rfl⟩⟩
  | zero => exact ⟨⊤, isOpen_univ, zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨H, hH, ha⟩ := ha
    obtain ⟨H', hH', hb⟩ := hb
    exact ⟨H ⊓ H', hH.inter hH', add_mem (isoM_mono σ ρ inf_le_left ha) (isoM_mono σ ρ inf_le_right hb)⟩

private theorem out_act (σ : Representation ℂ G W) (N H : Subgroup G) {x : W} (hx : x ∈ fixed σ H) (c : N) :
    σ ((QuotientGroup.mk c : N ⧸ H.subgroupOf N).out : N).1 x = σ c.1 x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf N) c
  rw [hh]
  have h1 : ((h : N) : G) ∈ H := Subgroup.mem_subgroupOf.1 h.2
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LocEx.mem_fix.1 hx _ h1]

private def cs {U : Type} [AddCommGroup U] [Module ℂ U] (r : Representation ℂ G U) (N H : Subgroup G)
    [Fintype (N ⧸ H.subgroupOf N)] : Module.End ℂ U :=
  ∑ q : N ⧸ H.subgroupOf N, r (q.out : N).1

private theorem cs_fixed (σ : Representation ℂ G W) (N H : Subgroup G) [Fintype (N ⧸ H.subgroupOf N)] {x : W}
    (hx : x ∈ fixed σ H) : cs σ N H x ∈ fixed σ N := by
  refine LocEx.mem_fix.2 fun n hn => ?_
  have key : ∀ q : N ⧸ H.subgroupOf N, σ n (σ (q.out : N).1 x) =
      σ (((⟨n, hn⟩ : N) • q).out : N).1 x := fun q => by
    have e : ((⟨n, hn⟩ : N) • q) = QuotientGroup.mk ((⟨n, hn⟩ : N) * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e, out_act σ N H hx]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cs, LinearMap.sum_apply, map_sum, key]
  exact Equiv.sum_comp (MulAction.toPerm (⟨n, hn⟩ : N)) fun q : N ⧸ H.subgroupOf N => σ (q.out : N).1 x

private theorem avg_mem (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (N H : Subgroup G)
    [Fintype (N ⧸ H.subgroupOf N)] {y : V} (hy : y ∈ isoM σ ρ H) (hf : y ∈ fixed ρ N) : y ∈ isoM σ ρ N := by
  have h1 : cs ρ N H y ∈ isoM σ ρ N := by
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : isoM σ ρ H ≤ (isoM σ ρ N).comap (cs ρ N H)) hy)
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_iSup_of_mem f ⟨cs σ N H x, cs_fixed σ N H hx, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cs, LinearMap.sum_apply, map_sum, f.2]
  have h2 : cs ρ N H y = (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) • y := by
    simp only [cs, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => LocEx.mem_fix.1 hf _ (q.out : N).2]
    simp [Nat.cast_smul_eq_nsmul]
  have h3 : (Fintype.card (N ⧸ H.subgroupOf N) : ℂ) ≠ 0 := by
    haveI : Nonempty (N ⧸ H.subgroupOf N) := ⟨QuotientGroup.mk 1⟩
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [h2] at h1
  exact (Submodule.smul_mem_iff _ h3).1 h1

private theorem iso_abs [TopologicalSpace G] [IsTopologicalGroup G] [Nontrivial W] [Nontrivial V]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (hσ : IsSmooth σ) (N : Subgroup G)
    (hNc : IsCompact (N : Set G))
    (hI : ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤)
    (p : FreeAlgebra ℂ (G → ℂ)) (hp : ∀ x ∈ fixed σ N, FreeAlgebra.lift ℂ (Lv σ N) p x = 0)
    (y : V) (hy : y ∈ fixed ρ N) : FreeAlgebra.lift ℂ (Lv ρ N) p y = 0 := by
  obtain ⟨H, hH, hyH⟩ := exists_open σ ρ hσ (hI ▸ Submodule.mem_top : y ∈ _)
  haveI : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  haveI : Finite (N ⧸ H.subgroupOf N) :=
    Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (N ⧸ H.subgroupOf N)
  have hyN := avg_mem σ ρ N H hyH hy
  refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ :
    isoM σ ρ N ≤ (⊥ : Submodule ℂ V).comap (FreeAlgebra.lift ℂ (Lv ρ N) p)) hyN)
  rintro _ ⟨x, hx, rfl⟩
  rw [Submodule.mem_comap, Submodule.mem_bot, ← lift_inter σ ρ f.1 f.2 N p x, hp x hx, map_zero]

end Abs

section Conc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem iso_top (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) (τ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hτ : π.IsLocComp w τ) :
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤ := by
  set M : Submodule ℂ π.V :=
    ⨆ f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 with hM
  have comm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ M, T x ∈ M := by
    intro T hT x hx
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap T) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2, hT]; rfl⟩ ⟨v, rfl⟩
  have loc : ∀ g, ∀ x ∈ M, π.locRep w g x ∈ M := by
    intro g x hx
    refine Submodule.mem_comap.1 ((iSup_le fun f => ?_ : M ≤ M.comap (π.locRep w g)) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨τ.ρ g v, f.2 g v⟩
  have hop : ∀ (o : Op E n), ∀ x ∈ M, π.op o x ∈ M := by
    intro o x hx
    cases o with
    | fin k =>
      set c := GeneralLinearGroup.map (pLoc E w) k
      have h1 := loc c _ (comm (π.finPart ((locGL E n w c)⁻¹ * k)) (fun g y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) x hx)
      have e : π.locRep w c (π.finPart ((locGL E n w c)⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine comm _ (fun g y => Subtype.ext ?_) x hx
      change (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 =
        (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      exact comm _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) x hx
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred (M.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · obtain ⟨f, f0, hf⟩ := hτ
    have hb : M = ⊥ := hi (h.trans (Submodule.map_bot _).symm)
    refine absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 ?_)) f0
    rw [← hb]
    exact le_iSup (fun f : {f : τ.V →ₗ[ℂ] π.V // ∀ g v, f (τ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩
  · exact hi (h.trans (Submodule.map_subtype_top _).symm)

end Conc

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.IsotypicAlt in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.isot_pf :
    SlotBasic → Isot := by
  intro _ E _ _ _ n π w τ hτ N hNo hNK p hp y hyπ hy
  have hNc : IsCompact (N : Set (GLw n w)) :=
    (Asm.unitHecke E n 0 0 w).2.2.2.1.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  obtain ⟨f, f0, hf⟩ := id hτ
  haveI : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact f0 (LinearMap.ext fun v => by rw [Subsingleton.elim v 0]; simp)
  haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  haveI : Nontrivial (Sm E n) := π.V.injective_subtype.nontrivial
  have hy' : (⟨y, hyπ⟩ : π.V) ∈ fixed (π.locRep w) N :=
    LocEx.mem_fix.2 fun k hk => Subtype.ext (LocEx.mem_fix.1 hy k hk)
  have h1 := iso_abs τ.ρ (π.locRep w) τ.smooth N hNc (iso_top π w τ hτ) p hp _ hy'
  have h2 := lift_inter (π.locRep w) (rw' n w false) π.V.subtype (fun _ _ => rfl) N p ⟨y, hyπ⟩
  rw [h1, map_zero] at h2
  exact h2.symm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSimpleFix
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

open GlobalTheory.PRep GlobalTheory.BCT GlobalTheory.TwTrLevel

section

variable {G : Type} [Group G]

private def Mg (N : Subgroup G) (g : G) : Subgroup G := N ⊓ N.comap (MulAut.conj g⁻¹).toMonoidHom

private theorem mem_Mg (N : Subgroup G) (g m : G) : m ∈ Mg N g ↔ m ∈ N ∧ g⁻¹ * m * g ∈ N := by
  simp [Mg, Subgroup.mem_comap, MulAut.conj_apply]

private def dc (N : Subgroup G) (g : G) : Set G := {y | ∃ a ∈ N, ∃ b ∈ N, y = a * g * b}

private theorem dc_left (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : k * x ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨k⁻¹ * a, N.mul_mem (N.inv_mem hk) ha, b, hb, ?_⟩
    simp only [mul_assoc] at e ⊢
    rw [eq_inv_mul_iff_mul_eq]
    exact e
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨k * a, N.mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩

private theorem dc_right (N : Subgroup G) (g : G) {k : G} (hk : k ∈ N) (x : G) : x * k ∈ dc N g ↔ x ∈ dc N g := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b * k⁻¹, N.mul_mem hb (N.inv_mem hk), ?_⟩
    rw [← mul_assoc, ← e]
    simp
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b * k, N.mul_mem hb hk, by simp only [mul_assoc]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isOpen_Mg (N : Subgroup G) (hNo : IsOpen (N : Set G)) (g : G) : IsOpen (Mg N g : Set G) := by
  have e : (Mg N g : Set G) = (N : Set G) ∩ (fun m => g⁻¹ * m * g) ⁻¹' (N : Set G) := by
    ext m
    simp [mem_Mg]
  rw [e]
  exact hNo.inter (hNo.preimage (by fun_prop))

private theorem hecke_dc (N : Subgroup G) (hNc : IsCompact (N : Set G)) (g : G) :
    IsHecke N ((dc N g).indicator 1) := by
  refine ⟨?_, ?_⟩
  · have hc : IsCompact (dc N g) := by
      have e : dc N g = (fun p : G × G => p.1 * g * p.2) '' ((N : Set G) ×ˢ (N : Set G)) := by
        ext y
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
          exact ⟨a, ha, b, hb, rfl⟩
      rw [e]
      exact (hNc.prod hNc).image (by fun_prop)
    exact hc.closure_of_subset Set.support_indicator_subset
  · intro k hk x
    constructor
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_left N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_left N g hk x).1 h')]
    · by_cases h : x ∈ dc N g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_right N g hk x).2 h)]
        rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((dc_right N g hk x).1 h')]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem fixed_Mg (ρ : Representation ℂ G V) (N : Subgroup G) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    ρ g x ∈ fixed ρ (Mg N g) := by
  rw [mem_fixed_iff] at hx ⊢
  intro m hm
  have h := hx _ ((mem_Mg N g m).1 hm).2
  have e : m * g = g * (g⁻¹ * m * g) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]

private theorem lv_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) :
    levOp ρ N N ((dc N g).indicator 1) LinearMap.id x =
      ∑ᶠ j : N ⧸ (Mg N g).subgroupOf N, ρ (j.out : G) (ρ g x) := by
  have hH := hecke_dc N hNc g
  have hs := finite_supp N hNo _ hH.1
  have hx' := (mem_fixed_iff ρ N x).1 hx
  rw [levOp_apply ρ N N _ _ x hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  set f : G → ℂ := (dc N g).indicator 1 with hf
  set F : G → V := fun y => f y • ρ y x with hF
  have hFr : ∀ y, ∀ h ∈ N, F (y * h) = F y := by
    intro y h hh
    simp only [hF, (hH.2 h hh y).2, map_mul, Module.End.mul_apply, hx' h hh]
  let Φ : N ⧸ (Mg N g).subgroupOf N → G ⧸ N := fun j => QuotientGroup.mk ((j.out : G) * g)
  have hinj : Function.Injective Φ := by
    intro a b hab
    have h1 : ((a.out : G) * g)⁻¹ * ((b.out : G) * g) ∈ N := QuotientGroup.eq.1 hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ((mem_Mg N g _).2 ⟨?_, ?_⟩))
    · exact N.mul_mem (N.inv_mem (a.out).2) (b.out).2
    · have e : g⁻¹ * (((a.out⁻¹ * b.out : N)) : G) * g = ((a.out : G) * g)⁻¹ * ((b.out : G) * g) := by
        simp [mul_assoc]
      rw [e]
      exact h1
  have hsup : Function.support (fun q : G ⧸ N => F q.out) ⊆ Set.range Φ := by
    intro q hq
    have hne : f q.out ≠ 0 := by
      intro h0
      exact hq (by simp [hF, h0])
    have hmem : q.out ∈ dc N g := by
      by_contra hn
      exact hne (Set.indicator_of_notMem hn _)
    obtain ⟨a, ha, b, hb, e⟩ := hmem
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((Mg N g).subgroupOf N) (⟨a, ha⟩ : N)
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    have hm' := (mem_Mg N g _).1 (Subgroup.mem_subgroupOf.1 m.2)
    show QuotientGroup.mk (((QuotientGroup.mk (⟨a, ha⟩ : N) : N ⧸ (Mg N g).subgroupOf N).out : G) * g) = q
    rw [hm, ← QuotientGroup.out_eq' q, e]
    refine QuotientGroup.eq.2 ?_
    have e2 : ((((⟨a, ha⟩ : N) * (m : N) : N) : G) * g)⁻¹ * (a * g * b) =
        (g⁻¹ * ((m : N) : G) * g)⁻¹ * b := by
      simp [mul_assoc]
    rw [e2]
    exact N.mul_mem (N.inv_mem hm'.2) hb
  change ∑ᶠ q : G ⧸ N, F q.out = _
  have hR : ∑ᶠ q ∈ Set.range Φ, F (Quotient.out q) = ∑ᶠ q : G ⧸ N, F (Quotient.out q) := by
    rw [← finsum_mem_inter_support (fun q : G ⧸ N => F (Quotient.out q)) (Set.range Φ), Set.inter_eq_right.2 hsup,
      finsum_mem_support]
  rw [← hR, finsum_mem_range hinj]
  refine finsum_congr fun j => ?_
  have h1 : F (Φ j).out = F ((j.out : G) * g) := out_eq_of_inv N F (fun y h hh => hFr y h hh) _
  rw [h1]
  have hmem : (j.out : G) * g ∈ dc N g := ⟨j.out, (j.out).2, 1, N.one_mem, by simp⟩
  simp [hF, hf, Set.indicator_of_mem hmem, map_mul, Module.End.mul_apply]

private theorem avg_dc (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (g : G) (x : V) (hx : x ∈ fixed ρ N) [Finite (N ⧸ (Mg N g).subgroupOf N)] :
    avgOp ρ N (Mg N g) (ρ g x) =
      (((Mg N g).relIndex N : ℕ) : ℂ)⁻¹ • levOp ρ N N ((dc N g).indicator 1) LinearMap.id x := by
  rw [avgOp_apply, lv_dc ρ N hNo hNc g x hx]

private theorem avg_level (ρ : Representation ℂ G V) (N M M' : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G)) (hMo : IsOpen (M : Set G)) (hM'o : IsOpen (M' : Set G)) (hMN : M ≤ N)
    (hle : M' ≤ M) (v : V) (hv : v ∈ fixed ρ M) : avgOp ρ N M' v = avgOp ρ N M v := by
  haveI h1 := finite_quot N N M' hNc hNo hM'o le_rfl
  haveI h2 := finite_quot N N M hNc hNo hMo le_rfl
  haveI h3 := finite_quot N M M' hNc hMo hM'o hMN
  haveI h4 := finite_quot N N (Mg N 1) hNc hNo (isOpen_Mg N hNo 1) le_rfl
  have hH := hecke_dc N hNc 1
  have hHM : IsHecke M ((dc N 1).indicator 1) := ⟨hH.1, fun k hk y => hH.2 k (hMN hk) y⟩
  have hvM' : v ∈ fixed ρ M' := by
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  have e1 := levOp_le ρ N N M' (hle.trans hMN) le_rfl hNo hM'o _ hH v hvM'
  have e2 := levOp_le ρ N M M' hle hMN hMo hM'o _ hHM v hvM'
  rw [avgOp_fix ρ M M' v hv] at e2
  have e3 := levOp_le ρ N N M hMN le_rfl hNo hMo _ hH v hv
  have back : ∀ y ∈ fixed ρ N, y = (((Mg N 1).relIndex N : ℕ) : ℂ)⁻¹ •
      levOp ρ N N ((dc N 1).indicator 1) LinearMap.id y := by
    intro y hy
    rw [← avg_dc ρ N hNo hNc 1 y hy, map_one, Module.End.one_apply, avgOp_fix ρ N _ y hy]
  rw [back _ (avgOp_mem ρ N M' v hvM'), back _ (avgOp_mem ρ N M v hv), ← e1, e2, e3]

private theorem core (ρ : Representation ℂ G V) (N : Subgroup G) (hNo : IsOpen (N : Set G))
    (hNc : IsCompact (N : Set G))
    (hirr : ∀ W : Submodule ℂ V, (∀ g x, x ∈ W → ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule ℂ V) (hW : W ≤ fixed ρ N)
    (hst : ∀ f, IsHecke N f → ∀ x ∈ W, levOp ρ N N f LinearMap.id x ∈ W) : W = ⊥ ∨ W = fixed ρ N := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  refine Or.inr (le_antisymm hW ?_)
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hb
  have hxN := hW hxW
  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp⟩
  have hO : O = ⊤ := by
    have hinv : ∀ g y, y ∈ O → ρ g y ∈ O := by
      intro g y hy
      refine Submodule.span_induction (p := fun y _ => ρ g y ∈ O) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, rfl⟩
        refine Submodule.subset_span ⟨g * a, ?_⟩
        simp [map_mul, Module.End.mul_apply]
      · simp
      · intro a b _ _ ha hb
        rw [map_add (f := _)]
        exact O.add_mem ha hb
      · intro c a _ ha
        rw [map_smul]
        exact O.smul_mem c ha
    rcases hirr O hinv with h | h
    · exact absurd (by simpa [h] using hxO) hx0
    · exact h
  have hp : ∀ v ∈ O, ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧ v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∃ M : Subgroup G, IsOpen (M : Set G) ∧ M ≤ N ∧
      v ∈ fixed ρ M ∧ avgOp ρ N M v ∈ W) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, rfl⟩
      haveI := finite_quot N N (Mg N g) hNc hNo (isOpen_Mg N hNo g) le_rfl
      refine ⟨Mg N g, isOpen_Mg N hNo g, inf_le_left, fixed_Mg ρ N g x hxN, ?_⟩
      show avgOp ρ N (Mg N g) (ρ g x) ∈ W
      rw [avg_dc ρ N hNo hNc g x hxN]
      exact W.smul_mem _ (hst _ (hecke_dc N hNc g) x hxW)
    · exact ⟨N, hNo, le_rfl, (fixed ρ N).zero_mem, by simp⟩
    · rintro a b _ _ ⟨M₁, ho₁, hl₁, hf₁, hw₁⟩ ⟨M₂, ho₂, hl₂, hf₂, hw₂⟩
      have ho : IsOpen ((M₁ ⊓ M₂ : Subgroup G) : Set G) := ho₁.inter ho₂
      have hm : ∀ (M : Subgroup G) (y : V), M₁ ⊓ M₂ ≤ M → y ∈ fixed ρ M → y ∈ fixed ρ (M₁ ⊓ M₂) := by
        intro M y hle hy
        rw [mem_fixed_iff] at hy ⊢
        exact fun h hh => hy h (hle hh)
      refine ⟨M₁ ⊓ M₂, ho, inf_le_left.trans hl₁,
        (fixed ρ _).add_mem (hm _ _ inf_le_left hf₁) (hm _ _ inf_le_right hf₂), ?_⟩
      rw [map_add (f := _), avg_level ρ N M₁ _ hNo hNc ho₁ ho hl₁ inf_le_left a hf₁,
        avg_level ρ N M₂ _ hNo hNc ho₂ ho hl₂ inf_le_right b hf₂]
      exact W.add_mem hw₁ hw₂
    · rintro c a _ ⟨M, ho, hl, hf, hw⟩
      refine ⟨M, ho, hl, (fixed ρ M).smul_mem c hf, ?_⟩
      rw [map_smul]
      exact W.smul_mem c hw
  intro z hz
  obtain ⟨M, ho, hl, -, hw⟩ := hp z (hO ▸ Submodule.mem_top)
  haveI := finite_quot N N M hNc hNo ho le_rfl
  rwa [avgOp_fix ρ N M z hz] at hw

end

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.simpleFix_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SimpleFix := by
  intro _ E _ _ _ n w τ N hNo hNle
  have hKc := (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w).2.2.2.1
  have hNc : IsCompact (N : Set (GlobalTheory.BCT.GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNle
  obtain ⟨-, hirr⟩ := (GlobalTheory.CuspRep.isIrreducible_iff τ.ρ).1 τ.irred
  refine ⟨fun f hf x hx => GlobalTheory.TraceLevel.levOp_mem_fixed τ.ρ N N N f hf hNo le_rfl x hx, ?_⟩
  exact fun W hW hst => UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.SimpleFixedVectors.core τ.ρ N hNo hNc hirr W hW hst
end
