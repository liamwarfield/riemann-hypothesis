module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceFormNondegenerate
open Formalism.MainNotions.N GlobalTheory.TraceSemisimple

namespace GlobalTheory.SemisimpleTraceForm

theorem idem_eq_zero_of_trace {k : Type} [Field k] [CharZero k] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) k) (he : e * e = e) (ht : e.trace = 0) : e = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' e) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' e)) (Matrix.toLin' e) :=
    ⟨fun v => ⟨v, rfl⟩, by
      rintro _ ⟨v, rfl⟩
      exact congrArg (fun f : Module.End k (Fin n → k) => f v) hf⟩
  have h1 := hp.trace
  rw [Matrix.trace_toLin'_eq, ht] at h1
  have h2 : Module.finrank k (LinearMap.range (Matrix.toLin' e)) = 0 := by
    exact_mod_cast h1.symm
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h2
  exact (LinearEquiv.map_eq_zero_iff _).1 h2

theorem semisimple_span {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (h : IsSSRep ρ) : IsSemisimpleRing (spanAlg ρ) := by
  let φ : spanAlg ρ →+* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  letI : Module (spanAlg ρ) (Fin n → k) := Module.compHom _ φ
  have hs : ∀ (a : spanAlg ρ) (v : Fin n → k),
      a • v = (a : Matrix (Fin n) (Fin n) k).mulVec v := fun _ _ => rfl
  have hinv : ∀ W, IsInv ρ W → ∀ a : spanAlg ρ, ∀ v ∈ W, a • v ∈ W := by
    rintro W hW ⟨a, ha⟩ v hv
    rw [hs]
    show a.mulVec v ∈ W
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add y z _ _ hy hz => rw [Matrix.add_mulVec]; exact W.add_mem hy hz
    | smul c y _ hy => rw [Matrix.smul_mulVec]; exact W.smul_mem c hy
  have hV : IsSemisimpleModule (spanAlg ρ) (Fin n → k) := by
    rw [isSemisimpleModule_iff]
    refine ⟨fun U => ?_⟩
    let W : Submodule k (Fin n → k) :=
      { toAddSubmonoid := U.toAddSubmonoid
        smul_mem' := fun c v hv => by
          have h1 : (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v ∈ U :=
            U.smul_mem (c • (1 : spanAlg ρ)) hv
          rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h1
          exact h1 }
    have hW : IsInv ρ W := fun g v hv =>
      U.smul_mem ⟨(ρ g : GL (Fin n) k), Submodule.subset_span ⟨g, rfl⟩⟩ hv
    obtain ⟨W', hW', hc⟩ := h W hW
    let U' : Submodule (spanAlg ρ) (Fin n → k) :=
      { toAddSubmonoid := W'.toAddSubmonoid
        smul_mem' := fun a v hv => hinv W' hW' a v hv }
    refine ⟨U', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      exact fun v hv hv' => Submodule.disjoint_def.1 hc.disjoint v hv hv'
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
      exact Submodule.add_mem_sup hy hz
  let ψ : spanAlg ρ →ₗ[spanAlg ρ] (Fin n → Fin n → k) :=
    LinearMap.pi fun j => LinearMap.toSpanSingleton _ _ (Pi.single j 1)
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    ext i j
    have h1 : (a : Matrix (Fin n) (Fin n) k).mulVec ((Pi.single j 1 : Fin n → k)) i = 0 :=
      congrFun (congrFun ha j) i
    simpa using h1
  have hP : IsSemisimpleModule (spanAlg ρ) (Fin n → Fin n → k) :=
    instIsSemisimpleModuleForallOfFinite fun _ => Fin n → k
  exact IsSemisimpleModule.of_injective ψ hψ

theorem trace_form_nondegenerate :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (ρ : Γ →* GL (Fin n) k),
      IsSSRep ρ → ∀ x ∈ spanAlg ρ,
        (∀ g : Γ, Matrix.trace (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = 0) →
        x = 0 := by
  intro Γ k _ _ _ n ρ h x hx ht
  have := semisimple_span ρ h
  have hA : ∀ a ∈ spanAlg ρ, (x * a).trace = 0 := by
    intro a ha
    rw [mem_spanAlg] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact ht g
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  let y : spanAlg ρ := ⟨x, hx⟩
  obtain ⟨C, hC⟩ := exists_isCompl (Submodule.span (spanAlg ρ) {y})
  have h1 : (1 : spanAlg ρ) ∈ Submodule.span (spanAlg ρ) {y} ⊔ C := by
    rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  have key : ∀ z ∈ Submodule.span (spanAlg ρ) {y}, z * e = z := by
    intro z hz
    have h2 : z * f = z - z * e := by
      rw [eq_sub_iff_add_eq', ← mul_add, hef, mul_one]
    have h3 : z * f = 0 :=
      Submodule.disjoint_def.1 hC.disjoint _
        (h2 ▸ Submodule.sub_mem _ hz (Submodule.smul_mem _ z he)) (C.smul_mem z hf)
    rw [h3] at h2
    exact (sub_eq_zero.1 h2.symm).symm
  have he0 : (e : Matrix (Fin n) (Fin n) k) = 0 := by
    refine idem_eq_zero_of_trace _ (congrArg Subtype.val (key e he)) ?_
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 he
    show ((a : Matrix (Fin n) (Fin n) k) * x).trace = 0
    rw [Matrix.trace_mul_comm]
    exact hA a a.2
  have h4 : x * (e : Matrix (Fin n) (Fin n) k) = x :=
    congrArg Subtype.val (key y (Submodule.mem_span_singleton_self y))
  rw [← h4, he0, mul_zero]

end GlobalTheory.SemisimpleTraceForm
end

open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem trace_nondegenerate_of_isSSRep {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ spanAlg ρ)
    (htr : ∀ g, (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).trace = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4; revert Γ k h_2 h_3 h_4 n ρ hρ x hx htr; exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate)
  | exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | (apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate ..)

theorem isSSRep_mapRep :
    ∀ (Γ k k' : Type) [Group Γ] [Field k] [Field k'] [CharZero k] (ι : k →+* k') (n : ℕ)
      (ρ : Γ →* GL (Fin n) k), IsSSRep ρ → IsSSRep (mapRep ι ρ) := by
  intro Γ k k' _ _ _ _ ι n ρ hρ
  let _ : Algebra k k' := ι.toAlgebra
  have hφι : ∀ (φ : k' →ₗ[k] k) (c : k') (r : k), φ (c * ι r) = φ c * r := by
    intro φ c r
    rw [mul_comm c, mul_comm (φ c), ← smul_eq_mul r, ← map_smul]
    rfl
  have hent : ∀ g i j, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') i j =
      ι (((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := fun _ _ _ => rfl
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  have hmem : ∀ φ : k' →ₗ[k] k, x.map φ ∈ spanAlg ρ := by
    clear htr
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro φ
      have : ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k').map φ =
          φ 1 • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
        ext i j
        rw [Matrix.map_apply, hent, Matrix.smul_apply, smul_eq_mul, ← hφι, one_mul]
      rw [this]
      exact (spanAlg ρ).smul_mem (Submodule.subset_span ⟨g, rfl⟩) _
    | zero =>
      intro φ
      have : (0 : Matrix (Fin n) (Fin n) k').map φ = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      intro φ
      have : (y + z).map φ = y.map φ + z.map φ := by ext i j; simp
      rw [this]; exact add_mem (hy φ) (hz φ)
    | smul c y _ hy =>
      intro φ
      exact hy (φ ∘ₗ LinearMap.mulLeft k c)
  have hzero : ∀ φ : k' →ₗ[k] k, x.map φ = 0 := by
    intro φ
    refine trace_nondegenerate_of_isSSRep ρ hρ _ (hmem φ) fun g => ?_
    have := congrArg φ (htr g)
    rw [map_zero] at this
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, hent, hφι, Matrix.map_apply]
  ext i j
  rw [Matrix.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  exact congrFun (congrFun (hzero φ) i) j

end GlobalTheory.TraceSemisimple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamilies
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.PointConditions

theorem sum_single_jumps {M : Type} [AddCommMonoid M] [One M] (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : M) else 0)) = if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    rw [Finset.sum_eq_single (n + 1)]
    · rw [if_pos (by push_cast; ring)]
    · intro c _ hne
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem isSSRep_rhoChiK (D : D7) (i : D.nd.Loc) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.BlockSemisimple ρ (D.nd.chi i) D.R.t) : IsSSRep (rhoChiK D i ρ) := by
  rw [GlobalTheory.ComplementCompare.isSSRep_iff]
  refine (GlobalTheory.ComplementCompare.semisimple_congr (splitRT (KK D.nd i) D.R.r D.R.t) ?_).2 h
  intro g v
  change splitRT _ _ _ (((rhoChiK D i ρ g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) :
      Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec v) = _
  unfold rhoChiK
  rw [blockRep_coe, blockHom_mulVec, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply]
  refine Prod.ext rfl (funext fun c => ?_)
  show (Matrix.diagonal _).mulVec _ c = _
  rw [Matrix.mulVec_diagonal]
  rfl

theorem main : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  intro D r ρ h i π hπ
  have hc := h.compl i π hπ
  refine ⟨h.frob i π hπ, isSSRep_rhoChiK D i (ρ i π) hc.ss, ?_, ?_⟩
  · intro _ _ _ w hw C τ
    have hB := h.block i π hπ w hw C.LL C.le τ
    refine ⟨fun a => ?_, fun c hc a => hB.2 c hc a⟩
    have h2 : ∀ c ∈ Finset.Icc 1 D.R.t, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0 := fun c hc => hB.2 c hc a
    rw [Finset.sum_congr rfl h2, sum_single_jumps]
    exact hB.1 a
  · obtain ⟨e, he⟩ := hc.rho
    refine ⟨e, fun g u => ?_⟩
    have := he g u
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.blockRep_apply] at this
    exact this

end GlobalTheory.PointConditions
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamiliesStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  first | exact @GlobalTheory.PointConditions.main | exact GlobalTheory.PointConditions.main | (intros; apply GlobalTheory.PointConditions.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ResAbsIrrGood

theorem absIrrSub_top_of_irred {k L : Type} [Field k] [Field L] [IsAlgClosed L] (φ : k →+* L)
    {Γ : Type} [Group Γ] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (h : ∀ W : Submodule L (Fin a → L),
      (∀ g, ∀ x ∈ W, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  letI : Algebra k L := φ.toAlgebra
  let ψ : K →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : ∀ x : k, ψ (f x) = φ x := fun x => ψ.commutes x
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hspan : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' ((⊤ : Submodule k (Fin a → k)) : Set _)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (v i) : Fin a → K) = v i • (f ∘ (Pi.single i (1 : k) : Fin a → k)) := by
      ext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, trivial, rfl⟩)
  unfold AbsIrrSub
  rw [hspan]
  have hmat : ∀ g, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      (((mapRep f ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).map ψ := by
    intro g
    ext i j
    simp [mapRep, hψ]
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW' => ?_⟩
  set W'' : Submodule L (Fin a → L) := Submodule.span L ((fun v : Fin a → K => ψ ∘ v) '' (W' : Set _))
  have hst : ∀ g, ∀ x ∈ W'', ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W'' := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine Submodule.subset_span ⟨_, hW' g u hu, ?_⟩
      ext p
      rw [hmat g]
      exact RingHom.map_mulVec ψ.toRingHom _ u p
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  rcases h W'' hst with h1 | h1
  · left
    rw [Submodule.span_eq_bot] at h1
    rw [eq_bot_iff]
    intro v hv
    have := h1 _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_bot]
    ext p
    apply hψinj
    simpa using congrFun this p
  · right
    by_contra hne
    obtain ⟨θ, hθ0, hθ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin a → L := fun i => ψ (θ (Pi.single i 1))
    have hθv : ∀ v : Fin a → K, θ v = ∑ i, v i * θ (Pi.single i 1) := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (v i) : Fin a → K) = v i • (Pi.single i (1 : K) : Fin a → K) by
        ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, smul_eq_mul]
    have hkill : ∀ X ∈ W'', ∑ i, X i * c i = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        have h0 : θ u = 0 := hθ hu
        have := congrArg ψ (hθv u)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h0, map_zero, map_sum] at this
        rw [this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul s x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]
    apply hθ0
    apply LinearMap.pi_ext
    intro i x
    have hci : c i = 0 := by
      have := hkill (Pi.single i 1) (h1 ▸ Submodule.mem_top)
      simpa [Pi.single_apply] using this
    have : θ (Pi.single i 1) = 0 := hψinj (by simpa [c] using hci)
    rw [show (Pi.single i x : Fin a → K) = x • (Pi.single i (1 : K) : Fin a → K) by
      ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, this]
    simp

end GlobalTheory.ResAbsIrrGood

theorem GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred : ∀ D : D7, ResidualIrreducibleRankR D → GlobalTheory.PtCore.ResAbsIrr D := by
  intro D hN9 a π hπ ρ hρ
  obtain ⟨hcont, r, hr, e, he⟩ := hρ
  have hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) a (fun _ => r) (fun _ => ρ) π := ⟨e, he⟩
  have hrb : IsRhoBar D.nd a (redRep D.nd a ρ) := by
    refine ⟨isOpen_ker_redRep D a ρ hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a)))
      (charpoly_of_decomp D a _ _ π hdec σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D a x π w, ← hr.2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hHG : HG D.nd D.naut a := ⟨π, (D.Zgood_tie a π).1 hπ⟩
  have hirr := (hN9 a hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  exact GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar a) hpos _
    fun W hW => hirr W fun g _ x hx => hW g x hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEOfIsBlockSum
noncomputable section

namespace GlobalTheory.BlockEnl

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.BlockJumps GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount GlobalTheory.HTW.SumJumps GlobalTheory.Cmp.SmallJumps

theorem multV_oneByOne {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL]
    (hF : IsField BdR) (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (σ : Representation LL G (Fin 1 → LL)) (e : ℕ)
    (he : ∀ g u c, σ g u c = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e * u c)
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD σ τ a = if a = e then 1 else 0 := by
  let χ : Fin 1 → G →* LLˣ := fun _ => ((cycLL PD LL)⁻¹) ^ e
  have hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e := fun c g => by
    simp [χ, cycLL]
  have hσ : σ = diagRep χ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun c => ?_
    rw [he, diagRep_apply, hχ c]
  rw [hσ, multV_diagRep PD hF, Fin.sum_univ_one]
  exact multV_twist PD hs (Formalism.WeaklyAdmissibleFiltrations.charRep (χ 0)) e (fun g x => by rw [← hχ 0]; rfl) τ a

theorem twistM_one_apply {O Γ : Type} [CommRing O] [Group Γ] (χ : Γ →* Oˣ) (g : Γ) :
    twistM (1 : Γ →* Matrix (Fin 1) (Fin 1) O) χ g 0 0 = ((χ g : Oˣ) : O) := by
  simp [twistM]


set_option maxHeartbeats 1000000 in
theorem blockE_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π) : BlockE D i r ρ π := by
  obtain ⟨e, he⟩ := hB
  intro w hw L' hL τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥L'.1 := L'.2
  let s : Br.G D.nbr i w hw → Formalism.MainNotions.N.GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let j := inc D i w hw L' hL
  let f := j.comp (Br.toLLK (D.nbr i w hw))
  have hf : ∀ c, f (toK D.nd i c) = j ((D.nbr i w hw).toLL c) :=
    fun c => congrArg j (Br.toLLK_alg (D.nbr i w hw) c)
  have hχ0 : ∀ (c : ℕ), c + 1 ≤ D.R.t → ∀ g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i (c + 1) g =
      (epsU D.nd i g)⁻¹ ^ c := fun c hc g => by
    have h := D.nd.chi_def i (c + 1) (by omega) hc
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i (c + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  have hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g =
      (epsU D.nd i g)⁻¹ ^ (c : ℕ) := fun c g => hχ0 c c.2 g
  have hε : ∀ g, j ((D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i)) =
      algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    have h1 : (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
        algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
      rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
      exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
    rw [h1]
    exact (IntermediateField.inclusion hL).commutes _
  have hM : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (locE D i w hw L' hL M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = locE D i w hw L' hL M g from
      Matrix.ext fun a b => hf _]
    rfl
  have hs : ∃ x ∈ (Br.PD D.loc D.nbr i w hw).Fil (-1),
      (Br.PD D.loc D.nbr i w hw).ι (Br.PD D.loc D.nbr i w hw).t * x = 1 := by
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  have hpow : ∀ g (n : ℕ), f (toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ n : (D.nd.O i)ˣ) : D.nd.O i)) =
      (algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹ ^ n := fun g n => by
    rw [hf, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv, map_inv₀, hε]
  refine ⟨fun a => ?_, fun c hc a => ?_⟩
  · obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
      (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
      (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
        have h1 : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
            (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
              toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
                (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
          rw [← Matrix.smul_mulVec]
          congr 1
          ext a b
          exact map_mul (toK D.nd i) _ _
        rw [rTwO, WpO, h1, h1, map_smul, he]
        refine Prod.ext rfl (funext fun c => ?_)
        simp only [← hχ, Units.val_mul, map_mul, mul_assoc]
        rfl)
    obtain ⟨J, h1, h2⟩ := jumps_of_split (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs
      (matRep (locE D i w hw L' hL (rTwO D.nd i r π))) (matRep (locE D i w hw L' hL (WpO D.nd i ρ π))) e'
      (fun g u => by
        rw [hM, hM, he']
        exact Prod.ext rfl (funext fun c => congrArg (· * (e' u).2 c) (hpow g c))) τ
    rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
    push_cast
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    rw [multV_oneByOne (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs _ n
      (fun g u b => ?_) τ a, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [hM, ← hpow, ← hχ0 n hc2, Subsingleton.elim b 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue]
    congr 1
    change f (toK D.nd i (chiRatO D.nd i (n + 1) (s g) 0 0)) = _
    rw [chiRatO, twistM_one_apply, MonoidHom.mul_apply, mul_comm]

end GlobalTheory.BlockEnl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecomposition
noncomputable section

namespace GlobalTheory.AmbBlockDecomp

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem sum_ind_block (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : ℤ) else 0)) =
      if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [Finset.sum_eq_single (n + 1)]
    · simp
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  intro D i r ρ π hD _ _ _ w hw C τ
  have hB : GlobalTheory.PtCore.BlockE D i r ρ π :=
    GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by
      obtain ⟨e, he⟩ := hD
      exact ⟨e, fun g u => he g u⟩)
  obtain ⟨h1, h2⟩ := hB w hw C.LL C.le τ
  have hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)),
      TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M := fun _ => rfl
  simp only [hl]
  refine ⟨fun a => ?_, fun c hc a => h2 c hc a⟩
  rw [h1 a]
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => h2 c hc a)]
  exact (sum_ind_block D.R.t a).symm

end GlobalTheory.AmbBlockDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  first | exact @GlobalTheory.AmbBlockDecomp.main | exact GlobalTheory.AmbBlockDecomp.main | (intros; apply GlobalTheory.AmbBlockDecomp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.Proof.LocalGlobalAssembly

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GlobalTheory.PtCore.GoodPtRow D := by
  intro D _ _ hZ a π hπ
  have hπ' : π ∈ ZgoodN D.nd D.naut a := (D.Zgood_tie a π).1 hπ
  obtain ⟨-, Sig, hX, hg⟩ := id hπ'
  have hHG : HG D.nd D.naut a := ⟨π, hπ'⟩
  have h1 := ((hZ a hHG).1 π hπ' Sig hX).2

  have hE : eigC D.nd D.naut a π ≠ ⊥ := by
    obtain ⟨P, hP, -⟩ := hX
    intro h
    apply D.naut.typeV_ne a P
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | D.naut.ptV a P = some π}) => D.naut.typeV a P) P hP le_rfl
  have hM : MjSig D.nd D.naut a Sig ≠ ⊥ := by
    intro h
    apply hE
    rw [← h1, h, Submodule.map_bot]
  obtain ⟨σ, hW, hσ⟩ : ∃ σ, HasParamW D.nd D.naut a σ Sig ∧ D.what₂.isot (D.nd.j a) σ ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    apply hM
    unfold MjSig
    exact le_bot_iff.1 (iSup₂_le fun σ hW => (hc σ hW).le)
  have hgr : D.nd.goodRow σ := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW.2.2).2 hg
  exact ⟨σ, Sig, ⟨hgr, hσ⟩, hW, hX⟩

end GlobalTheory.Proof.LocalGlobalAssembly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime]

scoped instance algZlBdR : Algebra ℤ_[l] (Per.BdR l) :=
  ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((GlobalTheory.MemLoc.aDp l).comp (algebraMap ℤ_[l] (Ainf l)))).toAlgebra


variable (l) in
def bdRpToBdR : Per.BdRp l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := algebraMap (Per.BdRp l) (Per.BdR l)
  commutes' _ := rfl

theorem core_ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) := by
  rw [GlobalTheory.RingIface.aB_eq_alg l w, C.ι_j, GlobalTheory.RingIface.tower l w, C.j_cris.on0, Subalgebra.coe_algebraMap]
  exact congrArg _ (RingHom.comp_apply _ _ _).symm

def iotaZ (C : GlobalTheory.MemLoc.Core l) : Per.Bcris l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := C.ι
  commutes' z := core_ι_aB C (algebraMap ℤ_[l] (Ainf l) z)


variable (l) in
abbrev OdR (O : Type) [CommRing O] [Algebra ℤ_[l] O] : Type := O ⊗[ℤ_[l]] Per.BdR l

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O]


variable (l O) in
def dRO : OD l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (bdRpToBdR l)


variable (O) in
def iotaO (C : GlobalTheory.MemLoc.Core l) : OB l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (iotaZ C)

theorem iotaO_toB (C : GlobalTheory.MemLoc.Core l) (x : OA l O) : iotaO O C (toB l O x) = dRO l O (toOD l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y)
      ((congrArg C.ι (GlobalTheory.RingIface.aB_eq_alg l w).symm).trans (core_ι_aB C w))
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.PotDual

def bundle {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_of_eq {k : ℕ} (M U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose) :
    IsDual1 PD (matRep M) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

end

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact (hM.comp hι).matrix_map hfc

theorem isDual1_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsDual1 ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) (dotProductBilin _ _) := by
  refine isDual1_of_eq _ _ _ fun g => ?_
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  have e : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
      ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥(D.nbr i w hw).LL.1 g :
        (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) :=
    congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  rw [← e]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

end


set_option maxHeartbeats 1600000 in
theorem stepPotDual : StepPotDual := by
  classical
  intro D hT i r hr Xs w hw n ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1, hc, hx⟩
  refine ⟨K', h, hN, hF, hS, Sig.image (fun a => a⁻¹), Fr, hFr, ?_, ?_,
    le_trans Finset.card_image_le hc, fun x => ?_⟩
  · intro a ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, hb, hab⟩ := hst a ha'
    refine ⟨b⁻¹, Finset.mem_image.2 ⟨b, hb, rfl⟩, fun g g' hg => ?_⟩
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hab g g' hg]
  · exact Finset.mem_image.2 ⟨1, h1, inv_one⟩
  · have hcont := GlobalTheory.Pass.FamCont.stepCont D i r hr x
    exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (continuous_loc D i w hw _ hcont.1))
      (bundle _ _ (Br.loc D.nbr i w hw (rDuO D.nd i r x)) (continuous_loc D i w hw _ hcont.2))
      Sig (Sig.image (fun a => a⁻¹)) (hx x).1 (hx x).2).2 (dotProductBilin _ _)
      (isDual1_loc D i w hw r x)
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.PotDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

theorem charpoly_redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (s : G D.host.E D.nd.Om) :
    Matrix.charpoly ((redF D i ρ s : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) := by
  rw [← Matrix.charpoly_map]
  rfl

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CycBridge

theorem locChi_epsU_eq_cycLL : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.locChi D.nbr i w hw (epsU D.nd i) = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) :=
  fun D i w hw => MonoidHom.ext (GlobalTheory.CycBridge.locChi_epsU D i w hw)

end GlobalTheory.CycBridge
end
