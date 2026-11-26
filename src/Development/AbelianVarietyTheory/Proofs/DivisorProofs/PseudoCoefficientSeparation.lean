module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyEqOfMemHomFinDS
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

theorem exists_clm_of_inner_eq {ι H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (v : ι → H) (v' : ι → K) (c : ℂ) (hc : ∀ i j, ⟪v' i, v' j⟫_ℂ = c * ⟪v i, v j⟫_ℂ)
    (hd : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    ∃ A : H →L[ℂ] K, ∀ i, A (v i) = v' i := by
  set p := Finsupp.linearCombination ℂ v with hp
  set p' := Finsupp.linearCombination ℂ v' with hp'
  have hin : ∀ f f', ⟪p' f, p' f'⟫_ℂ = c * ⟪p f, p f'⟫_ℂ := by
    intro f f'
    simp only [p, p', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hn : ∀ f, ‖p' f‖ = Real.sqrt ‖c‖ * ‖p f‖ := by
    intro f
    have h := congrArg norm (hin f f)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, norm_pow] at h
    simp only [RCLike.norm_ofReal, Complex.norm_real, abs_norm, norm_norm] at h
    rw [← Real.sqrt_sq (norm_nonneg (p' f)), h, Real.sqrt_mul (norm_nonneg c), Real.sqrt_sq (norm_nonneg _)]
  have hker : LinearMap.ker p ≤ LinearMap.ker p' := fun f hf => by
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← norm_eq_zero, hn, hf, norm_zero, mul_zero]
  let L : LinearMap.range p →ₗ[ℂ] K := (LinearMap.ker p).liftQ p' hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap
  have hL : ∀ f, L ⟨p f, f, rfl⟩ = p' f := fun f => by
    have : p.quotKerEquivRange.symm ⟨p f, f, rfl⟩ = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hb : ∀ x, ‖L x‖ ≤ Real.sqrt ‖c‖ * ‖x‖ := by
    rintro ⟨_, f, rfl⟩
    rw [hL, hn]; rfl
  let A0 := L.mkContinuous _ hb
  let e := (LinearMap.range p).subtypeL
  have hrange : (LinearMap.range p : Set H) = Submodule.span ℂ (Set.range v) := by
    rw [hp, Finsupp.range_linearCombination]
  have hdense : DenseRange e := by
    have : Dense ((Submodule.span ℂ (Set.range v) : Submodule ℂ H) : Set H) :=
      (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
    rw [← hrange] at this
    exact this.denseRange_val
  have hui : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨A0.extend e, fun i => ?_⟩
  have h1 : p (Finsupp.single i 1) = v i := by simp [p]
  have h2 : p' (Finsupp.single i 1) = v' i := by simp [p']
  have := ContinuousLinearMap.extend_eq A0 hdense hui ⟨p (Finsupp.single i 1), _, rfl⟩
  simp only [e, Submodule.subtypeL_apply, A0, LinearMap.mkContinuous_apply, hL] at this
  rw [← h1, this, h2]

end GlobalTheory.TrExt

namespace GlobalTheory.TrExt

open scoped InnerProductSpace ComplexConjugate

theorem apply_eq_of_mem_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type}
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {ρ : GA D V →* (X →L[ℂ] X)} {U : Submodule ℂ X}
    {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H X} (h : T ∈ homFinDS σ M ρ U) (g : GA D V) (w : W)
    (y : ∀ τ, M.H τ) : ρ g (T w y) =
      T (σ (toFin V g) w) (fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ)) := by
  classical
  have hm := mem_homTensorPi.1 h
  conv_lhs => rw [← toInf_mul_toFin g, map_mul, ContinuousLinearMap.mul_apply]
  have h1 : ρ (toFin V g : GA D V) (T w y) = T (σ (toFin V g) w) y := (hm.2.1 (toFin V g) w y).symm
  rw [h1]
  exact GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise D V S M X ρ U _ (h.1 _) g y


open Classical in
theorem exists_homIn_extend : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : GA D V →* (K →L[ℂ] K)), IsUnitaryRep ρ → ∀ U : Submodule ℂ K, IsClosed (U : Set K) → ∀ T' ∈ homFinDS σ M ρ U, ∃ A ∈ homIn π ρ U, ∀ w y, A (T w y) = T' w y := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ π hπ T hT hinj hd K _ _ _ ρ hρ U hU T' hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hTw : ∀ w, T w ∈ homDS M π ⊤ := fun w => hT.1 w
  have hTw' : ∀ w, T' w ∈ homDS M ρ U := fun w => hT'.1 w
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T' w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hπ (hTw x) ((map_ne_zero_iff T hinj).2 hx)
  have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
    change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
    rw [hTm.2.1, hTm.2.1, inner_map_map hπ]
  have hC : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g x y => by
    change ⟪T' (σ g y) _, T' (σ g x) _⟫_ℂ = ⟪T' y _, T' x _⟫_ℂ
    rw [hTm'.2.1, hTm'.2.1, inner_map_map hρ]
  obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible (GfC V) K₀ hKo hKc W W σ σ hadm hadm.1 B C hBpos hB hC
  obtain ⟨c, rfl⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K₀ hKo hKc W σ hirr hadm φ hφ

  have hbe : ∀ x y, bePi (T' x) (T' y) = conj c * bePi (T x) (T y) := fun x y => by
    have : bePi (T' x) (T' y) = bePi (T x) (T (c • y)) := hCB x y
    rw [this, map_smul, bePi, bePi, ContinuousMultilinearMap.smul_apply, inner_smul_left]
  have hinner : ∀ q r : W × (∀ τ, M.H τ), ⟪T' q.1 q.2, T' r.1 r.2⟫_ℂ = conj c * ⟪T q.1 q.2, T r.1 r.2⟫_ℂ := by
    rintro ⟨w, y⟩ ⟨w', y'⟩
    rw [inner_eq_bePi hδ hρ (hTw' w') (hTw' w), inner_eq_bePi hδ hπ (hTw w') (hTw w), hbe, mul_assoc]
  have hset : {v | ∃ w y, v = T w y} = Set.range (fun q : W × (∀ τ, M.H τ) => T q.1 q.2) := by
    ext v; constructor
    · rintro ⟨w, y, rfl⟩; exact ⟨(w, y), rfl⟩
    · rintro ⟨⟨w, y⟩, rfl⟩; exact ⟨w, y, rfl⟩
  rw [hset] at hd
  obtain ⟨A, hA⟩ := exists_clm_of_inner_eq _ _ _ hinner hd
  have hA' : ∀ w y, A (T w y) = T' w y := fun w y => hA (w, y)
  have hdense : Dense ((Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2)) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  refine ⟨A, ⟨fun x => ?_, fun g => ?_⟩, fun w y => hA (w, y)⟩
  · have hle : Submodule.span ℂ (Set.range fun q : W × (∀ τ, M.H τ) => T q.1 q.2) ≤ U.comap (A : H →ₗ[ℂ] K) :=
      Submodule.span_le.2 (by
        rintro _ ⟨⟨w, y⟩, rfl⟩
        show A (T w y) ∈ U
        rw [show A (T w y) = T' w y from hA (w, y)]
        exact hTm'.1 w y)
    have := Submodule.topologicalClosure_minimal _ hle (hU.preimage A.continuous)
    rw [hd] at this
    exact this trivial
  ·
    refine DFunLike.congr_fun (ContinuousLinearMap.ext_on (f := A ∘L π g) (g := ρ g ∘L A) hdense ?_)
    rintro _ ⟨⟨w, y⟩, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [apply_eq_of_mem_homFinDS hT, hA', hA', apply_eq_of_mem_homFinDS hT']

end GlobalTheory.TrExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDS
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqBotOrEqOfStarProjectionEqSmul
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.TrCopy

theorem eq_bot_or_eq_of_starProjection_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U U' : Submodule ℂ H} [U'.HasOrthogonalProjection] (hle : U' ≤ U) (a : ℂ)
    (hPU : ∀ v ∈ U, U'.starProjection v = a • v) {u0 : H} (hu0 : u0 ∈ U) (hne : u0 ≠ 0) : U' = ⊥ ∨ U' = U := by
  have haa : a * a = a := by
    have h1 : U'.starProjection (U'.starProjection u0) = U'.starProjection u0 :=
      (Submodule.starProjection_eq_self_iff (K := U')).2 (U'.starProjection_apply_mem _)
    rw [hPU _ hu0, map_smul, hPU _ hu0, smul_smul] at h1
    exact smul_left_injective ℂ hne h1
  rcases mul_eq_zero.1 (show a * (a - 1) = 0 by rw [mul_sub, haa, mul_one, sub_self]) with h0 | h1
  · left
    refine (Submodule.eq_bot_iff U').2 fun v hv => ?_
    rw [← (Submodule.starProjection_eq_self_iff (K := U')).2 hv, hPU v (hle hv), h0, zero_smul]
  · right
    refine le_antisymm hle fun v hv => ?_
    have hv' : U'.starProjection v = v := by rw [hPU v hv, sub_eq_zero.1 h1, one_smul]
    exact hv' ▸ U'.starProjection_apply_mem v

theorem eq_smul_on_closure_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Set H) (P : H →L[ℂ] H) (a : ℂ)
    (hP : ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v ∈ (Submodule.span ℂ s).topologicalClosure)
    (h : ∀ u ∈ s, ∀ u' ∈ s, ⟪u', P u - a • u⟫_ℂ = 0) :
    ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v = a • v := by
  set A := Submodule.span ℂ s with hA
  let Q : H →L[ℂ] H := P - a • ContinuousLinearMap.id ℂ H
  have hQ : ∀ v, Q v = P v - a • v := fun v => rfl
  have hQA : ∀ v ∈ A, Q v ∈ Aᗮ := by
    intro v hv
    refine (Submodule.span_le (p := Aᗮ.comap (Q : H →ₗ[ℂ] H))).2 ?_ hv
    intro u hu
    show Q u ∈ Aᗮ
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hle : A ≤ (ℂ ∙ Q u)ᗮ := Submodule.span_le.2 (by
      intro u' hu'
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hQ]
      exact h u hu u' hu')
    exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hx))
  have hQcl : ∀ v ∈ A.topologicalClosure, Q v ∈ Aᗮ := fun v hv =>
    (Submodule.topologicalClosure_minimal (s := A) (t := Aᗮ.comap (Q : H →ₗ[ℂ] H)) (fun u hu => hQA u hu)
      ((Submodule.isClosed_orthogonal A).preimage Q.continuous)) hv
  have hcl : A.topologicalClosure ≤ Aᗮᗮ :=
    Submodule.topologicalClosure_minimal _ A.le_orthogonal_orthogonal (Submodule.isClosed_orthogonal _)
  intro v hv
  have h1 : Q v ∈ A.topologicalClosure := by
    rw [hQ]
    exact sub_mem (hP v hv) (Submodule.smul_mem _ _ hv)
  have h2 : ⟪Q v, Q v⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (hQcl v hv) (hcl h1)
  rw [inner_self_eq_zero, hQ, sub_eq_zero] at h2
  exact h2

theorem isIrredSubrep_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type)
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)),
    IsUnitaryRep ρ → ∀ U : Submodule ℂ H, IsCopyFinDS σ M ρ U → IsIrredSubrep ρ U := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ ρ hρ U hU
  classical
  obtain ⟨T, hT, hinj, rfl⟩ := hU
  have hTm := mem_homTensorPi.1 hT
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M

  have hgen : ∀ g w y, ρ g (T w y) ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g w y
    have e1 := GlobalTheory.TrAct.toInf_apply_homDS D V S M H ρ ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
    rw [hTm.2.1] at e1
    have e2 : ρ g (T w y) = ρ (toInf V g : GA D V) (ρ ((GfC V).subtype (toFin V g)) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]
      rfl
    rw [e2, e1]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  have hsub : IsSubrep ρ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    isSubrep_topologicalClosure fun g v hv => Submodule.mem_comap.1
      ((Submodule.span_le (p := Submodule.comap (ρ g : H →ₗ[ℂ] H) _)).2
        (by rintro _ ⟨w, y, rfl⟩; exact hgen g w y) hv)

  obtain ⟨w0, hw0⟩ : ∃ w : W, w ≠ 0 := by
    by_contra h
    push Not at h
    have hne : (⊥ : Subrepresentation σ) ≠ ⊤ := bot_ne_top
    exact hne (by ext v; simp [h v])
  have hTw0 : T w0 ≠ 0 := fun h => hw0 (hinj (h.trans (map_zero T).symm))
  obtain ⟨y0, hy0⟩ : ∃ y, T w0 y ≠ 0 := by
    by_contra h
    push Not at h
    exact hTw0 (ContinuousMultilinearMap.ext h)
  have hu0 : T w0 y0 ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w0, y0, rfl⟩)
  refine ⟨hsub, fun h => hy0 ((Submodule.mem_bot ℂ).1 (h ▸ hu0)), fun U' hU'le hU' => ?_⟩
  haveI : CompleteSpace U' := hU'.1.completeSpace_coe

  have hPc : ∀ g v, U'.starProjection (ρ g v) = ρ g (U'.starProjection v) := by
    intro g v
    have h1 : ρ g (U'.starProjection v) ∈ U' := hU'.2 g _ (U'.starProjection_apply_mem v)
    have h2 : ρ g (v - U'.starProjection v) ∈ U'ᗮ :=
      (hU'.orthogonal hρ).2 g _ (Submodule.sub_starProjection_mem_orthogonal (K := U') v)
    have e : ρ g v = ρ g (U'.starProjection v) + ρ g (v - U'.starProjection v) := by
      rw [← map_add (f := _), add_sub_cancel]
    rw [e, map_add (f := _), (Submodule.starProjection_eq_self_iff (K := U')).2 h1,
      (Submodule.starProjection_apply_eq_zero_iff U').2 h2, add_zero]

  obtain ⟨T', hT'a⟩ : ∃ T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H, ∀ w y, T' w y = U'.starProjection (T w y) :=
    ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H U'.starProjection).toLinearMap ∘ₗ T,
      fun _ _ => rfl⟩
  have hΦ' : ∀ w, T' w ∈ homDS M ρ ⊤ := fun w => mem_homPi.2 ⟨fun _ => trivial, fun τ g y => by
    rw [hT'a, hT'a, (hT.1 w).2 τ g y, hPc]⟩

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hρ (hT.1 x) ((map_ne_zero_iff T hinj).2 hx)
  have hBinv : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g v w => by
    change ⟪T (σ g w) _, T (σ g v) _⟫_ℂ = _
    rw [hTm.2.1, hTm.2.1, inner_map_map hρ]
    rfl
  have hCinv : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g v w => by
    change ⟪T (σ g w) _, T' (σ g v) _⟫_ℂ = _
    rw [hT'a, hTm.2.1, hTm.2.1, hPc, inner_map_map hρ, ← hT'a]
    rfl
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hC⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K hKo hKc W W σ σ hadm hadm.1 B C hBpos hBinv hCinv
  obtain ⟨c, hc⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K hKo hKc W σ hirr hadm φ hφ
  have key : ∀ x y, bePi (T' x) (T y) = conj c * bePi (T x) (T y) := fun x y => by
    have := hC x y
    rw [hc, LinearMap.smul_apply, LinearMap.id_apply, map_smulₛₗ, smul_eq_mul] at this
    exact this
  have hgen2 : ∀ u ∈ {v | ∃ w y, v = T w y}, ∀ u' ∈ {v | ∃ w y, v = T w y},
      ⟪u', U'.starProjection u - conj c • u⟫_ℂ = 0 := by
    rintro _ ⟨w, z, rfl⟩ _ ⟨w', z', rfl⟩
    rw [inner_sub_right, inner_smul_right, ← hT'a, inner_eq_bePi hδ hρ (hΦ' w) (hT.1 w'),
      inner_eq_bePi hδ hρ (hT.1 w) (hT.1 w'), key, mul_assoc, sub_self]
  exact eq_bot_or_eq_of_starProjection_eq_smul hU'le (conj c)
    (eq_smul_on_closure_span _ U'.starProjection (conj c) (fun v _ => hU'le (U'.starProjection_apply_mem v)) hgen2)
    hu0 hy0

end GlobalTheory.TrCopy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDS
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

theorem topologicalClosure_span_eq_top_of_le {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) (s : Set U)
    (h : U ≤ (Submodule.span ℂ (Subtype.val '' s)).topologicalClosure) :
    (Submodule.span ℂ s).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s) := by
    exact congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)
  have h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U)) := by
    rw [hmap, ← Submodule.topologicalClosure_coe]
    exact h hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  exact h2

theorem exists_isIrrUnitary_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)),
      IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  intro D V S M μ _ _ W _ _ σ hirr hadm hm
  classical
  have hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥ := fun h => hm (by rw [mCuspDS, h]; simp)
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinj : Function.Injective T := injective_of_mem_homInto hirr hT hT0
  have hTt : T ∈ homFinDS σ M (RG V μ) ⊤ := homTensorPi_mono le_top hT
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U :=
    ⟨_, rfl⟩
  have hcopy : IsCopyFinDS σ M (RG V μ) U := ⟨T, hTt, hinj, hUdef⟩
  have hU := TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy
  refine ⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩
  have hmem : ∀ w y, T w y ∈ U := fun w y =>
    hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)
  let T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U :=
    { toFun := fun w => (T w).codRestrict U (hmem w)
      map_add' := fun a b => by ext y; simp
      map_smul' := fun c a => by ext y; simp }
  have hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y := fun _ _ => rfl
  have hTm := mem_homTensorPi.1 hTt
  refine ⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩,
    fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩
  · exact hTm.2.1 g w y
  · exact hTm.2.2 i g w y
  · have himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨w, y, rfl⟩, rfl⟩
        exact ⟨w, y, rfl⟩
      · rintro ⟨w, y, rfl⟩
        exact ⟨T' w y, ⟨w, y, rfl⟩, rfl⟩
    exact topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))

end GlobalTheory.AutMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDSStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  first | exact @GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS | exact GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS | (intros; apply GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeries
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.AutMult

theorem isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  classical
  intro D V S M H _ _ π hπ W _ _ σ hσ hσa hc H' _ _ π' hπ' W' _ _ σ' hσ' hσa' hc'
  have := hπ.complete
  have := hπ'.complete
  obtain ⟨T, hT, hTi, hTd⟩ := hc
  obtain ⟨T', hT', hTi', hTd'⟩ := hc'
  have hTf : T ∈ homFinDS σ M π ⊤ := hT
  have hTf' : T' ∈ homFinDS σ' M π' ⊤ := hT'
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  haveI : σ.IsIrreducible := hσ
  haveI : σ'.IsIrreducible := hσ'
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ.asModule
  haveI : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ'.asModule
  constructor
  · rintro ⟨A, hA⟩
    have hAs : ∀ g x, A.symm (π' g x) = π g (A.symm x) := fun g x => by
      apply A.injective
      rw [hA, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    let Ac : H' →L[ℂ] H := A.symm.toLinearIsometry.toContinuousLinearMap
    let T'' : W' →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
      (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H' H Ac).toLinearMap ∘ₗ T'
    have hT''v : ∀ w y, T'' w y = A.symm (T' w y) := fun _ _ => rfl
    have hT'' : ∀ w, T'' w ∈ homDS M π ⊤ := fun w => ⟨fun _ => trivial, fun τ g y => by
      rw [hT''v, hT''v, hTm'.2.2, hAs]⟩
    let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    let C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T'' w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
      bePi_self_pos hδ hπ.unitary (hT.1 x) ((map_ne_zero_iff T hTi).2 hx)
    have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
      change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
      rw [hTm.2.1, hTm.2.1, inner_map_map hπ.unitary]
    have hC : ∀ g x y, C (σ g x) (σ' g y) = C x y := fun g x y => by
      change ⟪T'' (σ' g y) _, T (σ g x) _⟫_ℂ = ⟪T'' y _, T x _⟫_ℂ
      rw [hT''v, hT''v, hTm'.2.1, hAs, hTm.2.1, inner_map_map hπ.unitary]
    obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
    obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W' σ σ' hσa hσa'.1 B C hBpos hB hC
    obtain ⟨w', hw'⟩ := exists_ne (0 : W')
    have h1 : T'' w' ≠ 0 := by
      intro h
      apply hw'
      apply hTi'
      rw [map_zero]
      ext y
      apply A.symm.injective
      rw [← hT''v, h]
      simp
    obtain ⟨y', hy'⟩ : ∃ y', T'' w' y' ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    obtain ⟨w, y, hwy⟩ : ∃ w y, ⟪T'' w' y', T w y⟫_ℂ ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hy'
      have hsub : Submodule.span ℂ {v | ∃ w y, v = T w y} ≤ (ℂ ∙ T'' w' y')ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨w, y, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hn w y))
      have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
      rw [hTd] at hcl
      exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
    have hC0 : C w w' ≠ 0 := fun h => hwy (by
      rw [inner_eq_bePi hδ hπ.unitary (hT.1 w) (hT'' w') y y']
      change C w w' * _ = 0
      rw [h, zero_mul])
    have hφ0 : φ w' ≠ 0 := fun h => hC0 (by rw [hCB, h, map_zero])
    let f : Representation.IntertwiningMap σ' σ := ⟨φ, fun g => LinearMap.ext fun y => hφ g y⟩
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hf0
    · exact ⟨(Representation.IntertwiningMap.ofBijective f hb).symm⟩
    · exact absurd (congrArg (fun F : Representation.IntertwiningMap σ' σ => F w') hf0) hφ0
  · rintro ⟨e⟩
    let T₂ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H' := T' ∘ₗ e.toLinearMap
    have hT₂ : T₂ ∈ homFinDS σ M π' ⊤ := by
      refine mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => ?_, fun τ g w y => hTm'.2.2 τ g (e w) y⟩
      change T' (e (σ g w)) y = _
      rw [show e (σ g w) = σ' g (e w) from Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w]
      exact hTm'.2.1 g (e w) y
    obtain ⟨B, hB, hBv⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hσ hσa H π hπ.unitary T hTf hTi hTd H' π'
      hπ'.unitary ⊤ isClosed_univ T₂ hT₂
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : T' (e w) ≠ 0 := fun h => hw (e.injective (hTi' (h.trans (map_zero T').symm) |>.trans (map_zero e).symm))
    obtain ⟨y, hy⟩ : ∃ y, T' (e w) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    have hB0 : B ≠ 0 := fun h => hy (by rw [← show B (T w y) = T' (e w) y from hBv w y, h]; rfl)
    have hm : multIn π π' ⊤ ≠ 0 := by
      intro h0
      rw [multIn, Submodule.rank_eq_zero] at h0
      exact hB0 (by simpa [h0] using hB)
    obtain ⟨f, hf⟩ := uEquiv_of_multIn_ne_zero hπ hπ' hm
    exact ⟨f, hf⟩

end GlobalTheory.AutMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeriesStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  first | exact @GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | exact GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | (intros; apply GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModel
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutMult

open scoped InnerProductSpace
open GlobalTheory.Cusp


open Classical in
theorem rank_homIn_eq_rank_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W} (hirr : σ.IsIrreducible)
    (hadm : IsAdmissible σ) (hcopy : IsCopyFinDS σ M π ⊤) {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : GA D V →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) {U : Submodule ℂ K} (hU : IsClosed (U : Set K)) :
    Module.rank ℂ (homIn π ρ U) = Module.rank ℂ (homFinDS σ M ρ U) := by
  obtain ⟨T, hT, hinj, hd⟩ := hcopy
  have hTm := mem_homTensorPi.1 hT
  let f : homIn π ρ U →ₗ[ℂ] (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) :=
    { toFun := fun A => (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H K (A : H →L[ℂ] K)).toLinearMap ∘ₗ T
      map_add' := fun A B => by ext w y; simp
      map_smul' := fun c A => by ext w y; simp }
  have hmem : ∀ A, f A ∈ homFinDS σ M ρ U := fun A => by
    refine mem_homTensorPi.2 ⟨fun w y => ?_, fun g w y => ?_, fun i g w y => ?_⟩
    · exact A.2.1 _
    · change (A : H →L[ℂ] K) (T (σ g w) y) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.1 g w y)).trans (A.2.2 _ _)
    · change (A : H →L[ℂ] K) (T w _) = _
      exact (congrArg (A : H →L[ℂ] K) (hTm.2.2 i g w y)).trans (A.2.2 _ _)
  let F : homIn π ρ U →ₗ[ℂ] homFinDS σ M ρ U := f.codRestrict _ hmem
  have hdense : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
    (Submodule.dense_iff_topologicalClosure_eq_top).2 hd
  have hbij : Function.Bijective F := by
    constructor
    · intro A B hAB
      have e : ∀ w y, (A : H →L[ℂ] K) (T w y) = (B : H →L[ℂ] K) (T w y) := fun w y =>
        congrArg (fun Φ : homFinDS σ M ρ U => ((Φ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H K) w) y) hAB
      refine Subtype.ext (ContinuousLinearMap.ext_on hdense ?_)
      rintro _ ⟨w, y, rfl⟩
      exact e w y
    · intro Φ
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hirr hadm H π hπ T hT hinj hd K ρ hρ U hU Φ.1 Φ.2
      exact ⟨⟨A, hA⟩, Subtype.ext (LinearMap.ext fun w => ContinuousMultilinearMap.ext fun y => hAe w y)⟩
  exact (LinearEquiv.ofBijective F hbij).rank_eq


open Classical in
theorem mCusp_eq_mCuspDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  intro D V S M μ _ _ H _ _ π hπ W _ _ σ hirr hadm hcopy
  haveI : CompleteSpace H := hπ.complete
  exact rank_homIn_eq_rank_homFinDS hπ.unitary hirr hadm hcopy (isUnitaryRep_RG V μ) (isSubrep_L2cusp V μ).1

end GlobalTheory.AutMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → mCusp V μ π = mCuspDS μ σ M := by
  first | exact @GlobalTheory.AutMult.mCusp_eq_mCuspDS | exact GlobalTheory.AutMult.mCusp_eq_mCuspDS | (intros; apply GlobalTheory.AutMult.mCusp_eq_mCuspDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily
open Finset

namespace GlobalTheory

theorem hasSum_eq_sum_of_matching_family : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  intro C n m t m' c R s hs h1 h2 h3 h4 h5
  classical
  set P : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => m' i ≠ 0) with hPdef
  let g : P → C := fun i => Classical.choose (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have hg : ∀ i : P, R (g i) i.1 := fun i => Classical.choose_spec (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have ginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    have hj := hg j
    rw [← hij] at hj
    exact h4 _ _ _ (hg i) hj
  have hT : ∀ x ∉ (Finset.univ.image g), (m x : ℂ) * t x = 0 := by
    intro x hx
    by_contra hne
    have hm : m x ≠ 0 := by intro h; apply hne; simp [h]
    have ht : t x ≠ 0 := by intro h; apply hne; simp [h]
    obtain ⟨i, hi⟩ := h1 x hm ht
    have hmi : m' i ≠ 0 := by rw [← (h3 x i hi).1]; exact hm
    have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmi⟩
    apply hx
    rw [Finset.mem_image]
    exact ⟨⟨i, hiP⟩, Finset.mem_univ _, h5 _ _ _ (hg ⟨i, hiP⟩) hi⟩
  have hs2 : HasSum (fun x => (m x : ℂ) * t x) (∑ x ∈ Finset.univ.image g, (m x : ℂ) * t x) := hasSum_sum_of_ne_finset_zero hT
  rw [hs.unique hs2, Finset.sum_image (fun i _ j _ h => ginj h)]
  rw [← Finset.sum_filter_of_ne (p := fun i => m' i ≠ 0) (fun i _ hne => by intro h; apply hne; simp [h])]
  rw [← hPdef, ← Finset.sum_attach P (fun i => (m' i : ℂ) * c i), Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [(h3 _ _ (hg i)).1, (h3 _ _ (hg i)).2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamilyStatement
open Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  first | exact @GlobalTheory.hasSum_eq_sum_of_matching_family | exact GlobalTheory.hasSum_eq_sum_of_matching_family | (intros; apply GlobalTheory.hasSum_eq_sum_of_matching_family <;> assumption)
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpecTraceProof

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem isCopyFinDS_of_equiv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : GA D V →* (H →L[ℂ] H)} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ (GfC V) W} {σ' : Representation ℂ (GfC V) W'} (f : σ.Equiv σ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ' M ρ ⊤ := by
  obtain ⟨T, hT, hinj, hspan⟩ := h
  refine ⟨T ∘ₗ f.symm.toLinearEquiv.toLinearMap, ?_, hinj.comp f.symm.toLinearEquiv.injective, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => h3 i g _ y⟩
    have e : f.symm.toLinearEquiv (σ' g w) = σ g (f.symm.toLinearEquiv w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' g) w
    have h2' := h2 g (f.symm.toLinearEquiv w) y
    rw [← e] at h2'
    exact h2'
  · rw [← hspan]
    congr 2
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, y, hv⟩ => ⟨_, y, hv⟩, fun ⟨w, y, hv⟩ => ⟨f.toLinearEquiv w, y, by simpa using hv⟩⟩


open Classical in
theorem isCopyFinDS_of_uEquiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : GA D V →* (H →L[ℂ] H)} {ρ' : GA D V →* (H' →L[ℂ] H')} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hρ : UEquiv ρ ρ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ M ρ' ⊤ := by
  obtain ⟨A, hA⟩ := hρ
  obtain ⟨T, hT, hinj, hspan⟩ := h
  let C := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H'
    (A.toContinuousLinearEquiv : H →L[ℂ] H')).toLinearMap
  have hC : ∀ w y, (C ∘ₗ T) w y = A (T w y) := fun _ _ => rfl
  refine ⟨C ∘ₗ T, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => ?_⟩
    · rw [hC, hC, h2, hA]
    · rw [hC, hC, h3, hA]
  · intro w w' e
    refine hinj (ContinuousMultilinearMap.ext fun y => A.injective ?_)
    rw [← hC, ← hC, e]
  · have hS : {v | ∃ w y, v = (C ∘ₗ T) w y} = A '' {v | ∃ w y, v = T w y} := by
      ext v
      simp only [hC, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨w, y, hv⟩ => ⟨_, ⟨w, y, rfl⟩, hv.symm⟩, fun ⟨_, ⟨w, y, rfl⟩, hv⟩ => ⟨w, y, hv.symm⟩⟩
    rw [hS]
    have hd : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 hspan
    refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
    have e2 : (Submodule.span ℂ ((A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y}) : Set H') =
        (A.toLinearEquiv : H →ₗ[ℂ] H') '' (Submodule.span ℂ {v | ∃ w y, v = T w y} : Set H) := by
      rw [Submodule.span_image, Submodule.map_coe]
    have e3 : (A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y} = A '' {v | ∃ w y, v = T w y} := rfl
    rw [← e3, e2]
    exact A.surjective.denseRange.dense_image A.continuous hd

theorem not_isIntegralOp_zero {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    {ν : Measure G} {σ : Representation ℂ G W} {F : G → ℂ} {c : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ F c) (hc : c ≠ 0) : ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ F 0 := by
  intro h0
  obtain ⟨A, hA, -, rfl⟩ := h
  obtain rfl := hA.unique h0
  refine hc ?_
  have e : (LinearMap.restrict (0 : W →ₗ[ℂ] W) (p := LinearMap.range (0 : W →ₗ[ℂ] W))
      (q := LinearMap.range (0 : W →ₗ[ℂ] W)) fun v _ => LinearMap.mem_range_self _ v) = 0 :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [e, map_zero]

theorem specTrace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → SpecTrace := by
  intro hDSC _ _ _ hFlath hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.T.discrete_series_multiplicity hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := GlobalTheory.T.discrete_series_model_trace_terms hDSC hFlath hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := GlobalTheory.T.exists_irreducibleUnitary_completion_finiteTimesDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [GlobalTheory.T.cuspMultiplicity_completion_eq_discreteSeriesModel D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

end GlobalTheory.SpecTraceProof

end
