module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaG
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem tfg_gen {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (S : Submodule ℂ (Fin n → M))
    (hV : tensSub V ≤ S) (hS : ∀ a b, ∀ f ∈ S, tensF dual E a b f ∈ S) : tensSub (genSub E V) ≤ S := by
  let T : Submodule ℂ M := ⨅ c, S.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hT : ∀ m, m ∈ T ↔ ∀ c, (Pi.single c m : Fin n → M) ∈ S := fun m => by simp [T, Submodule.mem_iInf]
  have hle : genSub E V ≤ T := sInf_le ⟨fun v hv => (hT v).2 fun c => hV (tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using hv
      · simp [h]),
    fun a b m hm => (hT _).2 fun c => by
      have hm' := (hT m).1 hm
      cases dual
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF false E a b (Pi.single c m) - if b = c then Pi.single a m else 0 := by
          funext d
          simp only [tensF, cond_false, Pi.sub_apply, tensV_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = a <;> by_cases h3 : b = c <;>
            simp_all
        rw [e]
        refine S.sub_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' a
        · exact S.zero_mem
      · have e : (Pi.single c (E a b m) : Fin n → M) =
            tensF true E a b (Pi.single c m) + if a = c then Pi.single b m else 0 := by
          funext d
          simp only [tensF, cond_true, Pi.add_apply, tensVd_coord]
          by_cases h1 : d = c <;> by_cases h2 : d = b <;> by_cases h3 : a = c <;>
            simp_all
        rw [e]
        refine S.add_mem (hS a b _ (hm' c)) ?_
        split_ifs
        · exact hm' b
        · exact S.zero_mem⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact S.sum_mem fun c _ => (hT _).1 (hle (tset_mem.mp hf c)) c

theorem tfg_real {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ X} (hU : IsInfUnitary ε E) {c : ℂ} {v : X}
    (h : casimir E v = c • v) : casimir E v = ((c.re : ℝ) : ℂ) • v := by
  by_cases hv : v = 0
  · simp [hv]
  have h1 : inner ℂ (casimir E v) v = inner ℂ v (casimir E v) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have e1 := hU b a v (E b a v)
    have e2 := hU a b (E b a v) v
    have e3 : inner ℂ v (E a b (E b a v)) = starRingEnd ℂ (inner ℂ (E a b (E b a v)) v) :=
      (inner_conj_symm _ _).symm
    rw [e3, e2, map_mul, inner_conj_symm]
    congr 1
    unfold adjSign; split_ifs <;> simp
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 := mul_right_cancel₀ (inner_self_ne_zero.mpr hv) h1
  rw [h, Complex.conj_eq_iff_re.mp h2]

theorem tf_closure_stable (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {y : D} (hy : y ∈ genSub E V) :
    ∀ g ∈ UJset ε, ∀ v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure,
      tfRdiag ε g v ∈ (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure := by
  have hη : ∀ c, (Pi.single c (tfSgn ε c • y) : Fin n → D) ∈ tensSub (genSub E V) := fun c =>
    tset_mem.mpr fun d => by
      by_cases h : d = c
      · subst h; simpa using Submodule.smul_mem _ _ hy
      · simp [h]
  have hco : ∀ c, (fun d => (((Pi.single c (tfSgn ε c • y) : Fin n → D) d : D) : H)) =
      Pi.single c (tfSgn ε c • (y : H)) := fun c => funext fun d => by
    by_cases h : d = c
    · subst h; simp
    · simp [h]
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (hη c) f hf
  simp only [hco] at hce
  have hR := tfRdiag_isURepOn ε
  have hDR := isDerivedOn_smE hR
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        cases dual <;> simp [coefMap, tensGrp, inner_sum, inner_smul_right, mul_sum,
          mul_assoc, mul_left_comm, mul_comm]) }
  have hΦE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
      Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f =>
    Subtype.ext (vectorL2_ext fun c => by
      refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
      refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
      exact (hce c f.1 f.2).2.1 a b g hg)
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let Ξ := Φ ∘ₗ P'
  have hΞE : ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Ξ f) =
      Ξ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := fun a b f => by
    refine (hΦE a b (P' f)).trans (congrArg Φ (Subtype.ext ?_))
    exact (hP.2.1 a b f.1 f.2).symm
  let W : Submodule ℂ (tensSub (n := n) (genSub E V)) := (tensSub V).comap (tensSub (genSub E V)).subtype
  have := hV.1
  have hVle : tensSub (n := n) V ≤ tensSub (genSub E V) := fun f hf =>
    tset_mem.mpr fun c => Submodule.mem_sInf.mpr fun _ hT => hT.1 (tset_mem.mp hf c)
  have hfd : FiniteDimensional ℂ (tensSub (n := n) V) :=
    Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict V
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub V).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hW' : FiniteDimensional ℂ W := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hVle).symm
  have hkst : IsKStableSub ε (smE ε (tfRdiag ε)) (W.map Ξ) := by
    rintro a b hab _ ⟨f, hf, rfl⟩
    refine ⟨_, ?_, (hΞE a b f).symm⟩
    have hf' := tset_mem.mp (show f.1 ∈ tensSub V from hf)
    refine tset_mem.mpr fun c => ?_
    show tensF dual E a b f.1 c ∈ V
    cases dual
    · simp only [tensF, cond_false, tensV_coord]
      exact V.add_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' b, V.zero_mem])
    · simp only [tensF, cond_true, tensVd_coord]
      exact V.sub_mem (hV.2.1 a b hab _ (hf' c)) (by split_ifs; exacts [hf' a, V.zero_mem])
  have hcas : ∀ v ∈ W.map Ξ, casimir (smE ε (tfRdiag ε)) v =
      (((((casVal lam : ℝ) : ℂ) + n + 2 * z).re : ℝ) : ℂ) • v := by
    rintro _ ⟨f, -, rfl⟩
    refine tfg_real (isInfUnitary_of_isDerivedOn hR hDR) ?_
    have h3 : diagOp (casimir E) (P f.1) = ((casVal lam : ℝ) : ℂ) • P f.1 := funext fun c => by
      rw [diagOp_coord, casimir_genSub hD.glRep hc _ (tset_mem.mp (hP.1 _ f.2) c)]; rfl
    have h2 : casimir (tensF dual E) (P f.1) = (((casVal lam : ℝ) : ℂ) + n + 2 * z) • P f.1 := by
      rw [add_smul, add_smul, mul_smul, ← hEP f.1 f.2, ← h3]
      cases dual
      · exact LinearMap.congr_fun (casimir_tensV hD.glRep) _
      · exact LinearMap.congr_fun (casimir_tensVd hD.glRep) _
    show casimir _ (Φ (P' f)) = _ • Φ (P' f)
    rw [← map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hΦE, ← map_sum]
    refine congrArg Φ (Subtype.ext ?_)
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [show ((P' f : tensSub (n := n) (genSub E V)) : Fin n → D) = P f.1 from rfl, ← h2]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply]
  have hgen : genSub (smE ε (tfRdiag ε)) (W.map Ξ) = LinearMap.range Ξ := by
    refine le_antisymm (sInf_le ⟨LinearMap.map_le_range, ?_⟩) ?_
    · rintro a b _ ⟨f, rfl⟩
      exact ⟨_, (hΞE a b f).symm⟩
    · rintro _ ⟨f, rfl⟩
      have h1 := tfg_gen dual E V (((genSub (smE ε (tfRdiag ε)) (W.map Ξ)).comap Ξ).map
        (tensSub (genSub E V)).subtype)
        (fun f hf => ⟨⟨f, hVle hf⟩, Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨_, hf, rfl⟩, rfl⟩)
        (by
          rintro a b _ ⟨f, hf, rfl⟩
          refine ⟨⟨_, tensSub_stable dual a b f.1 f.2⟩, ?_, rfl⟩
          show Ξ _ ∈ genSub _ _
          rw [← hΞE]
          exact tset_genSub_E _ _ a b hf) f.2
      obtain ⟨f', hf', e⟩ := h1
      rwa [← Subtype.ext e]
  have hspan : Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
      v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} =
      (genSub (smE ε (tfRdiag ε)) (W.map Ξ)).map (smD ε (tfRdiag ε)).subtype := by
    rw [hgen, ← Submodule.span_eq (Submodule.map _ _)]
    congr 1
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f.1, f.2, rfl⟩
  rw [hspan]
  exact closure_genSub_stable hR hDR inferInstance hkst hcas

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaE
noncomputable section

open Finset MeasureTheory
open Formalism.MainNotions.S (umat)

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

private theorem memLp_of_weighted_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (y : H)
    (hW : MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) :=
    continuous_const.inner ((hσ.2.2 y).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton (Formalism.REAL.UJ ε) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 (Fin.cast hn i)))⟩
    have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
    refine MemLp.of_bound hcont.aestronglyMeasurable (‖y‖ * ‖y‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖inner ℂ y (σ (umat g) y)‖ ≤ ‖y‖ * ‖σ (umat g) y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  · refine hW.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have hs : 1 ≤ Real.sqrt (S7.hs (umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) hs

private theorem memLp_coefficients {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) (v w : H) :
    MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  have hall (x : H) : MemLp (fun g => inner ℂ y (ρ g x)) 2 μ :=
    GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 x
  have hinv := ((hall w).comp_measurePreserving hInv).star
  have e : star ((fun g => inner ℂ y (ρ g w)) ∘ Inv.inv) = fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs := GraphTrick.star_eq (ρ := ρ) hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e] at hinv
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hinv v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ (w : H) (σ (umat g) (v : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  let ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (umat g)
  have hone : ρ 1 = 1 := by
    change tfClRep σ (closGen E V) 1 = 1
    exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    exact hU.1.2 (umat a) (umat_mem_UJset ε a) (umat b) (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 (umat g) (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = fun g => inner ℂ (y : H) (σ (umat g) (y : H)) := by
    funext g
    change inner ℂ (y : H) (↑(tfClRep σ (closGen E V) (umat g) y0) : H) = _
    rw [tfClRep_coe σ _ (hst (umat g) (umat_mem_UJset ε g))]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    rw [hcoe]
    exact memLp_of_weighted_diagonal hσ (y : H) (hW y hyG y hyG)
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  exact memLp_coefficients (ρ := ρ) (MeasureTheory.measurePreserving_mul_right (Formalism.REAL.muG ε))
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaD
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem coe_toL2_ae_eq_of_memLp {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ((toL2 ε F : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun g => F (Formalism.MainNotions.S.umat g) := by
  unfold toL2
  rw [dite_eq_left h]
  exact h.coeFn_toLp

theorem tfd_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool) (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ζ : Fin n → H) (c : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ g =
      tfSgn ε c * ∑ d, tfCoef dual g c d * inner ℂ y (σ g (ζ d)) := by
  unfold coefMap
  rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left,
    tf_tensGrp_apply, inner_sum]
  simp only [inner_smul_right]
  congr 1
  exact tf_star_sgn ε c

theorem tensor_functor_separation (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {y : H} (hy : y ∈ closGen E V) {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V)
    (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    inner ℂ (tfPh dual ε σ y ζ) (tfJ ε (tfPh dual ε σ y ζ')) = tfFormBH ε ζ ζ' * inner ℂ y y / (d : ℂ) := by
  set F : (Fin n → H) → Fin n → Formalism.REAL.UJ ε → ℂ := fun ζ c g =>
    coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ (Formalism.MainNotions.S.umat g) with hF
  have h1 : ∀ c, inner ℂ (tfPh dual ε σ y ζ c) (tfJ ε (tfPh dual ε σ y ζ') c) =
      ∫ g, tfSgn ε c * (star (F ζ c g) * F ζ' c g) ∂(Formalism.REAL.muG ε) := fun c => by
    rw [tfJ_apply, inner_smul_right, integral_const_mul, tfPh_apply, tfPh_apply, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coe_toL2_ae_eq_of_memLp (hm c), coe_toL2_ae_eq_of_memLp (hm' c)] with g e1 e2
    rw [e1, e2, RCLike.inner_apply, mul_comm]
    rfl
  have hi : ∀ c, Integrable (fun g => tfSgn ε c * (star (F ζ c g) * F ζ' c g)) (Formalism.REAL.muG ε) :=
    fun c => ((hm c).star.integrable_mul (hm' c)).const_mul _
  have hs := fun c => tfClRep_schur hgap hσ hD hV hc hVK hd hy (hζ' c) hy (hζ c)
  rw [PiLp.inner_apply, sum_congr rfl fun c _ => h1 c, ← integral_finsetSum _ fun c _ => hi c]
  have h2 : ∀ g : Formalism.REAL.UJ ε, ∑ c, tfSgn ε c * (star (F ζ c g) * F ζ' c g) =
      ∑ c, tfSgn ε c * (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)) *
        star (inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c)))) := fun g => by
    have h3 := tf_jquad (tfCoef dual (Formalism.MainNotions.S.umat g)) (tfSgn ε) (tfCoef_orth dual (umat_mem_UJset ε g))
      (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ c))) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' c)))
    refine Eq.trans (sum_congr rfl fun c _ => ?_) (h3.trans (sum_congr rfl fun c _ => by ring))
    simp only [hF, tfd_coef, star_mul', tf_star_sgn]
    linear_combination (tfSgn ε c * star (∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
      inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ d))) * ∑ d, tfCoef dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ y (σ (Formalism.MainNotions.S.umat g) (ζ' d))) * tfSgn_mul_self ε c
  simp only [h2]
  rw [integral_finsetSum _ fun c _ => (hs c).1.const_mul _, tfFormBH, sum_mul, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, (hs c).2]
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaB
noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem tf_rep_closure {n : ℕ} {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hρ : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (S : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hS : ∀ v ∈ S, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v)) :
    ∀ v ∈ S.topologicalClosure, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v) := by
  intro v hv c
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have huc : Tendsto (fun k => u k c) atTop (𝓝 (v c)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => PiLp.dist_apply_le _ _ c) (tendsto_iff_dist_tendsto_zero.1 hu))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huc).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ k, ((u k c : Lp ℂ 2 μ) : G → ℂ) g = inner ℂ (w c) (ρ g (u k)) :=
    ae_all_iff.2 (fun k => hS (u k) (huS k) c)
  filter_upwards [hns, hall] with g hg hgall
  have h2 : Tendsto (fun i => inner ℂ (w c) (ρ g (u (ns i)))) atTop (𝓝 (inner ℂ (w c) (ρ g v))) := by
    have h3 : Tendsto (fun i => u (ns i)) atTop (𝓝 v) :=
      hu.comp (hmono.tendsto_atTop)
    exact ((continuous_const.inner continuous_id).tendsto _).comp ((ρ g).continuous.tendsto v |>.comp h3)
  simp only [hgall] at hg
  exact tendsto_nhds_unique hg h2

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

section TR

variable {n : ℕ} {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G] {μ : Measure G} [μ.IsInvInvariant]

theorem tf_inner_conj_conj (a b : ℂ) :
    inner ℂ (starRingEnd ℂ a) (starRingEnd ℂ b) = starRingEnd ℂ (inner ℂ a b) := by
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]

theorem tf_tr_swap (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hadj : ∀ g x y, inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y))
    (J : PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)) (s : Fin n → ℝ)
    (hJ : ∀ x c, J x c = (s c : ℂ) • x c) (hρJ : ∀ g x, ρ g (J x) = J (ρ g x))
    (HP : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))) [HP.HasOrthogonalProjection]
    (hst : ∀ g, ∀ v ∈ HP, ρ g v ∈ HP) (d : ℝ) (u w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (hu : ∀ c, u c ∈ HP) (hw : ∀ c, w c = (d : ℂ) • HP.starProjection (J (u c)))
    (hrep : ∀ v ∈ HP, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v))
    (c c' : Fin n) :
    inner ℂ (u c c') (w c c') = starRingEnd ℂ (inner ℂ (u c' c) (w c' c)) := by
  have hJs : ∀ x y, inner ℂ (J x) y = inner ℂ x (J y) := by
    intro x y
    simp only [PiLp.inner_apply, hJ, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hP : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hwm : ∀ c, w c ∈ HP := fun c => by
    rw [hw c]; exact HP.smul_mem _ (Submodule.starProjection_apply_mem HP _)
  have k1 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (u b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (u a))) := by
    intro g a b
    rw [inner_conj_symm, hw a, hw b, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    calc inner ℂ (HP.starProjection (J (u a))) (ρ g⁻¹ (u b))
        = inner ℂ (J (u a)) (HP.starProjection (ρ g⁻¹ (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
      _ = inner ℂ (J (u a)) (ρ g⁻¹ (u b)) := by rw [hP _ (hst _ _ (hu b))]
      _ = inner ℂ (u a) (ρ g⁻¹ (J (u b))) := by rw [hJs, hρJ]
      _ = inner ℂ (ρ g (u a)) (J (u b)) := (hadj _ _ _).symm
      _ = inner ℂ (HP.starProjection (ρ g (u a))) (J (u b)) := by rw [hP _ (hst _ _ (hu a))]
      _ = inner ℂ (ρ g (u a)) (HP.starProjection (J (u b))) :=
          Submodule.inner_starProjection_left_eq_right HP _ _
  have k2 : ∀ g a b, inner ℂ (w a) (ρ g⁻¹ (w b)) = starRingEnd ℂ (inner ℂ (w b) (ρ g (w a))) := by
    intro g a b
    rw [inner_conj_symm, hadj]
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  have e1 : ∫ g, inner ℂ ((u c c' : Lp ℂ 2 μ) g) ((w c c' : Lp ℂ 2 μ) g) ∂μ =
      ∫ g, inner ℂ (inner ℂ (w c') (ρ g (u c))) (inner ℂ (w c') (ρ g (w c))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c) c', hrep _ (hwm c) c'] with g h1 h2
    rw [h1, h2]
  have e2 : ∫ g, starRingEnd ℂ (inner ℂ ((u c' c : Lp ℂ 2 μ) g) ((w c' c : Lp ℂ 2 μ) g)) ∂μ =
      ∫ g, starRingEnd ℂ (inner ℂ (inner ℂ (w c) (ρ g (u c'))) (inner ℂ (w c) (ρ g (w c')))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hrep _ (hu c') c, hrep _ (hwm c') c] with g h1 h2
    rw [h1, h2]
  rw [e1, e2, ← integral_inv_eq_self _ μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [k1, k2, tf_inner_conj_conj]

end TR

section Core

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_single_smul_mem {D : Submodule ℂ H} {S : Submodule ℂ D} (c : Fin n) (a : ℂ) {y : D} (hy : y ∈ S) :
    (Pi.single c (a • y) : Fin n → D) ∈ tensSub S := by
  rw [tset_mem]
  intro i
  by_cases h : i = c
  · subst h; simpa using S.smul_mem a hy
  · simp [h]

theorem tf_coe_single {D : Submodule ℂ H} (c : Fin n) (a : ℂ) (y : D) :
    (fun i => (((Pi.single c (a • y) : Fin n → D) i : D) : H)) = Pi.single c (a • (y : H)) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_coe_single' {D : Submodule ℂ H} (c : Fin n) (y : D) :
    (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) = Pi.single c (y : H) := by
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

theorem tf_ph_memLp (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {y : D} (hy : y ∈ genSub E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) (c : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
      (fun d => ((f d : D) : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have h := ((coef_embed dual hσ hD hsm hgap hV hc hVK hW _ (tf_single_smul_mem c (tfSgn ε c) hy) f hf).1).2 []
  rw [tf_coe_single] at h
  exact h

theorem tfRdiag_tfPh (dual : Bool) {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε) (y : H) (ζ : Fin n → H) :
    tfRdiag ε h (tfPh dual ε σ y ζ) = tfPh dual ε σ y (tensGrp dual σ h ζ) := by
  refine vectorL2_ext fun c => ?_
  rw [tfRdiag_apply, tfPh_apply, tfPh_apply, rightRegular_toL2 ε _ hh]
  refine toL2_congr_of_eq_on_UJset fun x hx => ?_
  simp only [coefMap]
  rw [tf_tensGrp_mul dual hσ hx hh]

theorem tfJ_inner (ε : Fin n → Bool) (x x' : tfL2n ε) : inner ℂ (tfJ ε x) x' = inner ℂ x (tfJ ε x') := by
  simp only [PiLp.inner_apply, tfJ_apply, inner_smul_left, inner_smul_right]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  exact tf_star_sgn ε i

theorem tfFormBH_sub_left (ε : Fin n → Bool) (f f' g : Fin n → H) :
    tfFormBH ε (f - f') g = tfFormBH ε f g - tfFormBH ε f' g := by
  simp only [tfFormBH, Pi.sub_apply, inner_sub_left, mul_sub, sum_sub_distrib]

end Core

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem tf_trace_data (dual : Bool) {lam : Fin n → ℝ} [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε))
    {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    (hPP : ∀ f ∈ tensSub (genSub E V), P (P f) = P f)
    (hPB : ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      tfFormBH ε (fun c => ((P f c : D) : H)) (fun c => ((g c : D) : H)) =
        tfFormBH ε (fun c => ((f c : D) : H)) (fun c => ((P g c : D) : H)))
    {z : ℂ} (hEP : ∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f)
    {c0 : ℂ} (hc0 : ∀ x ∈ genSub E V, ptr P x = c0 • x) {y : D} (hyV : y ∈ V) (hy0 : (y : H) ≠ 0) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) :
    ∃ (HP : Submodule ℂ (tfL2n ε)) (w : Fin n → tfL2n ε), IsClosed (HP : Set (tfL2n ε)) ∧
      HP = (Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
        v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))}).topologicalClosure ∧
      (∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP) ∧
      (∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v)) ∧
      c0 = (((∑ c, ‖w c‖ ^ 2) / d : ℝ) : ℂ) := by
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  have hyC : (y : H) ∈ closGen E V := Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩
  have hdpos : 0 < d := hd.1
  have hst0 := closGen_stable hgap hσ hD hV hc hVK

  set S : Submodule ℂ (tfL2n ε) := Submodule.span ℂ {v : tfL2n ε | ∃ f ∈ tensSub (genSub E V),
    v = tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H))} with hS
  set HP : Submodule ℂ (tfL2n ε) := S.topologicalClosure with hHP
  have hHPc : IsClosed (HP : Set (tfL2n ε)) := S.isClosed_topologicalClosure
  have : CompleteSpace HP := hHPc.completeSpace_coe
  have hst : ∀ g ∈ UJset ε, ∀ v ∈ HP, tfRdiag ε g v ∈ HP :=
    tf_closure_stable dual hσ hD hsm hgap hV hc hVK hW hP hEP hyG
  have hSHP : S ≤ HP := S.le_topologicalClosure
  have hPm : ∀ f ∈ tensSub (genSub E V), P f ∈ tensSub (genSub E V) := hP.1
  have hcoeC : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c : Fin n, ((f c : D) : H) ∈ closGen E V := fun f hf c =>
    Submodule.le_topologicalClosure _ ⟨f c, (tset_mem.1 hf) c, rfl⟩
  have hmem := fun {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) =>
    tf_ph_memLp dual hσ hD hsm hgap hV hc hVK hW hyG hf

  have hT2 := fun {ζ ζ' : Fin n → H} (hζ : ∀ c, ζ c ∈ closGen E V) (hζ' : ∀ c, ζ' c ∈ closGen E V)
    (hm : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hm' : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ' (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) =>
    tensor_functor_separation dual hσ hD hgap hV hc hVK hd hyC hζ hζ' hm hm'

  set Nr : ℝ := ‖(y : H)‖ ^ 2 with hNr
  have hNpos : 0 < Nr := pow_pos (norm_pos_iff.2 hy0) 2
  have hNc : inner ℂ (y : H) (y : H) = (Nr : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hNr, Complex.ofReal_pow]
    rfl
  set κ : ℝ := d / Nr with hκ
  have hκpos : 0 < κ := div_pos hdpos hNpos
  have hsing : ∀ b, (Pi.single b y : Fin n → D) ∈ tensSub (genSub E V) := fun b => by
    simpa using tf_single_smul_mem b (1 : ℂ) hyG
  set u : Fin n → tfL2n ε := fun b => tfPh dual ε σ (y : H) (fun c => ((P (Pi.single b y) c : D) : H)) with hu
  have huHP : ∀ b, u b ∈ HP := fun b => hSHP (Submodule.subset_span ⟨_, hsing b, rfl⟩)
  set a : Fin n → tfL2n ε := fun b => HP.starProjection (tfJ ε (u b)) with ha
  set w : Fin n → tfL2n ε := fun b => (κ : ℂ) • a b with hw
  have haHP : ∀ b, a b ∈ HP := fun b => Submodule.starProjection_apply_mem HP _
  have hwHP : ∀ b, w b ∈ HP := fun b => HP.smul_mem _ (haHP b)
  have hPself : ∀ v ∈ HP, HP.starProjection v = v := fun v hv => Submodule.starProjection_eq_self_iff.2 hv
  have hproj : ∀ x v, v ∈ HP → inner ℂ (HP.starProjection x) v = inner ℂ x v := by
    intro x v hv
    rw [Submodule.inner_starProjection_left_eq_right HP, hPself v hv]
  have hsubι : ∀ f g : Fin n → D, (fun c => (((f - g) c : D) : H)) =
      (fun c => ((f c : D) : H)) - (fun c => ((g c : D) : H)) := by
    intro f g; funext c; simp

  have hA : ∀ η ∈ tensSub (genSub E V), ∀ v ∈ HP,
      inner ℂ (tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H)))) v = 0 := by
    intro η hη
    have hη' : η - P η ∈ tensSub (genSub E V) := Submodule.sub_mem _ hη (hPm η hη)
    set q := tfJ ε (tfPh dual ε σ (y : H) (fun c => (((η - P η) c : D) : H))) with hq
    have hle : S ≤ (ℂ ∙ q)ᗮ := by
      rw [hS, Submodule.span_le]
      rintro v ⟨f, hf, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, hq, tfJ_inner,
        hT2 (hcoeC _ hη') (hcoeC _ (hPm f hf)) (hmem hη') (hmem (hPm f hf)), hsubι, tfFormBH_sub_left,
        ← hPB η hη f hf, hPB η hη (P f) (hPm f hf), hPP f hf, ← hPB η hη f hf, sub_self, zero_mul, zero_div]
    intro v hv
    have h2 : v ∈ (ℂ ∙ q)ᗮ := Submodule.topologicalClosure_minimal S hle (Submodule.isClosed_orthogonal _) hv
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2)

  have hcoefS : ∀ (c : Fin n) (ζ : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ),
      coefMap dual σ (Pi.single c (tfSgn ε c • (y : H))) ζ g = tfSgn ε c * inner ℂ (y : H) (tensGrp dual σ g ζ c) := by
    intro c ζ g
    unfold coefMap
    rw [sum_eq_single c (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same, inner_smul_left]
    congr 1
    exact tf_star_sgn ε c
  have hformS : ∀ (c : Fin n) (ζ : Fin n → H),
      tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H)) ζ = tfSgn ε c * inner ℂ (y : H) (ζ c) := by
    intro c ζ
    rw [tf_coe_single', tfFormBH_single_left]

  have htr : ∀ f ∈ tensSub (genSub E V), ∀ g : Formalism.REAL.UJ ε,
      (∀ c, tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H)) c ∈ closGen E V) ∧
      ∀ c, MemLp (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) 2 (Formalism.REAL.muG ε) := by
    intro f hf g
    refine ⟨fun c => ?_, fun c => ?_⟩
    · rw [tf_tensGrp_apply]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (hst0 _ (umat_mem_UJset ε g) _ (hcoeC _ (hPm f hf) d))
    · have h1 := (hmem (hPm f hf) c).comp_measurePreserving (measurePreserving_mul_right ε g)
      have e : (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) (Formalism.MainNotions.S.umat x)) =
          (fun x : Formalism.REAL.UJ ε => coefMap dual σ (Pi.single c (tfSgn ε c • (y : H)))
            (fun i => ((P f i : D) : H)) (Formalism.MainNotions.S.umat x)) ∘ (fun x => x * g) := by
        funext x
        simp only [Function.comp_apply, coefMap]
        rw [show Formalism.MainNotions.S.umat (x * g) = Formalism.MainNotions.S.umat x * Formalism.MainNotions.S.umat g from rfl,
          tf_tensGrp_mul dual hσ (umat_mem_UJset ε x) (umat_mem_UJset ε g)]
      rw [e]
      exact h1

  have hrepGen : ∀ f ∈ tensSub (genSub E V), ∀ c,
      ((tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)) c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H)))) := by
    intro f hf c
    filter_upwards [coe_toL2_ae_eq_of_memLp (hmem (hPm f hf) c)] with g hg
    rw [tfPh_apply, hg]
    obtain ⟨hζC, hζm⟩ := htr f hf g
    have hRv : tfRdiag ε (Formalism.MainNotions.S.umat g) (tfPh dual ε σ (y : H) (fun i => ((P f i : D) : H))) ∈ HP :=
      hst _ (umat_mem_UJset ε g) _ (hSHP (Submodule.subset_span ⟨f, hf, rfl⟩))
    have hs' : Pi.single c y - P (Pi.single c y) ∈ tensSub (genSub E V) :=
      Submodule.sub_mem _ (hsing c) (hPm _ (hsing c))
    have hA1 := hA _ (hsing c) _ hRv
    rw [tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), tfJ_inner,
      hT2 (hcoeC _ hs') hζC (hmem hs') hζm, hsubι, tfFormBH_sub_left] at hA1
    have hA2 : tfFormBH ε (fun i => (((Pi.single c y : Fin n → D) i : D) : H))
        (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) =
        tfFormBH ε (fun i => ((P (Pi.single c y) i : D) : H))
          (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun i => ((P f i : D) : H))) := by
      have hne : (inner ℂ (y : H) (y : H)) / (d : ℂ) ≠ 0 := by
        rw [hNc]
        exact div_ne_zero (Complex.ofReal_ne_zero.2 hNpos.ne') (Complex.ofReal_ne_zero.2 hdpos.ne')
      rw [mul_div_assoc] at hA1
      exact sub_eq_zero.1 ((mul_eq_zero.1 hA1).resolve_right hne)
    rw [hcoefS, ← hformS, hA2, hw]
    simp only
    rw [inner_smul_left, Complex.conj_ofReal, ha]
    simp only
    rw [hproj _ _ hRv, tfJ_inner, tfRdiag_tfPh dual hσ (umat_mem_UJset ε g), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing c))) hζC (hmem (hPm _ (hsing c))) hζm, hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hrepS : ∀ v ∈ S, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact hrepGen f hf
    | zero =>
      intro c
      filter_upwards [Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε)] with g hg
      rw [map_zero, inner_zero_right]
      exact hg
    | add x x' _ _ hx hx' =>
      intro c
      filter_upwards [Lp.coeFn_add (x c) (x' c), hx c, hx' c] with g h1 h2 h3
      rw [map_add (f := _), inner_add_right, ← h2, ← h3, ← Pi.add_apply, ← h1]
      rfl
    | smul r x _ hx =>
      intro c
      filter_upwards [Lp.coeFn_smul r (x c), hx c] with g h1 h2
      rw [map_smul, inner_smul_right, ← h2, ← smul_eq_mul, ← Pi.smul_apply, ← h1]
      rfl
  have hrep : ∀ v ∈ HP, ∀ c, ((v c : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun g => inner ℂ (w c) (tfRdiag ε (Formalism.MainNotions.S.umat g) v) :=
    tf_rep_closure (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g))
      (fun g x => le_of_eq ((tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) x)) w S hrepS

  have hT1 : c0 * (Nr : ℂ) = ∑ b, tfSgn ε b *
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    have h1 : inner ℂ (y : H) ((ptr P y : D) : H) = c0 * (Nr : ℂ) := by
      rw [hc0 y hyG, Submodule.coe_smul, inner_smul_right, hNc]
    rw [← h1, ptr_apply, Submodule.coe_sum, inner_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [hPB _ (hsing b) _ (hPm _ (hsing b)), hPP _ (hsing b), hformS, ← mul_assoc, tfSgn_mul_self, one_mul]
  have hub : ∀ b, inner ℂ (u b) (w b) =
      tfFormBH ε (fun i => ((P (Pi.single b y) i : D) : H)) (fun i => ((P (Pi.single b y) i : D) : H)) := by
    intro b
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← Submodule.inner_starProjection_left_eq_right HP, hPself _ (huHP b), hu]
    simp only
    rw [hT2 (hcoeC _ (hPm _ (hsing b))) (hcoeC _ (hPm _ (hsing b))) (hmem (hPm _ (hsing b)))
      (hmem (hPm _ (hsing b))), hNc]
    have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdpos.ne'
    have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
    rw [hκ, Complex.ofReal_div]
    field_simp

  have hone : tfRdiag ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) = 1 := (tfRdiag_isURepOn ε).1.1
  have hmul : ∀ a b : Formalism.REAL.UJ ε, tfRdiag ε (Formalism.MainNotions.S.umat (a * b)) =
      (tfRdiag ε (Formalism.MainNotions.S.umat a)).comp (tfRdiag ε (Formalism.MainNotions.S.umat b)) := fun a b =>
    (tfRdiag_isURepOn ε).1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  have hiso : ∀ (g : Formalism.REAL.UJ ε) v, ‖tfRdiag ε (Formalism.MainNotions.S.umat g) v‖ = ‖v‖ := fun g v =>
    (tfRdiag_isURepOn ε).2.1 _ (umat_mem_UJset ε g) v
  have hadj : ∀ (g : Formalism.REAL.UJ ε) (x x' : tfL2n ε), inner ℂ (tfRdiag ε (Formalism.MainNotions.S.umat g) x) x' =
      inner ℂ x (tfRdiag ε (Formalism.MainNotions.S.umat g⁻¹) x') := by
    intro g x x'
    have hs := GraphTrick.star_eq (ρ := fun g : Formalism.REAL.UJ ε => tfRdiag ε (Formalism.MainNotions.S.umat g)) hone hmul hiso g
    rw [← hs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hJr : ∀ (x : tfL2n ε) c, tfJ ε x c = (((if ε c then (1 : ℝ) else -1 : ℝ)) : ℂ) • x c := by
    intro x c
    rw [tfJ_apply]
    congr 1
    unfold tfSgn
    split_ifs <;> simp
  have hswap := tf_tr_swap (μ := Formalism.REAL.muG ε) (fun g => tfRdiag ε (Formalism.MainNotions.S.umat g)) hadj (tfJ ε)
    (fun c => if ε c then (1 : ℝ) else -1) hJr (fun g x => tfRdiag_tfJ ε _ x) HP
    (fun g v hv => hst _ (umat_mem_UJset ε g) v hv) κ u w huHP (fun c => rfl) hrep

  have hJu : ∀ c', starRingEnd ℂ (inner ℂ (tfJ ε (u c')) (w c')) =
      ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
    intro c'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PiLp.inner_apply, map_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [tfJ_apply, inner_smul_left, map_mul, Complex.conj_conj]
  have haa : ∀ c', inner ℂ (tfJ ε (u c')) (w c') = (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
    intro c'
    rw [hw]
    simp only
    rw [inner_smul_right, ha]
    simp only
    rw [← hproj _ _ (Submodule.starProjection_apply_mem HP (tfJ ε (u c'))), inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow]
    rfl
  set T : ℝ := ∑ c', ‖a c'‖ ^ 2 with hT
  have hTnn : 0 ≤ T := sum_nonneg fun c' _ => sq_nonneg _
  have hmain : c0 * (Nr : ℂ) = ((κ * T : ℝ) : ℂ) := by
    rw [hT1, sum_congr rfl fun b _ => by rw [← hub b]]
    have e1 : ∀ b, tfSgn ε b * inner ℂ (u b) (w b) =
        ∑ c', tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) := by
      intro b
      rw [PiLp.inner_apply, mul_sum]
      exact sum_congr rfl fun c' _ => by rw [hswap b c']
    rw [sum_congr rfl fun b _ => e1 b, sum_comm]
    have e : ∀ c', ∑ b, tfSgn ε b * starRingEnd ℂ (inner ℂ (u c' b) (w c' b)) =
        (κ : ℂ) * ((‖a c'‖ ^ 2 : ℝ) : ℂ) := by
      intro c'
      rw [← hJu, haa, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [sum_congr rfl fun c' _ => e c', ← mul_sum, hT]
    push_cast
    rfl
  have hN0 : (Nr : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hNpos.ne'
  have hc0eq : c0 = ((κ * T / Nr : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← hmain]
    field_simp
  have hwT : ∑ c', ‖w c'‖ ^ 2 = κ ^ 2 * T := by
    rw [hT, mul_sum]
    refine sum_congr rfl fun c' _ => ?_
    rw [hw]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκpos.le, mul_pow]
  refine ⟨HP, w, hHPc, rfl, hst, hrep, ?_⟩
  rw [hc0eq, hwT]
  congr 1
  rw [hκ]
  field_simp

end ReciprocityTheory.ChartRestriction.DS.G2
