module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSchAlt
noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def reidxCLE {α β : Type} (e : α ≃ β) : (β → V) ≃L[ℝ] (α → V) where
  toFun y a := y (e a)
  invFun x b := x (e.symm b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := funext fun b => by simp
  right_inv x := funext fun a => by simp
  continuous_toFun := continuous_pi fun a => continuous_apply (e a)
  continuous_invFun := continuous_pi fun b => continuous_apply (e.symm b)

def optCLE (α : Type) : (Option α → V) ≃L[ℝ] V × (α → V) where
  toFun y := (y none, fun a => y (some a))
  invFun p o := Option.elim o p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := funext fun o => by cases o <;> rfl
  right_inv p := rfl
  continuous_toFun := (continuous_apply none).prodMk (continuous_pi fun a => continuous_apply (some a))
  continuous_invFun := continuous_pi fun o => by
    cases o with
    | none => exact continuous_fst
    | some a => exact (continuous_apply a).comp continuous_snd

def oneSch : 𝓢(PEmpty → V, ℂ) where
  toFun _ := 1
  smooth' := contDiff_const
  decay' k n := ⟨1, fun x => by
    have hx : ‖x‖ = 0 := by rw [Subsingleton.elim x 0, norm_zero]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · rw [hx]; exact pow_le_one₀ le_rfl zero_le_one
    · cases n with
      | zero => rw [norm_iteratedFDeriv_zero]; simp
      | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; simp⟩


variable (V) in
def PS (α : Type) [Fintype α] : Prop := ∀ S : α → 𝓢(V, ℂ), ∃ T : 𝓢(α → V, ℂ), ∀ y, T y = ∏ w, S w (y w)

theorem piProdSch' (W : Type) [Fintype W] (S : W → 𝓢(V, ℂ)) :
    ∃ T : 𝓢(W → V, ℂ), ∀ y, T y = ∏ w, S w (y w) := by
  revert S
  change PositivityTheory.SiegelWeilFormula.KFock.PS V W
  refine Fintype.induction_empty_option (P := fun α (_ : Fintype α) => PositivityTheory.SiegelWeilFormula.KFock.PS V α)
    ?_ ?_ ?_ W
  · intro α β _ e hα S
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨T, hT⟩ := hα (fun a => S (e a))
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PositivityTheory.SiegelWeilFormula.KFock.reidxCLE e) T,
      fun y => ?_⟩
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]
    exact Fintype.prod_equiv e _ _ (fun a => rfl)
  · intro S
    refine ⟨PositivityTheory.SiegelWeilFormula.KFock.oneSch, fun y => ?_⟩
    show (1 : ℂ) = _
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  · intro α _ hα S
    obtain ⟨T₀, hT₀⟩ := hα (fun a => S (some a))
    obtain ⟨f, hf⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod (S none) T₀
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PositivityTheory.SiegelWeilFormula.KFock.optCLE α) f,
      fun y => ?_⟩
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hf, Fintype.prod_option]
    show S none (y none) * T₀ (fun a => y (some a)) = _
    rw [hT₀]

end PositivityTheory.SiegelWeilFormula.KFock

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.EvXTemperate
noncomputable section

open scoped SchwartzMap
open PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

private theorem hasTemperateGrowth_evX' {m n : ℕ} (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth
      (fun x : Fin m → Fin n → ℂ => if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) := by
  obtain ⟨a, i, b⟩ := k
  have hc : Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => x a i) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)).hasTemperateGrowth
  cases b with
  | false => simpa using hc
  | true =>
    have hs := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a))).hasTemperateGrowth
    convert hs using 1
    funext x
    simp

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun x : Fin m → Fin n → ℂ => evX P x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext x
    simp [evX]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp [evX]
  | mul_X p k hp =>
    have e : (fun x : Fin m → Fin n → ℂ => evX (p * MvPolynomial.X k) x) =
        fun x => evX p x * (if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) := by
      funext x
      simp [evX]
    rw [e]
    exact hp.fun_mul (hasTemperateGrowth_evX' k)

def eucl (m n : ℕ) (s : ℝ) (hs : s ≠ 0) : (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  ((LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs).trans
    ((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm)).toContinuousLinearEquiv

theorem eucl_norm_sq (m n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Fin m → Fin n → ℂ) :
    ‖eucl m n s hs x‖ ^ 2 = s ^ 2 * ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eucl, norm_smul, mul_pow]

theorem gsSch (m n : ℕ) {c : ℝ} (hc : 0 < c) : ∃ G : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, G x = gs c x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set s := Real.sqrt (c / Real.pi) with hsdef
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (div_pos hc hpi)).ne'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eucl m n s hs)
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℂ (Fin m × Fin n))), fun x => ?_⟩
  have hs2 : s ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc hpi).le
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, eucl_norm_sq, gs]
  rw [hs2, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp

end PositivityTheory.SiegelWeilFormula.KFock

end
end

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KFock

theorem piProdSch (W : Type) [Fintype W] (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (S : W → 𝓢(V, ℂ)) :
    ∃ T : 𝓢(W → V, ℂ), ∀ y, T y = ∏ w, S w (y w) :=
  piProdSch' W S

theorem fPSch {m n : ℕ} (P : PositivityTheory.Rg.Sw.PX m n) {c : ℝ} (hc : 0 < c) :
    ∃ S : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, S x = PositivityTheory.Rg.Sw.evX P x * PositivityTheory.Rg.Sw.gs c x := by
  obtain ⟨G, hG⟩ := gsSch m n hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => PositivityTheory.Rg.Sw.evX P x) G, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (evX_temperate P), hG, smul_eq_mul]

end PositivityTheory.SiegelWeilFormula.KFock

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isSw_fP {m n : ℕ} (P : PX m n) : IsSw (fP P) := by
  obtain ⟨S, hS⟩ := fPSch P (c := 2 * Real.pi) (by positivity)
  exact ⟨S, funext fun x => by rw [hS]; rfl⟩

theorem prodGen_mem (d : SD σ) (R : RD d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨L, hL⟩ := archEquiv d R
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  rw [SD.schM, Submodule.mem_comap]
  apply Submodule.subset_span
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, hT, hL, crd_cmb]

theorem fock_le (d : SD σ) (R : RD d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨P, g, hg, rfl⟩
  choose S hS using fun w => isSw_fP (P w)
  simp only [← hS]
  exact prodGen_mem d R S g hg

theorem tens_mem (d : SD σ) (R : RD d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  subst hφ
  change Ψ ∈ R.fockOn (Finset.univ.erase w) at hΨ
  unfold RD.fockOn at hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, g, hg, rfl⟩ := hx
    choose S hS using fun w' => isSw_fP (P w')
    have hmem := prodGen_mem d R (Function.update S w φ) g hg
    have heq : R.tens w ⇑φ
        (fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
        fun X => (∏ w', (Function.update S w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2 := by
      funext X
      rw [← Finset.mul_prod_erase Finset.univ (fun w' => (Function.update S w φ w') (R.loc w' X))
        (Finset.mem_univ w)]
      have hpr : ∏ w' ∈ Finset.univ.erase w, (Function.update S w φ w') (R.loc w' X) =
          ∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X) :=
        Finset.prod_congr rfl fun w' hw' => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), hS w']
      rw [hpr]
      simp only [RD.tens, Function.update_self]
      ring
    rw [heq]
    exact hmem
  | zero =>
    have h0 : R.tens w ⇑φ 0 = 0 := by
      funext X
      simp [RD.tens]
    rw [h0]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [tens_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [tens_smul]
    exact Submodule.smul_mem _ a hx

end PositivityTheory.SiegelWeilFormula.KFock

end
