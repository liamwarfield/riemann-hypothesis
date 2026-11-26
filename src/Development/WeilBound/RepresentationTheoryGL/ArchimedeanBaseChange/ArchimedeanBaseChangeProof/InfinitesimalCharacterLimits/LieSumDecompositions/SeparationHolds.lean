module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLog
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocks
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.LeafHolds2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypes
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SliceUOfNoLog2
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSliceUA
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Rs.SliceClasses

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem F_slicesU (V : Submodule ℂ (Sm E (r + s))) (hVs : _root_.GlobalTheory.CuspRep.IsStable V) (hVa : ∀ φ ∈ V, IsAutForm φ)
    (hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ c : ℂ, ∀ ψ ∈ V, cap τ u ψ = c • ψ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s))
    (hequiv : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (τs : Finset ℝ) (a : ℝ → ℂ)
    (hTval : ∀ φ ∈ V, ∀ g, (T φ).1 g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (φ : Sm E (r + s)) (hφ : φ ∈ V) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ ∀ m₁, ψ.1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    (∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ ∀ m₂, ψ.1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) := by
  have hAφ := hVa φ hφ

  have hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (T φ).1 (unip x * g) = (T φ).1 g := by
    intro x g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    rw [← mul_assoc, hy, mul_assoc, ctn_unip hAφ]

  have hM : ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      (T φ).1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = (T φ).1 g := by
    intro γ g
    rw [hTval φ hφ, hTval φ hφ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_lev, mul_assoc, ctn_lev_rat hAφ]

  let L := GlobalTheory.DiscClosure.stabSub φ
  have hLo : IsOpen (L : Set (GL (Fin (r + s)) (Af E))) := hAφ.level
  have hLv : ∀ h ∈ L, finRep E (r + s) h (T φ) = T φ := fun h hh => by
    have e := hequiv (.fin h) φ hφ
    have hh' : finRep E (r + s) h φ = φ := hh
    change T (finRep E (r + s) h φ) = finRep E (r + s) h (T φ) at e
    rw [← e, hh']

  let S := GlobalTheory.CuspRep.LocEx.orbSpan (T φ)
  haveI : FiniteDimensional ℂ S := by
    haveI := hAφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun κ => cptRep E (r + s) κ φ)).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨κ, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨κ, rfl⟩, hequiv (.cpt κ) φ hφ⟩
  let ρ := GlobalTheory.PRep.sub (cptRep E (r + s)) S (GlobalTheory.CuspRep.LocEx.orbSpan_stable (T φ))
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := GlobalTheory.CuspRep.LocEx.isContRep_sub S _
  have hC : ∀ g : GA E (r + s), (fun κ : Kinf E (r + s) => (cptRep E (r + s) κ (T φ)).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan ρ := fun g =>
    GlobalTheory.Published.AutFinGL.type_of_map ρ S.subtype (fun _ _ => rfl) ⟨T φ, Submodule.subset_span ⟨1, by simp⟩⟩ g

  have hG : ∀ g₀ : GA E (r + s), ∃ (C : ℝ) (n : ℕ), ∀ y, ‖(T φ).1 (g₀ * infGL E (r + s) y)‖ ≤ C * height y ^ n := by
    intro g₀
    choose C n hCn using fun t => ctn_growth hAφ r (aT E (r + s) r t * g₀)
    refine ⟨∑ t ∈ τs, ‖a t‖ * |C t|, ∑ t ∈ τs, n t, fun y => ?_⟩
    rw [hTval φ hφ, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have hy := one_le_height y
    have e1 : height y ^ n t ≤ height y ^ (∑ t ∈ τs, n t) :=
      pow_le_pow_right₀ hy (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht)
    have hp : (0 : ℝ) ≤ height y ^ n t := pow_nonneg (by linarith) _
    calc ‖a t * An.ctn r φ.1 (aT E (r + s) r t * (g₀ * infGL E (r + s) y))‖
        = ‖a t‖ * ‖An.ctn r φ.1 (aT E (r + s) r t * g₀ * infGL E (r + s) y)‖ := by rw [norm_mul, mul_assoc]
      _ ≤ ‖a t‖ * (C t * height y ^ n t) := mul_le_mul_of_nonneg_left (hCn t y) (norm_nonneg _)
      _ ≤ ‖a t‖ * (|C t| * height y ^ (∑ t ∈ τs, n t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (le_abs_self _) e1 hp (abs_nonneg _)) (norm_nonneg _)
      _ = ‖a t‖ * |C t| * height y ^ (∑ t ∈ τs, n t) := by ring

  choose cc hcc using hsc
  let J : Set (Module.End ℂ (Sm E (r + s))) :=
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r + s) τ u) (Polynomial.X - Polynomial.C (cc τ u))}
  have hJZ : J ⊆ Zalg E (r + s) := by
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  have hJ : Cofin J := GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic E (r + s) J hJZ fun τ u =>
    ⟨_, Polynomial.monic_X_sub_C _, τ, u, rfl⟩
  have hZ : ∀ z ∈ J, z (T φ) = 0 := by
    rintro _ ⟨τ, u, rfl⟩
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
    rw [← GlobalTheory.SpehInfChar.cap_comm_quot (fun X ψ hψ => hVs (.lie X) ψ hψ) T hequiv τ u φ hφ,
      hcc τ u φ hφ, map_smul, sub_self]
  have hgood : T φ ∈ goodCT L ρ J := ⟨hN, hM, hLv, hC, hG, hZ⟩
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  have e : ∀ m : GA E r × GA E s, lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
      lev (Ad E) r s m * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k) := by
    intro m
    rw [infGL_comm, mul_assoc]
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨L₁, ρ₁, -, -, h⟩ := Slice1.slice_mem_genSpace E r s L hLo S ρ hρ J hJ J₁ c₁ k₁ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₂
    exact ⟨G, hG.1, fun m₁ => by rw [hG', e]⟩
  · obtain ⟨L₂, ρ₂, -, -, h⟩ := Slice2.slice2 E r s L hLo S ρ hρ J hJ J₂ c₂ k₂ g k
    obtain ⟨G, hG, hG'⟩ := h (T φ) hgood m₁
    exact ⟨G, hG.1, fun m₂ => by rw [hG', e]⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.LieSumUnipotentSlice

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar
noncomputable section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

def expChar (c : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (c * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem lagrange (C : Finset ℂ) (c : ℂ) : ∃ (τs : Finset ℝ) (a : ℝ → ℂ), ∀ c' ∈ C,
    ∑ t ∈ τs, a t * Complex.exp (c' * t) = if c' = c then 1 else 0 := by
  classical
  have expChar_injective : Function.Injective expChar := by
    intro c c' h
    have hd : ∀ d : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (d * (t : ℂ))) d 0 := by
      intro d
      have h1 : HasDerivAt (fun t : ℝ => d * (t : ℂ)) (d * 1) 0 :=
        ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul d
      have h2 := h1.cexp
      simpa using h2
    have hf : (fun t : ℝ => Complex.exp (c * (t : ℂ))) = fun t : ℝ => Complex.exp (c' * (t : ℂ)) := by
      funext t
      have := DFunLike.congr_fun h (Multiplicative.ofAdd t)
      simpa [expChar] using this
    have e := hd c
    rw [hf] at e
    exact e.unique (hd c')
  let v : ℝ → (C → ℂ) := fun t c' => Complex.exp ((c' : ℂ) * t)
  have hli : LinearIndependent ℂ (fun c' : C => (expChar (c' : ℂ) : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp (fun c' : C => expChar (c' : ℂ))
      (expChar_injective.comp Subtype.val_injective)
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hw : ∀ i : C, f (Pi.single i 1) = 0 := by
      have hsum : ∑ i : C, f (Pi.single i 1) • (expChar (i : ℂ) : Multiplicative ℝ → ℂ) = 0 := by
        funext x
        have hx : f (v (Multiplicative.toAdd x)) = 0 := hle (Submodule.subset_span ⟨_, rfl⟩)
        have hv : v (Multiplicative.toAdd x) = ∑ i : C, (v (Multiplicative.toAdd x) i) • Pi.single i 1 := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hv, map_sum] at hx
        simp only [map_smul, smul_eq_mul] at hx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hx]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [expChar, v, mul_comm]
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hsum i
    exact (Pi.basisFun ℂ C).ext fun i => by simpa using hw i
  have hmem : (fun c' : C => if (c' : ℂ) = c then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range v) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨a.support, a, fun c' hc' => ?_⟩
  have := congrFun ha ⟨c', hc'⟩
  rw [Finsupp.sum, Finset.sum_apply] at this
  simpa [v] using this

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

end
end

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness


open LieSumUnipotentSlice PositivityTheory.Rg.Rs.SliceClasses in
theorem sliceU_of_noLog2 (hNL : NoLog) : SliceU := by
  intro E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc
  have hD := dict_holds
  have hFin := finTr_holds
  obtain ⟨F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hAφ := hU.2 φ hφU
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]

  obtain ⟨S, hSU, hSgen⟩ := hFG
  have hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup := by
    intro ψ hψ τ
    obtain ⟨m, ⟨hcard, hm⟩, hnd⟩ := hReg τ
    exact ⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩
  have hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := fun ψ hψ =>
    hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)
  choose! Cs Gs hsum hGeig using hdec
  obtain ⟨τs, a, ha⟩ := SliceUB2.lagrange (insert c (S.biUnion Cs)) c
  have ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1 := by
    rw [ha c (Finset.mem_insert_self _ _), if_pos rfl]

  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a
  have hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g) := by
    intro ψ hψ g
    rw [hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]
  have hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ) := by
    intro o ψ hψ
    rw [hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]

  have hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
    intro ψ hψ g
    rw [hTval ψ (hSU hψ), hsum ψ hψ]
    calc ∑ t ∈ τs, a t * (∑ c' ∈ Cs ψ, Gs ψ c') (aT E (r + s) r t * g)
        = ∑ t ∈ τs, ∑ c' ∈ Cs ψ, a t * (Complex.exp (c' * t) * Gs ψ c' g) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']
      _ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : _root_.GlobalTheory.CuspRep.IsStable W := by
    rintro o ψ ⟨hψ, he⟩
    refine ⟨hU.1 o ψ hψ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o ψ hψ]
    exact e2
  have hSW : (↑S : Set (Sm E (r + s))) ⊆ W := by
    intro ψ hψ
    refine ⟨hSU hψ, fun t g => ?_⟩
    rw [hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [hGeig ψ hψ c' hc']
    split_ifs with h
    · subst h
      ring
    · simp
  have hUW : U ≤ W := hSgen W hWst hSW
  have heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g :=
    fun ψ hψ => (hUW hψ).2

  have hTφ : T φ ≠ 0 := by
    intro h0
    have hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0 := by
      intro g
      rw [← hTval φ hφU g, h0]
      rfl
    apply hFne
    funext g
    have hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) =
        aT E (r + s) r t * (aT E (r + s) r t' * g) := by
      intro t t'
      rw [← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]
    calc F g = (∑ t' ∈ τs, a t' * Complex.exp (c * t')) * F g := by rw [ha1, one_mul]
      _ = ∑ t' ∈ τs, a t' * F (aT E (r + s) r t' * g) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring
      _ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by
          simp_rw [hFval, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hcomm]
          ring
      _ = 0 := by simp [hz]
  have hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g := by
    intro ψ hψ t g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hSI ψ hψ)]
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ := by
    intro τ u
    obtain ⟨m, ⟨-, hm⟩, -⟩ := hReg τ
    exact ⟨_, hm u⟩
  refine ⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩
  · intro ψ hψ x g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]
  · intro ψ hψ k g m₂
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂
    refine ⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hχ, hχ, e, mul_assoc, heig ψ hψ]
  · intro ψ hψ k g m₁
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁
    refine ⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.NodeHolds
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open PositivityTheory.Rg.Rs.ParabolicProjection in
theorem node_holds : Node := by
  intro E _ _ _ r s _ _ U W₁ W₂ T hU hW₁ hW₂ hTe hmem hC₁ hC₂ φ₀ hφ₀U hφ₀
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hmem φ₀ hφ₀U).1
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀U).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw W₁ ((s : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  have hc₁ := hC₁ χ₁ hχ₁ hχ₁0
  obtain ⟨t₁, p₁, ht₁, hpos₁, hp₁e, hp₁V, hp₁0⟩ := hc₁
  have hf₁ : twMap r ((s : ℂ) / 2) p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r ((s : ℂ) / 2) p₁ (mulChi r (Model.absC E ((s : ℂ) / 2)) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r ((s : ℂ) / 2) p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw W₂ (-(r : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  have hc₂ := hC₂ χ₂ hχ₂ hχ₂0
  obtain ⟨t₂, p₂, ht₂, hpos₂, hp₂e, hp₂V, hp₂0⟩ := hc₂
  have hf₂ : twMap s (-(r : ℂ) / 2) p₂ (∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s (-(r : ℂ) / 2) p₂ (mulChi s (Model.absC E (-(r : ℂ) / 2)) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s (-(r : ℂ) / 2) p₂) hf₂

  have hI := indMap_holds E r s U (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) T (twMap r ((s : ℂ) / 2) p₁)
    (twMap s (-(r : ℂ) / 2) p₂) hU.1 hU.2 (isStable_tw hW₁.1 _) (isStable_tw hW₂.1 _) hTe hmem
    (twMap_equiv hW₁.1 hp₁e) (twMap_equiv hW₂.1 hp₂e)
  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI
  have hT'm : ∀ φ ∈ U, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) (T' φ) := by
    intro φ hφ
    refine ⟨hT'u φ hφ, fun k g => ?_⟩
    obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁' i)).1 m.1 *
        (twMap s (-(r : ℂ) / 2) p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  refine ⟨Tr.node t₁ t₂, T', ⟨ht₁, ht₂⟩, ⟨hpos₁, hpos₂⟩, hT'e, fun φ hφ => ?_, fun h => ?_⟩
  · rw [Tr.space]
    exact Submodule.subset_span ⟨hT'm φ hφ,
      InducedTensorMap.Main.finVec_of_equiv hT'e hφ (hU.2 φ hφ).kfin⟩
  · have e := hT's φ₀ hφ₀U k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SeparationOfSixInputs
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

namespace TwistSymmetryDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_tw_neg {N : ℕ} (U : Submodule ℂ (Sm E N)) (w : ℂ) : tw (tw U w) (-w) = U := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    change mulChi N (Model.absC E (-w)) (mulChi N (Model.absC E w) φ) ∈ U
    rw [ParabolicProjection.mulChi_absC_neg]
    exact hφ
  · intro h
    exact ⟨mulChi N (Model.absC E w) ψ, ⟨ψ, h, rfl⟩, ParabolicProjection.mulChi_absC_neg N w ψ⟩

theorem pE_sub_imag (N r : ℕ) (c w : ℂ) (hw : w.re = 0) :
    pE E N r (c - w * r * (Module.finrank ℚ E : ℂ)) = pE E N r c := by
  simp [pE, Complex.sub_re, Complex.mul_re, hw]

theorem central_tw {a : ℕ} (w e : ℂ) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) =
      Complex.exp ((e + w * a * (Module.finrank ℚ E : ℂ)) * t) * (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl,
    add_mul, Complex.exp_add]
  ring

theorem hyp_tw {N : ℕ} {τ : E →+* ℂ} {U : Submodule ℂ (Sm E N)} (hU : Hyp τ U) (w : ℂ) (hw : w.re = 0) :
    Hyp τ (tw U w) := by
  obtain ⟨⟨hst, haut⟩, ⟨S, hSU, hS⟩, hnp, ⟨z, hz, hzU⟩, ⟨m, hm, hnd⟩, hreg⟩ := hU
  classical
  have aut_tw {a : ℕ} {ψ : Sm E a} (h : IsAutForm ψ) (χ : Formalism.L2.Host.HChar E) :
      IsAutForm (mulChi a χ ψ) := by
    exact {
      left γ g := by simp [h.left, chiDet_ratGL]
      level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
        ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
          have h1 : GlobalTheory.CuspRep.rt E a (finGL E a k) ψ = ψ := hk.1
          have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
          change GlobalTheory.CuspRep.rt E a (finGL E a k) _ = _
          rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
      kfin := by
        have := h.kfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)).map
          (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ ψ).symm⟩
      zfin := by
        have := h.zfin
        refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) ''
          Zalg E a)).map (GlobalTheory.CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
        exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 ψ).symm⟩
      growth g := by
        obtain ⟨C, N, h1⟩ := h.growth g
        obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
        refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
        rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
        refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
          ((norm_nonneg _).trans (h1 y))).trans_eq ?_
        ring }
  refine ⟨⟨ParabolicProjection.isStable_tw hst w, ?_⟩, ⟨S.image (mulChi N (Model.absC E w)), ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact aut_tw (haut φ hφ) _
  · intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨φ, hφ, rfl⟩ := hx
    exact ⟨φ, hSU hφ, rfl⟩
  · intro W' hW' hSW'
    have h1 : U ≤ tw W' (-w) := hS _ (ParabolicProjection.isStable_tw hW' (-w)) fun φ hφ =>
      ⟨mulChi N (Model.absC E w) φ, hSW' (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hφ)),
        ParabolicProjection.mulChi_absC_neg N w φ⟩
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := h1 hφ
    change mulChi N (Model.absC E w) φ ∈ W'
    rw [← e]
    change mulChi N (Model.absC E w) (mulChi N (Model.absC E (-w)) ψ) ∈ W'
    rw [ParabolicProjection.mulChi_absC_neg']
    exact hψ
  · rintro _ ⟨φ, hφ, rfl⟩ r hr hrN c hc
    have h := expTw_holds E N φ w (haut φ hφ) r hr hrN c hc
    have h2 := hnp φ hφ r hr hrN _ h
    rwa [pE_sub_imag N r c w hw] at h2
  · refine ⟨z + w * N * (Module.finrank ℚ E : ℂ), ?_, ?_⟩
    · simp [Complex.add_re, Complex.mul_re, hz, hw]
    · rintro _ ⟨φ, hφ, rfl⟩ t g
      exact central_tw w z φ (hzU φ hφ) t g
  · exact ⟨_, GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hm (Model.absC E w), hnd.map (add_left_injective _)⟩
  · intro τ'
    obtain ⟨m', hm', hnd'⟩ := hreg τ'
    exact ⟨_, GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hm' (Model.absC E w), hnd'.map (add_left_injective _)⟩

theorem core (h1 : SliceU) (h2 : Blocks) (h3 : Leaf) (h4 : Node) (h6 : TwConc) (τ : E →+* ℂ) :
    ∀ (N : ℕ) (U : Submodule ℂ (Sm E N)), 0 < N → Hyp τ U → ∀ φ ∈ U, φ ≠ 0 → Conc U φ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro U hN hU φ hφ hne
  by_cases hneg : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0
  · exact h3 E N τ hN U hU φ hφ hneg hne
  push_neg at hneg
  obtain ⟨r, hr, hrN, c, hc, hc0⟩ := hneg
  have hc0' : pE E N r c = 0 := le_antisymm (hU.2.2.1 φ hφ r hr hrN c hc) hc0
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs : 0 < s := by omega
  obtain ⟨z, hz, hzU⟩ := hU.2.2.2.1
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hN0 : ((r + s : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = -z / (((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) := ⟨_, rfl⟩
  have hw : w.re = 0 := by
    have e : (((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) = (((r + s) * Module.finrank ℚ E : ℕ) : ℂ) := by
      push_cast; ring
    rw [hwdef, e, Complex.div_natCast_re, Complex.neg_re, hz, neg_zero, zero_div]
  have hzw : z + w * ((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ) = 0 := by
    rw [hwdef]
    field_simp
    ring
  have hU' : Hyp τ (tw U w) := hyp_tw hU w hw
  have hsplit : SplitInv (tw U w) := by
    rintro _ ⟨ψ, hψ, rfl⟩ t g
    exact ChordArithmetic.central_twist w z hzw ψ (hzU ψ hψ) t g
  have hφ' : mulChi (r + s) (Model.absC E w) φ ∈ tw U w := ⟨φ, hφ, rfl⟩
  have hne' : mulChi (r + s) (Model.absC E w) φ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hne
  have hc' : c - -w * r * (Module.finrank ℚ E : ℂ) ∈ Exp r (mulChi (r + s) (Model.absC E w) φ).1 := by
    refine expTw_holds E (r + s) (mulChi (r + s) (Model.absC E w) φ) (-w) (hU'.1.2 _ hφ') r hr hrN c ?_
    rw [ParabolicProjection.mulChi_absC_neg]
    exact hc
  have hpc' : pE E (r + s) r (c - -w * r * (Module.finrank ℚ E : ℂ)) = 0 := by
    rw [pE_sub_imag (r + s) r c (-w) (by simp [hw])]
    exact hc0'
  obtain ⟨T, hT, hTφ⟩ := h1 E r s hr hs (tw U w) hU'.1 hU'.2.1 hsplit hU'.2.2.2.2.2 _ hφ' _ hc'
  obtain ⟨J, P, W₁, W₂, hW, hP, hsum, hind⟩ := h2 E r s τ hr hs (tw U w) hU' hsplit _ T hT hpc'
  obtain ⟨j, hj, hPj⟩ : ∃ j ∈ J, P j (T (mulChi (r + s) (Model.absC E w) φ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hTφ
    rw [← hsum _ hφ']
    exact Finset.sum_eq_zero hcon
  have hconc' : Conc (tw U w) (mulChi (r + s) (Model.absC E w) φ) := by
    refine h4 E r s hr hs (tw U w) (W₁ j) (W₂ j) (P j ∘ₗ T) hU'.1 (hW j hj).1.1 (hW j hj).2.1 ?_ ?_ ?_ ?_ _ hφ' hPj
    · intro o ψ hψ
      simp only [LinearMap.comp_apply]
      rw [hT.equiv o ψ hψ, hP j hj o ψ hψ]
    · intro ψ hψ
      exact hind j hj ψ hψ
    · intro ψ hψ hψ0
      exact ih r (by omega) (W₁ j) hr (hW j hj).1 ψ hψ hψ0
    · intro ψ hψ hψ0
      exact ih s (by omega) (W₂ j) hs (hW j hj).2 ψ hψ hψ0
  have h := h6 E (r + s) (tw U w) (-w) (by simp [hw]) hU'.1 _ hφ' hconc'
  rwa [tw_tw_neg, ParabolicProjection.mulChi_absC_neg] at h

def evalAt {N : ℕ} (h : GA E N) : Sm E N →ₗ[ℂ] ℂ := (LinearMap.proj h).comp (Sm E N).subtype

theorem typeB_map {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {U : Submodule ℂ (Sm E N)} {T : Sm E N →ₗ[ℂ] Sm E N} (haut : ∀ φ ∈ U, IsAutForm φ)
    (hTe : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) {φ : Sm E N} (hφ : φ ∈ U) (hT : TypeB K W φ) :
    TypeB K W (T φ) := by
  obtain ⟨hK, hW⟩ := hT
  constructor
  · intro u hu g
    have e1 : act (Op.fin u) φ = φ := Subtype.ext (funext fun x => hK u hu x)
    calc (T φ).1 (g * finGL E N u) = (act (Op.fin u) (T φ)).1 g := rfl
      _ = (T φ).1 g := by rw [← hTe _ φ hφ, e1]
  · intro g
    set V : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ) with hV
    have : FiniteDimensional ℂ V := (haut φ hφ).kfin
    have hF : ∀ k, cptRep E N k φ ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
    let Sd : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (Set.range fun h : GA E N => evalAt h ∘ₗ V.subtype)
    have hco : Sd.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Subtype.ext
      funext h
      exact hv _ (Submodule.subset_span ⟨h, rfl⟩)
    have htop : Sd = ⊤ := by
      set_option synthInstance.maxHeartbeats 400000 in
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sd), hco, Submodule.dualAnnihilator_bot]
    have key : ∀ f ∈ Sd, (fun k => f ⟨cptRep E N k φ, hF k⟩) ∈ W := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        exact hW h
      | zero => exact W.zero_mem
      | add x y _ _ hx hy => exact W.add_mem hx hy
      | smul a x _ hx => exact W.smul_mem a hx
    have hℓ := key (evalAt g ∘ₗ T ∘ₗ V.subtype) (htop ▸ Submodule.mem_top)
    convert hℓ using 1
    funext k
    change (T φ).1 (g * infGL E N (Unitary.toUnits k)) = (T (cptRep E N k φ)).1 g
    calc (T φ).1 (g * infGL E N (Unitary.toUnits k)) = (act (Op.cpt k) (T φ)).1 g := rfl
      _ = (T (cptRep E N k φ)).1 g := by rw [← hTe _ φ hφ]; rfl

end TwistSymmetryDecomposition

theorem allLeaves_and {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q →
      t.AllLeaves (fun M V => P M V ∧ Q M V)
  | _, .leaf _ _, hp, hq => ⟨hp, hq⟩
  | _, .node t₁ t₂, hp, hq => ⟨allLeaves_and t₁ hp.1 hq.1, allLeaves_and t₂ hp.2 hq.2⟩

theorem separation_of_six_inputs (h1 : SliceU) (h2 : Blocks) (h3 : Leaf) (h4 : Node) (h5 : Types) (h6 : TwConc) : Sep4 := by
  intro E _ _ _ N W hW
  obtain ⟨Ω, hΩ, hK⟩ := h5 E N W hW
  refine ⟨Ω, hΩ, fun K hKo => ?_⟩
  obtain ⟨Θ, hΘ, hty⟩ := hK K hKo
  refine ⟨Θ, hΘ, ?_⟩
  intro U hN hst haut hS hnp hci hreg hU0
  obtain ⟨S, hSty, hSU, hSmin⟩ := hS

  obtain ⟨φ, hφS, hne⟩ : ∃ φ ∈ S, φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : _root_.GlobalTheory.CuspRep.IsStable (⊥ : Submodule ℂ (Sm E N)) := by
      intro o ψ hψ
      rw [Submodule.mem_bot] at hψ ⊢
      rw [hψ, map_zero]
    exact hU0 (eq_bot_iff.2 (hSmin ⊥ hbot fun ψ hψ => (Submodule.mem_bot ℂ).2 (hcon ψ hψ)))
  have hφ : φ ∈ U := hSU hφS
  have hfg : FinGen U := ⟨S, hSU, hSmin⟩
  let τ : E →+* ℂ := Classical.arbitrary _
  obtain ⟨m, hm, hnd⟩ := hreg τ
  obtain ⟨t, T, ht, hpos, hTe, hTs, hTφ⟩ :=
    TwistSymmetryDecomposition.core h1 h2 h3 h4 h6 τ N U hN ⟨⟨hst, haut⟩, hfg, hnp, hci, ⟨m, hm, hnd⟩, hreg⟩ φ hφ hne
  exact ⟨t, T, ht,
    allLeaves_and t hpos (hty t (T φ) ht (hTs φ hφ) hTφ (TwistSymmetryDecomposition.typeB_map haut hTe hφ (hSty φ hφS))), hTe, hTs,
    φ, hφ, hTφ⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTwConc
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem chiDet_unip {a r : ℕ} (χ : Formalism.L2.Host.HChar E) (x : BlockIx a r → Ad E) : chiDet a χ (unip x) = 1 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
  rw [det_unip, map_one]

omit [IsCMField E] in
theorem chiDet_lev {r s : ℕ} (χ : Formalism.L2.Host.HChar E) (m : GA E r × GA E s) :
    chiDet (r + s) χ (lev (Ad E) r s m) = chiDet r χ m.1 * chiDet s χ m.2 := by
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (lev (Ad E) r s m)) =
    (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.1) *
      (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det m.2)
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  have h : (lev (Ad E) r s m : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) =
      Matrix.reindex (stdSum (rfl : r + s = r + s)) (stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [lev, emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal'_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

omit [IsCMField E] in
theorem chiDet_zero (χ : Formalism.L2.Host.HChar E) (g : GA E 0) : chiDet 0 χ g = 1 := by
  have h : Matrix.GeneralLinearGroup.det g = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
  change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det g) = 1
  rw [h, map_one]

theorem mulChi_mulChi {n : ℕ} (a b : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E b) (mulChi n (Model.absC E a) φ) = mulChi n (Model.absC E (a + b)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add, add_mul]

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  unfold tw
  rw [← Submodule.map_comp]
  congr 1
  ext φ : 1
  exact mulChi_mulChi a b φ

theorem tw_zero_dim (V : Submodule ℂ (Sm E 0)) (z : ℂ) : tw V z = V := by
  have h : (mulChi 0 (Model.absC E z)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, chiDet_zero, Units.val_one, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

theorem tw_zero' {n : ℕ} (V : Submodule ℂ (Sm E n)) : tw V 0 = V := by
  have h : (mulChi n (Model.absC E 0)).toLinearMap = LinearMap.id := by
    ext φ : 1
    refine Subtype.ext (funext fun g => ?_)
    rw [LinearEquiv.coe_coe, mulChi_apply, ExponentTwist.chiDet_absC_val, zero_mul, Complex.exp_zero, mul_one]
    rfl
  unfold tw
  rw [h, Submodule.map_id]

variable {r s : ℕ}

theorem tensor_span_mul_det_character {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 W₁ W₂) :
    (fun m => F m * (((chiDet r (Model.absC E z) m.1 : ℂˣ) : ℂ) * ((chiDet s (Model.absC E z) m.2 : ℂˣ) : ℂ))) ∈
      tens2 (tw W₁ z) (tw W₂ z) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    refine Submodule.subset_span ⟨mulChi r (Model.absC E z) φ₁, ⟨φ₁, h₁, rfl⟩, mulChi s (Model.absC E z) φ₂,
      ⟨φ₂, h₂, rfl⟩, funext fun m => ?_⟩
    simp only [mulChi_apply]
    ring
  | zero =>
    convert zero_mem (tens2 (tw W₁ z) (tw W₂ z)) using 1
    funext m
    simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext m
    simp [add_mul]
  | smul c F _ hF =>
    convert Submodule.smul_mem _ c hF using 1
    funext m
    simp [mul_assoc]

theorem memInd2_tw {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) {φ : Sm E (r + s)}
    (hφ : MemInd2 W₁ W₂ φ) : MemInd2 (tw W₁ z) (tw W₂ z) (mulChi (r + s) (Model.absC E z) φ) := by
  refine ⟨fun x g => ?_, fun k g => ?_⟩
  · rw [mulChi_apply, mulChi_apply, hφ.1 x g, map_mul, chiDet_unip, one_mul]
  · set y := infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g
    have h1 := Submodule.smul_mem _ ((chiDet (r + s) (Model.absC E z) y : ℂˣ) : ℂ) (tensor_span_mul_det_character z (hφ.2 k g))
    convert h1 using 1
    funext m
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mulChi_apply, map_mul, chiDet_lev, Units.val_mul, Units.val_mul]
    ring

theorem memInd2_tw_iff {W₁ : Submodule ℂ (Sm E r)} {W₂ : Submodule ℂ (Sm E s)} (z : ℂ) (ψ : Sm E (r + s)) :
    (MemInd2 (tw W₁ z) (tw W₂ z) ψ ∧ ψ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ↔
      ∃ φ, (MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))) ∧ mulChi (r + s) (Model.absC E z) φ = ψ := by
  constructor
  · rintro ⟨h, hK⟩
    refine ⟨mulChi (r + s) (Model.absC E (-z)) ψ, ⟨?_, Trees.mulChi_mem_finVec _ hK⟩, ParabolicProjection.mulChi_absC_neg' _ z ψ⟩
    have h2 := memInd2_tw (-z) h
    rwa [tw_tw, tw_tw, add_neg_cancel, tw_zero', tw_zero'] at h2
  · rintro ⟨φ, ⟨hφ, hK⟩, rfl⟩
    exact ⟨memInd2_tw z hφ, Trees.mulChi_mem_finVec _ hK⟩

theorem span_memInd2_tw (W₁ : Submodule ℂ (Sm E r)) (W₂ : Submodule ℂ (Sm E s)) (z : ℂ) :
    Submodule.span ℂ {φ | MemInd2 (tw W₁ z) (tw W₂ z) φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))} =
      tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z := by
  rw [show tw (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}) z =
    (Submodule.span ℂ {φ | MemInd2 W₁ W₂ φ ∧ φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}).map
      (mulChi (r + s) (Model.absC E z)).toLinearMap from rfl,
    Submodule.map_span]
  congr 1
  ext ψ
  exact memInd2_tw_iff z ψ

def twT (z : ℂ) : {N : ℕ} → Tr E N → Tr E N
  | M, .leaf V w => .leaf V (if M = 0 then w else w + z)
  | _, .node t₁ t₂ => .node (twT z t₁) (twT z t₂)

theorem space_twT (z : ℂ) {N : ℕ} (t : Tr E N) : (twT z t).space = tw t.space z := by
  induction t with
  | @leaf M V w =>
    by_cases hM : M = 0
    · subst hM
      simp only [twT, Tr.space, tw_zero_dim]
    · simp only [twT, if_neg hM, Tr.space]
      rw [tw_tw]
  | @node r s t₁ t₂ ih₁ ih₂ =>
    simp only [twT, Tr.space]
    rw [ih₁, ih₂, tw_tw, tw_tw, add_comm z, add_comm z, ← tw_tw _ _ z, ← tw_tw _ _ z, span_memInd2_tw]

theorem good_twT {z : ℂ} (hz : z.re = 0) {N : ℕ} (t : Tr E N) (ht : t.Good) : (twT z t).Good := by
  induction t with
  | @leaf M V w =>
    rcases ht with ⟨hM, hV, hw⟩ | ⟨hM, hV, hw⟩
    · subst hM
      simp only [twT]
      exact Or.inl ⟨rfl, hV, hw⟩
    · simp only [twT, if_neg hM.ne']
      exact Or.inr ⟨hM, hV, by rw [Complex.add_re, hw, hz, add_zero]⟩
  | @node r s t₁ t₂ ih₁ ih₂ =>
    exact ⟨ih₁ ht.1, ih₂ ht.2⟩

theorem pos_twT (z : ℂ) {N : ℕ} (t : Tr E N) (ht : t.AllLeaves (fun M _ => 0 < M)) :
    (twT z t).AllLeaves (fun M _ => 0 < M) := by
  induction t with
  | @leaf M V w => exact ht
  | @node r s t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ ht.1, ih₂ ht.2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.TwistConcentration

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open TwistConcentration in
theorem twConc_holds : TwConc := by
  intro E _ _ _ N U z hz hU φ _ hc
  obtain ⟨t, T, ht, hpos, hTe, hTm, hT0⟩ := hc
  refine ⟨twT z t, ParabolicProjection.twMap N z T, good_twT hz t ht, pos_twT z t hpos, ParabolicProjection.twMap_equiv hU.1 hTe, fun ψ hψ => ?_, ?_⟩
  · rw [space_twT]
    exact ParabolicProjection.twMap_mem hTm ψ hψ
  · rw [ParabolicProjection.twMap_apply, ParabolicProjection.mulChi_absC_neg]
    exact (LinearEquiv.map_ne_zero_iff _).2 hT0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
end
end

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem separation_holds : Sep4 :=
  separation_of_six_inputs (SliceUniqueness.sliceU_of_noLog2 noLog_holds) blocks_holds leaf_holds2 node_holds types_holds twConc_holds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
