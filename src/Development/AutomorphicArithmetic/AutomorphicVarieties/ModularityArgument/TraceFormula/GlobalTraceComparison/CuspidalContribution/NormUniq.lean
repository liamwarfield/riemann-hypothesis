module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.AwayPartMulIotaWPart

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.NormUniq
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.normUniq :
    NormUniq := by
  intro E _ _ _ N hN π π₀ z hπ h₀ e
  have hI : π.Iso (π₀.twist (Model.absC E z)) := Quotient.exact e.symm
  have hz : z = 0 := PositivityTheory.Rg.Rs.StrStepB.eq_zero_of_iso_twist hN hπ h₀ hI
  subst hz
  have e' := (UpperTheory.ConvolutionTheory.Dp.isoEq E N π (π₀.twist (Model.absC E 0))).1 hI
  rw [PositivityTheory.Rg.Rs.StrStepB.absC_zero, CuspSub.twist_one] at e'
  exact e'.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrinkAlt
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open GroundTheory.Automorphic.AdelicGLn

private theorem int_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (u : GL (Fin N) (Af E)) :
    u ∈ integralFiniteGL E N ↔ ∀ w, GeneralLinearGroup.map (pLoc E w) u ∈ KGL w (n := N) := by
  rw [mem_integralFiniteGL_iff]
  refine ⟨fun h w => GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => h.1 i j w, fun i j => ?_⟩, fun h => ⟨fun i j w =>
    (GlobalTheory.AdelicU.mem_GLint_iff.1 (h w)).1 i j, fun i j w => ?_⟩⟩
  · rw [← map_inv]
    exact h.2 i j w
  · have := (GlobalTheory.AdelicU.mem_GLint_iff.1 (h w)).2 i j
    rwa [← map_inv] at this

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.levShrink :
    LevShrink := by
  intro E _ _ _ N bad K ho hl
  obtain ⟨L, hL, hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL E N K ho
  let K' : Subgroup (GL (Fin N) (Af E)) :=
    { carrier := {u | u ∈ integralFiniteGL E N ∧ ∀ c ∈ integralFiniteGL E N, c⁻¹ * u * c ∈ K}
      one_mem' := ⟨one_mem _, fun c _ => by simpa using K.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun c hc => by
        simpa [mul_assoc] using K.mul_mem (ha.2 c hc) (hb.2 c hc)⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun c hc => by simpa [mul_assoc] using K.inv_mem (ha.2 c hc)⟩ }
  refine ⟨K', fun u hu => by simpa using hu.2 1 (one_mem _), ⟨?_, fun u hu => (int_iff u).1 hu.1, fun w hw k hk => ⟨?_, fun c hc => ?_⟩⟩,
    fun c hc u hu => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := L ⊓ integralFiniteGL E N) (fun u hu => ⟨hu.2, fun c hc => hle (hconj c hc u hu.1)⟩)
      (hL.inter (isOpen_integralFiniteGL E N))
  · refine (int_iff _).2 fun v => ?_
    by_cases h : v = w
    · subst h; rwa [pLoc_locGL]
    · rw [pLoc_locGL_of_ne h]; exact one_mem _
  · have h1 := (int_iff c).1 hc w
    have e : c⁻¹ * locGL E N w k * c = locGL E N w ((GeneralLinearGroup.map (pLoc E w) c)⁻¹ * k * GeneralLinearGroup.map (pLoc E w) c) :=
      PositivityTheory.Rg.Rs.C3.Fl.glAf_ext fun v => by
        by_cases h : v = w
        · subst h; simp only [map_mul, map_inv, pLoc_locGL]
        · simp only [map_mul, map_inv, pLoc_locGL_of_ne h, mul_one, inv_mul_cancel, inv_one]
    rw [e]
    exact hl w hw _ (mul_mem (mul_mem (inv_mem h1) hk) h1)
  · have h1 := (int_iff c).2 hc
    exact ⟨mul_mem (mul_mem (inv_mem h1) hu.1) h1, fun c' hc' => by simpa [mul_assoc] using hu.2 (c * c') (mul_mem h1 hc')⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.TypeSat
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.typeSat :
    TypeSat := by
  intro G _ W hW
  let W0 : Submodule ℂ (G → ℂ) :=
    { carrier := {f | ∀ a, (fun k => f (a * k)) ∈ W}
      add_mem' := fun {f g} hf hg a => W.add_mem (hf a) (hg a)
      zero_mem' := fun _ => W.zero_mem
      smul_mem' := fun c f hf a => W.smul_mem c (hf a) }
  have hle : W0 ≤ W := by
    intro f hf
    have h1 : (fun k => f (1 * k)) ∈ W := hf 1
    simpa using h1
  haveI : FiniteDimensional ℂ W0 := Submodule.finiteDimensional_of_le hle
  have hstab : ∀ (a : G) (f : G → ℂ), f ∈ W0 → (fun k => f (a * k)) ∈ W0 := by
    intro a f hf c
    have h1 : (fun k => f ((a * c) * k)) ∈ W := hf (a * c)
    simpa [mul_assoc] using h1
  let L : G → (W0 →ₗ[ℂ] W0) := fun a =>
    { toFun := fun f => ⟨fun k => f.1 (a * k), hstab a f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b := Module.finBasis ℂ W0
  let c : (Fin (Module.finrank ℂ W0) × Fin (Module.finrank ℂ W0)) → G → ℂ :=
    fun p k => b.repr (L k (b p.2)) p.1
  refine ⟨Submodule.span ℂ (Set.range c),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range c), ?_⟩
  intro f hf y
  let F : W0 := ⟨f, hf⟩
  have key : (fun k => f (k * y)) =
      ∑ i, ∑ j, ((b i).1 y * b.repr F j) • c (i, j) := by
    funext k
    have h3 : L k F = ∑ j, b.repr F j • L k (b j) := by
      conv_lhs => rw [← b.sum_repr F]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    have h4 : ∀ i, b.repr (L k F) i = ∑ j, b.repr F j * c (i, j) k := by
      intro i
      rw [h3]
      simp [c, Finsupp.finsetSum_apply]
    have h5 : f (k * y) = (L k F).1 y := rfl
    have h6 : (L k F).1 y = ∑ i, b.repr (L k F) i * (b i).1 y := by
      have h7 := congrArg (fun v : W0 => (v : G → ℂ) y) (b.sum_repr (L k F))
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul] at h7
      exact h7.symm
    rw [h5, h6]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h4, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.TyComm
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S Formalism.UG.P
open GroundTheory.Automorphic.AutomorphicForm (archCompact infEmb)

private theorem ty_comm {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ))
    [FiniteDimensional ℂ W] (T : Module.End ℂ (Sm E a)) (hT : ∀ k, Commute T (cptRep E a k)) (φ : Sm E a)
    (h : ∀ g, (fun k : Kinf E a => φ.1 (g * infGL E a (Unitary.toUnits k))) ∈ W) (g) :
    (fun k : Kinf E a => (T φ).1 (g * infGL E a (Unitary.toUnits k))) ∈ W := by
  let e := LinearEquiv.funCongrLeft ℂ ℂ (UpperTheory.V.Cm.cptEq E a).symm.toEquiv
  have key : ∀ (ψ : Sm E a) g, e (fun k : Kinf E a => ψ.1 (g * infGL E a (Unitary.toUnits k))) =
      fun k : archCompact E a => ψ.1 (g * infEmb E a k.1) := fun ψ g => funext fun k => by
    obtain ⟨k, rfl⟩ := (UpperTheory.V.Cm.cptEq E a).surjective k
    rw [UpperTheory.V.Cm.infEmb_cptEq]
    simp [e, LinearMap.funLeft]
  have h1 := typesComm E a (W.map e.toLinearMap) inferInstance T hT φ (fun g => ⟨_, h g, key φ g⟩) g
  obtain ⟨f, hf, e1⟩ := h1
  rwa [← e.injective (e1.trans (key (T φ) g).symm)]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.stabT :
    StabT := by
  intro E _ _ _ a bad L W hL hW S hS hty
  obtain ⟨h1, h2, h3⟩ := hullOps capAct E a S
  have hb := hullBdd typesComm E a S hS L hL.isOpen
  have hK : ∀ w ∉ bad, fixed (finRep E a) L ≤ fixed (fL a w) (KGL w (n := a)) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ (hL.loc w hw k hk)
  refine ⟨hull S ⊓ fixed (finRep E a) L, le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ⟨?_, fun u hu g => ?_, ?_⟩,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · exact GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => (hty φ hφ).1 u hu g)
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · exact congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hφ.2 u hu)) g
  · have h4 := hφ.1
    clear hφ
    induction h4 using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨T, hT, φ, hφ, rfl⟩ := hψ
      exact ty_comm W T hT.1 φ (hty φ hφ).2
    | zero => exact fun _ => W.zero_mem
    | add x y _ _ hx hy => exact fun g => W.add_mem (hx g) (hy g)
    | smul c x _ hx => exact fun g => W.smul_mem c (hx g)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((capAct E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w (n := a)) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w (n := a) => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w (n := a)) h φ) = heckeVec (fL a w) (KGL w (n := a)) h φ
        have hk := hL.int u hu w
        obtain ⟨u', hu', e1, e3⟩ : ∃ u' ∈ L, GeneralLinearGroup.map (pLoc E w) u' = 1 ∧
            u = locGL E a w (GeneralLinearGroup.map (pLoc E w) u) * u' :=
          ⟨_, L.mul_mem (L.inv_mem (hL.loc w hw _ hk)) hu, by rw [map_mul, map_inv, pLoc_locGL, inv_mul_cancel],
            (mul_inv_cancel_left _ _).symm⟩
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [e3, map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) _ hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SplitLim
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

private theorem rel_le_mono {s t : Multiset ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ a) s t) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ b) s t :=
  h.mono fun _ _ _ _ hxy => hxy.trans hab

private theorem rel_shift {s c : Multiset ℂ} {ε : ℝ} (α : ℂ)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (s.map (· + α)) c) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) s (c.map (· - α)) := by
  rw [Multiset.rel_map_left] at h
  rw [Multiset.rel_map_right]
  refine h.mono fun x _ y _ hxy => ?_
  have : x - (y - α) = x + α - y := by ring
  rw [this]
  exact hxy

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.splitLim :
    SplitLim := by
  classical
  intro E _ _ _ m₀ α β
  let A : (E →+* ℂ) → Set (Multiset ℂ × Multiset ℂ) := fun t => {x | x.1 + x.2 = m₀ t}
  have hA : ∀ t, (A t).Finite := fun t => by
    refine ((Multiset.antidiagonal (m₀ t)).toFinset.finite_toSet).subset ?_
    intro x hx
    simpa [A, Multiset.mem_antidiagonal] using hx
  have hS : (Set.pi Set.univ A).Finite := Set.Finite.pi' hA |>.subset (fun σ hσ t => hσ t (Set.mem_univ t))
  let F : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) →
      ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) :=
    fun σ => (fun t => (σ t).1.map (· - α), fun t => (σ t).2.map (· - β))
  refine ⟨(hS.image F).toFinset, ?_⟩
  intro m m₁ m₂ hm hto
  let Good : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) → ℕ → ℕ → Prop := fun σ j k =>
    ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₁ k t) ((F σ).1 t) ∧
      Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₂ k t) ((F σ).2 t)
  have hmono : ∀ σ {i j : ℕ} {k : ℕ}, i ≤ j → Good σ j k → Good σ i k := by
    intro σ i j k hij h t
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      Nat.one_div_le_one_div hij
    exact ⟨rel_le_mono hle (h t).1, rel_le_mono hle (h t).2⟩
  have step1 : ∀ j, ∀ᶠ k in atTop, ∃ σ ∈ Set.pi Set.univ A, Good σ j k := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hall : ∀ᶠ k in atTop, ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m k t) (m₀ t) :=
      eventually_all.2 fun t => hto t _ hpos
    filter_upwards [hall] with k hk
    have hsplit : ∀ t, ∃ x : Multiset ℂ × Multiset ℂ, x.1 + x.2 = m₀ t ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₁ k t).map (· + α)) x.1 ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₂ k t).map (· + β)) x.2 := by
      intro t
      have h := hk t
      rw [hm k t, Multiset.rel_add_left] at h
      obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := h
      exact ⟨(c₁, c₂), hc.symm, h₁, h₂⟩
    choose σ hσ h₁ h₂ using hsplit
    exact ⟨σ, fun t _ => hσ t, fun t => ⟨rel_shift α (h₁ t), rel_shift β (h₂ t)⟩⟩
  have step2 : ∃ σ ∈ Set.pi Set.univ A, ∀ j, ∃ᶠ k in atTop, Good σ j k := by
    by_contra hcon
    have hJ : ∀ σ, ∃ j, σ ∈ Set.pi Set.univ A → ∀ᶠ k in atTop, ¬ Good σ j k := by
      intro σ
      by_cases hσ : σ ∈ Set.pi Set.univ A
      · by_contra hno
        refine hcon ⟨σ, hσ, fun j => ?_⟩
        intro hev
        exact hno ⟨j, fun _ => hev⟩
      · exact ⟨0, fun h => absurd h hσ⟩
    choose J hJ using hJ
    let N := hS.toFinset.sup J
    have hN : ∀ᶠ k in atTop, ∀ σ ∈ Set.pi Set.univ A, ¬ Good σ N k := by
      refine (Filter.eventually_all_finite hS).2 fun σ hσ => ?_
      filter_upwards [hJ σ hσ] with k hk hg
      exact hk (hmono σ (Finset.le_sup (f := J) (hS.mem_toFinset.2 hσ)) hg)
    obtain ⟨k, hk₁, hk₂⟩ := (hN.and (step1 N)).exists
    obtain ⟨σ, hσ, hg⟩ := hk₂
    exact hk₁ σ hσ hg
  obtain ⟨σ, hσ, hfreq⟩ := step2
  obtain ⟨s, hs, hgood⟩ := Filter.extraction_forall_of_frequently hfreq
  have hlim : ∀ (ε : ℝ), 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop j₀] with k hk
    exact (Nat.one_div_le_one_div hk).trans hj₀.le
  refine ⟨F σ, ?_, s, hs, ?_, ?_⟩
  · simpa using Set.mem_image_of_mem F hσ
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).1
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.EigTOf
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S Formalism.UG.P
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB)

private theorem eigT_of {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {T : Set (UpperTheory.V.Cj.S.Pl E)} {K W}
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hty : TypeB K W φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w (n := a)))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : UpperTheory.V.Cj.S.Pl E → Multiset ℂˣ), EigT T K W φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : UpperTheory.V.Cj.S.Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := capOfEig E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : UpperTheory.V.Cj.S.Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := satOfEig E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hty, hm, hB⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

private def tySub {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (K : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Sm E a) where
  carrier := {φ | TypeB K W φ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  add_mem' h h' := ⟨fun u hu g => congrArg₂ (· + ·) (h.1 u hu g) (h'.1 u hu g), fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  smul_mem' c _ h := ⟨fun u hu g => congrArg (c * ·) (h.1 u hu g), fun g => W.smul_mem c (h.2 g)⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.stepT :
    IwaT → SliceT → StabT → StepT := by
  intro hI hSl hSt E _ _ _ r s bad K W hK hW
  obtain ⟨K', W', hK', hW', hI⟩ := hI E r s bad K W hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hSl⟩ := hSl E r s bad K' W' hK' hW'
  refine ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, fun φ₀ m B h₀ hne₀ => ?_⟩
  obtain ⟨φ, hφ, hne⟩ := hI φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := sliceBdd singleBdd E r s φ hφ.aut
  obtain ⟨t₁, t₂⟩ := hSl φ hφ.aut hφ.ty
  obtain ⟨V₁, a₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r bad K₁ W₁ l₁ f₁ (S₁ ⊓ tySub K₁ W₁)
    (hS₁.mono (Submodule.map_mono inf_le_left)) fun _ h => h.2
  obtain ⟨V₂, a₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s bad K₂ W₂ l₂ f₂ (S₂ ⊓ tySub K₂ W₂)
    (hS₂.mono (Submodule.map_mono inf_le_left)) fun _ h => h.2
  obtain ⟨ψ, hψ, hNI, hcap⟩ := ctCap E (r + s) r φ hφ.aut
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, e₁, e₂, n₁, n₂, g₁, g₂, H⟩ :=
    twoVar tensEigB _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r bad) (Ix s bad) opIx opIx st₁ st₂
      (fun i i' v hv => opComm capAct E r bad i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => opComm capAct E s bad i i' v fun w hw => fix₂ w hw hv) (res (constantTerm r φ.1)) hne
      (fun y => (hs₁ y).imp fun f hf => ⟨a₁ ⟨hf.1, t₁ y f hf.2⟩, hf.2⟩)
      (fun x => (hs₂ x).imp fun f hf => ⟨a₂ ⟨hf.1, t₂ x f hf.2⟩, hf.2⟩)
  rw [← hψ] at hne H
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eigT_of φ₁ n₁ (aut₁ _ hφ₁).1 (aut₁ _ hφ₁).2 (fun w hw => fix₁ w hw hφ₁) e₁ g₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eigT_of φ₂ n₂ (aut₂ _ hφ₂).1 (aut₂ _ hφ₂).2 (fun w hw => fix₂ w hw hφ₂) e₂ g₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t => ?_, fun ν ν' hν hν' w hw => ?_⟩
  · refine capArith (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2, ← c₁, ← c₂]
    have := H Unit (fun _ => 1) (fun _ => .inl (t, _)) (fun _ => .inl (t, _)) (fun _ => _) ((m t).map (u + ·)).prod
      (fun _ => capRel slice capBlock E r s ψ hNI t u) fun x y => by
        rw [hcap t u, (hφ.cap t).2 u, hψ]
        simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton,
          one_mul]
        exact MeasureTheory.integral_const_mul _ _
    simpa using this
  · have hv := ctSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) (hφ.sat w hw)
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine satArith (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) (hφ.sat w hw).2.2.1 (E₁.sat w hw).2.2.1 (E₂.sat w hw).2.2.1
      (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_to_adelic_embedding E r s ψ hNI w hv.2.1 ϖ hu j hj
      have := H (Fin (r + 1) × Fin (s + 1)) _ (fun p => .inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
        (fun p => .inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G (satEig (qV E w) (r + s) (B w) j) hG fun x y => by
          rw [hsum x y]
          have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
          rw [this]
          rfl
      rw [← this]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [s₁ w hw ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.RtEig
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

private theorem rt_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)}
    {K K' : Subgroup (GL (Fin a) (Af E))} {W W' : Submodule ℂ (Kinf E a → ℂ)} (hle : K' ≤ K)
    (hn : ∀ c : GL (Fin a) (Af E), (∀ w, GeneralLinearGroup.map (pLoc E w) c ∈ KGL w (n := a)) → ∀ u ∈ K', c⁻¹ * u * c ∈ K')
    (hT : ∀ f : Kinf E a → ℂ, (∀ a, (fun k => f (a * k)) ∈ W) → ∀ b, (fun k => f (k * b)) ∈ W') {φ m B} (h : EigT bad K W φ m B)
    {k : GA E a} (hk : k ∈ Reduction.maxCompact (K := E) (n := a)) : EigT bad K' W' (rt E a k φ) m B := by
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  set kf := GeneralLinearGroup.map (pFin E) k with hkf
  have hmem : ∀ w, GeneralLinearGroup.map (pLoc E w) kf ∈ KGL w (n := a) := fun w => by
    have hGL : GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a =
        KGL w (n := a) := by
      change GLint (Fin a) (ValuativeRel.valuation (w.adicCompletion E)).integer =
        GLint (Fin a) (w.adicCompletionIntegers E).toSubring
      exact congrArg (GLint (Fin a))
        (Subring.ext fun x => GroundTheory.Global.mem_valuationInteger_iff w x)
    rw [← hGL]
    have e : GeneralLinearGroup.map (pLoc E w) kf = Reduction.finAt w k := by
      ext i j : 2
      rfl
    rw [e]
    exact hk.2 w
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Kinf E a, k = infGL E a (Unitary.toUnits k₀) * finGL E a kf := by
    obtain ⟨k₀, e⟩ := (UpperTheory.V.Cm.cptEq E a).surjective ⟨archPart k, archPart_mem_archCompact hk⟩
    refine ⟨k₀, ?_⟩
    rw [← UpperTheory.V.Cm.infEmb_cptEq, e, ← UpperTheory.V.Fb.finEmb_eq]
    exact (infEmb_archPart_mul_finEmb_finPart k).symm
  refine ⟨hne, (UpperTheory.V.Cm.isAutForm_iff _).2 (((UpperTheory.V.Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    ⟨fun u hu g => ?_, fun g => ?_⟩, fun t => ⟨(h.cap t).1, fun u => ?_⟩, fun w hw' => ?_⟩
  · change φ.1 (g * finGL E a u * k) = φ.1 (g * k)
    rw [← h.ty.1 _ (hle (hn kf hmem u hu)) (g * k)]
    congr 1
    conv_lhs => rw [hk₀]
    conv_rhs => rw [hk₀]
    rw [mul_assoc g, ← mul_assoc (finGL E a u), ← infGL_comm]
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  · have h1 := hT (fun k' => φ.1 (g * finGL E a kf * infGL E a (Unitary.toUnits k'))) (fun c => by
      simpa only [map_mul, mul_assoc] using h.ty.2 (g * finGL E a kf * infGL E a (Unitary.toUnits c))) k₀
    convert h1 using 2 with k'
    change φ.1 (g * _ * k) = _
    congr 1
    conv_lhs => rw [hk₀]
    rw [mul_assoc g (finGL E a kf), ← infGL_comm, map_mul, map_mul]
    simp only [mul_assoc]
  · have e := LinearMap.congr_fun ((capAct E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · have hw := h.sat w hw'
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw (hmem w)
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hloc : u * locGL E a w g = locGL E a w g * u := by
      have hproj (v : Pl E) :
          GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
            GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := by
        rw [map_mul (GeneralLinearGroup.map (pLoc E v)) u (locGL E a w g),
          map_mul (GeneralLinearGroup.map (pLoc E v)) (locGL E a w g) u]
        by_cases hv : v = w
        · subst hv
          rw [hu1, one_mul, mul_one]
        · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
      ext i j : 2
      exact FiniteAdeleRing.ext _ fun v =>
        congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (hproj v)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), hloc, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.iwaT :
    LevShrink → TypeSat → IwaT := by
  intro hL hT E _ _ _ r s bad K W hK hW
  obtain ⟨K', hle, hK', hn⟩ := hL E _ bad K hK.isOpen hK.loc
  obtain ⟨W', hW', hT⟩ := hT _ W hW
  refine ⟨K', W', hK', hW', fun φ m B h ⟨g, hg⟩ => ?_⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, rt_eig hle hn hT h hk, m₁, m₂, ?_⟩
  have hl : IsLeftInvariant φ.1 := h.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← constantTerm_rightTranslate] at hg
  exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.CuspMem
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open UpperTheory.V.Cj.S (CI mem_CI fL ciBasic ciCompl capAct locOf Pl)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke

section Lin

variable {M O : Type*} [AddCommGroup M] [Module ℂ M]

private theorem exists_irr_compl (act : O → Module.End ℂ M) (C : Submodule ℂ M) (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C) {φ : M} (hφ : φ ∈ C) (h0 : φ ≠ 0) :
    ∃ V D : Submodule ℂ M, V ≤ C ∧ D ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      (∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V) ∧ (∀ o, ∀ x ∈ D, act o x ∈ D) ∧
      V ⊓ D = ⊥ ∧ V ⊔ D = C ∧ φ ∉ D := by
  let U : Submodule ℂ M := sInf {W | φ ∈ W ∧ ∀ o, ∀ x ∈ W, act o x ∈ W}
  have hUC : U ≤ C := sInf_le ⟨hφ, hC⟩
  have hφU : φ ∈ U := Submodule.mem_sInf.2 fun W hW => hW.1
  have hUs : ∀ o, ∀ x ∈ U, act o x ∈ U := fun o x hx =>
    Submodule.mem_sInf.2 fun W hW => hW.2 o x (Submodule.mem_sInf.1 hx W hW)
  have hle := UpperTheory.V.TR.SS.le_sSup_minimal act U hUs fun W hW hs => by
    obtain ⟨D, -, d2, d3, d4⟩ := hc W (hW.trans hUC) hs
    refine ⟨D ⊓ U, inf_le_right, fun o x hx => ⟨d2 o x hx.1, hUs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, d3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hW, d4, inf_eq_right.2 hUC]
  by_contra hn
  refine h0 ((Submodule.mem_bot ℂ).1 ((hle.trans (sSup_le ?_)) hφU))
  rintro V ⟨v1, v2, v3, v4⟩
  obtain ⟨D, d1, d2, d3, d4⟩ := hc V (v1.trans hUC) v2
  by_cases hD : φ ∈ D
  · rw [← d3]
    exact le_inf le_rfl (v1.trans (sInf_le ⟨hD, d2⟩))
  · exact absurd ⟨V, D, v1.trans hUC, d1, v2, v3, v4, d2, d3, d4, hD⟩ hn

private theorem compl_sub (act : O → Module.End ℂ M) {C D : Submodule ℂ M}
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C)
    (hD : D ≤ C) (hs : ∀ o, ∀ x ∈ D, act o x ∈ D) :
    ∀ U ≤ D, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D' ≤ D, (∀ o, ∀ x ∈ D', act o x ∈ D') ∧ U ⊓ D' = ⊥ ∧ U ⊔ D' = D := by
  intro U hU hUs
  obtain ⟨D₀, -, a2, a3, a4⟩ := hc U (hU.trans hD) hUs
  refine ⟨D₀ ⊓ D, inf_le_right, fun o x hx => ⟨a2 o x hx.1, hs o x hx.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, a3, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, a4, inf_eq_right.2 hD]

end Lin

private theorem exists_proj {M : Type*} [AddCommGroup M] [Module ℂ M] {C V D : Submodule ℂ M} (hV : V ≤ C) (hD : D ≤ C)
    (h1 : V ⊓ D = ⊥) (h2 : V ⊔ D = C) :
    ∃ p : C →ₗ[ℂ] V, (∀ x : C, x.1 - (p x).1 ∈ D) ∧ ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v := by
  have hc : IsCompl (V.comap C.subtype) (D.comap C.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, h1, Submodule.comap_bot, Submodule.ker_subtype]
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (h2.ge hx)
      exact Submodule.mem_sup.2 ⟨⟨v, hV hv⟩, hv, ⟨d, hD hd⟩, hd, rfl⟩
  let p : C →ₗ[ℂ] V := (Submodule.comapSubtypeEquivOfLe hV).toLinearMap ∘ₗ Submodule.projectionOnto _ _ hc
  have hp : ∀ x : C, x.1 - (p x).1 ∈ D := fun x => by
    obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top.ge (Submodule.mem_top (x := x)))
    have e1 : Submodule.projectionOnto _ _ hc v = ⟨v, hv⟩ := Submodule.projectionOnto_apply_left hc ⟨v, hv⟩
    have e2 : Submodule.projectionOnto _ _ hc d = 0 := Submodule.projectionOnto_apply_right hc ⟨d, hd⟩
    have : (p (v + d)).1 = v.1 := by
      simp only [p, LinearMap.comp_apply, map_add (f := _), e1, e2, map_zero, add_zero]
      rfl
    rw [this]
    simpa using hd
  refine ⟨p, hp, fun x v h => Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 (h1.le ⟨V.sub_mem (p x).2 v.2, ?_⟩)))⟩
  have := D.sub_mem h (hp x)
  rwa [sub_sub_sub_cancel_left] at this

section Forms

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def stRep (C : Submodule ℂ (Sm E a)) (hC : _root_.GlobalTheory.CuspRep.IsStable C) : Representation ℂ (GL (Fin a) (Af E)) C :=
  GlobalTheory.PRep.sub (finRep E a) C fun k => hC (.fin k)

private theorem proj_rep {C V D : Submodule ℂ (Sm E a)} (hC : _root_.GlobalTheory.CuspRep.IsStable C) (hV : _root_.GlobalTheory.CuspRep.IsStable V) (hD : _root_.GlobalTheory.CuspRep.IsStable D)
    (p : C →ₗ[ℂ] V) (p1 : ∀ x : C, x.1 - (p x).1 ∈ D) (p2 : ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v)
    (g : GL (Fin a) (Af E)) (y : C) : p (stRep C hC g y) = stRep V hV g (p y) := by
  refine p2 _ _ ?_
  have := hD (.fin g) _ (p1 y)
  rw [map_sub] at this
  exact this

private theorem hasSat_of_map {C : Submodule ℂ (Sm E a)} (hC : _root_.GlobalTheory.CuspRep.IsStable C) (π : CuspSub E a) (f : C →ₗ[ℂ] π.V)
    (hf : ∀ g (y : C), f (stRep C hC g y) = π.finPart g (f y)) (w : Pl E) (B : Multiset ℂˣ) {x : C}
    (hx : IsSatVecGL w (fL a w) x.1 B) (h0 : f x ≠ 0) : HasSatGL w (π.locRep w) B := by
  have h1 : IsSatVecGL w (locOf (stRep C hC) w) x B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hx
  have h2 : IsSatVecGL w (π.locRep w) (f x) B := h1.map f (fun g y => hf _ y) h0
  obtain ⟨B', hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨f x, h2.2.1, h0⟩)
  rwa [(hB.2 _ h2.2.1 h0).unique h2] at hB

end Forms

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.GeneralLocalHecke in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.cuspMem :
    CuspMem := by
  intro E _ _ _ N hN bad hbad K W φ m B h hc
  have hb := ciBasic capAct E N m
  have hc0 := ciCompl (ciBasic capAct) E N hN m
  have hφ : φ ∈ CI N m := mem_CI.2 ⟨hc, fun t => (h.cap t).2⟩
  obtain ⟨V, D, v1, d1, v2, v3, v4, d2, h1, h2, hφD⟩ := exists_irr_compl act (CI N m) hb.1 hc0 hφ h.ne
  let π : CuspSub E N := ⟨V, fun ψ hψ => (mem_CI.1 (v1 hψ)).1, v2, v3, v4⟩
  let x : CI N m := ⟨φ, hφ⟩
  obtain ⟨p, p1, p2⟩ := exists_proj v1 d1 h1 h2
  obtain ⟨q, q1, q2⟩ := exists_proj d1 v1 (by rwa [inf_comm]) (by rwa [sup_comm])
  have hp0 : p x ≠ 0 := fun e => hφD (by simpa [e, x] using p1 x)
  have hS : ∀ w ∉ bad, HasSatGL w (π.locRep w) (B w) := fun w hw =>
    hasSat_of_map hb.1 π p (proj_rep hb.1 v2 d2 p p1 p2) w (B w) (x := x) (h.sat w hw) hp0
  have hq : q x = 0 := by
    by_contra hq0
    have hq0' : (q x).1 ≠ 0 := fun e => hq0 (Subtype.ext e)
    obtain ⟨V', D', u1, e1, u2, u3, u4, e2, g1, g2, hD'⟩ :=
      exists_irr_compl act D d2 (compl_sub act hc0 d1 d2) (q x).2 hq0'
    let π' : CuspSub E N := ⟨V', fun ψ hψ => (mem_CI.1 (d1 (u1 hψ))).1, u2, u3, u4⟩
    obtain ⟨p', p1', p2'⟩ := exists_proj u1 e1 g1 g2
    have hp0' : p' (q x) ≠ 0 := fun e => hD' (by simpa [e] using p1' (q x))
    have hS' : ∀ w ∉ bad, HasSatGL w (π'.locRep w) (B w) := fun w hw =>
      hasSat_of_map hb.1 π' (p' ∘ₗ q) (fun g y => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, proj_rep hb.1 d2 v2 q q1 q2, proj_rep d2 u2 e2 p' p1' p2']
        rfl) w (B w) (x := x) (h.sat w hw) hp0'
    have e : V = V' := UpperTheory.V.Af.strongMultOneC E N π π'
      (Filter.eventually_cofinite.2 (hbad.subset fun w hw => by_contra fun hn => hw ⟨B w, hS w hn, hS' w hn⟩))
    exact v3 (eq_bot_iff.2 (h1 ▸ le_inf le_rfl (e.le.trans u1)))
  have hφV : φ ∈ V := by simpa [hq, x] using q1 x
  exact ⟨π, hφV, fun t => ⟨(h.cap t).1, fun u ψ hψ => (mem_CI.1 (v1 hψ)).2 t u⟩,
    fun w hw => (CG.hasSat_mk π w _).2 (hS w hw)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.SliceT
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem st_emb_val {R : Type} [CommRing R] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) R) (i j : Fin a) :
    (emb e g).val (e i) (e j) = g.val i j := by
  rw [coe_emb, Matrix.add_apply, matrixExtendByZero_apply, Matrix.sub_apply]
  simp [Matrix.one_apply]

private theorem st_mem_of_emb {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {h : GL (Fin a) L}
    (hk : emb e h ∈ GLint (Fin n) O) : h ∈ GLint (Fin a) O := by
  obtain ⟨k, hk⟩ := hk
  have hk' : bc O.subtype k⁻¹ = emb e h⁻¹ := by rw [map_inv, hk, map_inv]
  let A : Matrix (Fin a) (Fin a) O := fun i j => k.val (e i) (e j)
  let B : Matrix (Fin a) (Fin a) O := fun i j => (k⁻¹).val (e i) (e j)
  have hA : A.map O.subtype = h.val := by
    ext i j
    rw [← st_emb_val e h, ← hk]
    rfl
  have hB : B.map O.subtype = (h⁻¹).val := by
    ext i j
    rw [← st_emb_val e h⁻¹, ← hk']
    rfl
  have inj : Function.Injective (fun M : Matrix (Fin a) (Fin a) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    change (A * B).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (mul_inv_cancel h))
  have hBA : B * A = 1 := inj (by
    change (B * A).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (inv_mul_cancel h))
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable {R S : Type} [CommRing R] [CommRing S]

private theorem st_corner_sub {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem st_corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [st_corner_sub, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, st_corner_sub]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

end SlopeTestRemainingChoices

section Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB)
open UpperTheory.V.Cj.S (res)

variable {E : Type} [Field E] [NumberField E]

private theorem st_emb_fin {a n : ℕ} (e : Fin a ↪ Fin n) (u : GL (Fin a) (Af E)) :
    emb e (finGL E a u) = finGL E n (emb e u) := by
  simp only [finGL, st_corner_emb]

private theorem st_emb_loc {a n : ℕ} (e : Fin a ↪ Fin n) (w) (k : GL (Fin a) (HeightOneSpectrum.adicCompletion E w)) :
    emb e (locGL E a w k) = locGL E n w (emb e k) := by
  simp only [locGL, st_corner_emb]

variable [IsCMField E]

private theorem st_lev {a n : ℕ} (e : Fin a ↪ Fin n) {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K : Subgroup (GL (Fin n) (Af E))}
    (hK : Lev bad K) : Lev bad (K.comap (emb e)) := by
  refine ⟨hK.isOpen.preimage
    (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E a n e).2.2, ?_, ?_⟩
  · intro u hu w
    have h := hK.int _ hu w
    rw [emb_map] at h
    exact st_mem_of_emb _ e h
  · intro w hw k hk
    change emb e (locGL E a w k) ∈ K
    rw [st_emb_loc]
    refine hK.loc w hw _ ?_
    obtain ⟨k, rfl⟩ := hk
    exact ⟨emb e k, emb_map e _ k⟩

private theorem st_arch {a n : ℕ} (e : Fin a ↪ Fin n) (k : archCompact E a) : embArch e k.1 ∈ archCompact E n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat E a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1] at h
  exact Subgroup.mem_comap.2 h

private noncomputable def stJ {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) : Kinf E n :=
  (UpperTheory.V.Cm.cptEq E n).symm ⟨embArch e (UpperTheory.V.Cm.cptEq E a k).1, st_arch e _⟩

private theorem st_emb_inf {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) :
    emb e (infGL E a (Unitary.toUnits k)) = infGL E n (Unitary.toUnits (stJ e k)) := by
  rw [← UpperTheory.V.Cm.infEmb_cptEq, ← UpperTheory.V.Cm.infEmb_cptEq, stJ, MulEquiv.apply_symm_apply]
  exact (UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1 _

private theorem st_ct_fin {n r : ℕ} {K : Subgroup (GL (Fin n) (Af E))} {φ : Sm E n}
    (h : ∀ u ∈ K, ∀ g, φ.1 (g * finGL E n u) = φ.1 g) :
    ∀ u ∈ K, ∀ g, constantTerm r φ.1 (g * finGL E n u) = constantTerm r φ.1 g := by
  intro u hu g
  unfold constantTerm
  simp only [← mul_assoc, h u hu]

private theorem st_ct_inf {n r : ℕ} (W : Submodule ℂ (Kinf E n → ℂ)) (hW : FiniteDimensional ℂ W) {φ : Sm E n}
    (hc : Continuous φ.1) (h : ∀ g, (fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W) (g : GA E n) :
    (fun k : Kinf E n => constantTerm r φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W := by
  refine @UpperTheory.locallyFinite_of_algMod_criterion _ (Kinf E n) (_) _ W hW (fun X k => φ.1 (unipGL X * (g * infGL E n (Unitary.toUnits k)))) (fun X => ?_)
    (fun k => integrableOn_constantTerm hc _)
  simpa only [mul_assoc] using h (unipGL X * g)

private theorem st_slice {a n : ℕ} (e : Fin a ↪ Fin n) {K : Subgroup (GL (Fin n) (Af E))} {W : Submodule ℂ (Kinf E n → ℂ)}
    {Φ : GA E n → ℂ} (h1 : ∀ u ∈ K, ∀ g, Φ (g * finGL E n u) = Φ g)
    (h2 : ∀ g, (fun k : Kinf E n => Φ (g * infGL E n (Unitary.toUnits k))) ∈ W) (f : Sm E a) (g₀ : GA E n)
    (hf : ∀ m, f.1 m = Φ (g₀ * emb e m)) :
    TypeB (K.comap (emb e)) (W.map (LinearMap.funLeft ℂ ℂ (stJ e))) f := by
  refine ⟨fun u hu g => ?_, fun g => ⟨_, h2 (g₀ * emb e g), funext fun k => ?_⟩⟩
  · rw [hf, hf, map_mul, st_emb_fin, ← mul_assoc]
    exact h1 _ hu _
  · simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, st_emb_inf, mul_assoc]

end Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.sliceT :
    SliceT := by
  intro E _ _ _ r s bad K W hL hW
  refine ⟨K.comap (emb (e1 r s)), W.map (LinearMap.funLeft ℂ ℂ (stJ (e1 r s))), K.comap (emb (e2 r s)),
    W.map (LinearMap.funLeft ℂ ℂ (stJ (e2 r s))), st_lev _ hL, Module.Finite.map W _, st_lev _ hL, Module.Finite.map W _,
    fun φ hφ hT => ?_⟩
  have hc : Continuous φ.1 := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  have h1 := st_ct_fin (r := r) hT.1
  have h2 := st_ct_inf (r := r) W hW hc hT.2
  refine ⟨fun y f hf => st_slice _ h1 h2 f (emb (e2 r s) y) fun m => ?_,
    fun x f hf => st_slice _ h1 h2 f (emb (e1 r s) x) fun m => ?_⟩
  · rw [hf, ← emb_comm]
    rfl
  · rw [hf]
    rfl
end
