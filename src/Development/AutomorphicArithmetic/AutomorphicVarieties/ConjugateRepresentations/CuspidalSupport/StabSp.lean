module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.StabSp
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.stabSp :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.LevelSplit → UpperTheory.V.Cj.S.HullBdd → UpperTheory.V.Cj.S.HullOps → UpperTheory.V.Cj.S.StabSp := by
  intro hC hL hB hO E _ _ _ a S hS
  obtain ⟨L, hLo, hl⟩ := hS.level
  obtain ⟨L', hL'o, hle, T, hT, hsp⟩ := hL E a L hLo
  obtain ⟨h1, h2, h3⟩ := hO E a S
  have hb := hB E a S hS L' hL'o
  have hK : ∀ w ∉ T, fixed (finRep E a) L' ≤ fixed (fL a w) (KGL w (n := a)) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ ((hsp w hw).1 k hk)
  refine ⟨T, hT, hull S ⊓ fixed (finRep E a) L', le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ?_,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · refine GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => ?_)
    have := hl _ ⟨φ, hφ, rfl⟩ u (hle hu) g
    rw [UpperTheory.V.Fb.finEmb_eq] at this
    exact this
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((hC E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w (n := a)) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w (n := a) => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w (n := a)) h φ) = heckeVec (fL a w) (KGL w (n := a)) h φ
        obtain ⟨k, hk, u', hu', e1, rfl⟩ := (hsp w hw).2 u hu
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) k hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TauSat
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

private theorem rank_le_aleph0_of_irred [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    {ρ : Representation ℂ G V} (hs : GlobalTheory.PRep.IsSmooth ρ) (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => stable_eq hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

end

private theorem biSimple {E : Type} [Field E] [NumberField E] {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin a) (Af E)) V} (hi : ρ.IsIrreducible) (w : Pl E) :
    GlobalTheory.CompanionTheory.SatAe.IsBiSimple (locOf ρ w) := by
  intro S h1 h2
  refine stable_eq hi S fun k x hx => ?_
  let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
  have h3 := h2 (ρ (k * (locGL E a w g)⁻¹)) (fun g' => by
    change ρ _ * ρ _ = ρ _ * ρ _
    rw [← map_mul, ← map_mul, LocSph.comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])])
    _ (h1 g x hx)
  have h4 : ρ (k * (locGL E a w g)⁻¹) (locOf ρ w g x) = ρ k x := by
    change ρ _ (ρ _ x) = ρ k x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rwa [h4] at h3

theorem UpperTheory.V.Cj.S.tauSat :
    UpperTheory.V.Cj.S.TauSat := by
  intro E _ _ _ a τ v hv
  haveI := GlobalTheory.CompanionTheory.SatAe.secondCountable_GL (E := E) (a := a)
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change V at v
  have hr := rank_le_aleph0_of_irred hs hi hv
  filter_upwards [LocSph.eventually_mem ((hs v).mem_nhds (by simp))] with w hw
  have hfix : v ∈ fixed (locOf ρ w) (KGL w (n := a)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hsl : GlobalTheory.PRep.IsSmooth (locOf ρ w) := fun x => (hs x).preimage (CuspSub.continuous_locGL w)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => GlobalTheory.CompanionTheory.SatAe.exists_scalar hsl
    (SatCompare.isOpen_isCompact_KGL w a).2 (Final.GLintComm E w a) (Final.HeckeCommGL E w a ℂ) (biSimple hi w) hr h hh)
    ((Submodule.ne_bot_iff _).2 ⟨v, hfix, hv⟩)
  exact ⟨B, hB, hB.2 v hfix hv⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TypesComm
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.exists_interp {Y : Type} (V : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (n : ℕ) (b : Fin n → V) (c : Fin n → Y →₀ ℂ),
      ∀ f ∈ V, ∀ y, f y = ∑ i, (b i).1 y * (c i).sum fun z t => t * f z := by
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  let b := Module.finBasis ℂ V
  have hc : ∀ i, ∃ c : Y →₀ ℂ, (c.sum fun z t => t • ev z) = b.coord i := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨_, b, c, fun f hf y => ?_⟩
  have h := congrArg (ev y) (b.sum_repr ⟨f, hf⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [map_smul] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h2 : b.repr ⟨f, hf⟩ i = (c i).sum fun z t => t * f z := by
    rw [← b.coord_apply, ← hc i, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
    rfl
  rw [h2, smul_eq_mul, mul_comm]
  rfl

theorem UpperTheory.V.Cj.S.typesComm :
    UpperTheory.V.Cj.S.TypesComm := by
  intro E _ _ _ a V hV T hT φ hφ g
  obtain ⟨n, b, c, hc⟩ := UpperTheory.V.Cj.S.exists_interp V
  let R : archCompact E a → Module.End ℂ (Sm E a) := fun k => cptRep E a ((Cm.cptEq E a).symm k)
  have hR : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (R k ψ).1 x = ψ.1 (x * infEmb E a k.1) := by
    intro k ψ x
    obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    simp only [R]
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  have hTR : ∀ (k : archCompact E a) (ψ : Sm E a), T (R k ψ) = R k (T ψ) := fun k ψ =>
    LinearMap.congr_fun (hT _).eq ψ
  have hev : ∀ (k : archCompact E a) (ψ : Sm E a) (x),
      (∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z ψ : Sm E a).1 x =
        ∑ i, (b i).1 k * (c i).sum fun z t => t * ψ.1 (x * infEmb E a z.1) := by
    intro k ψ x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, Finsupp.sum]
  have h1 : ∀ k : archCompact E a, R k φ = ∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z φ := by
    intro k
    refine Subtype.ext (funext fun x => ?_)
    rw [hR, hev]
    exact hc _ (hφ x) k
  have h2 : (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) =
      ∑ i, ((c i).sum fun z t => t * (T φ).1 (g * infEmb E a z.1)) • (b i).1 := by
    funext k
    rw [← hR k, ← hTR, h1 k]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hTR]
    rw [hev]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h2]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.LocComm
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem kgl_eq (w : Pl E) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = KGL w (n := a) := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a = GLint (Fin a) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem loc_comm (w : Pl E) (g : GL (Fin a) (w.adicCompletion E)) {u : GL (Fin a) (Af E)}
    (hu : GeneralLinearGroup.map (pLoc E w) u = 1) : u * locGL E a w g = locGL E a w g * u := by
  have H : ∀ v, GeneralLinearGroup.map (pLoc E v) (u * locGL E a w g) =
      GeneralLinearGroup.map (pLoc E v) (locGL E a w g * u) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hu, mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv, mul_one, one_mul]
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.rtK :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.RtK := by
  intro hc E _ _ _ a φ m B h k hk
  have hne : rt E a k φ ≠ 0 := fun e => h.ne (by
    have := congrArg (rt E a k⁻¹) e
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at this)
  refine ⟨hne, (Cm.isAutForm_iff _).2 (((Cm.isAutForm_iff _).1 h.aut).rightTranslate_of_mem_maxCompact hk),
    fun t => ⟨(h.cap t).1, fun u => ?_⟩, h.sat.mono fun w hw => ?_⟩
  · have e := LinearMap.congr_fun ((hc E a t u).1 k).eq φ
    simp only [Module.End.mul_apply] at e
    rw [e, (h.cap t).2 u, map_smul]
  · set kf := GeneralLinearGroup.map (pFin E) k with hkf
    set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
    have hmem : kw ∈ KGL w (n := a) := by
      rw [← kgl_eq]
      have e : kw = GroundTheory.Automorphic.Reduction.finAt w k := by
        ext i j : 2
        rfl
      rw [e]
      exact hk.2 w
    set u := kf * (locGL E a w kw)⁻¹ with hu
    have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
      rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
    set k' := infGL E a (GeneralLinearGroup.map (pInf E) k) * finGL E a u with hk'
    have hdec : k' * finGL E a (locGL E a w kw) = k := by
      rw [hk', mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]
    have hfix : rt E a (finGL E a (locGL E a w kw)) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hw.2.1 kw hmem
    have e : rt E a k' φ = rt E a k φ := by
      conv_rhs => rw [← hdec, map_mul (rt E a), Module.End.mul_apply, hfix]
    rw [← e] at hne ⊢
    refine hw.map (rt E a k') (fun g y => ?_) hne
    change rt E a k' (rt E a (finGL E a (locGL E a w g)) y) = rt E a (finGL E a (locGL E a w g)) (rt E a k' y)
    have hcm : k' * finGL E a (locGL E a w g) = finGL E a (locGL E a w g) * k' := by
      rw [hk', mul_assoc, ← map_mul (finGL E a), loc_comm w g hu1, map_mul (finGL E a), ← mul_assoc, ← mul_assoc,
        infGL_comm _ (locGL E a w g)]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul (rt E a), ← map_mul (rt E a), hcm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspProj
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_minimal_compl {M O : Type*} [AddCommGroup M] [Module ℂ M] (act : O → Module.End ℂ M)
    (C : Submodule ℂ M) (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
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

theorem UpperTheory.V.Cj.S.cuspProj :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl → UpperTheory.V.Cj.S.CuspProj := by
  intro _ hb hc E _ _ _ a ha m hm φ h0
  obtain ⟨V, D, v1, d1, v2, v3, v4, d2, h1, h2, hφ⟩ :=
    exists_minimal_compl act (CI a m) (hb E a m).1 (hc E a ha m) φ.2 fun h => h0 (Subtype.ext h)
  obtain ⟨p, p1, p2⟩ := exists_proj v1 d1 h1 h2
  refine ⟨⟨V, fun ψ hψ => (mem_CI.1 (v1 hψ)).1, v2, v3, v4⟩, fun t => ⟨hm t, fun u ψ hψ => (mem_CI.1 (v1 hψ)).2 t u⟩,
    p, fun h => hφ ?_, fun g x y hy => p2 _ _ ?_⟩
  · simpa [h] using p1 φ
  · have := d2 (.fin g) _ (p1 x)
    rw [map_sub] at this
    rw [hy]
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem left_slSp {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

private theorem bdd_slices {r s : ℕ} {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S) (hK : Sat S) :
    Bdd (slSp (e1 r s) (Set.range (emb (e2 r s))) (ctSp r S)) ∧
      Bdd (slSp (e2 r s) (Set.range (emb (e1 r s))) (ctSp r S)) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hK', hM⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K _ r S hS
  have hA := UpperTheory.algebraic_module_of_vanishing_block K r s _ hN (UpperTheory.constantTermSpace_centre_of_bdd K _ r S hS) ι D
  refine ⟨⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).1⟩,
    ⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).2⟩⟩
  · rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
    rw [← hM ψ hψ γ 1 (emb (e2 r s) m₂ * emb (e1 r s) m), map_mul, ← mul_assoc, ← emb_comm, blk, map_one, mul_one,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₂, rfl⟩ m
    rw [← emb_comm]
    exact hψ m m₂
  · rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
    rw [← hM ψ hψ 1 γ (emb (e1 r s) m₁ * emb (e2 r s) m), map_mul, ← mul_assoc, emb_comm, blk, map_one, one_mul,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₁, rfl⟩ m
    exact hψ m₁ m

private theorem exists_slice {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n)) {ψ : archSmooth K n} (hψ : ψ ∈ S) {g : AdelicGLn.AdelicGL K n} (hg : g ∈ Γ) :
    ∃ f ∈ slSp e Γ S, ∀ m, f.1 m = ψ.1 (g * emb e m) := by
  obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
  exact ⟨f ψ, Submodule.subset_span ⟨ψ, hψ, g, hg, hf ψ⟩, hf ψ⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.sliceBdd :
    UpperTheory.V.Cj.S.SingleBdd → UpperTheory.V.Cj.S.SliceBdd := by
  intro hB E _ _ _ r s φ hφ
  obtain ⟨S, hle, hS, hK⟩ := UpperTheory.exists_automorphic_saturation_submodule E (r + s) _ (hB E (r + s) φ hφ)
  have hmem : UpperTheory.V.Cm.smEq E (r + s) φ ∈ S :=
    hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self φ))
  obtain ⟨hs, -⟩ := UpperTheory.constantTerm_archSmooth E (r + s) r (UpperTheory.V.Cm.smEq E (r + s) φ) (UpperTheory.isAutomorphicForm_of_bdd_submodule E _ S hS _ hmem)
  have hψ : (⟨_, hs⟩ : GroundTheory.Automorphic.AutomorphicForm.archSmooth E (r + s)) ∈ UpperTheory.V.Af.Fin.ctSp r S :=
    Submodule.subset_span ⟨_, hmem, rfl⟩
  obtain ⟨h₁, h₂⟩ := bdd_slices hS hK
  refine ⟨Submodule.comap (UpperTheory.V.Cm.smEq E r).toLinearMap _, Submodule.comap (UpperTheory.V.Cm.smEq E s).toLinearMap _,
    h₁.mono (Submodule.map_comap_le _ _), h₂.mono (Submodule.map_comap_le _ _), fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e1 r s) (Set.range (emb (e2 r s))) _ hψ ⟨y, rfl⟩
    refine ⟨(UpperTheory.V.Cm.smEq E r).symm f, by simpa using hf, funext fun x => (hf' x).trans ?_⟩
    rw [← UpperTheory.V.Af.Fin.emb_comm]
    rfl
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e2 r s) (Set.range (emb (e1 r s))) _ hψ ⟨x, rfl⟩
    exact ⟨(UpperTheory.V.Cm.smEq E s).symm f, by simpa using hf, funext fun y => hf' y⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SatArith
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem es_zero (A : Multiset ℂ) : A.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem es_cons (a : ℂ) (A : Multiset ℂ) (k : ℕ) :
    (a ::ₘ A).esymm (k + 1) = A.esymm (k + 1) + a * A.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

private theorem es_big (A : Multiset ℂ) {k : ℕ} (h : A.card < k) : A.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

private theorem es_add (A C : Multiset ℂ) (j : ℕ) :
    (A + C).esymm j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm p.1 * C.esymm p.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [Finset.sum_eq_single (0, j)]
    · simp [es_zero]
    · rintro ⟨i, k⟩ hp hne
      have : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · simp at hp; simp [hp] at hne
        · exact h
      rw [es_big 0 (by simpa using this), zero_mul]
    · simp
  | cons a A ih =>
    cases j with
    | zero => simp [es_zero]
    | succ j =>
      rw [Multiset.cons_add, es_cons, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [es_cons, es_zero, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

private theorem es_add_fin (A C : Multiset ℂ) {r s : ℕ} (hA : A.card = r) (hC : C.card = s) (j : ℕ) :
    (A + C).esymm j =
      ∑ p : Fin (r + 1) × Fin (s + 1), if (p.1 : ℕ) + p.2 = j then A.esymm p.1 * C.esymm p.2 else 0 := by
  rw [es_add, ← Finset.sum_filter]
  symm
  refine Finset.sum_of_injOn (fun p => ((p.1 : ℕ), (p.2 : ℕ))) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro p hp
    simpa using hp
  · rintro ⟨i, k⟩ hp hn
    by_cases hi : r < i
    · rw [es_big A (hA ▸ hi), zero_mul]
    by_cases hk : s < k
    · rw [es_big C (hC ▸ hk), mul_zero]
    exact absurd ⟨(⟨i, by omega⟩, ⟨k, by omega⟩), by simpa using hp, rfl⟩ hn

private theorem es_scale (A : Multiset ℂˣ) (c : ℂˣ) (k : ℕ) :
    ((A.map (· * c)).map fun b : ℂˣ => (b : ℂ)).esymm k = (c : ℂ) ^ k * (A.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  rw [← smul_eq_mul, Multiset.pow_smul_esymm]
  simp [Multiset.map_map, mul_comm]

theorem UpperTheory.V.Cj.S.satArith :
    UpperTheory.V.Cj.S.SatArith := by
  intro q r s hq B B₁ B₂ hB h₁ h₂ h α β hα hβ
  refine eq_of_satEig_eq hq hB (by simp [h₁, h₂]) fun j hj => ?_
  rw [← h j hj, satEig, Multiset.map_add (f := _), es_add_fin (r := r) (s := s) _ _ (by simpa using h₁) (by simpa using h₂),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold coef
  split_ifs with hp
  swap
  · simp
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hk : (p.2 : ℕ) ≤ s := Nat.lt_succ_iff.1 p.2.2
  have key : (q : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) * (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((r : ℂ) - (p.1 : ℕ))) / 2) *
      (q : ℂ) ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) =
      (q : ℂ) ^ (((j : ℂ) * (((r + s : ℕ) : ℂ) - j)) / 2) * (α : ℂ) ^ (p.1 : ℕ) * (β : ℂ) ^ (p.2 : ℕ) := by
    rw [hα, hβ, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq',
      ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← hp]
    congr 1
    push_cast [hk]
    ring
  rw [es_scale, es_scale, satEig, satEig]
  linear_combination ((B₁.map fun b : ℂˣ => (b : ℂ)).esymm p.1 * (B₂.map fun b : ℂˣ => (b : ℂ)).esymm p.2) * key
end
