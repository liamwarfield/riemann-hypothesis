module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreSep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]

private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG

theorem UpperTheory.V.Hi.coreSep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := partAct0 hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cLoc_inf {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {x : UA L n} (h : x ∈ infU L n)
    (u : Plc L) : cLoc u x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := h
  have e : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc L u) (Matrix.GeneralLinearGroup.map (pFin L) x.1) := Units.ext rfl
  rw [e, h1, map_one]

private theorem exists_gen {M : Type} [AddCommGroup M] [Module ℂ M] (B : Submodule ℂ M) (T : Set M)
    (h : B ⊓ Submodule.span ℂ T ≠ ⊥) : ∃ x ∈ T, x ≠ 0 := by
  by_contra hc
  refine h ?_
  rw [Submodule.span_eq_bot.2 fun x hx => by_contra fun h0 => hc ⟨x, hx, h0⟩, inf_bot_eq]

private theorem wt_of_form {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) (V : s.Lev) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (J : UA L n → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1))
    (hJ : ∀ x, J x = ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x))
    (h3 : ∀ (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ℓ (x : UA L n),
      RU L n x (toForm ι e F ℓ) = toForm ι e (fun g => F (g * J x)) (ℓ ∘ₗ infRep ι lam x⁻¹))
    (h4 : Function.Surjective (fun k : finU (E := L) (n := n) => J k))
    (σ : Submodule ℂ (UA L n → ℂ)) (F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (hF : F ≠ 0)
    (hσ : ∀ ℓ, toForm ι e F ℓ ∈ σ) (y : Emb l (fun v : V.frame.Vl => s.w v.1)) :
    HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  haveI : Finite V.frame.Vl := @Finite.of_fintype _ V.frame.finV
  haveI : ∀ v : V.frame.Vl, Finite (W.Emb l (s.w v.1)) := fun v => GlobalTheory.HeckeGal.finite_contEmb _
  let Φ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    { toFun := fun ℓ => toForm ι e F ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine UpperTheory.hasWeightAt_of_tensor_dual_intertwiner L n hn _ (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.injective_infinitePlace_of_emb_at_split_places l L Ω s V ι) (fun y => lam y.res) σ Φ (fun h0 => hF (funext fun p => ?_)) hσ (fun ℓ x hx => ?_) y
  · obtain ⟨k, hk⟩ := h4 p
    have h1 : infRep (V := V) ι lam (k : UA L n)⁻¹ (e (F p)) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by
        have h2 := congrFun (LinearMap.congr_fun h0 ℓ) (k : UA L n)
        rw [← hk]
        simp only [hJ]
        exact h2
    have h2 := congrArg (infRep (V := V) ι lam (k : UA L n)) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at h2
    exact e.map_eq_zero_iff.1 h2
  · have h1 : J x = 1 := (hJ x).trans
      (Prod.ext (Subtype.ext (funext fun u => cLoc_inf hx u.1)) (funext fun v => cLoc_inf hx _))
    have h2 := h3 F ℓ x
    simp only [h1, mul_one] at h2
    exact h2

theorem UpperTheory.V.Hi.partUR2Wt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY y
  obtain ⟨F, hF, hF0⟩ := exists_gen _ _ hY
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  obtain ⟨-, -, h3, h4, -⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl
  exact wt_of_form hn V ι e _ (fun _ => rfl) h3 h4 σ (F i) hi (hF i) y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Fix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_mem {w : Plc L} (x : UA L n) (P : Subgroup (GLw n w)) (hx : cLoc w x ∈ P) :
    CaseU.cmp n w ((away l L n).rangeRestrict x) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal
  · rw [cmp_eq h]
    exact hx
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    exact P.one_mem

private theorem st_away (s : HidaSetting l L Ω) (u : s.St) : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => by
  refine s.St_l u.1 u.2 ((s.hA u.1 _).1 ?_)
  have h1 := (s.hw u.1 _).2 h
  simpa using h1

private theorem UpperTheory.V.Hi.inf_one {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n} (hk : k ∈ finU (E := L) (n := n)) :
    infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

private theorem key {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d m : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) {x : UA L n} (hx : x ∈ finU (E := L) (n := n))
    (hl : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) (a : Fin m → ℂ) (i : Fin m)
    (h : ∀ g k, ∑ j, a j * F j (g * ((away l L n).rangeRestrict x, 1)) k = F i g k) (ℓ) :
    ∑ j : Fin m, a j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  funext g
  rw [Finset.sum_apply]
  have e1 : ∀ j, RU L n x (toForm ι e (F j) ℓ) g = ℓ (infRep ι lam g⁻¹ (e (F j
      (((away l L n).rangeRestrict g, fun v : V.frame.Vl => cLoc (s.w v.1) g) * ((away l L n).rangeRestrict x, 1))))) := fun j => by
    change toForm ι e (F j) ℓ (g * x) = _
    unfold toForm
    rw [mul_inv_rev, map_mul, UpperTheory.V.Hi.inf_one V ι lam (inv_mem hx), one_mul]
    simp only [map_mul, hl, mul_one, Prod.mk_mul_mk]
  have e2 : ∀ g, F i g = ∑ j, a j • F j (g * ((away l L n).rangeRestrict x, 1)) := fun g => funext fun k => by
    rw [← h g k, Finset.sum_apply]
    rfl
  simp only [Pi.smul_apply, e1]
  unfold toForm
  rw [e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.partUR2Fix :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d), F ∈ (hset Q τ₀).Big ι ξ → ∀ x ∈ finU (E := L) (n := n), (∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) → ∀ k : KT n (wt s), (∀ u : s.St, k.1 u = cLoc (s.w u) x) → cLoc (s.w s.v0) x ∈ Kc _ n 1 →
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q, cLoc (Q.wq q) x = 1) →
    ∀ (i : Fin m) ℓ, ∑ j : Fin m, ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) k i j • RU L n x (toForm ι e (F j) ℓ) = toForm ι e (F i) ℓ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ _ F hF x hx hl k hk h0 hS hQ i ℓ
  let u : Ub n s := ⟨(away l L n).rangeRestrict x, Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u =>
    cmp_mem x _ (hk u ▸ k.2 u trivial), cmp_mem x _ h0⟩⟩
  have hu : u ∈ UQ n Q := Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw =>
    cmp_mem x _ (hS w hw), Subgroup.mem_iInf.2 fun q =>
      Subgroup.mem_bot.1 (cmp_mem (l := l) x ⊥ (Subgroup.mem_bot.2 (hQ q)))⟩
  have hk' : toKT n s u = k := Subtype.ext (funext fun a => (cmp_eq (st_away s a) x).trans (hk a).symm)
  have h1 := hF.2 u hu
  rw [← hk']
  exact key V ι lam e F hx hl _ i (fun g b => congrFun (congrFun (congrFun h1 i) g) b) ℓ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem cLoc_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact cLoc_ne hx hu
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    rfl

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ}

private theorem sec_eq (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) {x : UA L n}
    (hx : x ∈ locU n w) : ((sec n s w (cLoc w x) : Ub n s) : Ga l L n) = (away l L n).rangeRestrict x := by
  obtain ⟨hb, h1, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hS <| Or.inl <| by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ w.asIdeal
    rwa [map_natCast]
  have hU : (away l L n).rangeRestrict x ∈ Ub n s := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
      exact one_mem _
    · rw [Subgroup.mem_comap, cmp_loc hx (by
        rw [w_under]
        exact fun h => hS (Or.inr (Or.inr h.symm)))]
      exact one_mem _
  have hA : (⟨_, hU⟩ : Ub n s) ∈ locA n s w := Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
    MonoidHom.mem_ker.2 (cmp_loc hx hu)
  have h3 : (⟨_, h2 (cLoc w x)⟩ : locA n s w) = ⟨_, hA⟩ := hb.1 ((h1 _).trans (cmp_of hl x).symm)
  exact congrArg (fun y : locA n s w => (y.1 : Ga l L n)) h3

private theorem toKT_sec (hn : 1 ≤ n) {w : Plc L} (hw : IsSplitAt w) (hS : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) :
    toKT n s (sec n s w g) = 1 := by
  obtain ⟨-, -, h2⟩ := (secU l L Ω s n hn w hw).2 hS
  refine Subtype.ext (funext fun u => ?_)
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (h2 g) (s.w u)) (by
    rw [w_under]
    exact fun h => hS (Or.inr (Or.inl (h ▸ u.2)))))

private theorem infRep_fin {s : HidaSetting l L Ω} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infRep (V := V) ι lam k = 1 := by
  have h1 : ∀ τ : L →+* ℂ, cEmb τ k = 1 := fun τ => by
    change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]
  change PiTensorProduct.mapMonoidHom (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
    GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) k)) = 1
  simp only [h1, map_one]
  exact map_one _

end

private theorem raF_one {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (u : X.Ub) (hu : τ u = 1) (F : Fin m → X.Fn ℂ d) (i : Fin m) (x : Ga × Gp) :
    X.raF d τ u F i x = F i (x * ((u : Ga), 1)) := by
  funext k
  change X.ra τ u (fun g j => F j g k) x i = _
  rw [X.ra_apply, hu, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.V.Hi.partUR2AtW :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ w : Plc L, IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S → ∀ (j : GLw n w →* UA L n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) →
    ∀ (F : Fin m → (hset Q τ₀).X.Fn ℂ d) (g : GLw n w) (i : Fin m) ℓ, toForm ι e ((hset Q τ₀).atW ι d w g F i) ℓ = RU L n (j g) (toForm ι e (F i) ℓ) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ _ w hw hS j hj1 hj2 F g i ℓ
  funext x
  have h1 : (hset Q τ₀).τC ι (sec n s w g) = 1 := by
    change Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l))) (τ₀ (toKT n s (sec n s w g))) = 1
    rw [toKT_sec s hn hw hS, map_one, map_one]
  have h2 : ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (j g) := by
    have := sec_eq s hn hw hS (hj1 g)
    rwa [hj2] at this
  have h3 : ∀ v : V.frame.Vl, cLoc (s.w v.1) (j g) = 1 := fun v => cLoc_ne (hj1 g) (by
    rw [w_under]
    exact fun h => hS (Or.inl (h ▸ v.2)))
  have h4 : infRep (V := V) ι lam (x * j g)⁻¹ = infRep (V := V) ι lam x⁻¹ := by
    rw [mul_inv_rev, map_mul, infRep_fin V ι lam ((finU (E := L) (n := n)).inv_mem (Subgroup.mem_inf.1 (hj1 g)).1), one_mul]
  have h5 : (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from
        ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)) *
      (show Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) from (((sec n s w g : Ub n s) : Ga l L n), 1)) =
      ((away l L n).rangeRestrict (x * j g), fun v : V.frame.Vl => cLoc (s.w v.1) (x * j g)) := by
    refine Prod.ext ?_ (funext fun v => ?_)
    · change (away l L n).rangeRestrict x * ((sec n s w g : Ub n s) : Ga l L n) = (away l L n).rangeRestrict (x * j g)
      rw [h2, map_mul]
    · change cLoc (s.w v.1) x * 1 = cLoc (s.w v.1) (x * j g)
      rw [map_mul, h3]
  have h6 := (raF_one (hset Q τ₀).X ((hset Q τ₀).τC ι) (sec n s w g) h1 F i
    ((away l L n).rangeRestrict x, fun v : V.frame.Vl => cLoc (s.w v.1) x)).trans (congrArg (F i) h5)
  change _ = ℓ (infRep ι lam (x * j g)⁻¹ (e _))
  rw [h4]
  exact congrArg (fun y => ℓ (infRep (V := V) ι lam x⁻¹ (e y))) h6
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LevOut
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2LevOut :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), u ∈ (hset Q τ₀).lev K → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧ ∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K u hu
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  let P : Subgroup (Ub n s) :=
    (⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'),
      (KO (w.adicCompletion L) (Fin n)).comap ((CaseU.cmp n w).comp (Ub n s).subtype)) ⊓
    ⨅ q : Q.Q, Subgroup.comap ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype) (K.1 q)
  have hP : ∀ x : Ub n s, x ∈ P ↔
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
        ∀ q : Q.Q, CaseU.cmp n (Q.wq q) (x : Ga l L n) ∈ K.1 q := fun x =>
    ⟨fun h => ⟨fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).1 w) hw,
      fun q => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).2 q⟩,
     fun h => Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.1 w hw,
      Subgroup.mem_iInf.2 fun q => h.2 q⟩⟩
  have hle : (hset Q τ₀).lev K ≤ P := by
    refine sup_le (fun x hx => ?_) (iSup_le fun q => ?_)
    · have hx' : x ∈ UQ n Q := hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx').1, Subgroup.mem_iInf.2 fun q => ?_⟩
      have e := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx').2 q)
      exact Subgroup.mem_comap.2 (e ▸ one_mem _)
    · rintro _ ⟨g, hg, rfl⟩
      refine (hP (sec n s (Q.wq q) g)).2 ⟨fun w hw => ?_, fun q' => ?_⟩
      · rw [h1 q g w fun h => hw (h ▸ hS q)]
        exact one_mem _
      · by_cases h : q' = q
        · subst h
          exact Set.mem_of_eq_of_mem ((hsec q').2.1 g) hg
        · rw [h1 q g _ fun h' => h (Q.inj h')]
          exact one_mem _
  exact (hP u).1 (hle hu)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Compat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem lc_adic {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : Alg.AdicCont (maximalIdeal R) a) : Alg.AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem lc_chi {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : W.GDet n R G) (f : R →+* R') (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f ∧
      ∀ i, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at h

private theorem lc_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (Hi.heckePol n q a).map f = Hi.heckePol n q fun j => f (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Hi.heckePol, Polynomial.map_sum]

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {T' T : Type} [CommRing T'] [CommRing T] [Algebra c.O T'] [Algebra c.O T]
    (Φ : T' →ₐ[c.O] T) (v : H.V) (g : Dec (F := L) (H.pl v))

private theorem lc_eps (p : T'ˣ) (i : ℕ) :
    (Units.map Φ.toRingHom.toMonoidHom p * H.epsV T v g ^ i : Tˣ) = Units.map Φ.toRingHom.toMonoidHom (p * H.epsV T' v g ^ i) := by
  rw [map_mul, map_pow]
  congr 2
  exact Units.ext (Φ.commutes _).symm

private theorem lc_unit (p : Dec (F := L) (H.pl v) →* T'ˣ) (i : ℕ) (b' : T') (b : T) (hb : Φ b' = b)
    (h : (p g * H.epsV T' v g ^ i : T'ˣ) * b' = 1) : (W.pushCh Φ.toRingHom p g * H.epsV T v g ^ i : Tˣ) * b = 1 := by
  have e := congrArg Φ h
  rw [map_mul, map_one, hb] at e
  rw [← e]
  exact congrArg (fun u : Tˣ => (u : T) * b) (lc_eps H Φ v g (p g) i)

private theorem lc_unif (p : Fin n → Dec (F := L) (H.pl v) →* T'ˣ) (j : Fin n) (b' : T') (b : T) (hb : Φ b' = b)
    (h : ((∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ) : T'ˣ) : T') = b') :
    ((∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = b := by
  rw [← hb, ← h]
  have e : (∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) =
      Units.map Φ.toRingHom.toMonoidHom (∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => lc_eps H Φ v g (p i g) i
  rw [e]
  rfl

end

private theorem lc_cont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (D : W.GDet n R G) (h : D.IsCont (maximalIdeal R)) : (D.map f.toRingHom).IsCont (maximalIdeal R') := fun i => by
  rw [funext fun g => (lc_chi D f.toRingHom g).2 i]
  exact lc_adic f (h i)

private theorem lc_pcont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {G : Type} [Group G] [TopologicalSpace G]
    (p : G →* Rˣ) (h : Alg.AdicCont (maximalIdeal R) fun g => (p g : R)) :
    Alg.AdicCont (maximalIdeal R') fun g => (W.pushCh f.toRingHom p g : R') :=
  lc_adic f h

private theorem lc_frob {O : Type} [CommRing O] {R R' : Type} [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G]
    (D : W.GDet n R G) (g : G) (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ∀ j, P j → R) (b' : ∀ j, P j → R')
    (hb : ∀ j h, f (b j h) = b' j h)
    (h : D.chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b j h else 1) :
    (D.map f.toRingHom).chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b' j h else 1 := by
  rw [(lc_chi D f.toRingHom _).1, h, lc_pol]
  refine congrArg _ (funext fun j => ?_)
  split_ifs
  · exact hb _ _
  · exact map_one _

private theorem lc_comp {O : Type} [CommRing O] {R T' T : Type} [CommRing R] [Algebra O R] [CommRing T'] [Algebra O T']
    [CommRing T] [Algebra O T] (f' : R →ₐ[O] T') (Φ : T' →ₐ[O] T) (f : R →ₐ[O] T) {n : ℕ} {G V : Type} {Γ : V → Type} [Group G]
    [∀ v, Group (Γ v)] (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (hu : ∀ f g : R →ₐ[O] T, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : D.map f.toRingHom = (D.map f'.toRingHom).map Φ.toRingHom ∧
      (fun v i => W.pushCh f.toRingHom (ψ v i)) = fun v i => W.pushCh Φ.toRingHom (W.pushCh f'.toRingHom (ψ v i))) (t : R) :
    f t = Φ (f' t) := by
  rw [hu f (Φ.comp f') (h.1.trans ((CA.d_gmap D).2.1 _ _)) fun v i => congrFun (congrFun h.2 v) i]
  rfl

set_option maxHeartbeats 1600000 in
private theorem lc_univ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K)
    (hΦg : ∀ i, Φ (H.gen θ a K' i) = H.gen θ a K i) (hΦA : ∀ b, Φ (algebraMap A _ b) = algebraMap A _ b)
    (D : W.GDet n (H.TK θ a K') H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K')ˣ)
    (hU : H.IsUniv θ a K' (maximalIdeal _) D ψ) :
    H.IsUniv θ a K (maximalIdeal _) (D.map Φ.toRingHom) fun v i => W.pushCh Φ.toRingHom (ψ v i) := by
  refine { cont := lc_cont Φ D hU.cont, ψ_cont := ?_, frob := ?_, ψ_unit := ?_, ψ_unif := ?_ }
  · intro v i
    exact lc_pcont Φ (ψ v i) (hU.ψ_cont v i)
  · intro w B σ hB hσ
    exact lc_frob Φ D _ _ (fun j => 0 < j ∧ j - 1 < n) _ _ (fun _ _ => hΦg _) (hU.frob w B σ hB hσ)
  · intro v i s g u hg hs
    exact lc_unit H Φ v g (ψ v i) i _ _ (hΦA _) (hU.ψ_unit v i s g u hg hs)
  · intro v j s g hg hs
    exact lc_unif H Φ v g (ψ v) j _ _ (hΦg _) (hU.ψ_unif v j s g hg hs)

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2Compat :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → ∀ (f : R →ₐ[c.O] H.TK θ a K) (f' : R →ₐ[c.O] H.TK θ a K'), H.IsMap θ a K D₀ ψ₀ f → H.IsMap θ a K' D₀ ψ₀ f' → ∀ φ : H.MK θ a K →ₗ[A] H.MK θ a K', Function.Injective φ → (∀ i (y : H.MK θ a K), ((φ ((H.gen θ a K i : Module.End A (H.MK θ a K)) y) : H.MK θ a K') : H.X.Fn A H.m) = H.op A i (φ y)) → ∀ t y, φ ((f t : Module.End A (H.MK θ a K)) y) = (f' t : Module.End A (H.MK θ a K')) (φ y) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ a K K' _ _ _ _ R _ _ D₀ ψ₀ huniq f f' hf hf' φ hφ hgen t y
  obtain ⟨Ψ, hΨg, hΨ⟩ := levelUR2HeckeMap A _ _ _ _ (H.MK θ a K) (H.MK θ a K') (H.op A) (H.op A) φ id hφ hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K, ∀ x, Φ x = Ψ x := ⟨Ψ.restrictScalars c.O, fun _ => rfl⟩
  have hM := lc_univ H θ a K K' Φ (fun i => (hΦ _).trans (hΨg i)) (fun b => (hΦ _).trans (Ψ.commutes b)) _ _ hf'
  have e := lc_comp f' Φ f D₀ ψ₀ (huniq _) (coreUniq hN L Ω l n c H hA A θ hθ a K _ _ hM _ _ hf) t
  rw [e, hΦ]
  exact hΨ (f' t) y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelChangeBaseGroupHomApplyProjection
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace UpperTheory.V.Hi.LvR

section Abs

variable {l : ℕ} [Fact l.Prime] {F' F : W.GFrame l} (h : W.FHom F' F)

theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (W.GDet.ofRep ρ).comap φ = W.GDet.ofRep (ρ.comp φ) := by
  apply W.GDet.ext
  intro B _ _ y
  have key : ∀ z : MonoidAlgebra B H,
      W.GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ z) = W.GDet.repAlg (ρ.comp φ) B z := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g b => simp [W.GDet.repAlg, MonoidAlgebra.lift_single]
  exact congrArg Matrix.det (key y)

theorem chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
  simp only [W.GDet.chi, W.GDet.comap, MonoidAlgebra.mapRingHom_single, map_one]
  show (D.D A[X]) (MonoidAlgebra.mapDomainRingHom A[X] φ _) = _
  rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]

theorem polar_comap (O : Type) [CommRing O] [Algebra ℤ_[l] O] {R : Type} [CommRing R] [Algebra O R] {n : ℕ}
    (D : W.GDet n R F.G₀) (hD : F.IsPolar O D) : F'.IsPolar O (D.comap h.π₀) := by
  intro B _ _ _ _ y
  have key : ∀ z : MonoidAlgebra B F'.G₀, MonoidAlgebra.mapDomainRingHom B h.π₀ (F'.star O B n z) =
      F.star O B n (MonoidAlgebra.mapDomainRingHom B h.π₀ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at *
      rw [ha, hb]
    | single g b =>
      have hc : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
        apply Subtype.ext
        show h.π (F'.c * (g : F'.Γ) * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
        rw [map_mul, map_mul, map_inv, h.hc]
      have he : F'.eps O B g = F.eps O B (h.π₀ g) := by
        apply Units.ext
        show (algebraMap O B) ((algebraMap ℤ_[l] O) (F'.ε g : ℤ_[l])) =
          (algebraMap O B) ((algebraMap ℤ_[l] O) (F.ε (h.π g) : ℤ_[l]))
        rw [h.hε]
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, hc, he]
  show D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _) = D.D B (MonoidAlgebra.mapDomainRingHom B h.π₀ _)
  rw [key]
  exact hD B _

def upG {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 : ∀ i, IsOpen (((r.chib i).comp h.p₀).ker : Set G'.G₀))
    (h2 : Function.Injective fun i => (r.chib i).comp h.p₀)
    (h3 : G'.frame.IsPolar O (W.GDet.ofRep (W.diagRep fun i => (r.chib i).comp h.p₀))) : Resid G'.frame O n :=
  ⟨fun i => (r.chib i).comp h.p₀, h1, h2, h3, r.psib, r.psib_open, r.th, r.th_comm⟩

theorem upG_compat {Lc : Pa.Loc} {G' G : Pa.Glob l Lc} (h : G'.Hom G) {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid G.frame O n) (h1 h2 h3) : Pa.Glob.Compat h (upG h r h1 h2 h3) r := ⟨fun _ => rfl, rfl, rfl⟩

end Abs

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

def fh : W.FHom V.frame V0.frame where
  π := h.p
  π_cont := h.cont
  hη := h.η
  hc := h.c
  hε := h.ε
  vl v := v
  gv _ := MonoidHom.id _
  gv_cont _ := continuous_id
  hφ v g := (h.φ v g).symm
  hI _ _ hg := hg

def p0 : V.frame.G₀ →* V0.frame.G₀ := (fh h).π₀

theorem continuous_levelChangeBaseGroupHom : Continuous (p0 h) := (h.cont.comp continuous_subtype_val).subtype_mk _

theorem surjective_levelChangeBaseGroupHom : Function.Surjective (p0 h) := by
  intro g
  obtain ⟨x, hx⟩ := h.surj (g : V0.frame.Γ)
  have hxk : V.η x = 1 := by
    have := h.η x
    rw [hx] at this
    exact this.symm.trans g.2
  exact ⟨⟨x, hxk⟩, Subtype.ext hx⟩

theorem levelChangeBaseGroupHom_apply_projection (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (g : G L Ω) : p0 h (V.pr g) = V0.pr g := Subtype.ext (hp _)

def rUp : Resid V.frame O n where
  chib i := (r.chib i).comp (p0 h)
  chib_open i := (r.chib_open i).preimage (continuous_levelChangeBaseGroupHom h)
  chib_inj i j e := r.chib_inj (MonoidHom.ext fun g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    exact DFunLike.congr_fun e x)
  polar := by
    have := polar_comap (fh h) O (W.GDet.ofRep (W.diagRep r.chib)) r.polar
    rw [ofRep_comap] at this
    exact this
  psib := r.psib
  psib_open := r.psib_open
  th v i := @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i)
  th_comm v i := @id (∀ g : W.muG l (Dec (F := L) (s.A v.1)), (g : Dec (F := L) (s.A v.1)) ∈
    (commutator (Dec (F := L) (s.A v.1))).topologicalClosure → @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g = 1) (r.th_comm v i)

set_option maxHeartbeats 2000000 in
theorem psi_up {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ) :
    (rUp h).IsPsi v i ψ ↔ r.IsPsi v i ψ := by
  constructor
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩
  · intro H
    have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
        ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
    exact ⟨H.cont, H.red, hm⟩

theorem rUp_Dbar : (rUp h).Dbar = r.Dbar.comap (p0 h) := by
  rw [Resid.Dbar, Resid.Dbar, ofRep_comap]; rfl

def rN : Resid (Pa.globOf r V).frame O n :=
  upG h (Pa.residOf r) (rUp h).chib_open (rUp h).chib_inj (rUp h).polar

theorem rN_compat : Pa.Glob.Compat h (rN h) (Pa.residOf r) := upG_compat _ _ _ _ _

theorem rN_Ip_le (u : s.St) (g : V.η.ker) (hg : g ∈ (rN h).Ip u) : g ∈ (rUp h).Ip u := by
  obtain ⟨⟨γ, ⟨h1, -⟩, rfl⟩, h2⟩ := hg
  exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩

theorem psi_N {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (v : Vl l L) (i : Fin n) (ψ : Dec (F := L) (s.A v.1) →* Rˣ)
    (H : (rUp h).IsPsi v i ψ) : (rN h).IsPsi v i ψ := by
  have hm : ∀ g : W.muG l (Dec (F := L) (s.A v.1)),
      ((ψ g : Rˣ) : R) = algebraMap O R ((r.th v i g : Oˣ) : O) := fun g => H.mu g
  exact ⟨H.cont, H.red, hm⟩

def pairN {B : Type} [CommRing B] [Algebra O B] [Alg.IsCO O B] (u : Pair (rUp h) B) : Pair (rN h) B :=
  ⟨u.D, u.ψ, u.cont, u.red, fun v i => psi_N h v i _ (u.psi v i), u.P, u.Ord,
    fun w g hg => u.I w g (rN_Ip_le h w g hg)⟩

def lamUp (Λ : LamObj r) : LamObj (rUp h) where
  Λ := Λ.Λ
  κ := Λ.κ
  inert v i := by
    obtain ⟨ψ, hψ, e⟩ := Λ.inert v i
    exact ⟨ψ, (psi_up h v i ψ).2 hψ, e⟩
  univ R _ _ _ κ' hκ := Λ.univ R κ' fun v i => by
    obtain ⟨ψ, hψ, e⟩ := hκ v i
    exact ⟨ψ, (psi_up h v i ψ).1 hψ, e⟩

end Gen

end UpperTheory.V.Hi.LvR
end
end
