module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import GroundTheory.LocalFields.MainTheorem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.BlochKatoDimension

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {K : FinExt l} (e : G ≃* ↥(GK K))
  {E : Type} [Field E] [Algebra ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] E V] (ρ : Representation E G V)

private def tr : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom

private theorem tr_apply (g : G) (v : V) : tr e ρ (e g) v = ρ g v := by
  simp [tr, resCoef]

private theorem actVB_tr (g : G) (x : V ⊗[ℚ_[l]] Bcr l) :
    actVB ((PP l).PD K) (tr e ρ) (e g) x = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, actC, tr_apply, (PP l).PD_actB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actVdR_tr (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actVdR ((PP l).PD K) (tr e ρ) (e g) x = actD ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, actD, tr_apply, (PP l).PD_actdR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actD_res (φ : G →* GQ l) (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actD φ (resCoef ℚ_[l] ρ) g x = actD φ ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actD, resCoef]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem Ddr_res (φ : G →* GQ l) :
    Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Ddr, sub_eq_zero, actD_res]

private theorem DdR_tr :
    DdR ((PP l).PD K) (tr e ρ) = (Ddr ((GK K).subtype.comp e.toMonoidHom) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [DdR, Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply]
  rw [e.surjective.forall]
  simp only [actVdR_tr]

private theorem h0V_tr_eq_restrictScalars_h0 : H0V (tr e ρ) = (H0 ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [H0V, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, H0, Representation.mem_invariants]
  rw [e.surjective.forall]
  simp only [tr_apply]

variable (K E V) in
private theorem FilV_eq (a : ℤ) :
    FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a =
      (UpperTheory.V.Loc.FilT (l := l) E V a).restrictScalars ℚ_[l] := by
  have hF : (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] :=
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have h : ∀ (N : Submodule ℚ_[l] (Bdr l)) y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      N.subtype y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[E] V) N.subtype y := by
    intro N y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  rw [FilV, hF]
  simp only [UpperTheory.V.Loc.FilT, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
  [ContinuousConstSMul ℚ_[l] V]

private theorem mem_Z1f_transport_iff (he : Continuous e) (he' : Continuous e.symm) (c : ↥(GK K) → V) :
    c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ) ↔
      (c ∘ e) ∈ UpperTheory.V.Loc.finiteCocycles ((GK K).subtype.comp e.toMonoidHom) ρ := by
  show ((Continuous c ∧ ∀ g h, c (g * h) = c g + tr e ρ g (c h)) ∧
      ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) (tr e ρ) g x - x) ↔
    ((Continuous (c ∘ e) ∧ ∀ g h, c (e (g * h)) = c (e g) + ρ g (c (e h))) ∧
      ∃ x, ∀ g, c (e g) ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x - x)
  refine and_congr (and_congr ⟨fun h => h.comp he, fun h => ?_⟩ ?_) (exists_congr fun x => ?_)
  · simpa only [Function.comp_def, MulEquiv.apply_symm_apply] using h.comp he'
  · rw [e.surjective.forall₂]
    simp only [tr_apply, map_mul]
  · rw [e.surjective.forall]
    simp only [actVB_tr]

private def cocycleTransportToH1f (he : Continuous e) (he' : Continuous e.symm) :
    ↥(Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)) →ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) where
  toFun c := ⟨Submodule.Quotient.mk ⟨c.1 ∘ e, ((mem_Z1f_transport_iff e ρ he he' c.1).mp c.2).1⟩,
    ⟨_, (mem_Z1f_transport_iff e ρ he he' c.1).mp c.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cocycle_transport_H1f_surjective (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (cocycleTransportToH1f e ρ he he') := by
  rintro ⟨_, c, hc, rfl⟩
  have h : (c.1 ∘ e.symm) ∘ e = c.1 := by
    funext g
    simp
  refine ⟨⟨c.1 ∘ e.symm, (mem_Z1f_transport_iff e ρ he he' _).mpr (by rw [h]; exact hc)⟩, Subtype.ext ?_⟩
  exact congrArg Submodule.Quotient.mk (Subtype.ext h)

private theorem ker_cocycle_transport_H1f (he : Continuous e) (he' : Continuous e.symm) :
    LinearMap.ker (cocycleTransportToH1f e ρ he he') =
      (Formalism.WeaklyAdmissibleFiltrations.B1 (tr e ρ)).comap (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)).subtype := by
  ext c
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  refine (mem_coboundaries1 ρ (c.1 ∘ e)).trans ?_
  refine exists_congr fun m => ?_
  show (∀ g, c.1 (e g) = ρ g m - m) ↔ (fun g => tr e ρ g m - m) = c.1
  rw [funext_iff, e.surjective.forall]
  simp only [tr_apply]
  exact forall_congr' fun g => eq_comm

private def h1fEquiv (he : Continuous e) (he' : Continuous e.symm) :
    FiniteCohomology ((PP l).PD K) (tr e ρ) ≃ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
  (Submodule.quotEquivOfEq _ _ (ker_cocycle_transport_H1f e ρ he he').symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cocycle_transport_H1f_surjective e ρ he he'))

end UpperTheory.V.Loc.BlochKatoDimension

open UpperTheory.V.Loc.BlochKatoDimension in
theorem UpperTheory.V.Loc.bkDim :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → IsDr φ ρ → Module.Finite E ↥(finiteCohomology φ ρ) ∧
      finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(UpperTheory.V.Loc.FilD φ ρ 0) =
        finrank E ↥(H0 ρ) + φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hdR
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  rw [IsDr, hind, Ddr_res] at hdR
  rw [hind]
  clear hind hφ
  subst hφe
  have hD := (hP.bk l (PP l) (AIP l) T K).1
  have hcont : ∀ x, Continuous fun g => tr e ρ g x := fun x =>
    hc.comp (he'.prodMk continuous_const)
  have hdR' : IsDR ((PP l).PD K) (tr e ρ) := by
    rw [IsDR, DdR_tr]
    exact hdR
  obtain ⟨hfin, hdim⟩ := hD V (tr e ρ) hcont hdR'
  haveI : Module.Finite ℚ_[l] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
    Module.Finite.equiv (h1fEquiv e ρ he he')
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, ?_⟩
  have hH1 : finrank ℚ_[l] (FiniteCohomology ((PP l).PD K) (tr e ρ)) =
      finrank ℚ_[l] E * finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) := by
    rw [(h1fEquiv e ρ he he').finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (tr e ρ)) = finrank ℚ_[l] E * finrank E ↥(H0 ρ) := by
    rw [h0V_tr_eq_restrictScalars_h0, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR ((PP l).PD K) (tr e ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0) =
      finrank ℚ_[l] E * finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) := by
    rw [DdR_tr, FilV_eq K E V, ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [IsDR, ← finrank_mul_finrank ℚ_[l] E V] at hdR'
  rw [hH1, hH0, hdR', hF] at hdim
  have hd : (finrank ℚ_[l] E : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := E)).ne'
  push_cast at hdim
  have : ((finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) +
      finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) : ℕ) : ℤ) =
      ((finrank E ↥(H0 ρ) + finrank ℚ_[l] ↥K.1 * finrank E V : ℕ) : ℤ) := by
    push_cast
    refine mul_left_cancel₀ hd ?_
    linear_combination hdim
  exact_mod_cast this

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankPointDerivationsVanishingEqOfIsCompl
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

section SlopeTestRemainingChoices
open MvPowerSeries

private theorem low_mem {R σ : Type} [CommRing R] [Finite σ] (m : Ideal (MvPowerSeries σ R))
    (hF : ∀ s, (MvPowerSeries.X s : MvPowerSeries σ R) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : truncTotal n g = 0) : g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.fg_idealOfVars σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    rw [hg]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem mem_sq {E σ : Type} [Field E] [Finite σ] (g : MvPowerSeries σ E)
    (h0 : MvPowerSeries.constantCoeff g = 0) (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) g = 0) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  refine low_mem _ (fun s => (mem_max _).2 (by simp)) 2 g ?_
  ext d
  rw [coeff_truncTotal_eq_ite]
  split_ifs with hd
  · have : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases this with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simpa using h0
    · obtain ⟨i, rfl⟩ : ∃ i, Finsupp.single i 1 = d := by
        have : d ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
          rw [Finsupp.range_single_one]; exact h
        exact this
      simpa using h1 i
  · simp

private theorem of_mem_sq {E σ : Type} [Field E] (g : MvPowerSeries σ E)
    (h : g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) g = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_single_mul, (mem_max _).1 ha, (mem_max _).1 hb]; simp
  · rw [map_add (f := _), ha, hb, add_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (P : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → ∀ T : Submodule E (R →ₗ[O] E), (∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧ ∀ a ∈ P, δ a = 0) → Module.finrank E ↥T = n := by
  intro O R E _ _ _ _ _ _ _ n P x φ H T hT
  classical
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hne : ∀ c : O, c ≠ 0 → algebraMap O E c ≠ 0 := fun c hc h => hc (hinj (by simpa using h))
  let D : Fin n → (R →ₗ[O] E) := fun i =>
    ((MvPowerSeries.coeff (Finsupp.single i 1) : MvPowerSeries (Fin n) E →ₗ[E] E).restrictScalars O).comp
      φ.toLinearMap
  have hD : ∀ i a, D i a = MvPowerSeries.coeff (Finsupp.single i 1) (φ a) := fun i a => rfl
  have hDT : ∀ i, D i ∈ T := fun i => (hT _).2 ⟨fun a b => by
      rw [hD, hD, hD, map_mul, coeff_single_mul, H.const, H.const], fun a ha => by
      rw [← H.ker, RingHom.mem_ker] at ha
      rw [hD, ha, map_zero]⟩

  have hex : ∀ i : Fin n, ∃ (a : R) (c : O), c ≠ 0 ∧ ∀ j, D j a = if j = i then algebraMap O E c else 0 := by
    intro i
    obtain ⟨a, c, hc, h⟩ := H.dense 2 (MvPowerSeries.X i)
    refine ⟨a, c, hc, fun j => ?_⟩
    have := of_mem_sq _ h j
    rw [map_sub, sub_eq_zero, ← hD, ← algebraMap_smul E c, map_smul, MvPowerSeries.coeff_X] at this
    rw [← this]
    simp [Finsupp.single_left_inj]
  choose a c hc ha using hex
  have h1 : ∀ δ ∈ T, δ 1 = 0 := fun δ hδ => by
    have := ((hT δ).1 hδ).1 1 1
    simpa using this
  have hker : ∀ δ ∈ T, ∀ r, (∀ i, D i r = 0) → δ r = 0 := by
    intro δ hδ r hr
    have hsub : ∀ δ ∈ T, δ (r - x r • 1) = δ r := fun δ hδ => by
      rw [map_sub, map_smul, h1 δ hδ, smul_zero, sub_zero]
    have hm : φ (r - x r • 1) ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2 := by
      refine mem_sq _ ?_ fun i => ?_
      · rw [H.const]; simp
      · rw [← hD, hsub _ (hDT i), hr]
    obtain ⟨k, hk, hmem⟩ := H.inj 2 _ hm
    have hz : ∀ s ∈ RingHom.ker x ^ 2 ⊔ P, δ s = 0 := by
      intro s hs
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hs
      rw [map_add (f := _), ((hT δ).1 hδ).2 v hv, add_zero]
      rw [pow_two] at hu
      refine Submodule.mul_induction_on hu (fun p hp q hq => ?_) (fun p q hp hq => ?_)
      · rw [RingHom.mem_ker] at hp hq
        rw [((hT δ).1 hδ).1, hp, hq]; simp
      · rw [map_add (f := _), hp, hq, add_zero]
    have := hz _ hmem
    rw [map_smul, hsub δ hδ, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this).resolve_left (hne k hk)
  let ev : T →ₗ[E] (Fin n → E) := LinearMap.pi fun i => (LinearMap.applyₗ' E (a i)).comp T.subtype
  have hev : ∀ (δ : T) i, ev δ i = (δ : R →ₗ[O] E) (a i) := fun _ _ => rfl
  have hbij : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro δ hδ
      ext r
      obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
        (fun i => D i r / algebraMap O E (c i))
      choose! b hb using hk
      have hz := hker δ δ.2 ((k : O) • r - ∑ i, b i • a i) (fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, map_smul]
        simp only [map_smul, ha, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Algebra.smul_def, Algebra.smul_def, hb j (Finset.mem_univ _), Algebra.smul_def]
        have := hne _ (hc j)
        field_simp
        ring)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, map_smul] at hz
      simp only [map_smul, ← hev, hδ, Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero] at hz
      rw [Algebra.smul_def] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hne k (nonZeroDivisors.coe_ne_zero k))
    · intro v
      refine ⟨∑ j, (v j / algebraMap O E (c j)) • ⟨D j, hDT j⟩, ?_⟩
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
      simp only [hev, Submodule.coe_smul, LinearMap.smul_apply, ha, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [smul_eq_mul, div_mul_cancel₀ _ (hne _ (hc i))]
  rw [(LinearEquiv.ofBijective ev hbij).finrank_eq]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalClassFieldTheoryOfOpenEmbedding
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology

private theorem ag_lift {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup C]
    [TopologicalSpace C] [T2Space C] (q : G →* C) (hq : Continuous q) :
    ∃ F : TopologicalAbelianization G →* C, Continuous F ∧ ∀ g : G, F g = q g := by
  have hle : (commutator G).topologicalClosure ≤ q.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker q)
      (isClosed_singleton.preimage hq)
  refine ⟨QuotientGroup.lift _ q hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 hq

private theorem ag_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G', Continuous F ∧ ∀ g : G, F g = (f g : G') := by
  set M := (commutator G').topologicalClosure
  have hker : ((QuotientGroup.mk' M).comp f).ker = M.comap f := by
    ext x
    simp
  have hle : (commutator G).topologicalClosure ≤ M.comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [← hker]
      exact Abelianization.commutator_subset_ker _
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  refine ⟨QuotientGroup.map _ M f hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 (continuous_quotient_mk'.comp hf)

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem ag_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ε : G ≃* (Ω ≃ₐ[K] Ω))
    (hε : Continuous ε) (hε' : Continuous ε.symm) :
    ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative ProfiniteInteger),
      Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧
      (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
        ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧
      Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((ord (y : K) : ℤ) : ProfiniteInteger)) ∧
      ∀ g : G, D (QuotientGroup.mk' _ g) = unramifiedDegree K Ω (ε g) := by
  obtain ⟨F, hF, hFe⟩ := ag_map (ε : G →* (Ω ≃ₐ[K] Ω)) hε
  obtain ⟨F', hF', hF'e⟩ := ag_map (ε.symm : (Ω ≃ₐ[K] Ω) →* G) hε'
  have hFF' : ∀ b, F (F' b) = b := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF'e, hFe]
    simp
  have hF'F : ∀ a, F' (F a) = a := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hFe, hF'e]
    simp
  obtain ⟨U, hU, hUe⟩ := ag_lift (unramifiedDegree K Ω) continuous_unramifiedDegree
  set L := localReciprocityLimit K Ω
  have hLart : ∀ x, localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (L x) :=
    fun x => localArtinMap_apply x
  have hLc : Continuous L := by
    have h : (L : Kˣ → _) = (topologicalAbelianizationEquiv K Ω).symm ∘ localArtinMap K Ω := by
      funext x
      simp [hLart]
    rw [h]
    exact (topologicalAbelianizationEquiv K Ω).symm.continuous.comp continuous_localArtinMap
  have hLi : Function.Injective L := by
    intro x y hxy
    apply injective_localArtinMap (K := K) (Ω := Ω)
    rw [hLart, hLart, hxy]
  have hU' : ∀ x : Kˣ, U (L x) = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ProfiniteInteger) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (L x)
    rw [← hg, hUe]
    exact unramifiedDegree_of_mk_eq_localReciprocityLimit hg
  refine ⟨F'.comp L, U.comp F, hF'.comp hLc, ?_, ?_, ?_, hU.comp hF, ?_, ?_⟩
  · intro x y hxy
    apply hLi
    have := congrArg F hxy
    simpa [hFF'] using this
  · exact (Function.Surjective.denseRange (fun a => ⟨F a, hF'F a⟩)).comp
      (denseRange_localReciprocityLimit (K := K) (Ω := Ω)) hF'
  · intro H hHo hHf
    let H' : openFiniteIndex Kˣ := ⟨H, hHo, hHf⟩
    let ψ := ((artinCoord K Ω H').comp
      (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom).comp F
    have hψ : Continuous ψ :=
      (continuous_artinCoord H').comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF)
    haveI := openCompletion.discreteTopology_quotient H'
    refine ⟨ψ.ker, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Kˣ ⧸ (H : Subgroup Kˣ)))).preimage hψ
    · ext y
      simp only [Subgroup.mem_comap, MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, hFF']
      change artinCoord K Ω H' (topologicalAbelianizationEquiv K Ω (L y)) = 1 ↔ y ∈ H
      rw [← hLart, artinCoord_localArtinMap]
      exact QuotientGroup.eq_one_iff y
  · intro y
    simp [hFF', hU']
  · intro g
    simp [hFe, hUe]

open GroundTheory.LocalField ValuativeRel IsLocalRing in
private theorem ag_char (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Algebra ℚ_[l] k] [ValuativeExtension ℚ_[l] k] : CharP 𝓀[k] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hnu : ¬ IsUnit ((l : 𝒪[k])) := by
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (l : 𝒪[k]) = 1 := by
      rw [← hu]
      simp
    have h2 : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k)) = algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) h1
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left this
    have h3 : algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) ∈ (ValuativeRel.valuation k).integer := by
      rw [← h2]
      exact (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])).2
    rw [algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff] at h3
    rw [norm_inv, Padic.norm_p, inv_inv] at h3
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    linarith
  have hmem : (l : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := (mem_maximalIdeal _).2 hnu
  rw [← map_natCast (residue 𝒪[k]) l]
  exact (residue_eq_zero_iff _).2 hmem

theorem UpperTheory.local_class_field_theory_of_open_embedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), ∃ (K : Type) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K) (_ : IsNonarchimedeanLocalField K) (_ : Algebra ℚ_[l] K) (_ : ValuativeExtension ℚ_[l] K) (_ : FiniteDimensional ℚ_[l] K), φ.range.index = Module.finrank ℚ_[l] K ∧ ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative GroundTheory.LocalField.Abstract.ProfiniteInteger), Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧ (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex → ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧ Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((GroundTheory.LocalField.ord (y : K) : ℤ) : GroundTheory.LocalField.Abstract.ProfiniteInteger)) ∧ ∀ g : G, φ g ∈ Iq l ↔ D (QuotientGroup.mk' _ g) = 1 := by
  intro l _ G _ _ _ φ hφ
  obtain ⟨K, e, he, he', hcomp, -, hidx, -⟩ := openField φ hφ
  haveI hfin : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨vr, tp, hloc, hext⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1
  letI := vr
  letI := tp
  haveI := hloc
  haveI := hext
  haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1
  haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure K.1 (Om l) := inferInstance
  obtain ⟨hc1, hc2⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let ε : G ≃* Gal(Om l/K.1) := e.trans K.1.fixingSubgroupEquiv
  have hε : Continuous ε := hc1.comp he
  have hε' : Continuous ε.symm := he'.comp hc2
  obtain ⟨θ, D, h1, h2, h3, h4, h5, h6, hD⟩ := ag_field K.1 (Om l) ε hε hε'
  refine ⟨K.1, inferInstance, vr, tp, hloc, inferInstance, hext, hfin, hidx, θ, D,
    h1, h2, h3, h4, h5, h6, ?_⟩
  intro g
  have hεg : ∀ x, (ε g) x = φ g x := by
    intro x
    rw [← hcomp]
    rfl
  haveI := ag_char l K.1
  rw [hD g, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  simp only [Iq, MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff,
    GroundTheory.LocalField.mem_unramifiedRoots_iff, hεg]
  constructor
  · rintro h ξ ⟨m, hm, hξ⟩
    apply h
    refine ⟨m, ?_, ?_, hξ⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm
      · exact hpos
    · intro hdvd
      exact hm ((CharP.cast_eq_zero_iff _ l m).2 hdvd)
  · rintro h ξ ⟨m, -, hml, hξ⟩
    apply h
    exact ⟨m, fun h0 => hml ((CharP.cast_eq_zero_iff _ l m).1 h0), hξ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MuNone
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc Topology

private theorem mn_sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : TopologicalAbelianization G) (hh : h ≠ 1) :
    ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ h ∉ V := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hg : g ∉ (commutator G).topologicalClosure := fun hm => hh ((QuotientGroup.eq_one_iff g).2 hm)
  have hS : IsOpen {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage (continuous_mul_const g)
  have h1 : (1 : G) ∈ {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} := by
    show 1 * g ∉ ((commutator G).topologicalClosure : Set G)
    rw [one_mul]
    exact hg
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  refine ⟨(W : Subgroup G).map (QuotientGroup.mk' _), ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ W.isOpen
  · rintro ⟨w, hw, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    exact hW (inv_mem hw) he

private theorem mn_core {A M : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [CommGroup M] (r : M →* A) (hr : DenseRange r) {q : ℕ} (hq : q ≠ 0)
    (hM : ∀ x : M, x ^ q = 1 → x = 1)
    (hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set A, IsOpen V ∧ 1 ∈ V ∧ ∀ x, r x ∈ V → ∃ z, x = z ^ n)
    (a : A) (ha : a ^ q = 1) (n : ℕ) (hn : n ≠ 0) : ∃ z, a = z ^ n := by
  have hP : IsClosed (Set.range fun z : A => z ^ n) := (isCompact_range (continuous_pow n)).isClosed
  obtain ⟨V, hVo, hV1, hV⟩ := hopen (q * n) (mul_ne_zero hq hn)
  suffices hs : a ∈ closure (Set.range fun z : A => z ^ n) by
    rw [hP.closure_eq] at hs
    obtain ⟨z, hz⟩ := hs
    exact ⟨z, hz.symm⟩
  rw [mem_closure_iff]
  intro o ho hao
  have hW : IsOpen (o ∩ {y : A | y ^ q ∈ V}) := ho.inter (hVo.preimage (continuous_pow q))
  have haW : a ∈ o ∩ {y : A | y ^ q ∈ V} := ⟨hao, by show a ^ q ∈ V; rw [ha]; exact hV1⟩
  obtain ⟨x, hx1, hx2⟩ := hr.exists_mem_open hW ⟨a, haW⟩
  have hx3 : r (x ^ q) ∈ V := by
    rw [map_pow]
    exact hx2
  obtain ⟨z, hz⟩ := hV (x ^ q) hx3
  have hxz : x = z ^ n := by
    have h1 : (x * (z ^ n)⁻¹) ^ q = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, mul_comm n q, ← hz, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hM _ h1)
  exact ⟨r x, hx1, r z, by rw [hxz, map_pow]⟩

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem mn_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {q : ℕ} (hq : q ≠ 0) (hM : ∀ x : Kˣ, x ^ q = 1 → x = 1)
    (a : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) (ha : a ^ q = 1) : a = 1 := by
  haveI : IsClosed ((commutator (Ω ≃ₐ[K] Ω)).topologicalClosure : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set (TopologicalAbelianization (Ω ≃ₐ[K] Ω)), IsOpen V ∧ 1 ∈ V ∧
      ∀ x, localReciprocityLimit K Ω x ∈ V → ∃ z, x = z ^ n := by
    intro n hn
    haveI : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := finite_quotient_range_pow_of_charZero hn
    let H : openFiniteIndex Kˣ := ⟨(powMonoidHom n : Kˣ →* Kˣ).range,
      isOpen_range_pow (Nat.cast_ne_zero.mpr hn), Subgroup.finiteIndex_of_finite_quotient⟩
    haveI := openCompletion.discreteTopology_quotient H
    refine ⟨(fun b => artinCoord K Ω H (topologicalAbelianizationEquiv K Ω b)) ⁻¹' {1}, ?_, ?_, ?_⟩
    · exact (isOpen_discrete _).preimage
        ((continuous_artinCoord H).comp (topologicalAbelianizationEquiv K Ω).continuous)
    · show artinCoord K Ω H (topologicalAbelianizationEquiv K Ω 1) = 1
      rw [map_one, map_one]
    · intro x hx
      have hx' : artinCoord K Ω H (topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x)) = 1 := hx
      rw [← localArtinMap_apply, artinCoord_localArtinMap, QuotientGroup.eq_one_iff] at hx'
      obtain ⟨z, hz⟩ := hx'
      exact ⟨z, hz.symm⟩
  have hall : ∀ n : ℕ, n ≠ 0 → ∃ z, a = z ^ n := fun n hn =>
    mn_core (localReciprocityLimit K Ω) denseRange_localReciprocityLimit hq hM hopen a ha n hn
  by_contra hne
  obtain ⟨V, hVo, haV⟩ := mn_sep a hne
  haveI : Finite (TopologicalAbelianization (Ω ≃ₐ[K] Ω) ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨z, hz⟩ := hall V.index Subgroup.FiniteIndex.index_ne_zero
  exact haV (hz ▸ Subgroup.pow_index_mem V z)

private theorem mn_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) {g : G}
    (hg : g ∈ (commutator G).topologicalClosure) : f g ∈ (commutator H).topologicalClosure := by
  have hc : commutator G ≤ (commutator H).comap f := by
    rw [← Subgroup.map_le_iff_le_comap, commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hcl : (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f :=
    Subgroup.topologicalClosure_minimal _ (hc.trans (Subgroup.comap_mono (Subgroup.le_topologicalClosure _)))
      ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  exact hcl hg

private theorem mn_cyc {l : ℕ} [Fact l.Prime] (σ : GQ l) {ζ : Om l} (h1 : ζ ^ l = 1) (h2 : ζ ≠ 1)
    (h : σ ζ = ζ) : PadicInt.toZMod ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have hp : l.Prime := Fact.out
  have hprim : IsPrimitiveRoot ζ l := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  have hs := cyclotomicCharacter.spec (L := Om l) l (n := 1)
    (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ (by rw [pow_one]; exact h1)
  have hcyc : (cyc l l σ : ℤ_[l]ˣ) =
      cyclotomicCharacter (Om l) l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) := rfl
  rw [← hcyc] at hs
  set x : ℤ_[l] := ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) with hx
  have hσ : (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ = ζ := h
  have hs' : ζ ^ (PadicInt.toZModPow 1 x).val = ζ ^ 1 := by
    calc _ = _ := hs.symm
      _ = ζ := hσ
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hlt : (PadicInt.toZModPow 1 x).val < l :=
    lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow (p := l) 1 x)) (pow_one l)
  have hk : (PadicInt.toZModPow 1 x).val = 1 := hprim.pow_inj hlt hp.one_lt hs'
  have hk' : PadicInt.toZModPow 1 x = 1 := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x), hk, Nat.cast_one]
  have hmem : x - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, RingHom.map_sub, hk', map_one, sub_self]
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

theorem UpperTheory.V.Loc.muNone :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), (∃ g : G, PadicInt.toZMod ((cyc l l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∀ g : G, (QuotientGroup.mk' _ g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l → g ∈ (commutator G).topologicalClosure := by
  intro l _ G _ _ _ φ hφ hex g hg
  obtain ⟨g0, hg0⟩ := hex
  have hp : l.Prime := Fact.out
  obtain ⟨K, e, he1, he2, hφe, -⟩ := openField φ hφ
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  set L : IntermediateField ℚ_[l] (Om l) := K.1 with hL
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  haveI : IsAlgClosure L (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure L (Om l) := inferInstance
  obtain ⟨vr, ts, hloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] L
  let ψ : G →* Gal(Om l/L) := L.fixingSubgroupEquiv.toMonoidHom.comp e.toMonoidHom
  have hψ : Continuous ψ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).1.comp he1
  let ψi : Gal(Om l/L) →* G := e.symm.toMonoidHom.comp L.fixingSubgroupEquiv.symm.toMonoidHom
  have hψi : Continuous ψi := he2.comp (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).2
  have hψψ : ψi (ψ g) = g :=
    (congrArg e.symm (L.fixingSubgroupEquiv.symm_apply_apply (e g))).trans (e.symm_apply_apply g)
  obtain ⟨n, hn⟩ := hg
  have hgn : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply] at hn
    exact (QuotientGroup.eq_one_iff _).1 hn
  have hM : ∀ x : Lˣ, x ^ (l ^ n) = 1 → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
    set y := x ^ (l ^ (m - 1)) with hy
    have hy1 : y ^ l = 1 := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm, pow_orderOf_eq_one]
    have hy2 : y ≠ 1 := by
      intro h
      have h3 := orderOf_dvd_of_pow_eq_one h
      rw [hm, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h3
      omega
    have hz1 : (((y : L) : Om l)) ^ l = 1 := by
      have h4 := congrArg (fun u : Lˣ => ((u : L) : Om l)) hy1
      simpa using h4
    have hz2 : (((y : L) : Om l)) ≠ 1 := by
      intro h
      apply hy2
      apply Units.ext
      apply Subtype.ext
      simpa using h
    have hσ : φ g0 ∈ GK K := by
      rw [← hφe]
      exact (e g0).2
    have hfix : (φ g0) ((y : L) : Om l) = ((y : L) : Om l) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (y : L).2
    exact hg0 (mn_cyc (φ g0) hz1 hz2 hfix)
  have hψn : ψ g ^ (l ^ n) ∈ (commutator Gal(Om l/L)).topologicalClosure := by
    rw [← map_pow]
    exact mn_map ψ hψ hgn
  have ha : QuotientGroup.mk' (commutator Gal(Om l/L)).topologicalClosure (ψ g) = 1 := by
    refine mn_field L (Om l) (pow_ne_zero n hp.ne_zero) hM _ ?_
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hψn
  rw [← hψψ]
  exact mn_map ψi hψi ((QuotientGroup.eq_one_iff _).1 ha)
end
