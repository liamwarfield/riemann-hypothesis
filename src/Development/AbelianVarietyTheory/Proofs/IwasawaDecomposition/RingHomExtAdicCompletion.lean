module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible
public import Formalism.LocalToGlobal.Columns.QthPrincInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetAutSelfNaut
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr (D.nd.plOm.2 w) (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ k v :=
    let w := D.naut.plGw k v
    WD.tame_of_unr (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).1

end GlobalTheory.HeightCounting
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RowPar

section Sat
open Formalism.UG GlobalTheory.SatInd

theorem satAtS_indep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv Dv' : InertDatum L n v w) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv α) : NG.SatAtS S Dv' α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
  have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
    hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
    GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
      (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
        Dv.unram Dv'.unram hm)]

end Sat

section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

theorem ringHom_ext_adicCompletion {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {R : Type} [Ring R]
    [TopologicalSpace R] [T2Space R] (f g : v.adicCompletion K →+* R) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y : K, f (algebraMap K _ y) = g (algebraMap K _ y)) : f = g :=
  DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer hf hg (funext h))

theorem splitEmb_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (si si' : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (i i' : v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L) (hi : Continuous i) (hi' : Continuous i')
    (hix : ∀ x, i (si x) = algebraMap L _ x) (hix' : ∀ x, i' (si' x) = algebraMap L _ x) : si' = si ∧ i' = i := by
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i := by
    refine ringHom_ext_adicCompletion v _ _ hi' hi fun y => ?_
    have h1 := hix (algebraMap _ L y)
    have h2 := hix' (algebraMap _ L y)
    rw [AlgHom.commutes] at h1 h2
    exact h2.trans h1.symm
  have e' : i' = i := RingEquiv.ext fun x => congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  refine ⟨AlgHom.ext fun x => i.injective ?_, e'⟩
  rw [hix, ← hix' x, e']

theorem splitPlace_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (S S' : Submodule ℂ (GAf L n → W)) (s s' : SplitPlace L) (h : s'.w = s.w)
    (τ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (τ' : IrrRep (GL (Fin n) (s'.w.adicCompletion L)))
    (hτ : IsLocS S s τ) (hτ' : IsLocS S' s' τ') : s' = s := by
  obtain ⟨i, -, hi, hix, -⟩ := hτ
  obtain ⟨i', -, hi', hix', -⟩ := hτ'
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : s'.w = w)
      (j : s'.v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L), Continuous j →
      (∀ x, j (s'.i x) = algebraMap L _ x) → s' = s := by
    intro w hw j hj hjx
    rw [h] at hw
    subst hw
    obtain ⟨v, si⟩ := s
    obtain ⟨v', si'⟩ := s'
    dsimp only at hv
    subst hv
    obtain rfl := (splitEmb_eq _ _ si si' i j hi hj hix hjx).1
    rfl
  exact key _ rfl i' hi' hix'

theorem cl_eq_of_isLocS {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : NG.FinTyp L n) (s : SplitPlace L)
    (τ τ' : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hτ : IsLocS π.S s τ) (hτ' : IsLocS π.S s τ') : τ.cl = τ'.cl := by
  obtain ⟨i, T, hi, hix, hTi, hTS, hTe⟩ := hτ
  obtain ⟨i', T', hi', hix', hTi', hTS', hTe'⟩ := hτ'
  obtain rfl := (splitEmb_eq s.v s.w s.i s.i i' i hi' hi hix' hix).2
  obtain ⟨hdec, hcom, huniq⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose sec hsec using fun A => (huniq A).exists
  have sec_eq : ∀ x : GAf L n, TrivOutside {s.v} x → sec (s.loc n x) = x := fun x hx =>
    (huniq _).unique (hsec _) ⟨hx, rfl⟩
  have triv_mul : ∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    have h1 := hx v hv
    have h2 := hy v hv
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [Matrix.map_mul, h1, h2, one_mul]
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    simp [Matrix.map_one]
  let sH : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := sec
      map_one' := (huniq 1).unique (hsec 1) ⟨triv_one, map_one _⟩
      map_mul' := fun A B => (huniq (A * B)).unique (hsec (A * B))
        ⟨triv_mul _ _ (hsec A).1 (hsec B).1, by rw [map_mul, (hsec A).2, (hsec B).2]⟩ }
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt])
      map_mul' := fun g h => LinearMap.ext fun f => Subtype.ext (funext fun x => by simp [NG.rt, mul_assoc]) }
  have hρ : ρ.IsIrreducible := by
    refine (GlobalTheory.CuspRep.isIrreducible_iff ρ).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne, fun U hU => ?_⟩
    have hst : ∀ h, ∀ f ∈ U.map π.S.subtype, NG.rt L n h f ∈ U.map π.S.subtype := by
      rintro h _ ⟨u, hu, rfl⟩
      exact ⟨ρ h u, hU h u hu, rfl⟩
    rcases π.irr _ (Submodule.map_subtype_le _ _) hst with h0 | h1
    · left
      exact Submodule.map_injective_of_injective π.S.injective_subtype (h0.trans (Submodule.map_bot _).symm)
    · right
      refine Submodule.map_injective_of_injective π.S.injective_subtype ?_
      rw [h1, Submodule.map_subtype_top]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have he : Function.Surjective e := fun B =>
    ⟨Matrix.GeneralLinearGroup.map i.symm.toRingHom B, Units.ext (Matrix.ext fun a b => by simp [e])⟩
  have hnt : ∀ τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L)), Nontrivial τ₀.V := fun τ₀ =>
    ((GlobalTheory.CuspRep.isIrreducible_iff τ₀.ρ).1 τ₀.irr).1
  have key : ∀ (τ₀ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (T₀ : τ₀.V →ₗ[ℂ] (GAf L n → ℂ)),
      Function.Injective T₀ → (∀ a, T₀ a ∈ π.S) →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a,
        T₀ (τ₀.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T₀ a)) →
      ∃ f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH), f ≠ 0 := by
    intro τ₀ T₀ hT₀ hS₀ he₀
    refine ⟨⟨LinearMap.codRestrict π.S T₀ hS₀, fun A => LinearMap.ext fun a => Subtype.ext ?_⟩, fun h0 => ?_⟩
    · have h1 := he₀ (sec A) (hsec A).1 a
      rw [(hsec A).2] at h1
      exact h1
    · haveI := hnt τ₀
      obtain ⟨a, ha⟩ := exists_ne (0 : τ₀.V)
      refine ha (hT₀ ?_)
      have h2 := congrArg (fun f : Representation.IntertwiningMap (τ₀.ρ.comp e) (ρ.comp sH) => (f a : GAf L n → ℂ)) h0
      simpa using h2
  obtain ⟨f, hf⟩ := @key τ T hTi hTS hTe
  obtain ⟨f', hf'⟩ := key τ' T' hTi' hTS' hTe'
  have hcomm : ∀ g, ∃ u, ∀ y, Commute ((sH u)⁻¹ * g) (sH y) := by
    intro g
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec g
    refine ⟨s.loc n x, fun B => ?_⟩
    rw [show sH (s.loc n x) = x from sec_eq x hx, inv_mul_cancel_left]
    exact (hcom _ _ (hsec B).1 hy).symm
  obtain ⟨φ⟩ := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ ρ sH (τ.ρ.comp e) (τ'.ρ.comp e) hρ
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr e he) (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ'.irr e he)
    hcomm f hf).2 f' hf'
  refine IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk φ.toLinearEquiv fun B => ?_⟩
  obtain ⟨A, rfl⟩ := he B
  exact φ.isIntertwining' A

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

def LocAt (σ : D.what₂.FT) (w : PlE D.host) : Type 1 :=
  {p : (s : SplitPlace D.host.E) × IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) //
    p.1.w = w ∧ IsLocS (rep σ).S p.1 p.2}

def unrW : RowWD D := by
  let m : Multiset ℂ := Multiset.replicate D.R.r 1
  have hm : (0 : ℂ) ∉ m := fun h => zero_ne_one (Multiset.eq_of_mem_replicate h)
  exact
    { par := fun _ w => GlobalTheory.WeilDeligne.WD.lpUnr (D.nd.plOm.2 w) m
      sat := fun _ _ => m
      dim := fun _ w =>
        (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 w) m hm).2.2.trans
          (Multiset.card_replicate _ _)
      tame := fun _ k v =>
        GlobalTheory.WeilDeligne.WD.tame_of_unr
          (GlobalTheory.WeilDeligne.WD.lpUnr_spec (h := D.nd.plOm.2 (D.naut.plGw k v)) m hm).1 }

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

def satOf (S : Submodule ℂ (GAf L n → W)) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ := by
  classical
  exact if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α then Finset.univ.val.map h.choose_spec.choose_spec.choose else 0

theorem satAtS_transfer (S : Submodule ℂ (GAf L n → W)) {w : HeightOneSpectrum (𝓞 L)}
    (v0 v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv0 : InertDatum L n v0 w) (Dv : InertDatum L n v w)
    (hv : v0 = v) (α : Fin (n / 2) → ℂ) (hs : NG.SatAtS S Dv0 α) : NG.SatAtS S Dv α := by
  subst hv
  exact satAtS_indep S Dv0 Dv α hs

theorem satOf_spec (S : Submodule ℂ (GAf L n → W)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hO : NG.OverPl w v) (Dv : InertDatum L n v w) (hα : ∃ α, NG.SatAtS S Dv α) :
    ∃ α, NG.SatAtS S Dv α ∧ satOf S w = Finset.univ.val.map α := by
  classical
  obtain ⟨α, hα⟩ := hα
  have h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAtS S Dv α := ⟨v, Dv, α, hO, hα⟩
  have hsp := h.choose_spec.choose_spec.choose_spec
  refine ⟨h.choose_spec.choose_spec.choose, satAtS_transfer S _ v _ Dv
    (HeightOneSpectrum.ext (hsp.1.symm.trans hO)) _ hsp.2, ?_⟩
  unfold satOf
  rw [dite_eq_left h]

end GlobalTheory.RowPar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtBC

section DualBC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {G : Type} [Group G]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def dualBC : K' ⊗[K] Module.Dual K V ≃ₗ[K'] Module.Dual K' (K' ⊗[K] V) :=
  (TensorProduct.isBaseChange K V K').toDualBaseChange

theorem dualBC_tmul (a : K') (f : Module.Dual K V) (v : V) :
    dualBC (a ⊗ₜ[K] f) ((1 : K') ⊗ₜ[K] v) = a * algebraMap K K' (f v) :=
  (TensorProduct.isBaseChange K V K').toDualBaseChange_tmul a f v

theorem dualBC_natural (f : V →ₗ[K] V) (x : K' ⊗[K] Module.Dual K V) :
    dualBC (f.dualMap.baseChange K' x) = (f.baseChange K').dualMap (dualBC x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a g =>
    apply (TensorProduct.isBaseChange K V K').algHom_ext
    intro v
    simp only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.dualMap_apply, dualBC_tmul]

theorem isIrreducible_bcRep_dual (ρ : Representation K G V)
    (h : (bcRep (K' := K') ρ).dual.IsIrreducible) : (bcRep (K' := K') ρ.dual).IsIrreducible := by
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (dualBC (K' := K') (V := V)).symm ?_ h
  intro g x
  apply dualBC.injective
  rw [LinearEquiv.apply_symm_apply]
  show dualBC ((ρ g⁻¹).dualMap.baseChange K' _) = ((ρ g⁻¹).baseChange K').dualMap x
  rw [dualBC_natural, LinearEquiv.apply_symm_apply]

end DualBC

end GlobalTheory.AlgWtBC

noncomputable section

namespace GlobalTheory.AlgWtBC

open Formalism.L2.DIV

section CoefBC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {ι : Type} [Fintype ι] {n : ℕ}

theorem map_colAddGen {r m : ℕ} (l j : Fin m) (f : MvPolynomial (Fin r × Fin m) K) :
    MvPolynomial.map (algebraMap K K') (Formalism.GradedWeylDivisibility.colAddGen K l j f) =
      Formalism.GradedWeylDivisibility.colAddGen K' l j (MvPolynomial.map (algebraMap K K') f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem map_mem_dualWeyl {r m : ℕ} (ν : Fin m → ℕ) {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν) :
    MvPolynomial.map (algebraMap K K') f ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r m ν := by
  simp only [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨fun d hd => hf.1 (by
    intro h0
    apply hd
    rw [MvPolynomial.coeff_map, h0, map_zero]), fun l j hlj => ?_⟩
  rw [← map_colAddGen, hf.2 l j hlj, MvPolynomial.map_rename]

theorem map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    MvPolynomial.map (algebraMap K K') F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨G, hG, rfl⟩ := hP
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map (algebraMap K K') (G s), fun s => map_mem_dualWeyl _ (hG s), ?_⟩
    simp only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem detPow_map (g : GL (Fin n) K) (c : ℤ) :
    algebraMap K K' (detPow K n g c) = detPow K' n (Matrix.GeneralLinearGroup.map (algebraMap K K') g) c := by
  unfold detPow
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap K K') g) =
      Units.map (algebraMap K K' : K →* K') (Matrix.GeneralLinearGroup.det g) := by
    ext; simp [RingHom.map_det]
  rw [this, ← map_zpow (Units.map (algebraMap K K' : K →* K')) (Matrix.GeneralLinearGroup.det g) c, Units.coe_map]
  rfl

theorem map_trAct (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (algebraMap K K') (trAct g F) =
      trAct (fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (g τ)) (MvPolynomial.map (algebraMap K K') F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, map_sum]

theorem map_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (algebraMap K K') (actP lam g F) =
      actP lam (fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (g τ))
        (MvPolynomial.map (algebraMap K K') F) := by
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, map_trAct]
  congr 2
  simp only [detTwK, map_prod, detPow_map]

def bcPol (lam : ι → DomWeight n) : K' ⊗[K] VV K lam →ₗ[K'] Pol K' ι n :=
  (MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv.toLinearMap ∘ₗ (VV K lam).subtype.baseChange K'

theorem bcPol_tmul (lam : ι → DomWeight n) (a : K') (F : VV K lam) :
    bcPol lam (a ⊗ₜ[K] F) = a • MvPolynomial.map (algebraMap K K') (F : Pol K ι n) := by
  simp [bcPol]

theorem bcPol_injective (lam : ι → DomWeight n) : Function.Injective (bcPol (K := K) (K' := K') lam) := by
  refine (MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv.injective.comp ?_
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (VV K lam).injective_subtype

theorem bcPol_mem (lam : ι → DomWeight n) (x : K' ⊗[K] VV K lam) : bcPol lam x ∈ VV K' lam := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul a F => rw [bcPol_tmul]; exact (VV K' lam).smul_mem a (map_mem_VV lam F.2)

theorem finrank_bc_VV (lam : ι → DomWeight n) :
    Module.finrank K' (K' ⊗[K] VV K lam) = Module.finrank K' (VV K' lam) := by
  rw [Module.finrank_baseChange, Module.finrank_eq_card_basis (bVV K lam),
    Module.finrank_eq_card_basis (bVV K' lam)]

def bcVV (lam : ι → DomWeight n) : K' ⊗[K] VV K lam ≃ₗ[K'] VV K' lam :=
  LinearMap.linearEquivOfInjective (LinearMap.codRestrict (VV K' lam) (bcPol lam) (bcPol_mem lam))
    (by intro x y h; exact bcPol_injective lam (congrArg Subtype.val h)) (finrank_bc_VV lam)

theorem bcVV_val (lam : ι → DomWeight n) (x : K' ⊗[K] VV K lam) : (bcVV lam x : Pol K' ι n) = bcPol lam x := rfl

end CoefBC

section Weight

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
  {K K' : Type} [Field K] [Field K'] [Algebra K K']

theorem embGLF_comp (emb : ι → L →+* K) (γ : GL (Fin n) L) :
    GlobalTheory.AlgWtF.embGLF (fun τ => (algebraMap K K').comp (emb τ)) γ =
      fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (GlobalTheory.AlgWtF.embGLF emb γ τ) := by
  funext τ
  ext i j
  simp [GlobalTheory.AlgWtF.embGLF]

theorem isIrreducible_bcRep_tenRepF (emb : ι → L →+* K) (lam : ι → DomWeight n)
    (h : (GlobalTheory.AlgWtF.tenRepF (fun τ => (algebraMap K K').comp (emb τ)) lam).IsIrreducible) :
    (bcRep (K' := K') (GlobalTheory.AlgWtF.tenRepF emb lam)).IsIrreducible := by
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (bcVV (K := K) (K' := K') lam).symm ?_ h
  intro γ x
  apply (bcVV (K := K) (K' := K') lam).injective
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨y, rfl⟩ := (bcVV (K := K) (K' := K') lam).surjective x
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [bcVV_val]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Submodule.coe_add, hx, hy]
  | tmul a F =>
    show bcPol lam (a ⊗ₜ[K] (GlobalTheory.AlgWtF.tenRepF emb lam γ F)) =
      actP lam (GlobalTheory.AlgWtF.embGLF _ (GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ)) (bcVV lam (a ⊗ₜ[K] F) : Pol K' ι n)
    rw [bcVV_val, bcPol_tmul, bcPol_tmul, map_smul, embGLF_comp]
    congr 1
    exact map_actP lam _ _

end Weight

end GlobalTheory.AlgWtBC

noncomputable section

namespace GlobalTheory.AlgWtBC

theorem cmDist_comp {L : Type} [Field L] [NumberField L] [IsCMField L] {ι : Type} {K K' : Type} [Field K] [Field K']
    [Algebra K K'] (emb : ι → L →+* K) (h : GlobalTheory.AlgWtF.CMDist emb) :
    GlobalTheory.AlgWtF.CMDist (fun τ => (algebraMap K K').comp (emb τ)) := by
  refine ⟨fun τ τ' he => h.1 ?_, fun τ τ' he => h.2 τ τ' ?_⟩
  · ext x
    exact (algebraMap K K').injective (RingHom.congr_fun he x)
  · ext x
    exact (algebraMap K K').injective (RingHom.congr_fun he x)

theorem isIrreducible_bcRep_wtRepF : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (K' : Type) [Field K'] [Algebra K K'],
      (Formalism.IndefR.NX.bcRep (K' := K') (GlobalTheory.AlgWtF.wtRepF emb lam)).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM K' _ _
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  have h1 := GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible L n ι K' (fun τ => (algebraMap K K').comp (emb τ)) lam (cmDist_comp emb hCM)
  have h2 := isIrreducible_bcRep_tenRepF (K' := K') emb lam h1
  have h3 := GlobalTheory.T.contragredient_isIrreducible_finiteDimensional K' _ _ _ h2
  exact isIrreducible_bcRep_dual _ h3

end GlobalTheory.AlgWtBC
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (K' : Type) [Field K'] [Algebra K K'],
      (Formalism.IndefR.NX.bcRep (K' := K') (GlobalTheory.AlgWtF.wtRepF emb lam)).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | exact GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | (intros; apply GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliser
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section CutOpen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

omit [StarRing E] in
theorem intAt_iff_val_le_one {P : HeightOneSpectrum (𝓞 E)} {a : E} : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  intro h
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem mem_stdAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  rw [ciMem_stdAt]
  exact forall_congr' fun _ => intAt_iff_val_le_one

theorem lqPrinc_mono {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : lqPrinc P N' g) : lqPrinc P N g := by
  intro i j
  refine (hg i j).trans ?_
  change WithZero.exp (-(N' : ℤ)) ≤ WithZero.exp (-(N : ℤ))
  rw [WithZero.exp_le_exp]
  omega

theorem smul_sub_mem_of_princ {P : HeightOneSpectrum (𝓞 E)} {N a : ℕ} (g : ↥(GLint E n P))
    (hg : lqPrinc P (N + a) (g : Sp E n ≃ₗ[E] Sp E n)) {c : E} {z : Sp E n}
    (ha : ∀ j, P.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ)) {x : Sp E n}
    (hx : c⁻¹ • (x - z) ∈ stdAt E n P) : c⁻¹ • ((g : Sp E n ≃ₗ[E] Sp E n) x - z) ∈ stdAt E n P := by
  set f : Sp E n ≃ₗ[E] Sp E n := g.1 with hf
  have hgw : f (c⁻¹ • (x - z)) ∈ stdAt E n P := (g.2 _).2 hx
  have hsplit : c⁻¹ • (f x - z) = f (c⁻¹ • (x - z)) + c⁻¹ • (f z - z) := by
    rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
    abel
  rw [hsplit]
  refine (stdAt E n P).add_mem hgw ?_
  rw [mem_stdAt_iff_val]
  intro i
  have hfz : f z - z = (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) *ᵥ z := by
    rw [Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    rfl
  have e : (c⁻¹ • (f z - z)) i = ∑ j, (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j * (c⁻¹ * z j) := by
    rw [hfz, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc P.valuation E ((LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j) * P.valuation E (c⁻¹ * z j)
      ≤ WithZero.exp (-((N + a : ℕ) : ℤ)) * WithZero.exp (a : ℤ) := mul_le_mul' (hg i j) (ha j)
    _ = WithZero.exp (-(N : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem thetaOpen_cutQ {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ)
    (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) :
    ThetaOpen (cutQ Θ C) := by
  intro P
  obtain ⟨N, hN, hT⟩ := hΘ P
  have hstab : ∃ N' : ℕ, N ≤ N' ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N' (g : Sp E n ≃ₗ[E] Sp E n) →
      g ∈ frStab P.1 (C P) := by
    rcases hC P with h | ⟨z, c, _, h⟩
    · refine ⟨N, le_rfl, fun g _ => ?_⟩
      rw [mem_frStab, h]
      intro v
      simp
    · obtain ⟨a, ha⟩ := qth_bound P.1 (Matrix.of fun (_ j : Fin n) => c⁻¹ * z j)
      have ha' : ∀ j, P.1.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ) := fun j => by
        simpa using ha j j
      refine ⟨N + a, by omega, fun g hg => ?_⟩
      rw [mem_frStab, h]
      intro v
      show c⁻¹ • (g.1 v - z) ∈ stdAt E n P.1 ↔ c⁻¹ • (v - z) ∈ stdAt E n P.1
      constructor
      · intro hv
        have hi := smul_sub_mem_of_princ g⁻¹ (qth_princ_inv P.1 g hg) ha' hv
        have e : ((g⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) (g.1 v) = v := LinearEquiv.symm_apply_apply g.1 v
        rwa [e] at hi
      · exact smul_sub_mem_of_princ g hg ha'
  obtain ⟨N', hNN, hS⟩ := hstab
  refine ⟨N', by omega, fun g hg => ?_⟩
  obtain ⟨hH, hl⟩ := hT g (lqPrinc_mono hNN hg)
  exact ⟨⟨hH, hS g hg⟩, hl⟩

end CutOpen

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliserStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openLevel_cutByCosetStabiliser : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q), ThetaOpen Θ → ∀ (C : ∀ P : Q, Set (Sp E n)), (∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) → ThetaOpen (GlobalTheory.Mem.Col2.ChEx.cutQ Θ C) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | exact GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | (intros; apply GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ <;> assumption)
end
end
