module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarboux

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLaw

variable {D : D7}

theorem isRes_one_of_unrAt (χ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro ha
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (((k : D.host.E)) : PP.adicCompletion D.host.E) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
    exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 ha
  exact (h _ hv).symm

theorem natCast_mem_of_isConjPl {PP PP' : Pl D.host.E} (h : Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c, hc, hc'⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc']
    simp
  exact this ▸ hc

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_prime_mem_of_isTwistPlaces {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem_of_div {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem TameOn.mul {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c c' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P c') :
    TameOn (χ * χ') e P (fun PP => c PP * c' PP) := by
  intro x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, Circle.coe_mul, h x h1 hx h2 h3 u hu, h' x h1 hx h2 h3 u hu, ← Finset.prod_mul_distrib]
  simp

theorem TameOn.mul_inv_one {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P fun _ => 1) :
    TameOn (χ * χ'⁻¹) e P c := by
  intro x h1 hx h2 h3 u hu
  have h4 := h' x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, h x h1 hx h2 h3 u hu, h4]
  simp

theorem tameOn_step : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ ∀ (e : AE D) (P : Finset (Pl D.host.E)), (∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) → IsIdemSum e P → TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) ∧ TameOn (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) e P (resChr L t ((j : ℕ) + 1)) := by
  classical
  intro D T0 L μ0 hL t j

  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) (natCast_mem_of_isConjPl hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem_of_div hk)
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun e P hP he => ?_⟩
  have hM := L.C.isMu0 j
  have t1 : TameOn (L.mu0 ((j : ℕ) + 1)) e P (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.C.mu0 j) e P _ (hL.mu0 j) hM.tame he ?_ ?_
    · intro PP h1 h2
      refine hM.unr PP fun k hk => ?_
      rcases GlobalTheory.T.place_over_typePrime_divides_or_conjugate D L.C.P k PP hk with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inl ((hL.Pg PP).2 ⟨k, h⟩)))
      · exact h2 ⟨PP', (hP PP').2 (Or.inl ((hL.Pg PP').2 ⟨k, h⟩)), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact hL.chi j PP hg
      · simp only [if_neg hg]
        have hQ := ((hP PP).1 h).resolve_left hg
        exact isRes_one_of_unrAt _ _ (hM.unr PP fun k hk => (hoff k PP hk).1 hQ)
  have t2 : TameOn (L.xi t) e P (fun PP => if PP ∈ L.Pg then 1 else L.xiR t PP) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.xiH t) e P _ (hL.xi t) (hL.xi_tame t) he ?_ ?_
    · intro PP h1 h2
      by_contra hn
      rcases (hL.Q_ram t PP).1 hn with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inr h))
      · exact h2 ⟨PP', (hP PP').2 (Or.inr h), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        refine isRes_one_of_unrAt _ _ ?_
        by_contra hn
        rcases (hL.Q_ram t PP).1 hn with h | h
        · exact (hPg PP hg).1 h
        · exact (hPg PP hg).2 h
      · simp only [if_neg hg]
        exact hL.xiR t PP (((hP PP).1 h).resolve_left hg)
  have t3 : TameOn L.eta e P (fun _ => 1) :=
    GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ L.C.eta e P _ hL.eta (fun PP x hx _ => L.C.isEta.unr PP x hx) he
      (fun PP _ _ => L.C.isEta.unr PP) (fun PP _ => isRes_one_of_unrAt _ _ (L.C.isEta.unr PP))
  have t4 : TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) := by
    have h := t1.mul t2
    have hc : (fun PP => (if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) *
        (if PP ∈ L.Pg then 1 else L.xiR t PP)) = resChr L t ((j : ℕ) + 1) := by
      funext PP
      unfold resChr
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg, mul_one]
      · simp only [if_neg hg, one_mul]
    rw [hc] at h
    exact h
  exact ⟨t4, t4.mul_inv_one t3⟩

end GlobalTheory.StepLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidueStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepSplittingCharacters_tame_levelResidue : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ ∀ (e : AE D) (P : Finset (Pl D.host.E)), (∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) → IsIdemSum e P → TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) ∧ TameOn (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) e P (resChr L t ((j : ℕ) + 1)) := by
  first | exact @GlobalTheory.StepLaw.tameOn_step | exact GlobalTheory.StepLaw.tameOn_step | (intros; apply GlobalTheory.StepLaw.tameOn_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetKerEqBot
namespace GlobalTheory.FinsetKernelTrivial

open scoped BigOperators

noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))

lemma restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl

lemma exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by
  classical
  have hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf : ((w : V) : X → ℂ) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext y
      have := congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩
      simpa [restr_apply] using this
    · intro heq
      have : w ∈ LinearMap.ker (restr V W (insert x P)) := heq ▸ hwK
      rw [LinearMap.mem_ker] at this
      have := congrFun this ⟨x, Finset.mem_insert_self x P⟩
      exact hx (by simpa [restr_apply] using this)
  have hlt := Submodule.finrank_lt_finrank_of_lt hle
  have hmin := Nat.find_min hex (hP ▸ hlt)
  exact hmin ⟨insert x P, rfl⟩

theorem main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by
  intro X V W _
  classical
  obtain ⟨P, hP⟩ := exists_finset_ker_eq_bot V W
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (restr V W P) hP
  refine ⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩
  intro w hw
  have h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩) := by
    have := congrArg (fun g => g ⟨w, hw⟩) hL
    simpa using this.symm
  have h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ)) := by
    funext y
    simp [restr_apply, Finset.sum_apply, Pi.single_apply]
  have h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V) := by
    have := congrArg (fun u : W => (u : V)) h1
    simp only at this
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [this, h2, map_sum]
    simp [map_smul]
  conv_lhs => rw [h3]
  rw [← Finset.sum_attach P]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [x.2]

end GlobalTheory.FinsetKernelTrivial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory

theorem funSub_evalExpand_exists {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] :
    ∃ (P : Finset X) (e : X → V), ∀ w ∈ W, w = ∑ x ∈ P, (w : X → ℂ) x • e x := by
  first
  | exact @_root_.GlobalTheory.FinsetKernelTrivial.main
  | exact _root_.GlobalTheory.FinsetKernelTrivial.main
  | (apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetKernelTrivial.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetKernelTrivial.main ..)

theorem funSub_multilinear_expand {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {N : Type} [AddCommMonoid N] [Module ℂ N]
    (Φ : MultilinearMap (RingHom.id ℂ) (fun i => V i) N) (P : ∀ i, Finset (X i))
    (e : ∀ i, X i → V i)
    (h : ∀ i, V i) (hh : ∀ i, h i = ∑ x ∈ P i, (h i : X i → ℂ) x • e i x) :
    Φ h = ∑ x ∈ Fintype.piFinset P, (∏ i, (h i : X i → ℂ) (x i)) • Φ (fun i => e i (x i)) := by
  conv_lhs => rw [show h = fun i => ∑ x ∈ P i, (h i : X i → ℂ) x • e i x from funext hh]
  rw [Φ.map_sum_finset]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Φ.map_smul_univ, RingHom.id_apply]

end GlobalTheory

namespace GlobalTheory

theorem funProd_multilinear_sum_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap (RingHom.id ℂ) (fun i => V i)
      (MultilinearMap (RingHom.id ℂ) (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  intro ι κ Δ _ _ _ _ X Y V V' M τ f f' g g' hfg
  classical
  let Wf : ∀ i, Submodule ℂ (V i) := fun i =>
    Submodule.span ℂ ((τ.support.image (fun d => f d i) ∪ τ.support.image (fun d => f' d i) :
      Finset (V i)) : Set (V i))
  let Wg : ∀ j, Submodule ℂ (V' j) := fun j =>
    Submodule.span ℂ ((τ.support.image (fun d => g d j) ∪ τ.support.image (fun d => g' d j) :
      Finset (V' j)) : Set (V' j))
  choose P e hP using fun i => funSub_evalExpand_exists (V i) (Wf i)
  choose Q e' hQ using fun j => funSub_evalExpand_exists (V' j) (Wg j)
  have key : ∀ (F : Δ → ∀ i, V i) (G : Δ → ∀ j, V' j),
      (∀ d ∈ τ.support, ∀ i, F d i ∈ Wf i) → (∀ d ∈ τ.support, ∀ j, G d j ∈ Wg j) →
      (τ.sum fun d a => a * M (F d) (G d)) =
        ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
          M (fun i => e i (x i)) (fun j => e' j (y j)) *
            τ.sum fun d a => a * (∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j) := by
    intro F G hF hG
    have hM : ∀ d ∈ τ.support, M (F d) (G d) = ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
        M (fun i => e i (x i)) (fun j => e' j (y j)) *
          ((∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j)) := by
      intro d hd
      rw [funSub_multilinear_expand M P e (F d) (fun i => hP i _ (hF d hd i))]
      rw [sum_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [smul_apply,
        funSub_multilinear_expand (M fun i => e i (x i)) Q e' (G d) (fun j => hQ j _ (hG d hd j)),
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [smul_eq_mul]; ring
    rw [Finsupp.sum]
    refine (Finset.sum_congr rfl (fun d hd => congrArg (τ d * ·) (hM d hd))).trans ?_
    simp_rw [Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  have memf : ∀ d ∈ τ.support, ∀ i, f d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memf' : ∀ d ∈ τ.support, ∀ i, f' d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  have memg : ∀ d ∈ τ.support, ∀ j, g d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memg' : ∀ d ∈ τ.support, ∀ j, g' d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  rw [key f g memf memg, key f' g' memf' memg']
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [hfg x y]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap (RingHom.id ℂ) (fun i => V i)
      (MultilinearMap (RingHom.id ℂ) (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  exact @GlobalTheory.funProd_multilinear_sum_eq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorBlindToArchimedeanFibStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorIndependentOfArchimedeanFiber
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinFibre

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def fin (x : κ → AF F) : κ → Af F := fun i => (x i).2

def mkv (a : κ → Ainf F) (w : κ → Af F) : κ → AF F := fun i => (a i, w i)

def chi (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (w : κ → Af F) : ℂ := GlobalTheory.HeisSchA.finChar ψ (w ⬝ᵥ q)


variable (κ) in
def alg (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → Af F) → ℂ) := Submodule.span ℂ (Set.range (chi (κ := κ) ψ))

theorem chi_zero (ψ : AddChar (AF F) ℂ) : chi (κ := κ) ψ 0 = 1 := by
  funext w; simp [chi]

theorem chi_add (ψ : AddChar (AF F) ℂ) (q q' : κ → Af F) : chi (κ := κ) ψ (q + q') = chi ψ q * chi ψ q' := by
  funext w; simp [chi, dotProduct_add, AddChar.map_add_eq_mul]

theorem one_mem (ψ : AddChar (AF F) ℂ) : (1 : (κ → Af F) → ℂ) ∈ alg κ ψ :=
  chi_zero (κ := κ) ψ ▸ Submodule.subset_span ⟨0, rfl⟩

theorem mul_mem (ψ : AddChar (AF F) ℂ) {C D : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) (hD : D ∈ alg κ ψ) :
    C * D ∈ alg κ ψ := by
  have h := Submodule.mul_mem_mul hC hD
  rw [alg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨q, rfl⟩, _, ⟨q', rfl⟩, rfl⟩
  exact ⟨q + q', chi_add ψ q q'⟩

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {a : Af F}
    (ha : a ≠ 0) : ∃ b : Af F, GlobalTheory.HeisSchA.finChar ψ (a * b) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hψ v
  refine ⟨singleFin v (t / evalV F v a), ?_⟩
  have e : a * singleFin v (t / evalV F v a) = singleFin v t := by
    apply af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self]
      field_simp
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  rw [e]
  exact ht

theorem exists_chi_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {d : κ → Af F}
    (hd : d ≠ 0) : ∃ q : κ → Af F, chi ψ q d ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  obtain ⟨b, hb⟩ := exists_ne_one ψ hψ hi
  exact ⟨Pi.single i b, by rw [chi, dotProduct_single]; exact hb⟩

theorem chi_mul_eq_schr (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (Φ : (κ → AF F) → ℂ) :
    (fun x => chi ψ q (fin x) * Φ x) =
      schr ψ ((GlobalTheory.HeisSchA.mk 0 1 : AF F) • (0 : κ → AF F),
        (GlobalTheory.HeisSchA.mk 0 1 : AF F) • fun i => GlobalTheory.HeisSchA.mk 0 (q i)) Φ := by
  funext x
  simp only [schr, smul_zero, zero_dotProduct, mul_zero, add_zero]
  congr 1
  rw [chi, GlobalTheory.HeisSchA.finChar_apply]
  congr 1
  symm
  refine Prod.ext ?_ ?_
  · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ _) = 0
    rw [RingHom.map_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    change GlobalTheory.HeisSchA.p1 (x i) * (0 * 0) = 0
    simp
  · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ _) = _
    rw [RingHom.map_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i).2 * (1 * q i) = (x i).2 * q i
    rw [one_mul]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem comm_alg (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    {C : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    T (fun x => C (fin x) * Φ x) = fun x => C (fin x) * T Φ x := by
  induction hC using Submodule.span_induction with
  | mem C h =>
    obtain ⟨q, rfl⟩ := h
    have h0 : evI F (GlobalTheory.HeisSchA.mk 0 1 : AF F) = 0 := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    rw [chi_mul_eq_schr, chi_mul_eq_schr]
    exact hT _ h0 _ _ Φ hΦ
  | zero =>
    have e : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * T Φ x) = 0 := by funext x; simp
    have e' : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * Φ x) = 0 := by funext x; simp
    rw [e, e', map_zero]
  | add C D _ _ hC hD =>
    have e : (fun x : κ → AF F => (C + D) (fin x) * Φ x) =
        (fun x => C (fin x) * Φ x) + fun x => D (fin x) * Φ x := by funext x; simp [add_mul]
    rw [e, map_add (f := _), hC, hD]
    funext x; simp [add_mul]
  | smul a C _ hC =>
    have e : (fun x : κ → AF F => (a • C) (fin x) * Φ x) = a • fun x => C (fin x) * Φ x := by
      funext x; simp [mul_assoc]
    rw [e, map_smul, hC]
    funext x; simp [mul_assoc]

theorem exists_sep (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (hψ : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) (y₀ : κ → Af F) {S : Set (κ → Af F)} (hS : IsCompact S)
    (hy : y₀ ∉ S) : ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ S, C w = 0 := by
  have hlc := GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hc
  refine hS.induction_on (p := fun t => ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ t, C w = 0) ?_ ?_ ?_ ?_
  · exact ⟨1, one_mem ψ, rfl, fun _ h => h.elim⟩
  · rintro s t hst ⟨C, hC, h1, h0⟩
    exact ⟨C, hC, h1, fun w hw => h0 w (hst hw)⟩
  · rintro s t ⟨C, hC, h1, h0⟩ ⟨D, hD, h1', h0'⟩
    refine ⟨C * D, mul_mem ψ hC hD, by simp [h1, h1'], ?_⟩
    rintro w (hw | hw)
    · simp [h0 w hw]
    · simp [h0' w hw]
  · intro w hw
    have hne : w - y₀ ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ hw)
    obtain ⟨q, hq⟩ := exists_chi_ne_one ψ hψ hne
    set ζ := chi ψ q (w - y₀)
    have hζ : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    let C : (κ → Af F) → ℂ := (1 - ζ)⁻¹ • (GlobalTheory.HeisSchA.finChar ψ (-(y₀ ⬝ᵥ q)) • chi ψ q - ζ • chi ψ 0)
    have hCv : ∀ w', C w' = (1 - ζ)⁻¹ * (chi ψ q (w' - y₀) - ζ) := by
      intro w'
      simp only [C, chi_zero, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
      congr 2
      rw [chi, chi, sub_dotProduct, sub_eq_neg_add, AddChar.map_add_eq_mul]
    have hCm : C ∈ alg κ ψ := Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)))
    have hcont : Continuous fun w' : κ → Af F => (w' - y₀) ⬝ᵥ q :=
      (continuous_id.sub continuous_const).dotProduct continuous_const
    have hev := (IsLocallyConstant.iff_eventually_eq _).mp (hlc.comp_continuous hcont) w
    refine ⟨{w' | chi ψ q (w' - y₀) = ζ}, mem_nhdsWithin_of_mem_nhds hev, C, hCm, ?_, ?_⟩
    · rw [hCv, sub_self]
      have h1 : chi ψ q 0 = 1 := by simp [chi]
      rw [h1]
      exact inv_mul_cancel₀ hζ
    · intro w' hw'
      rw [hCv, show chi ψ q (w' - y₀) = ζ from hw', sub_self, mul_zero]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_struct {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x, fin x ∉ K → Φ x = 0) ∧
      ∀ w₀ : κ → Af F, ∀ᶠ w in nhds w₀, ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a w₀) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨⟨tsupport g, hg.2, fun x hx => ?_⟩, fun w₀ => ?_⟩
    · change _ * g (fin x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp hg.1 w₀] with w hw a
      change _ * g w = _ * g w₀
      rw [hw]
      rfl
  | zero => exact ⟨⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => Filter.Eventually.of_forall fun _ _ => rfl⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    obtain ⟨⟨K', hK', h0'⟩, h1'⟩ := hΨ
    refine ⟨⟨K ∪ K', hK.union hK', fun x hx => ?_⟩, fun w₀ => ?_⟩
    · simp only [Set.mem_union, not_or] at hx
      simp [h0 x hx.1, h0' x hx.2]
    · filter_upwards [h1 w₀, h1' w₀] with w hw hw' a
      simp [hw a, hw' a]
  | smul c Φ _ hΦ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    refine ⟨⟨K, hK, fun x hx => by simp [h0 x hx]⟩, fun w₀ => ?_⟩
    filter_upwards [h1 w₀] with w hw a
    simp [hw a]

theorem main (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ)
    (hnd : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1)
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨⟨K, hK, h0⟩, h1⟩ := schA_struct hΦ
  set U := {w : κ → Af F | ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a (fin y))}
  have hU : U ∈ nhds (fin y) := h1 (fin y)
  obtain ⟨C, hC, hC1, hC0⟩ := exists_sep ψ hψ.1 hnd (fin y) (hK.diff isOpen_interior)
    (fun h => h.2 (mem_interior_iff_mem_nhds.mpr hU))
  have hzero : (fun x => C (fin x) * Φ x) = 0 := by
    funext x
    by_cases hxK : fin x ∈ K
    · by_cases hxU : fin x ∈ interior U
      · have hx := interior_subset hxU (fun i => (x i).1)
        have e1 : mkv (fun i => (x i).1) (fin x) = x := rfl
        rw [e1] at hx
        have e2 : mkv (fun i => (x i).1) (fin y) = y + fun i => GlobalTheory.HeisSchA.mk ((x i).1 - (y i).1) 0 := by
          funext i
          refine Prod.ext ?_ ?_
          · change (x i).1 = (y i).1 + ((x i).1 - (y i).1)
            abel
          · change (y i).2 = (y i).2 + 0
            rw [add_zero]
        rw [hx, e2, hy _ (fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu)]
        simp
      · simp [hC0 _ ⟨hxK, hxU⟩]
    · simp [h0 x hxK]
  have h := congrFun (comm_alg ψ T hT hC hΦ) y
  rw [hzero, map_zero, hC1, one_mul] at h
  exact h.symm

end GlobalTheory.FinFibre


open GlobalTheory.FinFibre in
theorem GlobalTheory.FinFibre.fibre_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 :=
  fun ψ T hψ _ hT Φ hΦ y hy => main ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hT Φ hΦ y hy
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FinFibre.fibre_zero | exact GlobalTheory.FinFibre.fibre_zero | (intros; apply GlobalTheory.FinFibre.fibre_zero <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitLatSelfDual

theorem latAtV_selfDual_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _ _ z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.SplitLatSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDualStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  first | exact @GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split | exact GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split | (intros; apply GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowTheta

theorem isThetaFunO_cosVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.cosVec i κ) := by
  obtain ⟨e, -, h⟩ := W.cosVec_is
  exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) (W.vac_is i hi).2.2

theorem isThetaFunO_datum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (isThetaFunO_cosVec W i i.2 (Φ i)) (ρ i)

end GlobalTheory.RowTheta

theorem GlobalTheory.RowTheta.rowDatum_isThetaFunO : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ Φ i =>
    GlobalTheory.RowTheta.isThetaFunO_datum ch.W ch.ρ Φ i⟩⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowSchwartzDataIsThetaFunctionLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) := by
  first | exact @GlobalTheory.RowTheta.rowDatum_isThetaFunO | exact GlobalTheory.RowTheta.rowDatum_isThetaFunO | (intros; apply GlobalTheory.RowTheta.rowDatum_isThetaFunO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompMulFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.KerTrans

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_fin (p : Pair T) (k : FinPt G p.small) :
    (G.toPair p k.1 1).1 ∈ GfC (G.pS p) ∧ (G.toPair p k.1 1).2 ∈ GfC (G.pT p) := by
  cases p <;> simp [GridData.toPair]

theorem ker_mul_fin (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h : GA D (G.V p.big)) : W.ker p F (g * k) h = W.ker p (W.om p (G.toPair p k 1) F) g h := by
  have e : G.toPair p (g * k) h = G.toPair p g h * G.toPair p k 1 := by
    rw [← GlobalTheory.RowClaim.toPair_mul, mul_one]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G)
    {p : Pair T}, p.InRange D.R.m → ∀ (f : WO (G.pS p) (G.pT p) → ℂ), IsThetaFunO W.ψ (G.pS p) (G.pT p) f →
    ∀ (g k : FinPt G p.small) (h : FinPt G p.big),
      fockComp W B p f (g * k) h = fockComp W B p (W.om p (G.toPair p k.1 1) f) g h := by
  intro D T L sc G W B p hp f hf g k h
  have hk := toPair_fin p k
  unfold fockComp
  congr 1
  funext m
  unfold jetTab kerFin
  rw [Subgroup.coe_mul, ker_mul_fin]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) (W.om_is p hp) W.θ W.θ_is _ hk.1 _ hk.2 _ _ _ _ f _ hf

end GlobalTheory.KerTrans

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.EvenOnto

theorem upPair_itW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D)
    (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) →
    (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω →
      GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧
    ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω →
      GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  intro hDS hHC D t V W S S' M M' aS aT θ ψ hθ hP
  obtain ⟨X, hX, h1, h2, -⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 hB M M' τ hd e1 e2
  choose hr A hA using key
  refine ⟨?_, ?_⟩
  · obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.ContrObj.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectors_overVacuum_isometry D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
      fun τ => (hv τ).2.2
  · have hA' : ∀ τ, ∃ A', LocIt M' M τ (aT τ) (aS τ) A' := fun τ =>
      GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D V W _ _ M M' τ _ _ (A τ) (hA τ)
    choose A' hA' using hA'
    obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D W V _ _ M' M aT aS A' GlobalTheory.ContrObj.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA'
    refine ⟨It, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
    have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D W V _ _ M' M θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
    exact isItW_of_globIt hθ hI (fun τ => ⟨(hr τ).2, (hr τ).1⟩)
      (GlobalTheory.T.fockVectors_overVacuum_isometry D W V _ _ M' M ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1) fun τ => (hv τ).2.2

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiners_upwardThetaPair : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) → (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧ ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω → GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  first | exact @GlobalTheory.EvenOnto.upPair_itW | exact GlobalTheory.EvenOnto.upPair_itW | (intros; apply GlobalTheory.EvenOnto.upPair_itW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open Classical in
theorem exists_good_model : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  intro D Bs hB n d V Ws r s r' s' hV hW μ dom hμ hdom
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig Bs V Ws r s r' s' hB hV hW
  let M0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws := ⟨co, fun _ => 0, μ, dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin n × Fin d → Fv D.host.F v) → ℂ := fun v =>
    Set.indicator {x : Fin n × Fin d → Fv D.host.F v | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  refine ⟨⟨co, fun v => if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose, μ, dom⟩, rfl, rfl, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hμ, hdom⟩
  · change M0.IsVac Bs.ψ v (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose)
    split_ifs with h
    · exact h
    · exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    change (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose) = ind v
    exact if_pos hv

end GlobalTheory.SquareAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_rational_schroedingerModel : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  first | exact @GlobalTheory.SquareAgree.exists_good_model | exact GlobalTheory.SquareAgree.exists_good_model | (intros; apply GlobalTheory.SquareAgree.exists_good_model <;> assumption)
end
end
