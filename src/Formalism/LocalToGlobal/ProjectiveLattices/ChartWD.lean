module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
noncomputable section

namespace Formalism.L2.Pj

section Charts

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev locM (K : Type) [Field K] {S : Type} [CommRing S] [Algebra K S] (m : Ideal S) [m.IsPrime] :
    S →ₐ[K] Localization.AtPrime m :=
  IsScalarTower.toAlgHom K S (Localization.AtPrime m)

def FrChartAt {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] (A : TRing K)
    (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (a : A.R →ₐ[K] p'.R) (μ : p'.R →ₐ[K] Localization.AtPrime m)
      (y' : pts p'.R), mapR lam y y' ∧ mapR a u y' ∧ μ.comp lam = (locM K m).comp φ ∧ μ.comp a = c

def FrChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m), FrChartAt pts mapR w m A u c

def BorChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
    ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m) (B : TRing K) (uB uB' : pts B.R)
        (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R) (cB : B.R →ₐ[K] Localization.AtPrime m),
        FrChartAt pts mapR w m A u c ∧ FrChartAt pts mapR w' m A u c' ∧ mapR π u uB ∧ mapR π' u uB' ∧
          borR tB uB uB' ∧ cB.comp π = c ∧ cB.comp π' = c' ∧ ∀ i, cB (tB i : B.R) = locM K m (t i : S)

variable {pts mapR borR}

theorem chartAt_val {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by
  obtain ⟨p', lam, a, μ, y', h1, h2, h3, h4⟩ := hc p φ y hy
  have e1 : f p' y' = lam (f p y) := hf p p' lam y y' h1
  have e2 : f p' y' = a (f A u) := hf A p' a u y' h2
  calc locM K m (φ (f p y)) = ((locM K m).comp φ) (f p y) := rfl
    _ = (μ.comp lam) (f p y) := by rw [h3]
    _ = μ (f p' y') := by rw [e1]; rfl
    _ = (μ.comp a) (f A u) := by rw [e2]; rfl
    _ = c (f A u) := by rw [h4]

theorem eq_of_locM {S : Type} [CommRing S] [Algebra K S] {x y : S}
    (h : ∀ (m : Ideal S) (_ : m.IsMaximal), locM K m x = locM K m y) : x = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro J hJ
  haveI := hJ
  have hxy := h J hJ
  simp only [locM, IsScalarTower.coe_toAlgHom'] at hxy
  rw [map_sub, hxy, sub_self]

theorem evalWD_of_frChart (h : FrChart pts mapR) : EvalWD pts mapR := by
  intro f hf S _ _ p q φ ψ y z w hy hz
  apply eq_of_locM (K := K)
  intro m hm
  haveI := hm
  obtain ⟨A, u, c, hc⟩ := h S w m
  rw [chartAt_val hf hc hy, chartAt_val hf hc hz]

private theorem evalAt_spec_lemma {f : Rules pts} {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y0 : pts p.R),
      mapR φ y0 y ∧ evalAt pts mapR f y = φ (f p y0) := by
  refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
    hy.choose_spec.choose_spec.choose_spec, ?_⟩
  rw [evalAt, dite_eq_left hy]

theorem wtAll_of_borChart [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by
  obtain ⟨p, φ, y0, hm, hv⟩ := evalAt_spec_lemma (f := f) hy
  obtain ⟨p', φ', y0', hm', hv'⟩ := evalAt_spec_lemma (f := f) hy'
  rw [hv, hv']
  apply eq_of_locM (K := K)
  intro m hmax
  haveI := hmax
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hm', chartAt_val hf hc hm]
  calc c' (f A u) = (cB.comp π') (f A u) := by rw [e2]
    _ = cB (f B uB') := by rw [AlgHom.comp_apply, hf A B π' u uB' hπ']
    _ = cB (wchar e tB) * cB (f B uB) := by rw [hw B tB uB uB' hbB, map_mul]
    _ = locM K m (wchar e t) * c (f A u) := by
      have k1 : cB (f B uB) = c (f A u) := by rw [← e1, AlgHom.comp_apply, hf A B π u uB hπ]
      rw [k1]
      simp [wchar, map_prod, map_pow, e3, Units.coe_prod]

end Charts

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

section Alg

variable {K : Type} [Field K]

theorem eq_zero_of_pts {M : Type} [Field M] [IsAlgClosed M] [Algebra K M] (p : TRing K) (a : p.R)
    (h : ∀ ψ : p.R →ₐ[K] M, ψ a = 0) : a = 0 := by
  classical
  have hRdef : p.R = (MvPolynomial (Fin p.n) K ⧸ p.I) := rfl
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstanceAs (IsJacobsonRing (MvPolynomial (Fin p.n) K ⧸ p.I))
  haveI hFT : Algebra.FiniteType K p.R :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p.I) (Ideal.Quotient.mkₐ_surjective K p.I)
  have hrad : (⊥ : Ideal p.R).IsRadical := fun x ⟨k, hk⟩ =>
    (Submodule.mem_bot _).2 (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
  have hjac : (⊥ : Ideal p.R).jacobson = ⊥ := by
    first
    | exact IsJacobsonRing.out inferInstance hrad
    | exact IsJacobsonRing.out' ⊥ hrad
  have ha : a ∈ (⊥ : Ideal p.R).jacobson := by
    set_option synthInstance.maxHeartbeats 400000 in
    refine Ideal.mem_sInf.2 fun J hJ => ?_
    have hJm : J.IsMaximal := hJ.2
    letI := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (p.R ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)
    haveI : Module.Finite K (p.R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (p.R ⧸ J)
    haveI : Algebra.IsIntegral K (p.R ⧸ J) := Algebra.IsIntegral.of_finite K _
    haveI : Algebra.IsAlgebraic K (p.R ⧸ J) := Algebra.IsIntegral.isAlgebraic
    let ι : (p.R ⧸ J) →ₐ[K] M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h0 := h (ι.comp (Ideal.Quotient.mkₐ K J))
    have h1 : ι (Ideal.Quotient.mk J a) = ι 0 := by
      rw [map_zero]
      exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 (ι.toRingHom.injective h1)
  rw [hjac] at ha
  exact (Submodule.mem_bot _).1 ha

theorem eq_zero_of_cpts (σ : K →+* ℂ) (p : TRing K) (a : p.R) (h : ∀ ψ : p.R →ₐ[K] CAt σ, ψ a = 0) : a = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  exact eq_zero_of_pts (M := CAt σ) p a h

def cvalR (σ : K →+* ℂ) : CAt σ →+* ℂ := RingHom.id ℂ

def toCAt (σ : K →+* ℂ) (z : ℂ) : CAt σ := z

theorem cvalR_algebraMap (σ : K →+* ℂ) (t : K) : cvalR σ (algebraMap K (CAt σ) t) = σ t := rfl

theorem linIndep_alg_pts [CharZero K] {Kb : Type} [Field Kb] [IsAlgClosed Kb] [Algebra K Kb] [Normal K Kb] (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (v : Fin m → Kb)
    (h : ∀ φ : p.R →ₐ[K] Kb, ∑ i, v i * φ (a i) = 0) : v = 0 := by
  classical
  let L : IntermediateField K Kb := IntermediateField.adjoin K (Set.range v)
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let u : Fin m → L := fun i => ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hu : ∀ i, algebraMap L Kb (u i) = v i := fun i => rfl

  have hg : ∀ (g : L →ₐ[K] Kb) (φ : p.R →ₐ[K] Kb), ∑ i, g (u i) * φ (a i) = 0 := by
    intro g φ
    let G : Kb →ₐ[K] Kb := g.liftNormal Kb
    have hb : Function.Bijective G := Algebra.IsAlgebraic.algHom_bijective G
    let Ge : Kb ≃ₐ[K] Kb := AlgEquiv.ofBijective G hb
    have h1 := h ((Ge.symm : Kb →ₐ[K] Kb).comp φ)
    have h2 := congrArg G h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hu i, AlgHom.liftNormal_commutes]
    congr 1
    show φ (a i) = G (Ge.symm (φ (a i)))
    exact (Ge.apply_symm_apply (φ (a i))).symm

  have htr : ∀ lam : L, ∀ i, Algebra.trace K L (lam * u i) = 0 := by
    intro lam
    have hpt : ∀ φ : p.R →ₐ[K] Kb, φ (∑ i, Algebra.trace K L (lam * u i) • a i) = 0 := by
      intro φ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have : ∀ i, φ (Algebra.trace K L (lam * u i) • a i) =
          (∑ g : L →ₐ[K] Kb, g (lam * u i)) * φ (a i) := by
        intro i
        rw [map_smul, Algebra.smul_def, ← trace_eq_sum_embeddings]
      simp_rw [this, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have := hg g φ
      calc ∑ i, g (lam * u i) * φ (a i) = g lam * ∑ i, g (u i) * φ (a i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul, mul_assoc]
        _ = 0 := by rw [this, mul_zero]
    have h0 := eq_zero_of_pts p _ hpt
    exact fun i => (Fintype.linearIndependent_iff.1 ha _ h0) i
  funext i
  have hz : u i = 0 := by
    refine (traceForm_nondegenerate K L).1 (u i) fun lam => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact htr lam i
  rw [← hu i, hz, map_zero]
  rfl

theorem linIndep_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (w : Fin m → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ i, w i * cvalR σ (ψ (a i)) = 0) : w = 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let Kb := AlgebraicClosure K
  letI : Module Kb ℂ := Module.compHom ℂ (ι.toRingHom : Kb →+* ℂ)
  have hsm : ∀ (c : Kb) (z : ℂ), c • z = ι c * z := fun _ _ => rfl
  by_contra hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw (funext hne)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual Kb ℂ, ℓ (w j) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hj ((Module.forall_dual_apply_eq_zero_iff Kb (w j)).1 hne)
  have hv := linIndep_alg_pts (Kb := AlgebraicClosure K) p a ha (fun i => ℓ (w i)) fun φ => by
    have h1 := congrArg ℓ (h (ι.comp φ : p.R →ₐ[K] ℂ))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : w i * cvalR σ ((ι.comp φ : p.R →ₐ[K] ℂ) (a i)) = φ (a i) • w i := by
      rw [hsm, mul_comm]; rfl
    erw [e, map_smul, smul_eq_mul, mul_comm]
  exact hℓ (congrFun hv j)

theorem descend_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {r : ℕ} (a : Fin r → p.R) (w : Fin r → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ j, w j * cvalR σ (ψ (a j)) = 0) (θ : Module.Dual K (CAt σ)) :
    ∑ j, θ (toCAt σ (w j)) • a j = 0 := by
  classical
  let S : Submodule K p.R := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let e := Module.finBasis K S
  let t : Fin r → Fin (Module.finrank K S) → K := fun j l => e.repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  have hat : ∀ j, a j = ∑ l, t j l • (e l : p.R) := by
    intro j
    have := e.sum_repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩
    have h2 := congrArg (fun x : S => (x : p.R)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hind : LinearIndependent K (fun l => (e l : p.R)) :=
    e.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have key := linIndep_cpts σ p (fun l => (e l : p.R)) hind (fun l => ∑ j, σ (t j l) * w j) fun ψ => by
    rw [← h ψ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hat, map_sum, map_smul, Algebra.smul_def, map_mul, cvalR_algebraMap, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hk : ∀ l, ∑ j, t j l • toCAt σ (w j) = 0 := by
    intro l
    have := congrFun key l
    simp only [Pi.zero_apply] at this
    exact this
  calc ∑ j, θ (toCAt σ (w j)) • a j = ∑ l, θ (∑ j, t j l • toCAt σ (w j)) • (e l : p.R) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp_rw [hat, Finset.smul_sum, map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = 0 := by simp [hk]

end Alg

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Formalism.L2.Pj

namespace FJ

section Orbit

variable {Ω : Type} {N : ℕ}

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.Icc 0 1

def chr (ph : Fin N → ℝ) (t : Fin N → ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ k, t k * ph k : ℝ) : ℂ))

def integrand (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P : Ω → ℂ) (x : Ω)
    (t : Fin N → ℝ) : ℂ :=
  P (act t x) * chr ph t

def coefFn (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P : Ω → ℂ) (x : Ω) : ℂ :=
  ∫ t in cube N, integrand act ph P x t

theorem integrand_add (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P Q : Ω → ℂ) (x : Ω) :
    integrand act ph (P + Q) x = fun t => integrand act ph P x t + integrand act ph Q x t := by
  funext t; simp [integrand, add_mul]

theorem integrand_smul (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (a : ℂ) (P : Ω → ℂ) (x : Ω) :
    integrand act ph (a • P) x = fun t => a * integrand act ph P x t := by
  funext t; simp [integrand, mul_assoc]

theorem integrand_zero (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (x : Ω) :
    integrand act ph (0 : Ω → ℂ) x = fun _ => 0 := by
  funext t; simp [integrand]

def OrbInt (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) : Submodule ℂ (Ω → ℂ) where
  carrier := {P | ∀ (ph : Fin N → ℝ), ∀ x ∈ S, IntegrableOn (integrand act ph P x) (cube N)}
  zero_mem' := by
    intro ph x _
    rw [integrand_zero]
    exact integrableOn_zero
  add_mem' := by
    intro P Q hP hQ ph x hx
    rw [integrand_add]
    exact (hP ph x hx).add (hQ ph x hx)
  smul_mem' := by
    intro a P hP ph x hx
    rw [integrand_smul]
    exact (hP ph x hx).const_mul a


open Classical in
def coefL (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) (ph : Fin N → ℝ) :
    OrbInt act S →ₗ[ℂ] (Ω → ℂ) where
  toFun P := by
    classical
    exact fun x => if x ∈ S then coefFn act ph P x else 0
  map_add' P Q := by
    funext x
    by_cases hx : x ∈ S
    · simp only [hx, if_true, coefFn, Submodule.coe_add, Pi.add_apply]
      rw [integrand_add]
      exact integral_add (P.2 ph x hx) (Q.2 ph x hx)
    · simp [hx]
  map_smul' a P := by
    funext x
    by_cases hx : x ∈ S
    · simp only [hx, if_true, coefFn, Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      rw [integrand_smul]
      exact integral_const_mul a _
    · simp [hx]

theorem integrableOn_integrand [TopologicalSpace Ω] {act : (Fin N → ℝ) → Ω → Ω} {ph : Fin N → ℝ}
    {P : Ω → ℂ} {x : Ω} {T : Set Ω} (hP : ContinuousOn P T) (hact : Continuous fun t => act t x)
    (hT : ∀ t ∈ cube N, act t x ∈ T) : IntegrableOn (integrand act ph P x) (cube N) := by
  have h1 : ContinuousOn (fun t => P (act t x)) (cube N) :=
    hP.comp hact.continuousOn (fun t ht => hT t ht)
  have h2 : Continuous (chr ph) := by
    unfold chr; fun_prop
  exact (h1.mul h2.continuousOn).integrableOn_compact isCompact_Icc

end Orbit

section Via

variable {K : Type} [Field K]

def FnVia (_σ : K →+* ℂ) (Ω : Type) : Type := Ω → ℂ

variable (σ : K →+* ℂ) (Ω : Type)

instance : AddCommGroup (FnVia σ Ω) := inferInstanceAs (AddCommGroup (Ω → ℂ))

instance : Module K (FnVia σ Ω) := Module.compHom (Ω → ℂ) σ

variable {σ Ω}

def coefVia {N : ℕ} {C : Type} [AddCommGroup C] [Module K C] (act : (Fin N → ℝ) → Ω → Ω)
    (S : Set Ω) (ph : Fin N → ℝ) (rd : C →ₛₗ[σ] (Ω → ℂ)) (hrd : ∀ F, rd F ∈ OrbInt act S) :
    C →ₗ[K] FnVia σ Ω where
  toFun F := (coefL act S ph ⟨rd F, hrd F⟩ : Ω → ℂ)
  map_add' F G := by
    have h : (⟨rd (F + G), hrd (F + G)⟩ : OrbInt act S) = ⟨rd F, hrd F⟩ + ⟨rd G, hrd G⟩ :=
      Subtype.ext (by simp)
    rw [h, map_add (f := _)]
    rfl
  map_smul' a F := by
    have h : (⟨rd (a • F), hrd (a • F)⟩ : OrbInt act S) = σ a • ⟨rd F, hrd F⟩ :=
      Subtype.ext (by simp)
    rw [h, map_smul]
    rfl

end Via

section FD

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

structure CuspFD (X : Data E r) (ρ : ℕ) where
  e : Fin ρ → Fin r → E
  ind : LinearIndependent E e
  iso : ∀ a b, herm X.Gm (e a) (e b) = 0

def CuspFD.I {X : Data E r} (cu : CuspFD X ρ) : Submodule (𝓞 E) (Fin r → E) :=
  X.Λ ⊓ (Submodule.span E (Set.range cu.e)).restrictScalars (𝓞 E)

def crdI (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ (𝔄 : Submodule (𝓞 E) E), ∃ x ∈ cu.I, a • x = ∑ i, v i • cu.e i}

def dualZE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E) :=
  {l | ∀ x ∈ Xs, Algebra.trace ℚ E (∑ i, l i * x i) ∈ Set.range (Int.cast : ℤ → ℚ)}

def dualOE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E) :=
  {l | ∀ x ∈ Xs, ∑ i, l i * x i ∈ Set.range (algebraMap (𝓞 E) E)}

def XcFD (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  Submodule.span (𝓞 E) (dualZE (crdI 𝔄 cu))

def IsSkew (β : Matrix (Fin ρ) (Fin ρ) E) : Prop := ∀ a b, cc (β a b) = -β b a

def IsHermE (χ : Matrix (Fin ρ) (Fin ρ) E) : Prop := ∀ a b, cc (χ a b) = χ b a

def zMatE (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun k l => (if k = l then 1 else 0) + ∑ a, ∑ b, β a b * e a k * ∑ k', X.Gm l k' * cc (e b k')

def zMatC (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k l => (if k = l then 1 else 0) +
    ∑ a, ∑ b, β a b * τ (e a k) * ∑ k', τ (X.Gm l k') * conj (τ (e b k'))

def zGam (X : Data E r) (cu : CuspFD X ρ) : Set (Matrix (Fin ρ) (Fin ρ) E) :=
  {β | IsSkew β ∧ ∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β}

def nZ (X : Data E r) (ρ : ℕ) : ℕ := X.Ψ.card * ρ ^ 2

def IsZBasis (X : Data E r) (cu : CuspFD X ρ) (bs : Fin (nZ X ρ) → Matrix (Fin ρ) (Fin ρ) E) : Prop :=
  LinearIndependent ℤ bs ∧ ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range bs)

def zBas (X : Data E r) (cu : CuspFD X ρ) : Fin (nZ X ρ) → Matrix (Fin ρ) (Fin ρ) E :=
  Classical.epsilon (IsZBasis X cu)

def zAct (X : Data E r) (cu : CuspFD X ρ) (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (zMatC X cu.e τ.1 (∑ k, (t k : ℂ) • (zBas X cu k).map τ.1) * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def prE (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) : ℝ :=
  ∑ τ : X.Ψ, (τ.1 (Matrix.trace (χ.transpose * β) / (X.κ0 / 2))).re

def phZ (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : Fin (nZ X ρ) → ℝ :=
  fun k => prE X χ (zBas X cu k)

variable {Comp : Type}

abbrev CuF (X : Comp → Data E r) (ρ : ℕ) : Type := Σ c, CuspFD (X c) ρ

def XcF (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (cu : CuF X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  XcFD 𝔄 cu.2

variable {K : Type} [Field K] (σ : K →+* ℂ)

abbrev FJtF (X : Comp → Data E r) (cu : CuF X ρ) : Type := FnVia σ (Frame (X cu.1).Ψ r)

variable {C : Type} [AddCommGroup C] [Module K C]

def RdOrbInt (X : Comp → Data E r) (ρ : ℕ) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ)) : Prop :=
  ∀ f (cu : CuF X ρ), rd f cu.1 ∈ OrbInt (zAct (X cu.1) cu.2) (X cu.1).dom

def sgF (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ)) (h : RdOrbInt σ X ρ rd)
    (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : C →ₗ[K] FJtF σ X cu :=
  coefVia (zAct (X cu.1) cu.2) (X cu.1).dom (phZ (X cu.1) cu.2 χ)
    ((LinearMap.proj (φ := fun c => Frame (X c).Ψ r → ℂ) cu.1).comp rd) (fun f => h f cu)

def OrbDom (X : Comp → Data E r) (ρ : ℕ) : Prop :=
  ∀ (cu : CuF X ρ) t, ∀ x ∈ (X cu.1).dom, zAct (X cu.1) cu.2 t x ∈ (X cu.1).dom

theorem continuous_zAct (X : Data E r) (cu : CuspFD X ρ) (x : Frame X.Ψ r) :
    Continuous fun t => zAct X cu t x := by
  unfold zAct zMatC
  fun_prop

theorem rdOrbInt_of (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (hd : OrbDom X ρ) : RdOrbInt σ X ρ rd := by
  intro f cu ph x hx
  exact integrableOn_integrand (hc f cu.1) (continuous_zAct _ _ x) (fun t _ => hd cu t x hx)

def LatZ (X : Comp → Data E r) (ρ : ℕ) : Prop := ∀ cu : CuF X ρ, ∃ bs, IsZBasis (X cu.1) cu.2 bs

def XcLatF (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (ρ : ℕ) : Prop :=
  ∀ cu : CuF X ρ, Submodule.IsLattice E (XcF X 𝔄 cu)

def CuNeF (X : Comp → Data E r) (ρ : ℕ) : Prop := ∀ c, Nonempty (CuspFD (X c) ρ)

def ExpoMatch (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (ρ g : ℕ) : Prop :=
  ∀ (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsHermE χ →
    ((∀ β ∈ zGam (X cu.1) cu.2, ∃ n : ℤ, prE (X cu.1) χ β = n) ↔
      ∀ l ∈ dualOE (XcF X 𝔄 cu), ∀ m ∈ dualOE (XcF X 𝔄 cu),
        (g : E) * ∑ i, ∑ k, l i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))

end FD

end FJ

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem sum_castLE {R : Type} [AddCommMonoid R] {i n : ℕ} (h : i ≤ n) (f : Fin n → R)
    (hf : ∀ c : Fin n, i ≤ (c : ℕ) → f c = 0) : ∑ c, f c = ∑ c : Fin i, f (Fin.castLE h c) := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
    (fun c => f (Fin.castLE h c)) f (fun c hc => hf c ?_) (fun _ => rfl)).symm
  by_contra hlt
  push_neg at hlt
  exact hc ⟨⟨c, hlt⟩, rfl⟩

theorem sub_mul_tri {i : ℕ} (h : i ≤ r) (Q A : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular) :
    (Qᵀ * A * Q.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (Q.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (Q.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [sum_castLE h]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_castLE h]
    intro k hk
    have hz : Q k (Fin.castLE h a) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le a.isLt hk)
    rw [hz, zero_mul]
  · intro l hl
    have hz : Q l (Fin.castLE h b) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le b.isLt hl)
    rw [hz, map_zero, mul_zero]

theorem lminor_mul_tri (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hQ : Q.IsUpperTriangular) (i : Fin (r + 1)) :
    lminor (gram τ G (P * Q)) i =
      ((Complex.normSq (Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det : ℝ) : ℂ) * lminor (gram τ G P) i := by
  unfold lminor
  rw [gram_mul, sub_mul_tri (Nat.le_of_lt_succ i.isLt) Q (gram τ G P) hQ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  generalize Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = M
  rw [show (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det from (RingHom.map_det _ M).symm,
    ← Complex.mul_conj]
  ring

theorem det_sub_tri_ne {i : ℕ} (h : i ≤ r) (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular)
    (hd : Q.det ≠ 0) : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0 := by
  have hsub : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.submatrix_apply]
    exact hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE] at hab ⊢; exact hab)
  rw [Matrix.det_of_upperTriangular hsub]
  rw [Matrix.det_of_upperTriangular hQ] at hd
  rw [Finset.prod_ne_zero_iff] at hd ⊢
  intro c _
  exact hd _ (Finset.mem_univ _)

theorem bor_upper {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).IsUpperTriangular := by
  intro a c hac
  exact (hb τ).2 a c hac

theorem dom_rmul (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hQ := bor_upper hb τ
  have hbd : (mat b τ).det ≠ 0 := (hb τ).1
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero hdet hbd
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hm, lminor_mul_tri τ.1 X.Gm _ _ hQ i, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det :=
      Complex.normSq_pos.mpr (det_sub_tri_ne _ _ hQ hbd)
    rw [mul_left_comm]
    exact mul_pos hn hi

theorem ustab_mat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext k l
  have h1 := h.1 (Pi.single k 1) (Pi.single l 1)
  have hR : herm G (Pi.single k 1) (Pi.single l 1) = G k l := by
    have hs : ∀ b, cc ((Pi.single l (1 : E) : Fin r → E) b) = (Pi.single l (1 : E) : Fin r → E) b := by
      intro b
      by_cases hb : b = l <;> simp [hb, cc]
    simp only [herm, hs]
    simp [Pi.single_apply]
  have hL : herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1))
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single l 1)) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc) k l := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [← hL, h1, hR]

theorem dom_lact (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : IsUStab X.Gm X.Λ γ) : lact γ x ∈ X.dom := by
  have hU := ustab_mat hγ
  have hcc : ∀ (σ : E →+* ℂ) (a : E), σ (cc a) = starRingEnd ℂ (σ a) := by
    intro σ a
    exact NumberField.IsCMField.complexEmbedding_complexConj E σ a
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext a b
    simp only [Matrix.map_apply]
    exact hcc _ _
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [← hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hgr : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hm, gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
    rw [show ∀ M1 M2 M3 M4 M5 : Matrix (Fin r) (Fin r) ℂ,
        M1 * M2 * M3 * (M4 * M5) = M1 * (M2 * M3 * M4) * M5 from
      fun M1 M2 M3 M4 M5 => by simp only [Matrix.mul_assoc], key]
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ hdet
    rw [show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det from
      (RingHom.map_det τ.1 _).symm]
    exact (map_ne_zero τ.1).mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)).ne_zero
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hgr]
    exact hi

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RhoWApply
noncomputable section

namespace Formalism.L2.Pj

section Act

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)

def mvPt (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : pts S :=
  open Classical in if h : ∃ y', actR g y y' then h.choose else y

def actRule (g : G) (f : Rules pts) : Rules pts := fun p y => f p (mvPt pts actR g y)

def actL (g : G) : Rules pts →ₗ[K] Rules pts where
  toFun := actRule pts actR g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem actL_apply (g : G) (f : Rules pts) (p : TRing K) (y : pts p.R) :
    actL pts actR g f p y = f p (mvPt pts actR g y) := rfl

def ActTotal : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y : pts S), ∃ y', actR g y y'

def ActFun : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR g y y'' → mapR (AlgHom.id K S) y' y''

def ActOne : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (y : pts S), actR 1 y y

def ActMul : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR h y' y'' → actR (g * h) y y''

def ActNat : Prop :=
  ∀ (g : G) (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
    (y y' : pts S) (z z' : pts T), mapR φ y z → actR g y y' → actR g z z' → mapR φ y' z'

def ActBor : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' z z' : pts S),
    borR t y z → actR g y y' → actR g z z' → borR t y' z'

variable {pts actR}

theorem mvPt_spec (hT : ActTotal pts actR) (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    actR g y (mvPt pts actR g y) := by
  have h := hT g S y
  unfold mvPt
  rw [dite_eq_left h]
  exact h.choose_spec

variable (pts actR)

theorem actL_mem [Fintype ι] (hT : ActTotal pts actR) (hN : ActNat pts mapR actR) (hB : ActBor pts borR actR)
    (e : ι → ℕ) (g : G) {f : Rules pts} (hf : f ∈ secW pts mapR borR e) :
    actL pts actR g f ∈ secW pts mapR borR e := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact h1 p q φ _ _ (hN g p.R q.R φ y (mvPt pts actR g y) z (mvPt pts actR g z) hyz
      (mvPt_spec hT g y) (mvPt_spec hT g z))
  · intro p t y y' hyy
    exact h2 p t _ _ (hB g p.R t y (mvPt pts actR g y) y' (mvPt pts actR g y') hyy
      (mvPt_spec hT g y) (mvPt_spec hT g y'))

theorem actL_one (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hO : ActOne pts actR)
    {f : Rules pts} (hf : IsNatural pts mapR f) : actL pts actR 1 f = f := by
  funext p y
  show f p (mvPt pts actR 1 y) = f p y
  exact hf p p (AlgHom.id K p.R) y _ (hF 1 p.R y y _ (hO p.R y) (mvPt_spec hT 1 y))

theorem actL_mul (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hM : ActMul pts actR)
    (g h : G) {f : Rules pts} (hf : IsNatural pts mapR f) :
    actL pts actR (g * h) f = actL pts actR g (actL pts actR h f) := by
  funext p y
  show f p (mvPt pts actR (g * h) y) = f p (mvPt pts actR h (mvPt pts actR g y))
  have h1 : actR (g * h) y (mvPt pts actR h (mvPt pts actR g y)) :=
    hM g h p.R y _ _ (mvPt_spec hT g y) (mvPt_spec hT h _)
  exact (hf p p (AlgHom.id K p.R) _ _ (hF (g * h) p.R y _ _ (mvPt_spec hT (g * h) y) h1)).symm

structure ActLaws : Prop where
  total : ActTotal pts actR
  func : ActFun pts mapR actR
  one : ActOne pts actR
  mul : ActMul pts actR
  nat : ActNat pts mapR actR
  bor : ActBor pts borR actR

variable {pts mapR borR actR}

end Act

end Formalism.L2.Pj
end
end
