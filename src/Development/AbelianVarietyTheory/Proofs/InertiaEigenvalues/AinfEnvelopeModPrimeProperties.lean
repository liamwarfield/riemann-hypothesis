module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}

theorem pow_smul_top_eq {R : Type} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n • ⊤ : Submodule R R) = J ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem c_mem_of_mem (tb : TopBasis s I ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) (i : ι) :
    tb.c i x ∈ I ^ n := by
  have key : ∀ a : A, tb.c i (a * x) ∈ I ^ n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      rw [mul_comm, tb.c_mul]
      exact Ideal.mul_mem_right _ _ hz
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem mem_map_pow_iff (tb : TopBasis s I ι) (n : ℕ) (x : A) :
    x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n :=
  ⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩

theorem eq_zero_of_c_eq_zero (tb : TopBasis s I ι) (x : A) (h : ∀ i, tb.c i x = 0) : x = 0 := by
  refine tb.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]
  exact (mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _

theorem exists_coeffs_eq_of_null (tb : TopBasis s I ι) (hS : IsHausdorff I S) (a : ι → S)
    (ha : ∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) : ∃ x, ∀ i, tb.c i x = a i := by
  classical
  let F : ℕ → Finset ι := fun n => (ha n).toFinset
  have hF : ∀ n i, i ∉ F n → a i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  have hFm : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  let y : ℕ → A := fun n => ∑ i ∈ F n, s (a i) * tb.b i
  have hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s := by
    intro m n hmn
    have e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i := by
      simp only [y]; rw [← Finset.sum_sdiff (hFm hmn)]; ring
    rw [e]
    exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))
  obtain ⟨x, hx⟩ := tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]
    exact neg_mem (hy m n hmn))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
  have h1 : tb.c i (x - y n) ∈ I ^ n := by
    have h := hx n
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub] at h
    exact c_mem_of_mem tb n (by simpa using neg_mem h) i
  have h2 : tb.c i (y n) - a i ∈ I ^ n := by
    have e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_sum, tb.c_mul]
    rw [e]
    by_cases hi : i ∈ F n
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero])
        (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]
      exact neg_mem (hF n i hi)
  have e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i) := by rw [map_sub]; ring
  rw [e]
  exact add_mem h1 h2

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.coeff_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S)
    (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧
    (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) :=
  fun _ _ _ _ _ _ _ tb => ⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb,
    fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_zero_map_pow_null_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧ (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) := by
  first | exact @GlobalTheory.BSP.TopBasis.coeff_facts | exact GlobalTheory.BSP.TopBasis.coeff_facts | (intros; apply GlobalTheory.BSP.TopBasis.coeff_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimeProperties
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.dvd_iff_dvd_coeff {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (p : S)
    (hp : ∀ (n : ℕ) (y : S), p * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n) (x : A) :
    s p ∣ x ↔ ∀ i, p ∣ tb.c i x := by
  obtain ⟨h0, -, h2⟩ := GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨_, tb.c_mul i p y⟩
  · choose a ha using h
    obtain ⟨y, hy⟩ := h2 hI a fun n => (tb.fin x (2 * n + 2)).subset fun i hi hi' =>
      hi (hp n _ (ha i ▸ hi'))
    refine ⟨y, sub_eq_zero.1 (h0 _ fun i => ?_)⟩
    rw [map_sub, tb.c_mul, hy, ha, sub_self]

theorem TopBasis.mod_props {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (l : ℕ) (u : S)
    (hp : ∀ (n : ℕ) (y : S), (l : S) * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n)
    (h1 : ∀ y : S, (l : S) * y = 0 → y = 0) (h2 : ∀ y : S, (l : S) ∣ u * y → (l : S) ∣ y)
    (h3 : ∀ y : S, (∀ m : ℕ, ∃ z, (l : S) ∣ y - u ^ m * z) → (l : S) ∣ y) :
    (∀ x : A, (l : A) * x = 0 → x = 0) ∧ (∀ x : A, (l : A) ∣ s u * x → (l : A) ∣ x) ∧
      ∀ x : A, (∀ m : ℕ, ∃ z, (l : A) ∣ x - s u ^ m * z) → (l : A) ∣ x := by
  have key := tb.dvd_iff_dvd_coeff hI (l : S) hp
  rw [← map_natCast s l]
  refine ⟨fun x hx => (GlobalTheory.T.coeff_zero_map_pow_null_facts S A ι s I tb).1 x fun i => h1 _ ?_, fun x hx => (key x).2 fun i => h2 _ ?_,
    fun x hx => (key x).2 fun i => h3 _ fun m => ?_⟩
  · rw [← tb.c_mul, hx, map_zero]
  · rw [← tb.c_mul]
    exact (key _).1 hx i
  · obtain ⟨z, hz⟩ := hx m
    refine ⟨tb.c i z, ?_⟩
    rw [← tb.c_mul, ← map_sub, map_pow]
    exact (key _).1 hz i

theorem env_ainf_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En
  obtain ⟨hp, h2, h3, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  exact En.tb.mod_props (ainfObj K).complete.toIsHausdorff l (bk.ev X) hp ainf_torsionFree h2 h3

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimePropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_envelope_mod_prime_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.env_ainf_mod | exact GlobalTheory.BSP.env_ainf_mod | (intros; apply GlobalTheory.BSP.env_ainf_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransfer
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.ResSel.Transfer

section Alg

variable {O Λ K : Type} [CommRing O] [CommRing Λ] [CommRing K] [Algebra O Λ] [Algebra O K] [Module Λ K]
  (φ : Λ →ₐ[O] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b)

def idVec (r : ℕ) : (Fin r → K) →ₛₗ[(φ : Λ →+* K)] (Fin r → K) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := funext fun a => hs c (m a)

include hs in
theorem matAct_eq {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : Fin n → K) :
    matAct (M := K) Φ x = (Φ.map φ).mulVec x := by
  funext a
  simp [matAct, hs, Matrix.mulVec, dotProduct]

include hs in
theorem repOn_eq {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn ρ κ K g m = φ ((κ g : Λˣ) : Λ) • ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, hs, Matrix.mulVec, dotProduct]

theorem idVec_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
    (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1) (g : Γ) (m : Fin r → K) :
    idVec φ hs r (repOn ρ κ K g m) = repOn ρ (1 : Γ →* Kˣ) K g (idVec φ hs r m) := by
  change repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m
  rw [repOn_eq φ hs, hκ]
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

variable [TopologicalSpace K] [DiscreteTopology K] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {r : ℕ}
  (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

def tau : H1 (repOn ρ κ K) →ₛₗ[(φ : Λ →+* K)] H1 (repOn ρ (1 : Γ →* Kˣ) K) :=
  slH1 _ _ (idVec φ hs r) continuous_of_discreteTopology (idVec_repOn φ hs ρ κ hκ)

theorem tau_injective : Function.Injective (tau φ hs ρ κ hκ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
      (idVec_repOn φ hs ρ κ hκ) z) : H1 (repOn ρ (1 : Γ →* Kˣ) K)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    have e : repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m := idVec_repOn φ hs ρ κ hκ g m
    rw [e]
    exact hm g

def kerIn {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : LinearMap.ker (Φ.map φ).mulVecLin) :
    LinearMap.ker (matAct (M := K) Φ) :=
  ⟨x.1, by rw [LinearMap.mem_ker, matAct_eq φ hs]; exact x.2⟩

theorem exists_linear (hsurj : Function.Surjective (algebraMap O K)) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ)
    (S : Submodule Λ (H1 (repOn ρ κ K))) (e : LinearMap.ker (matAct (M := K) Φ) ≃ₗ[Λ] S) :
    ∃ E : LinearMap.ker (Φ.map φ).mulVecLin →ₗ[K] H1 (repOn ρ (1 : Γ →* Kˣ) K), Function.Injective E ∧
      ∀ x, E x = tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1 := by
  refine ⟨{ toFun := fun x => tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun x y hxy => ?_, fun _ => rfl⟩
  · rw [show kerIn φ hs Φ (x + y) = kerIn φ hs Φ x + kerIn φ hs Φ y from rfl, map_add (f := _), Submodule.coe_add, map_add (f := _)]
  · obtain ⟨o, rfl⟩ := hsurj c
    have h1 : kerIn φ hs Φ (algebraMap O K o • x) = algebraMap O Λ o • kerIn φ hs Φ x := by
      apply Subtype.ext
      funext b
      change algebraMap O K o * x.1 b = algebraMap O Λ o • x.1 b
      rw [hs, AlgHom.commutes]
    rw [h1, map_smul, Submodule.coe_smul, map_smulₛₗ, RingHom.id_apply]
    congr 1
    exact φ.commutes o
  · have h1 := e.injective (Subtype.ext (tau_injective φ hs ρ κ hκ hxy))
    have h2 : (kerIn φ hs Φ x).1 = (kerIn φ hs Φ y).1 := congrArg Subtype.val h1
    exact Subtype.ext h2

end Alg

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ K : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing K] [Algebra (X.O0 i) K] [Module Λ K]
  [TopologicalSpace K] [DiscreteTopology K]
  (φ : Λ →ₐ[X.O0 i] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b) (κ : GE N →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

theorem tau_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ K v) :
    slH1 ((repOn ρ κ K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype)
      (idVec φ hs r) continuous_of_discreteTopology (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
        (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, hs, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem tau_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ K)) (hx : x ∈ selOn bkP i ρ κ K Q) :
    tau φ hs ρ κ hκ x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ κ K) (repOn ρ (1 : GE N →* Kˣ) K) (idVec φ hs r) continuous_of_discreteTopology
    (idVec_repOn φ hs ρ κ hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact tau_mem_bkOn bkP i ρ φ hs κ hκ v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem tors_of_cast_eq_zero {B : Type} [CommRing B] {l : ℕ} (h : (l : B) = 0) (b : B) : ∃ n : ℕ, (l ^ n) • b = 0 :=
  ⟨1, by rw [pow_one, nsmul_eq_mul, h, zero_mul]⟩

theorem computes_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  intro D N X bkP i s M ι d Q a Φ hC k _ _ _ _ hk hsurj aug haug
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) k := Module.compHom k (aug : abelian₂ X i M ι →+* k)
  have hs : ∀ (y : abelian₂ X i M ι) (b : k), y • b = aug y * b := fun _ _ => rfl
  have hκ : ∀ g, aug ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = 1 := fun g =>
    haug (delAll X i M d g)⁻¹
  have hkT := tors_of_cast_eq_zero hk
  obtain ⟨E, hEi, hE⟩ := exists_linear aug hs (Tgl i s) (delInv i M d) hκ hsurj Φ _ (e k hkT)
  refine ⟨E, hEi, fun x => ?_, ?_⟩
  · rw [hE]
    exact tau_mem_selOn bkP i _ aug hs _ hκ Q _ (e k hkT (kerIn aug hs Φ x)).2
  intro B _ _ th hB x hx
  letI : Module (abelian₂ X i M ι) B := Module.compHom B (th : abelian₂ X i M ι →+* B)
  have hsB : ∀ (y : abelian₂ X i M ι) (b : B), y • b = th y * b := fun _ _ => rfl
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hBT := tors_of_cast_eq_zero hB
  let xB : LinearMap.ker (matAct (M := B) Φ) := ⟨x, by rw [LinearMap.mem_ker, matAct_eq th hsB]; exact hx⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B hBT xB).1
  refine ⟨z.1, (IsLocallyConstant.iff_continuous _).2 z.2.1, fun g h => ?_, fun f hf => ?_⟩
  · rw [z.2.2 g h, repOn_eq th hsB, Tgl_coe]
  let fl : B →ₗ[abelian₂ X i M ι] k :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun y b => hf y b }
  have hx' : (Φ.map aug).mulVec (fun c => f (x c)) = 0 := by
    funext c
    have h1 := congrArg f (congrFun hx c)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, hf] using h1
  let z₁ : Z1 (repOn (Tgl i s) (delInv i M d) k) :=
    cocycles1MapOfEquivariant _ _ (fl.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map (Tgl i s) (delInv i M d) fl) z
  refine ⟨⟨fun c => f (x c), hx'⟩, semilinearCoefficientMapCocycles _ _ (idVec aug hs D.R.r) continuous_of_discreteTopology
    (idVec_repOn aug hs (Tgl i s) (delInv i M d) hκ) z₁, fun _ => rfl, fun _ _ => rfl, ?_⟩
  rw [hE, he B k hBT hkT fl xB (kerIn aug hs Φ ⟨fun c => f (x c), hx'⟩) z z₁ (fun _ => rfl) (fun _ _ => rfl) hz.symm]
  rfl

end GlobalTheory.ResSel.Transfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransferStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixComputesTwistedSelmer_residual_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  first | exact @GlobalTheory.ResSel.Transfer.computes_transfer | exact GlobalTheory.ResSel.Transfer.computes_transfer | (intros; apply GlobalTheory.ResSel.Transfer.computes_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentsOfComputes
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.Growth

section Chg

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (h : ∀ g m, rho g m = rho' g m)

theorem mk_eq_mk_iff (z w : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = Submodule.Quotient.mk w ↔
    ∃ m, ∀ g, z.1 g - w.1 g = rho g m - m := by
  rw [Submodule.Quotient.eq]
  exact mem_coboundaries1 rho _

def chgZ (z : Z1 rho) : Z1 rho' := ⟨z.1, z.2.1, fun g k => by rw [← h]; exact z.2.2 g k⟩

def chg : H1 rho → H1 rho' :=
  Quotient.map' (chgZ rho rho' h) fun z w hzw => by
    obtain ⟨m, hm⟩ := (mk_eq_mk_iff rho z w).1 (Quotient.sound' hzw)
    exact Quotient.exact' ((mk_eq_mk_iff rho' _ _).2 ⟨m, fun g => by rw [← h]; exact hm g⟩)

theorem chg_mk (z : Z1 rho) : chg rho rho' h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (chgZ rho rho' h z) := rfl

theorem chg_zero : chg rho rho' h 0 = 0 := rfl

theorem chg_add (x y : H1 rho) : chg rho rho' h (x + y) = chg rho rho' h x + chg rho rho' h y := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  induction y using Submodule.Quotient.induction_on with
  | H w => rfl

theorem chg_smul (a : R) (a' : R') (ha : ∀ m : M, a • m = a' • m) (x : H1 rho) :
    chg rho rho' h (a • x) = a' • chg rho rho' h x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, chg_mk, chg_mk, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => ha _))

theorem chg_mem_span (hs : ∀ a : R, ∃ a' : R', ∀ m : M, a • m = a' • m) {S : Set (H1 rho)} {T : Submodule R' (H1 rho')}
    (hS : ∀ x ∈ S, chg rho rho' h x ∈ T) {x : H1 rho} (hx : x ∈ Submodule.span R S) : chg rho rho' h x ∈ T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [chg_zero]; exact T.zero_mem
  | add x y _ _ hx hy => rw [chg_add]; exact T.add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨a', ha⟩ := hs a
    rw [chg_smul _ _ _ a a' ha]
    exact T.smul_mem a' hx

theorem chg_chg (x : H1 rho) : chg rho' rho (fun g m => (h g m).symm) (chg rho rho' h x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem res_chg {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (chg rho rho' h x) =
      chg (rho.comp phi) (rho'.comp phi) (fun g m => h (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem chg_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) : chg rho rho' h x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_chg rho rho' h J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (chg_zero _ _ _))

end Chg

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw)

section Sel

variable {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ']
  [Algebra (X.O0 i) Λ'] (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ)
  {B : Type} [AddCommGroup B] [Module Λ B] [Module Λ' B] [TopologicalSpace B] [DiscreteTopology B]
  (h : ∀ g m, repOn ρ κ B g m = repOn ρ κ' B g m) (hs : ∀ a : Λ, ∃ a' : Λ', ∀ b : B, a • b = a' • b)
  (ho : ∀ (y : X.O0 i) (b : B), algebraMap (X.O0 i) Λ y • b = algebraMap (X.O0 i) Λ' y • b)

include hs ho

theorem chg_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) :
    chg _ ((repOn ρ κ' B).comp (DecV N v).subtype) (fun g m => h g.1 m) x ∈ bkOn bkP i ρ κ' B v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · refine chg_mem_span _ _ _ (fun a => (hs a).imp fun a' ha m => funext fun c => ha (m c)) ?_ hx
    rintro x ⟨z, c, y, b, hc, hy, hz, rfl⟩
    exact Submodule.subset_span ⟨chgZ _ _ (fun g m => h g.1 m) z, c, y, b, hc, hy,
      fun g a => (hz g a).trans (ho _ _), rfl⟩
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx]
    exact chg_zero _ _ _

theorem chg_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : chg _ (repOn ρ κ' B) h x ∈ selOn bkP i ρ κ' B Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_chg (repOn ρ κ B) (repOn ρ κ' B) h (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact chg_mem_bkOn bkP i ρ κ κ' h hs ho v _ hv
  · exact Submodule.mem_top
  · exact chg_ur _ _ _ _ _ hv

end Sel

def Represents {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {R : Type} [CommRing R] [Algebra (X.O0 i) R] (κ : GE N →* Rˣ)
    (Q : Finset (PlE D.host)) {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ E : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      (Fin a → B) → H1 (repOn ρ κ B),
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B),
      matAct Ψ u = 0 → E B u ∈ selOn bkP i ρ κ B Q) ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B),
      matAct Ψ u = 0 → matAct Ψ u' = 0 → E B u = E B u' → u = u') ∧
    (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B],
      ∀ y ∈ selOn bkP i ρ κ B Q, ∃ u, matAct Ψ u = 0 ∧ E B u = y) ∧
    ∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B),
      matAct Ψ u = 0 → E B' (fun c => f (u c)) = h1Map ρ κ f (E B u)

variable {bkP i}

theorem represents_of_computes {s : X.Sig i} {M : ℕ} {ι : Type} {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}
    {Q : Finset (PlE D.host)} {a : ℕ} {Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)} (hΦ : Computes bkP i s M d Q Φ)
    {R : Type} [CommRing R] [Algebra (X.O0 i) R] (p : abelian₂ X i M ι →ₐ[X.O0 i] R) (hp : Function.Surjective p)
    (κ : GE N →* Rˣ) (hκ : ∀ g, p (delInv i M d g : (abelian₂ X i M ι)ˣ) = κ g) (n : ℕ) (hn : ((X.l i ^ n : ℕ) : R) = 0) :
    Represents bkP i (Tgl i s) κ Q (Φ.map p) := by
  classical
  obtain ⟨e, he⟩ := hΦ
  have tor : ∀ (B : Type) [AddCommGroup B] [Module R B], ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0 := fun B _ _ b =>
    ⟨n, by rw [← Nat.cast_smul_eq_nsmul R, hn, zero_smul]⟩
  let inst : ∀ (B : Type) [AddCommGroup B] [Module R B], Module (abelian₂ X i M ι) B := fun B _ _ =>
    Module.compHom B p.toRingHom
  have hsm : ∀ (B : Type) [AddCommGroup B] [Module R B] (x : abelian₂ X i M ι) (b : B), x • b = p x • b := fun _ _ _ _ _ => rfl
  have hk : ∀ (B : Type) [AddCommGroup B] [Module R B] (u : Fin a → B), matAct (Φ.map p) u = matAct Φ u :=
    fun _ _ _ _ => rfl
  have ho : ∀ (B : Type) [AddCommGroup B] [Module R B] (y : X.O0 i) (b : B),
      algebraMap (X.O0 i) (abelian₂ X i M ι) y • b = algebraMap (X.O0 i) R y • b := fun B _ _ y b => by
    rw [hsm, AlgHom.commutes]
  have hr : ∀ (B : Type) [AddCommGroup B] [Module R B] g m,
      repOn (Tgl i s) (delInv i M d) B g m = repOn (Tgl i s) κ B g m := fun B _ _ g m => by
    funext c
    change (delInv i M d g : abelian₂ X i M ι) • ∑ j, algebraMap (X.O0 i) (abelian₂ X i M ι) _ • m j =
      (κ g : R) • ∑ j, algebraMap (X.O0 i) R _ • m j
    rw [hsm, hκ]
    simp only [ho]
  refine ⟨fun B _ _ _ _ u => if h : matAct Φ u = 0 then chg _ _ (hr B) (e B (tor B) ⟨u, h⟩).1 else 0,
    fun B _ _ _ _ u hu => ?_, fun B _ _ _ _ u u' hu hu' huu => ?_, fun B _ _ _ _ y hy => ?_,
    fun B B' _ _ _ _ _ _ _ _ f u hu => ?_⟩
  · rw [hk] at hu
    simp only [dif_pos hu]
    exact chg_mem_selOn bkP i _ _ _ (hr B) (fun x => ⟨p x, hsm B x⟩) (ho B) Q _ (e B (tor B) ⟨u, hu⟩).2
  · rw [hk] at hu hu'
    simp only [dif_pos hu, dif_pos hu'] at huu
    have h1 := congrArg (chg _ _ fun g m => (hr B g m).symm) huu
    rw [chg_chg, chg_chg] at h1
    exact congrArg Subtype.val ((e B (tor B)).injective (Subtype.ext h1))
  · have h1 := chg_mem_selOn bkP i _ _ _ (fun g m => (hr B g m).symm)
      (fun x => by obtain ⟨x', rfl⟩ := hp x; exact ⟨x', fun b => (hsm B x' b).symm⟩) (fun y b => (ho B y b).symm) Q y hy
    obtain ⟨u, hu⟩ := (e B (tor B)).surjective ⟨_, h1⟩
    have hu0 : matAct Φ u.1 = 0 := u.2
    refine ⟨u.1, hu0, ?_⟩
    simp only [dif_pos hu0]
    rw [show (⟨u.1, hu0⟩ : LinearMap.ker (matAct (M := B) Φ)) = u from rfl, hu]
    exact chg_chg _ _ _ y
  · rw [hk] at hu
    let f' : B →ₗ[abelian₂ X i M ι] B' := ⟨f.toAddHom, fun x b => f.map_smul (p x) b⟩
    have hu' : matAct Φ (fun c => f (u c)) = 0 := by
      show matAct Φ (fun c => f' (u c)) = 0
      funext c
      have := congrArg f' (congrFun hu c)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [matAct, map_sum] using this
    simp only [dif_pos hu, dif_pos hu']
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B (tor B) ⟨u, hu⟩).1
    rw [he B B' (tor B) (tor B') f' ⟨u, hu⟩ ⟨_, hu'⟩ z (cocycles1MapOfEquivariant _ _ (f'.compLeft _) continuous_of_discreteTopology
      (repOn_map _ _ f') z) (fun _ => rfl) (fun _ _ => rfl) hz.symm, ← hz]
    rfl

end GlobalTheory.Growth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpans
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpans
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.SatFree

theorem isBaseChange_between (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₁ D₂ : Type) [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₁] [Module E D₂] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (q : D₁ →ₗ[E] D₂) (hq : Function.Surjective q) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (S : Submodule A D₂) (hS : S ≤ N₂) (hqS : ∀ x ∈ N₁, q x ∈ S) :
    IsBaseChange E S.subtype := by
  let i : S →ₗ[A] N₂ := Submodule.inclusion hS
  have hi : Function.Injective i := Submodule.inclusion_injective hS
  have hiT : Function.Injective (LinearMap.lTensor E i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  let Φ : E ⊗[A] S →ₗ[E] D₂ := S.subtype.liftBaseChange E
  have hcomm : ∀ t : E ⊗[A] S, Φ t = h₂.equiv (LinearMap.lTensor E i t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hiT
    apply h₂.equiv.injective
    rw [← hcomm, ← hcomm, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨x, rfl⟩ := hq d
    have : q x ∈ LinearMap.range Φ := by
      refine h₁.inductionOn x ?_ ?_ ?_
      · intro m
        refine ⟨1 ⊗ₜ ⟨q m, hqS m m.2⟩, ?_⟩
        simp [Φ, LinearMap.liftBaseChange_tmul]
      · intro e y hy
        rw [map_smul]
        exact (LinearMap.range Φ).smul_mem e hy
      · intro a b ha hb
        rw [map_add (f := _)]
        exact (LinearMap.range Φ).add_mem ha hb
    exact this
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

theorem freeA_of_basis {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp]
    [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) S) : FreeA W T S := by
  refine ⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨b.equivFun ⟨x, hx⟩, ?_, ?_⟩
  · have h2 : ((⟨x, hx⟩ : S) : W.DD T) = ((∑ j, b.equivFun ⟨x, hx⟩ j • b j : S) : W.DD T) := by
      rw [b.sum_equivFun]
    rw [Submodule.coe_sum] at h2
    simpa only [Submodule.coe_smul] using h2
  · intro a ha
    have : (⟨x, hx⟩ : S) = ∑ j, a j • b j := by
      apply Subtype.ext
      simpa using ha
    rw [this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree


set_option maxHeartbeats 1600000 in
theorem satM_free_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (c1 : IsCrys (P.PD K) T₁.ρ) (c2 : IsCrys (P.PD K) T₂.ρ)
    (hsurj : Function.Surjective ((H.W K s LL h).map π))
    (hflat : Module.Flat (AA K LL) (H.W K s LL h).EE) :
    FreeA (H.W K s LL h) T₂ (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map (mapA (H.W K s LL h) π))
      ((H.W K s LL h).N T₂)) ∧
    IsBaseChange (H.W K s LL h).EE (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map
      (mapA (H.W K s LL h) π)) ((H.W K s LL h).N T₂)).subtype := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T₂
  generalize H.W K s LL h = W at hproj hsurj hflat ⊢
  set S := GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) with hSdef
  have hSN : S ≤ W.N T₂ := GlobalTheory.NL.Coker.satM_le _ _ _
  have hbc : IsBaseChange W.EE S.subtype := by
    refine isBaseChange_between (AA K LL) W.EE (W.DD T₁) (W.DD T₂) (W.map π) hsurj (W.N T₁) (W.N T₂)
      (W.N_base T₁ c1) (W.N_base T₂ c2) S hSN ?_
    intro x hx
    exact GlobalTheory.NL.Coker.le_satM l (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact W.map_N π c1 c2 z hz) ⟨x, hx, rfl⟩
  refine ⟨?_, hbc⟩
  obtain ⟨hfree, hrk⟩ := W.DD_free T₂
  haveI : Module.Finite (AA K LL) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  haveI hR : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  set_option synthInstance.maxHeartbeats 200000 in
  haveI hA : IsNoetherianRing (AA K LL) :=
    isNoetherian_of_tower (PowerSeries ↥(OL LL)) (isNoetherian_pi' (R := PowerSeries ↥(OL LL)))
  haveI hNn : IsNoetherian (AA K LL) ↥(W.N T₂) :=
    isNoetherian_of_isNoetherianRing_of_finite (AA K LL) ↥(W.N T₂)
  haveI : Module.Finite (AA K LL) ↥S :=
    Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp hNn S hSN)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hreg : ∀ u v : W.DD T₂, (letπ : AA K LL) • u = (letπ : AA K LL) • v → u = v := by
    intro u v h1
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (letπ : AA K LL) v] at h1
    exact W.EE_π.smul_left_cancel.mp h1
  have hlC : ((l : ℕ) : AA K LL) = fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
    funext i
    simp
  have hX : IsSMulRegular ↥S (fun _ => PowerSeries.X : AA K LL) := by
    intro x y hxy
    exact Subtype.ext (hreg _ _ (congrArg Subtype.val hxy))
  have hC : ∀ x y : ↥S, (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x =
      (fun _ => PowerSeries.X : AA K LL) • y → ∃ z : ↥S, x = (fun _ => PowerSeries.X : AA K LL) • z := by
    intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    let x' : ↥(W.N T₂) := ⟨x, hSN x.2⟩
    let y' : ↥(W.N T₂) := ⟨y, hSN y.2⟩
    have hxy' : (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' =
        (fun _ => PowerSeries.X : AA K LL) • y' := by
      apply Subtype.ext
      change _ • (x : W.DD T₂) = _ • (y : W.DD T₂)
      exact congrArg Subtype.val hxy
    obtain ⟨z, hz⟩ := GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x' y' hxy'
    have hzx : (letπ : AA K LL) • (z : W.DD T₂) = (x : W.DD T₂) := (congrArg Subtype.val hz).symm
    have hzy : ((l : ℕ) : AA K LL) • (z : W.DD T₂) = (y : W.DD T₂) := by
      apply hreg
      rw [smul_comm, hzx, hlC]
      exact congrArg Subtype.val hxy
    have hzS : (z : W.DD T₂) ∈ S := by
      refine GlobalTheory.NL.Coker.mem_satM_of_smul z.2 ?_ ?_
      · rw [hzy]; exact y.2
      · rw [hzx]; exact x.2
    exact ⟨⟨z, hzS⟩, Subtype.ext hzx.symm⟩
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥S) (E := W.EE) (D := W.DD T₂) W.EE_inj S.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hC
  exact freeA_of_basis W T₂ S b

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree

theorem satM_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π _ c1 c2 hses hflat
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) :=
    by
      haveI := GlobalTheory.EtaleExact.finite_OL LL
      haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
      have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
      refine GlobalTheory.EtaleExact.exact_of_tie (((F l).E K s LL h).tie)
        (GlobalTheory.EtaleExact.map_ne_top_of_tie (((F l).E K s LL h).tie) ?_ ?_) T₀ T₁ T₂ ι π hses
      · rw [hp]
        exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
      · rw [hp]
        exact GlobalTheory.EtaleExact.sep_RW LL
  exact satM_free_loc (HW l) K s LL h T₁ T₂ π c1 c2 hex.2.2 hflat

end GlobalTheory.NL.SatFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpansStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachSaturation_image_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  first | exact @GlobalTheory.NL.SatFree.satM_free_and_spans | exact GlobalTheory.NL.SatFree.satM_free_and_spans | (intros; apply GlobalTheory.NL.SatFree.satM_free_and_spans <;> assumption)
end
end
