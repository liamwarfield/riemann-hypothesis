module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowers
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowersStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_trace_powers : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  first | exact @GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | exact GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | (intros; apply GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.VirtualTrace

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def listSum (h : IsPlaceOver A w) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  L.foldr (fun x s => WD.std (x.2.sum s.2)) ⟨0, WDRep.diag h (ι := Fin 0) fun i => i.elim0⟩

theorem mk_listSum_cons (x : Σ n : ℕ, WDRep h (Fin n → ℂ)) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    WD.mk (listSum h (x :: L)).2 = WD.lpSum (WD.mk x.2) (WD.mk (listSum h L).2) := by
  rw [WD.lpSum_mk]
  exact WD.sound (WD.iso_std _).symm

theorem trace_std {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _

theorem trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']

theorem map_lpZero {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) : f (WD.lpZero (h := h)) = 1 := by
  have hzero := hf (WD.lpZero (h := h)) (WD.lpZero (h := h))
  rw [WD.lpSum_zero] at hzero
  exact mul_left_cancel (hzero.symm.trans (mul_one _).symm)

theorem map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by
  induction L with
  | nil => exact map_lpZero f hf
  | cons x L ih => rw [mk_listSum_cons, hf, ih, List.map_cons, List.prod_cons]

theorem prod_flatMap_replicate {ι α M : Type} [CommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).prod = ∏ i ∈ s, g (x i) ^ n i := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).prod =
      (l.map fun i => g (x i) ^ n i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_replicate, List.prod_replicate]
  rw [key, Finset.prod_map_toList]

theorem sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).sum =
      (l.map fun i => n i • g (x i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih, List.map_replicate, List.sum_replicate]
  rw [key, Finset.sum_map_toList]

end GlobalTheory.WeilDeligne.VirtualTrace


open GlobalTheory.WeilDeligne.VirtualTrace in
theorem GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ),
    (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) →
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ),
    (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) →
    ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  intro E Ω _ _ _ _ _ A w h f hf1 hf2 ι _ d a c hc
  classical
  let x : ι → Σ n : ℕ, WDRep h (Fin n → ℂ) := fun i => ⟨d i, a i⟩
  let L : (ι → ℕ) → List (Σ n : ℕ, WDRep h (Fin n → ℂ)) := fun n =>
    (Finset.univ : Finset ι).toList.flatMap fun i => List.replicate (n i) (x i)
  have hfL : ∀ n, f (WD.mk (listSum h (L n)).2) = ∏ i, f (WD.mk (a i)) ^ n i := fun n => by
    rw [map_listSum f hf1]
    exact prod_flatMap_replicate _ n x (fun y => f (WD.mk y.2))
  have htL : ∀ n σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L n)).2.ρ σ ^ k) =
      ∑ i, (n i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ ^ k) := fun n σ k => by
    rw [trace_listSum]
    rw [sum_flatMap_replicate _ n x (fun y => LinearMap.trace ℂ _ (y.2.ρ σ ^ k))]
    simp only [nsmul_eq_mul, x]
  have hcc : ∀ i, ((c i : ℤ) : ℂ) = (((c i).toNat : ℕ) : ℂ) - (((-c i).toNat : ℕ) : ℂ) := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    push_cast; ring
  have htr : ∀ σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L fun i => (c i).toNat)).2.ρ σ ^ k) =
      LinearMap.trace ℂ _ ((listSum h (L fun i => (-c i).toNat)).2.ρ σ ^ k) := fun σ k => by
    rw [htL, htL, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have := hc (σ ^ k)
    simp only [map_pow, hcc] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPQ : f (WD.mk (listSum h (L fun i => (c i).toNat)).2) =
      f (WD.mk (listSum h (L fun i => (-c i).toNat)).2) :=
    hf2 _ _ fun σ => by
      rw [WD.charPol_mk, WD.charPol_mk]
      exact GlobalTheory.T.charpoly_eq_of_trace_powers _ _ _ _ (htr σ)
  rw [hfL, hfL] at hPQ
  have hz : ∀ i, f (WD.mk (a i)) ^ c i =
      f (WD.mk (a i)) ^ (c i).toNat * (f (WD.mk (a i)) ^ (-c i).toNat)⁻¹ := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hPQ, mul_inv_cancel]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_virtual_character : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ), (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) → ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ), (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) → ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  first | exact @GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | exact GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | (intros; apply GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
open ReciprocityTheory.Gal

namespace GlobalTheory.CofinGen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_pow_smul_eq {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (n : ℕ) (m : M) : ∃ m', ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by simp⟩
  | succ n ih =>
    obtain ⟨m1, h1⟩ := ih m
    obtain ⟨m2, h2⟩ := hd m1
    exact ⟨m2, by rw [pow_succ, mul_smul, h2, h1]⟩

theorem baer_of_div (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) : Module.Baer O M := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have : (⟨x, hx⟩ : (⊥ : Ideal O)) = 0 := Subtype.ext (by simpa using hx)
    rw [this]; simp
  · obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
    subst hn
    obtain ⟨m, hm⟩ := exists_pow_smul_eq hd n (g ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩)
    refine ⟨LinearMap.toSpanSingleton O M m, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : (⟨c * ϖ ^ n, hx⟩ : Ideal.span {ϖ ^ n}) =
        c • ⟨ϖ ^ n, Ideal.mem_span_singleton_self _⟩ := Subtype.ext rfl
    rw [this, map_smul, ← hm, LinearMap.toSpanSingleton_apply, mul_smul]

theorem KO_div (hϖ : Irreducible ϖ) (m : Formalism.NG.KO O) : ∃ m', ϖ • m' = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * x), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem exists_inj (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (hd : ∀ m : M, ∃ m', ϖ • m' = m) (y : M) (hy : y ≠ 0) (hy' : ϖ • y = 0) :
    ∃ i : Formalism.NG.KO O →ₗ[O] M, Function.Injective i ∧ y ∈ LinearMap.range i := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by
    simpa using hϖ.ne_zero
  set w : FractionRing O := (algebraMap O (FractionRing O) ϖ)⁻¹ with hw
  have hinj : Function.Injective (LinearMap.toSpanSingleton O (FractionRing O) w) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_eq_zero] at hc
    rcases hc with hc | hc
    · simpa using hc
    · exact absurd hc (inv_ne_zero h0)
  obtain ⟨h, hh⟩ := (baer_of_div hϖ hd).extension_property _ hinj
    (LinearMap.toSpanSingleton O M y)
  have hw1 : h w = y := by simpa using LinearMap.congr_fun hh 1
  have h1 : h 1 = 0 := by
    have : (1 : FractionRing O) = ϖ • w := by rw [Algebra.smul_def, hw, mul_inv_cancel₀ h0]
    rw [this, map_smul, hw1, hy']
  have hle : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker h := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
    rw [LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  refine ⟨Submodule.liftQ _ h hle, ?_, ⟨Submodule.Quotient.mk w, by simpa using hw1⟩⟩
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => ?_
  rw [LinearMap.mem_ker] at hx
  by_cases hx0 : x = 0
  · subst hx0; exact Submodule.zero_mem _
  rcases ValuationRing.isInteger_or_isInteger O x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Submodule.mem_one.2 ⟨c, hc⟩
  · by_cases hu : IsUnit c
    · obtain ⟨d, hd'⟩ := hu.exists_right_inv
      refine Submodule.mem_one.2 ⟨d, ?_⟩
      have := congrArg (algebraMap O (FractionRing O)) hd'
      rw [map_mul, hc, map_one] at this
      field_simp at this
      exact this
    · exfalso
      have hm : c ∈ IsLocalRing.maximalIdeal O := hu
      rw [hϖ.maximalIdeal_eq] at hm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
      have : w = d • x := by
        rw [map_mul] at hc
        rw [Algebra.smul_def, hw]
        field_simp at hc ⊢
        rw [← hc]
      apply hy
      rw [← hw1, this, map_smul, hx, smul_zero]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_socle {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (T : Submodule O Y) (y : Y) (hy : y ∈ T) (h0 : y ≠ 0) :
    ∃ z ∈ T, z ≠ 0 ∧ ϖ • z = 0 := by
  obtain ⟨n, hn⟩ := hp y
  induction n generalizing y with
  | zero => exact absurd (by simpa using hn) h0
  | succ n ih =>
    by_cases h : ϖ • y = 0
    · exact ⟨y, hy, h0, h⟩
    · exact ih (ϖ • y) (T.smul_mem _ hy) h (by rw [← mul_smul, ← pow_succ, hn])

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_fiber {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (y : Y) : {z : Y | ϖ • z = y}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Y | ϖ • z = y} with h | ⟨z, hz⟩
  · rw [h]; exact Set.finite_empty
  · refine (hf.image (fun t => z + t)).subset fun x hx => ⟨x - z, ?_, by simp⟩
    simp only [Set.mem_setOf_eq] at hz hx ⊢
    rw [smul_sub, hz, hx, sub_self]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_pow {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (n : ℕ) : {z : Y | ϖ ^ n • z = 0}.Finite := by
  induction n with
  | zero => exact (Set.finite_singleton 0).subset fun x hx => by simpa using hx
  | succ n ih =>
    refine (ih.biUnion fun y _ => finite_fiber hf y).subset fun x hx => ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
    exact ⟨ϖ • x, by rw [← mul_smul, ← pow_succ, hx], rfl⟩

def pw (ϖ : O) (Y : Type) [AddCommGroup Y] [Module O Y] (n : ℕ) : Submodule O Y :=
  LinearMap.range (ϖ ^ n • LinearMap.id : Y →ₗ[O] Y)

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_pw {Y : Type} [AddCommGroup Y] [Module O Y] {n : ℕ} {y : Y} :
    y ∈ pw ϖ Y n ↔ ∃ z, ϖ ^ n • z = y := Iff.rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem pw_anti {Y : Type} [AddCommGroup Y] [Module O Y] {n m : ℕ} (h : n ≤ m) :
    pw ϖ Y m ≤ pw ϖ Y n := by
  intro y hy
  obtain ⟨z, rfl⟩ := mem_pw.1 hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact mem_pw.2 ⟨ϖ ^ k • z, by rw [pow_add, mul_smul]⟩


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_uniform {Y : Type} [AddCommGroup Y] [Module O Y] {S : Set Y} (hS : S.Finite) :
    ∃ N, ∀ y ∈ S, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
  have h1 : ∀ y : Y, ∃ N, y ∈ pw ϖ Y N → y ∈ ⨅ n, pw ϖ Y n := by
    intro y
    by_cases h : y ∈ ⨅ n, pw ϖ Y n
    · exact ⟨0, fun _ => h⟩
    · rw [Submodule.mem_iInf, not_forall] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, fun h => absurd h hn⟩
  choose f hf using h1
  obtain ⟨N, hN⟩ := (hS.image f).bddAbove
  exact ⟨N, fun y hy h => hf y (pw_anti (hN ⟨y, hy, rfl⟩) h)⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem iInf_div {Y : Type} [AddCommGroup Y] [Module O Y]
    (hf : {y : Y | ϖ • y = 0}.Finite) (m : (⨅ n, pw ϖ Y n : Submodule O Y)) :
    ∃ m', ϖ • m' = m := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) (finite_fiber hf m.1)
  obtain ⟨z, hz⟩ := mem_pw.1 ((Submodule.mem_iInf _).1 m.2 (N + 1))
  have h1 : ϖ • ϖ ^ N • z = m.1 := by rw [← mul_smul, ← pow_succ', hz]
  exact ⟨⟨ϖ ^ N • z, hN _ h1 (mem_pw.2 ⟨z, rfl⟩)⟩, Subtype.ext h1⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem finite_of_iInf_bot {Y : Type} [AddCommGroup Y] [Module O Y]
    (hp : ∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) (hf : {y : Y | ϖ • y = 0}.Finite)
    (hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥) : Finite Y := by
  obtain ⟨N, hN⟩ := exists_uniform (ϖ := ϖ) hf
  have : ∀ y : Y, ϖ ^ N • y = 0 := by
    intro y
    by_contra h
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp (pw ϖ Y N) _ (mem_pw.2 ⟨y, rfl⟩) h
    have := hN z hz1 hz
    rw [hb] at this
    exact hz0 (by simpa using this)
  exact Set.finite_univ_iff.1 ((finite_pow hf N).subset fun y _ => this y)

theorem aux (hϖ : Irreducible ϖ) (k : ℕ) : ∀ {Y : Type} [AddCommGroup Y] [Module O Y],
    (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) → {y : Y | ϖ • y = 0}.Finite →
    {y : Y | ϖ • y = 0}.ncard = k →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Y _ _ hp hf hk
  by_cases hb : (⨅ n, pw ϖ Y n : Submodule O Y) = ⊥
  · exact ⟨0, Y, inferInstance, inferInstance, finite_of_iInf_bot hp hf hb,
      ⟨(LinearEquiv.uniqueProd).symm⟩⟩
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hb
    obtain ⟨z, hz, hz0, hz1⟩ := exists_socle hp _ y hy hy0
    obtain ⟨i0, hi0, x, hx⟩ := exists_inj hϖ (iInf_div hf) ⟨z, hz⟩
      (fun h => hz0 (congrArg Subtype.val h)) (Subtype.ext hz1)
    set i : Formalism.NG.KO O →ₗ[O] Y := (Submodule.subtype _).comp i0 with hi
    have hinj : Function.Injective i := Subtype.val_injective.comp hi0
    have hxz : i x = z := congrArg Subtype.val hx
    obtain ⟨r, hr⟩ := (baer_of_div hϖ (KO_div hϖ)).extension_property i hinj LinearMap.id
    have hri : ∀ t, r (i t) = t := fun t => LinearMap.congr_fun hr t
    have hsub : Subtype.val '' {y : LinearMap.ker r | ϖ • y = 0} ⊂ {y : Y | ϖ • y = 0} := by
      refine ⟨?_, fun h => ?_⟩
      · rintro _ ⟨t, ht, rfl⟩
        exact congrArg Subtype.val ht
      · obtain ⟨t, -, ht⟩ := h hz1
        have h2 : r z = 0 := ht ▸ t.2
        rw [← hxz, hri] at h2
        exact hz0 (by rw [← hxz, h2, map_zero])
    have hf' : {y : LinearMap.ker r | ϖ • y = 0}.Finite :=
      (hf.subset hsub.1).of_finite_image Subtype.val_injective.injOn
    have hlt := Set.ncard_lt_ncard hsub hf
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, hk] at hlt
    obtain ⟨a, F, _, _, hF, ⟨e⟩⟩ := ih _ hlt (Y := LinearMap.ker r)
      (fun t => (hp t.1).imp fun n hn => Subtype.ext hn) hf' rfl
    have hbij : Function.Bijective (i.coprod (LinearMap.ker r).subtype) := by
      constructor
      · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        rintro ⟨s, t⟩ h
        have h1 : i s + t.1 = 0 := h
        have h2 := congrArg r h1
        rw [map_add (f := _), hri, t.2, add_zero, map_zero] at h2
        subst h2
        rw [map_zero, zero_add] at h1
        exact Prod.ext rfl (Subtype.ext h1)
      · intro y
        exact ⟨(r y, ⟨y - i (r y), by simp [hri]⟩), by simp⟩
    refine ⟨a + 1, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
    exact (LinearEquiv.ofBijective _ hbij).symm ≪≫ₗ (LinearEquiv.refl O _).prodCongr e ≪≫ₗ
      (LinearEquiv.prodAssoc O _ _ _).symm ≪≫ₗ
      (Fin.consLinearEquiv O fun _ : Fin (a + 1) => Formalism.NG.KO O).prodCongr (LinearEquiv.refl O F)

theorem exists_equiv_pi_prod_finite :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧
      Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  intro O _ _ _ ϖ hϖ Y _ _ hp hf
  exact aux hϖ _ hp hf rfl

end GlobalTheory.CofinGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFiniteStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
end
end
