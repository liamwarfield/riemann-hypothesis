module

public import Development.EtaleCohomology.DivisorCycles.CycleCount

@[expose] public section

section -- merged from Development.EtaleCohomology.DivisorCycles.ChainPf
open Matrix MvPolynomial
namespace LateralTheory.DivDb.ChainPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N M : ℕ}

noncomputable def lin (φ : Mat C N →ₗ[C] Mat C M) (q : Fin M × Fin M) : MP C N :=
  ∑ r : Fin N × Fin N, MvPolynomial.C (φ (Matrix.single r.1 r.2 1) q.1 q.2) * X r

theorem sum_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ∑ r : Fin N × Fin N, φ (Matrix.single r.1 r.2 1) q.1 q.2 * x r.1 r.2 = φ x q.1 q.2 := by
  have hx : x = ∑ r : Fin N × Fin N, x r.1 r.2 • Matrix.single r.1 r.2 (1 : C) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [Matrix.smul_single]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem ev_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ev x (lin φ q) = φ x q.1 q.2 := by
  rw [← sum_lin φ x q]; simp [ev, lin]

theorem dAt_lin (φ : Mat C N →ₗ[C] Mat C M) (x Y : Mat C N) (q : Fin M × Fin M) :
    dAt (lin φ q) x Y = φ Y q.1 q.2 := by
  rw [← sum_lin φ Y q]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dAt, lin, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [ev, Pi.single_apply, Finset.sum_ite_eq']

theorem ev_bind (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (f : MP C M) :
    ev x (bind₁ (lin φ) f) = ev (φ x) f := by
  show eval₂Hom (RingHom.id C) _ (bind₁ (lin φ) f) = eval₂Hom (RingHom.id C) _ f
  rw [eval₂Hom_bind₁]
  congr 2; funext q; exact ev_lin φ x q

theorem dAt_add (f g : MP C N) (x Y : Mat C N) : dAt (f + g) x Y = dAt f x Y + dAt g x Y := by
  simp [dAt, ev, add_mul, Finset.sum_add_distrib]

theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  simp only [dAt, Derivation.leibniz, smul_eq_mul, ev, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem dAt_C (a : C) (x Y : Mat C N) : dAt (MvPolynomial.C a : MP C N) x Y = 0 := by
  simp [dAt, ev]

theorem chain_of : Chain := by
  intro C _ N M φ f
  refine ⟨bind₁ (lin φ) f, fun x => ?_, ?_⟩
  · exact ev_bind φ x f
  · induction f using MvPolynomial.induction_on with
    | C a => intro x Y; simp [dAt_C]
    | add f g hf hg => intro x Y; rw [map_add (f := _), dAt_add, dAt_add, hf, hg]
    | mul_X f q hf =>
      intro x Y
      rw [map_mul, bind₁_X_right, dAt_mul, dAt_mul, hf, dAt_lin, ev_lin]
      rw [ev_bind]
      simp [dAt, ev, pderiv_X, Pi.single_apply]

end LateralTheory.DivDb.ChainPf

theorem LateralTheory.DivDb.Chain_of : LateralTheory.DivDb.Chain := LateralTheory.DivDb.ChainPf.chain_of
end

section -- merged from Development.EtaleCohomology.DivisorCycles.DegPoly2
open Matrix

namespace LateralTheory.DivDb.DegPoly₂

theorem exists_minor {F ι : Type*} [Field F] [Fintype ι] {k : ℕ} (v : Fin k → ι → F)
    (hv : LinearIndependent F v) :
    ∃ l : Fin k → ι, (Matrix.of fun a b => v b (l a)).det ≠ 0 := by
  classical
  let r : ι → Fin k → F := fun i b => v b i
  let V : Matrix ι (Fin k) F := Matrix.of r
  have h1 : V.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have : V.col = v := by funext b i; rfl
    rw [this, finrank_span_eq_card hv, Fintype.card_fin]
  have h2 : Submodule.span F (Set.range r) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Matrix.rank_eq_finrank_span_row V
    rw [h1] at this
    rw [Module.finrank_fin_fun]
    exact this.symm
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' F r
  rw [h2] at hsp
  let bs := Module.Basis.mk hli (by rw [hsp])
  have : Finite κ := Module.Finite.finite_basis bs
  haveI : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = k := by
    rw [← Module.finrank_eq_card_basis bs, Module.finrank_fin_fun]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ?_⟩
  have hrows : LinearIndependent F (Matrix.of fun a' b => v b ((a ∘ e) a')).row :=
    hli.comp e e.injective
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hrows
  exact hrows.ne_zero

theorem not_li_iff {F ι : Type*} [Field F] [Fintype ι] {k : ℕ} (v : Fin k → ι → F) :
    ¬ LinearIndependent F v ↔ ∀ l : Fin k → ι, (Matrix.of fun a b => v b (l a)).det = 0 := by
  classical
  constructor
  · intro h l
    rw [Fintype.not_linearIndependent_iff] at h
    obtain ⟨g, hg, i, hi⟩ := h
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨g, fun h0 => hi (by rw [h0]; rfl), ?_⟩
    funext a
    have := congrFun hg (l a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  · intro h hv
    obtain ⟨l, hl⟩ := exists_minor v hv
    exact hl (h l)

theorem deg_iff_not_li {F : Type} [Field F] {N n : ℕ} (x : Mat F N) :
    Deg n x ↔ ¬ LinearIndependent F (fun (b : Fin (n+1)) (p : Fin N × Fin N) => (x ^ (b : ℕ)) p.1 p.2) := by
  classical
  rw [Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨q, hq0, hqd, hqx⟩
    refine ⟨fun b => q.coeff b, ?_, ?_⟩
    · have h1 : q = ∑ i ∈ Finset.range (n+1), Polynomial.monomial i (q.coeff i) :=
        q.as_sum_range' (n+1) (by omega)
      have h2 : Polynomial.aeval x q = ∑ b : Fin (n+1), q.coeff b • x ^ (b : ℕ) := by
        conv_lhs => rw [h1]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.aeval x (Polynomial.monomial i (q.coeff i)))]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Polynomial.aeval_monomial, Algebra.smul_def]
      rw [h2] at hqx
      funext p
      have := congrArg (fun M : Mat F N => M p.1 p.2) hqx
      simpa [Matrix.sum_apply, Finset.sum_apply] using this
    · by_contra hall
      push Not at hall
      apply hq0
      ext i
      by_cases hi : i < n + 1
      · simpa using hall ⟨i, hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · rintro ⟨g, hg, i, hi⟩
    refine ⟨∑ b : Fin (n+1), Polynomial.monomial (b : ℕ) (g b), ?_, ?_, ?_⟩
    · intro h0
      apply hi
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (i : ℕ)) h0
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single i] at this
      · simpa using this
      · intro b _ hb
        simp [Finsupp.single_apply, show (b : ℕ) ≠ (i : ℕ) from fun h => hb (Fin.ext h)]
      · simp
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro b _
      exact (Polynomial.natDegree_monomial_le _).trans (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum]
        ext j k
        have := congrFun hg (j, k)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        simp only [Polynomial.aeval_monomial, Matrix.sum_apply, Matrix.zero_apply]
        rw [← this]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [← Algebra.smul_def, Matrix.smul_apply, smul_eq_mul]

noncomputable def gen (C : Type) [Field C] (N : ℕ) : Mat (MP C N) N :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

noncomputable def fam (C : Type) [Field C] (N n : ℕ) : Set (MP C N) :=
  Set.range fun l : Fin (n+1) → Fin N × Fin N =>
    (Matrix.of fun a b : Fin (n+1) => (gen C N ^ (b : ℕ)) (l a).1 (l a).2).det

theorem eval_fam {C : Type} [Field C] {N n : ℕ} {F : Type} [Field F] [Algebra C F] (x : Mat F N)
    (l : Fin (n+1) → Fin N × Fin N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2)
      ((Matrix.of fun a b : Fin (n+1) => (gen C N ^ (b : ℕ)) (l a).1 (l a).2).det) =
    (Matrix.of fun a b : Fin (n+1) => (x ^ (b : ℕ)) (l a).1 (l a).2).det := by
  set φ := MvPolynomial.aeval (R := C) (fun p : Fin N × Fin N => x p.1 p.2)
  have hG : φ.mapMatrix (gen C N) = x := by
    ext i j; simp [gen, φ, AlgHom.mapMatrix_apply]
  have hpow : ∀ b : ℕ, φ.mapMatrix (gen C N ^ b) = x ^ b := fun b => by rw [map_pow, hG]
  rw [AlgHom.map_det]
  congr 1
  ext a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← hpow b,
    AlgHom.mapMatrix_apply, Matrix.map_apply]

theorem DegPoly_of : DegPoly := by
  intro C _ N n
  refine ⟨fam C N n, ?_⟩
  intro F _ _ x
  rw [deg_iff_not_li, not_li_iff]
  constructor
  · rintro h f ⟨l, rfl⟩
    rw [eval_fam]; exact h l
  · intro h l
    rw [← eval_fam (C := C)]; exact h _ ⟨l, rfl⟩

end LateralTheory.DivDb.DegPoly₂
end

section -- merged from Development.EtaleCohomology.DivisorCycles.CycleCountPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.CycleCountPf
open LateralTheory.DivDb

def CycSpec : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Disj y π p →
  ∃ l : Fin n → C, Function.Injective l ∧ ∀ j, y.charpoly.IsRoot (l j) ∧
    ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0

def FixScal : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C), Sys p → (∀ j, y * p j = p (π j) * y) → Deg n y →
  Disj y π p → Function.Injective l →
  (∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0) →
  ∀ i, π i = i → ∃ c : C, y * p i = c • p i

theorem CycleCount_of (h1 : CycSpec) (h2 : FixScal) : CycleCount := by
  intro C _ _ _ N n p y π hp hy hyp hdeg hd
  obtain ⟨l, hl, hr⟩ := h1 C N n p y π hp hy hyp hd
  exact ⟨⟨l, hl, fun j => (hr j).1⟩, h2 C N n p y π l hp hyp hdeg hd hl (fun j => (hr j).2)⟩

end LateralTheory.DivDb.CycleCountPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.ExpVanPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ExpVanPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C] {N : ℕ}

noncomputable def E (Y : Mat C N) : Fin N × Fin N → PowerSeries C :=
  fun p => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) p.1 p.2

noncomputable def F (Y : Mat C N) (f : MP C N) : PowerSeries C := MvPolynomial.aeval (E Y) f

theorem deriv_E (Y : Mat C N) (p : Fin N × Fin N) :
    PowerSeries.derivative (R := C) (E Y p) = MvPolynomial.aeval (E Y) (DX Y (MvPolynomial.X p)) := by
  rw [DX, MvPolynomial.mkDerivation_X]
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_derivative, map_sum, map_sum]
  simp only [E, PowerSeries.coeff_mk, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  have hn : ((n + 1).factorial : C)⁻¹ * (n + 1) = (n.factorial : C)⁻¹ := by
    have : ((n:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ]; push_cast; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Algebra.smul_def, map_smul, PowerSeries.coeff_mk, smul_eq_mul, ← hn]; ring

omit [CharZero C] in
theorem cc_F (Y : Mat C N) (f : MP C N) : PowerSeries.constantCoeff (F Y f) = ev 1 f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F, ev]
  | add p q hp hq => simp only [F, ev, map_add (f := _)] at *; rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, ev, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X] at *
    rw [hp]; congr 1
    simp [E]

theorem deriv_F (Y : Mat C N) (f : MP C N) :
    PowerSeries.derivative (R := C) (F Y f) = F Y (DX Y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [F]
  | add p q hp hq => simp only [F, map_add (f := _)] at * <;> rw [hp, hq]
  | mul_X p i hp =>
    simp only [F, map_mul, Derivation.leibniz, MvPolynomial.aeval_X, smul_eq_mul, map_add (f := _)] at *
    rw [hp, ← deriv_E]

theorem coeff_F (hT : TanField) (S : Submonoid (Mat C N)) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) :
    ∀ k, ∀ f ∈ Van (S : Set (Mat C N)), PowerSeries.coeff k (F Y f) = 0 := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_F]
    exact hf 1 S.one_mem
  | succ k ih =>
    intro f hf
    have h := ih _ ((hT C N S Y).1 hY f hf)
    rw [← deriv_F, PowerSeries.coeff_derivative] at h
    have : ((k:C) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp h).resolve_right this

end LateralTheory.DivDb.ExpVanPf

namespace LateralTheory.DivDb
theorem ExpVan_of (hT : TanField) : ExpVan := by
  intro C _ _ N S Y hY f hf
  ext k
  have h := ExpVanPf.coeff_F hT S Y hY k f hf
  rw [map_zero]; exact h
end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.TangentDegree
open Matrix

namespace LateralTheory.DivDb.TangentDegree
open LateralTheory.DivDb

variable {C : Type} [Field C]

lemma aeval_self_eq_ev {N : ℕ} (x : Mat C N) (f : MP C N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = ev x f := rfl

noncomputable def U {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) i j

noncomputable def Z {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => (((k + 1).factorial : C)⁻¹ • Y ^ (k + 1)) i j

lemma U_eq {N : ℕ} (Y : Mat C N) : U Y = 1 + (PowerSeries.X : PowerSeries C) • Z Y := by
  ext i j k
  rcases k with _ | k
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      PowerSeries.coeff_zero_X_mul, add_zero, Matrix.one_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
    split_ifs <;> simp
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      PowerSeries.coeff_succ_X_mul, Matrix.one_apply]
    split_ifs <;> simp

lemma constantCoeff_Z {N : ℕ} (Y : Mat C N) (i j : Fin N) : PowerSeries.constantCoeff (Z Y i j) = Y i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Z, PowerSeries.coeff_mk]

lemma map_aeval_ring {R S σ : Type} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S] (k : R →+* S)
    (hk : k.comp (algebraMap C R) = algebraMap C S) (x : σ → R) (f : MvPolynomial σ C) :
    k (MvPolynomial.aeval x f) = MvPolynomial.aeval (k ∘ x) f := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hk]

lemma van_of (hD : DegPoly) {N n : ℕ} (S : Submonoid (Mat C N)) (hS : ∀ x ∈ S, Deg n x) :
    ∃ 𝓕 : Set (MP C N), (∀ (F : Type) [Field F] [Algebra C F] (x : Mat F N),
      Deg n x ↔ ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = 0) ∧
      ∀ f ∈ 𝓕, f ∈ Van (S : Set (Mat C N)) := by
  obtain ⟨𝓕, h𝓕⟩ := hD C N n
  refine ⟨𝓕, h𝓕, fun f hf x hx => ?_⟩
  rw [← aeval_self_eq_ev]
  exact (h𝓕 C x).1 (hS x hx) f hf

lemma tan_deg (hE : ExpVan) (hD : DegPoly) [CharZero C] {N n : ℕ} (S : Submonoid (Mat C N))
    (hS : ∀ x ∈ S, Deg n x) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) : Deg n Y := by
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  let F := FractionRing (PowerSeries C)
  let ι : PowerSeries C →+* F := algebraMap (PowerSeries C) F
  let alg : Algebra C F := (ι.comp (algebraMap C (PowerSeries C))).toAlgebra
  have hιinj : Function.Injective ι := IsFractionRing.injective (PowerSeries C) F
  have hmap : ∀ (M : Matrix (Fin N) (Fin N) (PowerSeries C)) (f : MP C N),
      @MvPolynomial.aeval C F _ _ _ alg (fun p : Fin N × Fin N => (M.map ι) p.1 p.2) f
        = ι (MvPolynomial.aeval (fun p : Fin N × Fin N => M p.1 p.2) f) := by
    intro M f
    rw [map_aeval_ring (S := F) ι rfl]
    rfl
  have hUF : Deg n ((U Y).map ι) := by
    refine (@h𝓕 F _ alg ((U Y).map ι)).2 fun f hf => ?_
    rw [hmap]
    have := hE C N S Y hY f (hvan f hf)
    simp only [U] at this ⊢
    rw [this, map_zero]
  set s : F := ι PowerSeries.X with hsdef
  have hs : s ≠ 0 := (map_ne_zero_iff ι hιinj).2 PowerSeries.X_ne_zero
  have hUZ : (U Y).map ι = 1 + s • (Z Y).map ι := by
    rw [U_eq]; ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      Matrix.one_apply, hsdef]
    split_ifs <;> simp
  have hZF : Deg n ((Z Y).map ι) := by
    obtain ⟨q, hq0, hqd, hqx⟩ := hUF
    refine ⟨q.comp (Polynomial.C s * Polynomial.X + Polynomial.C 1), ?_, ?_, ?_⟩
    · intro h
      rcases Polynomial.comp_eq_zero_iff.1 h with h | ⟨_, h⟩
      · exact hq0 h
      · have := congrArg Polynomial.natDegree h
        rw [Polynomial.natDegree_linear hs, Polynomial.natDegree_C] at this
        exact one_ne_zero this
    · rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hs, mul_one]; exact hqd
    · rw [Polynomial.aeval_comp]
      convert hqx using 2
      rw [hUZ]
      simp [Algebra.algebraMap_eq_smul_one, add_comm]
  have hZ0 : ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => Z Y p.1 p.2) f = 0 := by
    intro f hf
    have := (@h𝓕 F _ alg ((Z Y).map ι)).1 hZF f hf
    rw [hmap] at this
    exact (map_eq_zero_iff ι hιinj).1 this
  refine (h𝓕 C Y).2 fun f hf => ?_
  have hk : (PowerSeries.constantCoeff (R := C)).comp (algebraMap C (PowerSeries C)) = algebraMap C C := by
    ext c; simp
  have := congrArg PowerSeries.constantCoeff (hZ0 f hf)
  rw [map_aeval_ring _ hk, map_zero] at this
  convert this using 2
  congr 1
  funext p
  simp [constantCoeff_Z]

theorem TanDeg_of (hE : ExpVan) (hD : DegPoly) : TanDeg := by
  intro C _ _ N n S hS
  refine ⟨fun x hx => ?_, fun Y hY => tan_deg hE hD S hS Y hY⟩
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  refine (h𝓕 C x).2 fun f hf => ?_
  rw [aeval_self_eq_ev]
  exact hx f (hvan f hf)

end LateralTheory.DivDb.TangentDegree
end

section -- merged from Development.EtaleCohomology.DivisorCycles.SemisPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.SemisPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def img {A : Subalgebra C (Mat C N)} (I : Ideal A) : Submodule C (Fin N → C) :=
  Submodule.span C {w | ∃ x ∈ I, ∃ v, w = (x : Mat C N) *ᵥ v}

lemma img_step {A : Subalgebra C (Mat C N)} (J I : Ideal A) {x : A} (hx : x ∈ J) {u : Fin N → C}
    (hu : u ∈ img I) : (x : Mat C N) *ᵥ u ∈ img (J * I) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

lemma img_bot {A : Subalgebra C (Mat C N)} : img (⊥ : Ideal A) = ⊥ := by
  rw [img, Submodule.span_eq_bot]
  rintro w ⟨x, hx, v, rfl⟩
  rw [Submodule.mem_bot] at hx
  simp [hx]

lemma conj_pow (P B Q : Mat C N) (h : Q * P = 1) (n : ℕ) : (P * B * Q) ^ (n + 1) = P * B ^ (n + 1) * Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ B (n+1)]
    calc P * B ^ (n + 1) * Q * (P * B * Q) = P * B ^ (n + 1) * (Q * P) * B * Q := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring

lemma nil_conj (P B Q : Mat C N) (h : Q * P = 1) (hB : IsNilpotent B) : IsNilpotent (P * B * Q) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k + 1, ?_⟩
  rw [conj_pow P B Q h, pow_succ, hk]; simp

lemma inv_mul_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

lemma mul_inv_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Semis_of : Semis := by
  intro Γ C _ _ N ρ A hss hn hk Y hYA hY

  let S : Set (Mat C N) := {Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}
  let U : Submodule C (Fin N → C) := Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}
  have hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨Z, ⟨hZA, hZ⟩, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩,
        (ρ g : Mat C N) *ᵥ v, ?_⟩
      · intro a ha
        have ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A := hn g⁻¹ a ha
        rw [inv_inv] at ha'
        have := nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z)
          (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')
        convert this using 1
        calc a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N))
            = ((ρ g : Mat C N) * (ρ g⁻¹ : Mat C N)) * a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N)) := by
              rw [mul_inv_rho]; simp
          _ = _ := by noncomm_ring
      · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨W, hcompl, hWst⟩ := hss U hUst
  have hWA := hk W hWst
  have hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0 := by
    intro Z hZ w hw
    have h1 : Z *ᵥ w ∈ U := Submodule.subset_span ⟨Z, hZ, w, rfl⟩
    have h2 : Z *ᵥ w ∈ W := hWA Z hZ.1 w hw
    have := hcompl.inf_eq_bot
    have h3 : Z *ᵥ w ∈ U ⊓ W := ⟨h1, h2⟩
    rw [this] at h3
    exact (Submodule.mem_bot C).1 h3
  have : IsArtinianRing A := IsArtinianRing.of_finite C A
  let J : Ideal A := Ideal.jacobson ⊥
  have hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J := by
    intro Z hZ
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A)) := by
      obtain ⟨k, hk'⟩ := hZ.2 y y.2
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk'
    have hu := hnil.isUnit_one_add
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [Ideal.mem_bot]
    have h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1 := hu.val_inv_mul
    calc (↑hu.unit⁻¹ : A) * y * (⟨Z, hZ.1⟩ : A) + ↑hu.unit⁻¹ - 1
        = (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) - 1 := by noncomm_ring
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have key : ∀ k : ℕ, U ≤ img (J ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [Submodule.pow_one]
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      exact Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩
    | succ k ih =>
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      have hv : v ∈ U ⊔ W := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))
      rw [Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]
      exact img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)
  have hU : U = ⊥ := by
    have h := key m
    have hb : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]
    rw [hb, img_bot] at h
    exact le_bot_iff.1 h
  ext i j
  have hv : Y *ᵥ Pi.single j 1 ∈ U := Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩
  rw [hU, Submodule.mem_bot] at hv
  simpa using congrFun hv i
end LateralTheory.DivDb.SemisPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.MatUnitsOf
open Matrix

namespace LateralTheory.DivDb.MatrixUnitConstruction
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

def Pr (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) (x y : Mat C N) : Prop :=
  x ∈ A ∧ y ∈ A ∧ p i * x * p j = x ∧ p j * y * p i = y ∧ x * y = p i ∧ y * x = p j

def rel (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) : Prop := ∃ x y, Pr A p i j x y

section
variable {A : Subalgebra C (Mat C N)} {p : Fin n → Mat C N}

lemma idem (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq

lemma idemL (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, idem hp i]

lemma sand_left (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : p i * x = x := by
  conv_lhs => rw [← h]
  simp only [mul_assoc, idemL hp i]
  simpa only [mul_assoc] using h

lemma sand_right (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : x * p j = x := by
  conv_lhs => rw [← h]
  rw [mul_assoc (p i * x), idem hp j, h]

lemma pr_ne (hp : Sys p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : x ≠ 0 := by
  rintro rfl
  exact hp.2 i (by rw [← h.2.2.2.2.1, zero_mul])

lemma pr_symm {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : Pr A p j i y x :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma pr_refl (hp : Sys p) (hc : Corner A p) (i : Fin n) : Pr A p i i (p i) (p i) :=
  ⟨hc.1 i, hc.1 i, by rw [idem hp i, idem hp i], by rw [idem hp i, idem hp i], idem hp i, idem hp i⟩

lemma pr_trans (hp : Sys p) {i j k : Fin n} {x y x' y' : Mat C N} (h : Pr A p i j x y)
    (h' : Pr A p j k x' y') : Pr A p i k (x * x') (y' * y) := by
  refine ⟨A.mul_mem h.1 h'.1, A.mul_mem h'.2.1 h.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, sand_left hp h.2.2.1, mul_assoc, sand_right hp h'.2.2.1]
  · rw [← mul_assoc, sand_left hp h'.2.2.2.1, mul_assoc, sand_right hp h.2.2.2.1]
  · rw [show x * x' * (y' * y) = x * (x' * y') * y by simp only [mul_assoc], h'.2.2.2.2.1,
      sand_right hp h.2.2.1, h.2.2.2.2.1]
  · rw [show y' * y * (x * x') = y' * (y * x) * x' by simp only [mul_assoc], h.2.2.2.2.2,
      sand_right hp h'.2.2.2.1, h'.2.2.2.2.2]

lemma partner (hp : Sys p) (hc : Corner A p) (hA : NoNil A) {i j : Fin n} {Y : Mat C N}
    (hYA : Y ∈ A) (hYl : p i * Y = Y) (hYr : Y * p j = Y) (hY0 : Y ≠ 0) :
    ∃ w, Pr A p i j Y w := by
  obtain ⟨b, hb, hnil⟩ : ∃ b ∈ A, ¬ IsNilpotent (b * Y) := by
    by_contra h
    push Not at h
    exact hY0 (hA Y hYA h)
  have hwA : p j * b * p i ∈ A := A.mul_mem (A.mul_mem (hc.1 j) hb) (hc.1 i)
  obtain ⟨c, hc1⟩ := hc.2 (Y * b) (A.mul_mem hYA hb) i
  obtain ⟨d, hd1⟩ := hc.2 (b * Y) (A.mul_mem hb hYA) j
  have hYw : Y * (p j * b * p i) = c • p i := by
    rw [← hc1]
    calc Y * (p j * b * p i) = (Y * p j) * b * p i := by simp only [mul_assoc]
      _ = (p i * Y) * b * p i := by rw [hYr, hYl]
      _ = p i * (Y * b) * p i := by simp only [mul_assoc]
  have hwY : (p j * b * p i) * Y = d • p j := by
    rw [← hd1]
    calc p j * b * p i * Y = p j * b * (p i * Y) := by simp only [mul_assoc]
      _ = p j * b * (Y * p j) := by rw [hYl, hYr]
      _ = p j * (b * Y) * p j := by simp only [mul_assoc]
  have e1 : Y * (p j * b * p i) * Y = c • Y := by rw [hYw, smul_mul_assoc, hYl]
  have e2 : Y * (p j * b * p i) * Y = d • Y := by rw [mul_assoc, hwY, mul_smul_comm, hYr]
  have hcd : c = d := by
    by_contra h
    have h3 : (c - d) • Y = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact hY0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnil
    refine ⟨2, ?_⟩
    have h0 : Y * b * Y = 0 := by
      have : Y * b * Y = Y * (p j * b * p i) * Y := by
        rw [show Y * (p j * b * p i) * Y = (Y * p j) * b * (p i * Y) by simp only [mul_assoc], hYr, hYl]
      rw [this, e1, zero_smul]
    rw [pow_two, show b * Y * (b * Y) = b * (Y * b * Y) by simp only [mul_assoc], h0, mul_zero]
  refine ⟨c⁻¹ • (p j * b * p i), hYA, A.smul_mem hwA _, ?_, ?_, ?_, ?_⟩
  · rw [hYl, hYr]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, idem hp i, idemL hp j]
  · rw [mul_smul_comm, hYw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [smul_mul_assoc, hwY, ← hcd, smul_smul, inv_mul_cancel₀ hc0, one_smul]

lemma oneDim (hp : Sys p) (hc : Corner A p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y)
    {a : Mat C N} (ha : a ∈ A) : ∃ c : C, p i * a * p j = c • x := by
  obtain ⟨c, hc1⟩ := hc.2 (a * p j * y) (A.mul_mem (A.mul_mem ha (hc.1 j)) h.2.1) i
  refine ⟨c, ?_⟩
  have hy : y * p i = y := sand_right hp h.2.2.2.1
  have h1 : p i * a * p j * y = c • p i := by
    calc p i * a * p j * y = p i * a * p j * (y * p i) := by rw [hy]
      _ = p i * (a * p j * y) * p i := by simp only [mul_assoc]
      _ = c • p i := hc1
  calc p i * a * p j = p i * a * p j * p j := by rw [mul_assoc (p i * a) (p j) (p j), idem hp j]
    _ = p i * a * p j * (y * x) := by rw [h.2.2.2.2.2]
    _ = (p i * a * p j * y) * x := by simp only [mul_assoc]
    _ = c • x := by rw [h1, smul_mul_assoc, sand_left hp h.2.2.1]

lemma rel_equiv (hp : Sys p) (hc : Corner A p) : Equivalence (rel A p) := by
  refine ⟨fun i => ⟨_, _, pr_refl hp hc i⟩, ?_, ?_⟩
  · rintro i j ⟨_, _, h⟩
    exact ⟨_, _, pr_symm h⟩
  · rintro i j k ⟨_, _, h⟩ ⟨_, _, h'⟩
    exact ⟨_, _, pr_trans hp h h'⟩

end

open Classical in
theorem MatUnits_of : MatrixUnits₂ := by
  intro C _ N n A p hp hc hA
  have heq := rel_equiv hp hc
  let s : Setoid (Fin n) := ⟨rel A p, heq⟩
  obtain ⟨r, hr, hreq⟩ : ∃ r : Fin n → Fin n, (∀ i, ∃ x y, Pr A p i (r i) x y) ∧
      ∀ i j, rel A p i j → r i = r j :=
    ⟨fun i => (Quotient.mk s i).out, fun i => heq.symm (Quotient.mk_out (s := s) i),
      fun i j h => congrArg Quotient.out (Quotient.sound (s := s) h)⟩
  choose X Y hXY using hr
  have pairE : ∀ i j, rel A p i j → Pr A p i j (X i * Y j) (X j * Y i) := by
    intro i j h
    have h2 := hXY j
    rw [← hreq i j h] at h2
    exact pr_trans hp (hXY i) (pr_symm h2)
  refine ⟨fun i j => if rel A p i j then X i * Y j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).1
    · simp only [if_neg h]; exact A.zero_mem
  · intro i
    simp only [if_pos (heq.refl i)]
    exact (hXY i).2.2.2.2.1
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).2.2.1
    · simp only [if_neg h, mul_zero, zero_mul]
  · intro i j hne
    have h : rel A p i j := by
      by_contra h
      simp only [if_neg h] at hne
      exact hne rfl
    simp only [if_pos (heq.symm h)]
    exact pr_ne hp (pairE j i (heq.symm h))
  · intro i j k h1 h2
    have hij : rel A p i j := by
      by_contra h
      simp only [if_neg h] at h1
      exact h1 rfl
    have hjk : rel A p j k := by
      by_contra h
      simp only [if_neg h] at h2
      exact h2 rfl
    have hik := heq.trans hij hjk
    simp only [if_pos hij, if_pos hjk, if_pos hik]
    refine ⟨?_, pr_ne hp (pairE i k hik)⟩
    rw [show X i * Y j * (X j * Y k) = X i * (Y j * X j) * Y k by simp only [mul_assoc],
      (hXY j).2.2.2.2.2, ← hreq i j hij, sand_right hp (hXY i).2.2.1]
  · intro a ha i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact oneDim hp hc (pairE i j h) ha
    · refine ⟨0, ?_⟩
      simp only [if_neg h, smul_zero]
      by_contra h'
      obtain ⟨w, hw⟩ := partner (i := i) (j := j) hp hc hA (A.mul_mem (A.mul_mem (hc.1 i) ha) (hc.1 j))
        (by simp only [mul_assoc, idemL hp i]) (by rw [mul_assoc _ (p j), idem hp j]) h'
      exact h ⟨_, _, hw⟩

end LateralTheory.DivDb.MatrixUnitConstruction
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FinFinSub
section -- merged from Development.EtaleCohomology.DivisorCycles.FinSubOf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FiniteSubrepresentation

variable {K : Type} [Field K] {N n : ℕ}

theorem pow_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (k : ℕ) : X ^ k * T = T * Y ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem aeval_tw (X : Matrix (Fin N) (Fin N) K) (Y : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin N) (Fin n) K)
    (h : X * T = T * Y) (q : Polynomial K) : Polynomial.aeval X q * T = T * Polynomial.aeval Y q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, pow_tw X Y T h]

end LateralTheory.DivDb.FiniteSubrepresentation

theorem LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of : LateralTheory.DivDb.FinSub := by
  intro Γ K _ _ N n ρ r A B hS hρ
  obtain ⟨hBA, hAr, hspan⟩ := hS
  have hinj : ∀ w : Fin n → K, A *ᵥ w = 0 → w = 0 := by
    intro w hw
    have := congrArg (B *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, hBA] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨W'', hc, hs⟩ := hρ (W.map (Matrix.mulVecLin A)) (by
      rintro g _ ⟨w, hw, rfl⟩
      refine ⟨(r g : Matrix (Fin n) (Fin n) K) *ᵥ w, hW g w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAr g])
    refine ⟨W''.comap (Matrix.mulVecLin A), ?_, ?_⟩
    · constructor
      · rw [Submodule.disjoint_def]
        intro w hw hw'
        apply hinj
        have h1 : A *ᵥ w ∈ W.map (Matrix.mulVecLin A) := ⟨w, hw, rfl⟩
        exact (Submodule.disjoint_def.mp hc.disjoint) _ h1 hw'
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        have hv : A *ᵥ v ∈ W.map (Matrix.mulVecLin A) ⊔ W'' := by rw [hc.sup_eq_top]; trivial
        obtain ⟨y, ⟨w, hw, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
        rw [Submodule.mem_sup]
        refine ⟨w, hw, v - w, ?_, by abel⟩
        show A *ᵥ (v - w) ∈ W''
        rw [Matrix.mulVec_sub, ← hyz]
        simpa [Matrix.mulVecLin_apply] using hz
    · intro g v hv
      show A *ᵥ ((r g : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ W''
      rw [Matrix.mulVec_mulVec, ← hAr g, ← Matrix.mulVec_mulVec]
      exact hs g _ hv
  · apply le_antisymm
    · simpa using Matrix.rank_le_width A
    · have := Matrix.rank_mul_le_right B A
      rw [hBA, Matrix.rank_one] at this
      simpa using this
  · intro g
    rw [Matrix.mul_assoc, hAr g, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · intro g q
    constructor
    · intro h
      have h2 := aeval_tw _ _ A (hAr g) q
      rw [h, Matrix.zero_mul] at h2
      have h3 := congrArg (B * ·) h2
      simpa [← Matrix.mul_assoc, hBA] using h3.symm
    · intro h
      apply hspan
      intro T hT
      rw [aeval_tw _ _ T (hT g) q, h, Matrix.mul_zero]
end

namespace LateralTheory.Fin.FinSub
theorem finite_subrepresentation_etale_charpoly_instance : LateralTheory.DivDb.FinSub := by
  apply LateralTheory.DivDb.FiniteSubrepresentation.FinSub_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.FinSub := finite_subrepresentation_etale_charpoly_instance
end LateralTheory.Fin.FinSub
end
