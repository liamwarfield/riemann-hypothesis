module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHvPrimaryKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.AdaptExists

theorem mem_std {E : Type} [Field E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = v i := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem single_mem {E : Type} [Field E] {n : ℕ} (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro i
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem nat_smul_mem {E : Type} [Field E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (k : ℕ) {v : Fin n → E}
    (hv : v ∈ L) : (k : E) • v ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact L.toAddSubmonoid.nsmul_mem hv k

theorem exists_cols {E : Type} [Field E] {n : ℕ} (c : Fin n → Fin n → E) (hc : ∀ j, c j ∈ stdLat E n) :
    ∃ q : Matrix (Fin n) (Fin n) (𝓞 E), ∀ i j, algebraMap (𝓞 E) E (q i j) = c j i := by
  choose a ha using fun j => (mem_std (c j)).1 (hc j)
  exact ⟨Matrix.of fun i j => a j i, fun i j => ha j i⟩

theorem exists_adapt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n)
    (N M ℓ : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) (hl : ℓ.Prime) :
    ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  obtain ⟨hodd, -, hN⟩ := hL
  have hN0 : 0 < N := hodd.pos
  have hm : 0 < 2 * ℓ := Nat.mul_pos two_pos hl.pos
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  obtain ⟨k₂, ga, hk₂, hun, hin, hon⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted E H n Λ N hU hN0 (hN.trans inf_le_left) (2 * ℓ) hm
  obtain ⟨k₁, g, hk₁, -, hcols, hsp⟩ := LocBasis.exists_matrix_primeTo E n Λ.Ln N hN0 inf_le_right hN (2 * ℓ) hm
  set G := g.map (algebraMap (𝓞 E) E) with hG
  have hNe : ∀ j : Fin n, (N : E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.Ln := by
    intro j
    have h := hN (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) (single_mem (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  choose v hv hve using fun j => hsp _ (hNe j)
  obtain ⟨q, hq⟩ := exists_cols v hv
  obtain ⟨p, hp⟩ := exists_cols (fun j => (k₂ : E) • ga.mulVec (G.mulVec (Pi.single j 1)))
    (fun j => hin _ (hcols _ (single_mem j)).1)
  have hP : p.map (algebraMap (𝓞 E) E) = (k₂ : E) • (ga * G) := by
    ext i j
    rw [Matrix.map_apply, hp, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hGQ : G * q.map (algebraMap (𝓞 E) E) = ((k₁ * N : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h := congrFun (hve j) i
    simp only [Matrix.mul_apply, Matrix.map_apply, hq]
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h]
    simp [Matrix.one_apply, Pi.single_apply]
  have hprod : (p * q).map (algebraMap (𝓞 E) E) = ((k₁ * k₂ * N : ℕ) : E) • ga := by
    rw [Matrix.map_mul, hP, Matrix.smul_mul, Matrix.mul_assoc, hGQ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    push_cast
    ring
  have hk : Nat.Coprime (k₁ * k₂) (2 * ℓ) := Nat.Coprime.mul_left hk₁ hk₂
  refine ⟨{
    k := k₁ * k₂, k₁ := k₁, ga := ga, p := p, q := q, g := g
    odd := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right hk)
    cop := Nat.Coprime.coprime_mul_left_right hk
    cop₁ := Nat.Coprime.coprime_mul_left_right hk₁
    unitary := hun
    into := ?_
    onto := ?_
    prod := hprod
    cols := hcols
    spans := hsp
    gq := ?_ }, ?_⟩
  · intro w hw
    rw [Nat.cast_mul, mul_smul]
    exact nat_smul_mem _ _ (hin w hw)
  · intro w hw
    obtain ⟨u, hu, e⟩ := hon w hw
    exact ⟨(k₁ : E) • u, nat_smul_mem _ _ hu, by rw [Nat.cast_mul, mul_smul, e, Matrix.mulVec_smul]⟩
  · apply Matrix.map_injective hinj
    show (g * q).map _ = Matrix.map _ _
    rw [Matrix.map_mul, hGQ]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro j k
    apply hinj
    have he : ∀ a b, algebraMap (𝓞 E) E ((p * q) a b) = ((k₁ * k₂ * N : ℕ) : E) * ga a b :=
      fun a b => congrFun (congrFun hprod a) b
    have hb : ∀ a : 𝓞 E, algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq
    show algebraMap (𝓞 E) E (∑ i, H.bar ((p * q) i j) * (p * q) i k) =
      algebraMap (𝓞 E) E (if j = k then (((k₁ * k₂ * N) ^ 2 : ℕ) : 𝓞 E) else 0)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul (algebraMap (𝓞 E) E), hb, he, map_mul (IsCMField.complexConj E), map_natCast]
    have : ∀ i, ((k₁ * k₂ * N : ℕ) : E) * IsCMField.complexConj E (ga i j) * (((k₁ * k₂ * N : ℕ) : E) * ga i k) =
        ((k₁ * k₂ * N : ℕ) : E) ^ 2 * (IsCMField.complexConj E (ga i j) * ga i k) := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, hun]
    split_ifs <;> simp

end GlobalTheory.PlaceInt.AdaptExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsAdaptedSimilitudeDataAtPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_similitude_data_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  first | exact @GlobalTheory.PlaceInt.AdaptExists.exists_adapt | exact GlobalTheory.PlaceInt.AdaptExists.exists_adapt | (intros; apply GlobalTheory.PlaceInt.AdaptExists.exists_adapt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrix
set_option autoImplicit false

namespace GlobalTheory.TorsCount

theorem card_primary (C : Type) [AddCommGroup C] [Finite C] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {c : C // ∃ j : ℕ, ℓ ^ j • c = 0} = ℓ ^ (Nat.card C).factorization ℓ := by
  haveI := Fact.mk hℓ
  let P : Sylow ℓ (Multiplicative C) :=
    ⟨CommGroup.primaryComponent (Multiplicative C) ℓ, CommGroup.primaryComponent.isPGroup, fun {Q} hQ hle =>
      fun x hx => by
        obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
        exact CommGroup.mem_primaryComponent.2 ⟨k, congrArg Subtype.val hk⟩⟩
  have h := Sylow.card_eq_multiplicity P
  rw [Nat.card_congr (Multiplicative.toAdd (α := C))] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun c =>
    (CommGroup.mem_primaryComponent (G := Multiplicative C) (g := Multiplicative.ofAdd c)).symm)

theorem exists_inv {k m : ℕ} (h : Nat.Coprime k m) : ∃ a : ℤ, ∀ (U : Type) [AddCommGroup U] (u : U), m • u = 0 →
    a • k • u = u := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h)
  refine ⟨a, fun U _ u hu => ?_⟩
  have : (a * k + b * m) • u = u := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hu, smul_zero, add_zero] at this

theorem card_ker_eq {W U : Type} [AddCommGroup W] [AddCommGroup U] (Q G : W →ₗ[ℤ] W) (Q' : U →+ U) (ev : W →+ U)
    (k M ℓ : ℕ) (hk : Nat.Coprime k ℓ) (hk0 : k ≠ 0) (hM : M ≠ 0) (tf : ∀ (m : ℕ) (w : W), m ≠ 0 → m • w = 0 → w = 0)
    (hev : ∀ w, Q' (ev w) = ev (Q w)) (hGQ : ∀ w, G (Q w) = (k * M) • w) (hQG : ∀ w, Q (G w) = (k * M) • w)
    (hker : ∀ w, ev w = 0 ↔ ∃ b, w = M • b) (honto : ∀ u, M • u = 0 → ∃ w, ev w = u)
    (hQ' : ∀ u, Q' u = 0 → (k * M) • u = 0) :
    Nat.card {u : U // Q' u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      Nat.card {c : W ⧸ LinearMap.range Q // ∃ j : ℕ, ℓ ^ j • c = 0} := by
  have hM0 : ∀ w, ev (M • w) = 0 := fun w => (hker _).2 ⟨w, rfl⟩
  let φ : (W ⧸ LinearMap.range Q) →ₗ[ℤ] U := (LinearMap.range Q).liftQ (ev.toIntLinearMap ∘ₗ G) (by
    rintro _ ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
    rw [hGQ, mul_comm, mul_smul, hM0])
  have hφ : ∀ w, φ (Submodule.Quotient.mk w) = ev (G w) := fun w => rfl
  have hφk : ∀ c, φ c = 0 → k • c = 0 := fun c hc => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨b, hb⟩ := (hker _).1 ((hφ w).symm.trans hc)
    have h1 : M • (k • w - Q b) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hQG, hb, map_nsmul, sub_self]
    have h2 := sub_eq_zero.1 (tf M _ hM h1)
    change (LinearMap.range Q).mkQ (k • w) = 0
    rw [h2]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun c => ⟨φ c.1, ?_, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ c.1
    rw [← hw, hφ, hev, hQG, mul_comm, mul_smul, hM0]
  · obtain ⟨j, hj⟩ := c.2
    exact ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · rintro ⟨c, i, hi⟩ ⟨d, j, hj⟩ h
    have h1 : φ (c - d) = 0 := by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right (i + j))
    have h2 := ha _ (c - d) (by
      rw [smul_sub, pow_add, mul_smul _ _ d, hj, mul_comm, mul_smul, hi, smul_zero, smul_zero, sub_zero])
    rw [hφk _ h1, smul_zero] at h2
    exact Subtype.ext (sub_eq_zero.1 h2.symm)
  · rintro ⟨u, hu, j, hj⟩
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right j)
    have h1 : M • u = 0 := by
      rw [← ha _ (M • u) (by rw [smul_comm, hj, smul_zero]), smul_smul k, hQ' u hu, smul_zero]
    obtain ⟨v, rfl⟩ := honto u h1
    obtain ⟨w, hw⟩ := (hker _).1 ((hev v).symm.trans hu)
    have h2 : M • (G w - k • v) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hGQ, hw, map_nsmul, sub_self]
    have h3 : φ (Submodule.Quotient.mk w) = k • ev v := by
      rw [hφ, sub_eq_zero.1 (tf M _ hM h2), map_nsmul]
    refine ⟨⟨a • k • a • Submodule.Quotient.mk w, j, ?_⟩, Subtype.ext ?_⟩
    · have h4 := hφk (ℓ ^ j • Submodule.Quotient.mk w) (by rw [map_nsmul, h3, smul_comm, hj, smul_zero])
      rw [smul_comm k a, smul_comm _ a, smul_comm _ a, smul_comm, smul_comm (ℓ ^ j) k, h4, smul_zero, smul_zero]
    · change φ _ = ev v
      rw [map_zsmul, map_nsmul, map_zsmul, h3, ha _ _ hj, ha _ _ hj]

theorem det_eq_of_intertwine {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (h : Module.finrank ℤ A = Module.finrank ℤ B) (f : A →ₗ[ℤ] A) (g : B →ₗ[ℤ] B)
    (i : A →ₗ[ℤ] B) (hi : Function.Injective i) (hc : g ∘ₗ i = i ∘ₗ f) : LinearMap.det g = LinearMap.det f := by
  let e : A ≃ₗ[ℤ] B := LinearEquiv.ofFinrankEq A B h
  have h0 : LinearMap.det (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.2 (hi.comp e.symm.injective))
  have h1 : g ∘ₗ (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) =
      (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ∘ₗ ((e : A →ₗ[ℤ] B) ∘ₗ f ∘ₗ (e.symm : B →ₗ[ℤ] A)) := by
    ext x
    simpa using LinearMap.congr_fun hc (e.symm x)
  have h2 := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, LinearMap.det_comp (i ∘ₗ _), LinearMap.det_conj, mul_comm] at h2
  exact mul_left_cancel₀ h0 h2

section Mat
variable {O : Type} [CommRing O] {n : ℕ}

def mact (L : Type) [AddCommGroup L] [Module O L] (mu : Matrix (Fin n) (Fin n) O) : (Fin n → L) →ₗ[O] (Fin n → L) where
  toFun u i := ∑ j, mu i j • u j
  map_add' u v := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a u := by ext i; simp [Finset.smul_sum, smul_comm a]

variable {L : Type} [AddCommGroup L] [Module O L]

theorem mact_apply (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → L) (i : Fin n) : mact L mu u i = ∑ j, mu i j • u j := rfl

theorem mact_mul (a b : Matrix (Fin n) (Fin n) O) (u : Fin n → L) : mact L a (mact L b u) = mact L (a * b) u := by
  ext i
  simp only [mact_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem mact_nat (c : ℕ) (u : Fin n → L) : mact L ((c : O) • (1 : Matrix (Fin n) (Fin n) O)) u = c • u := by
  ext i
  simp only [mact_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero, ite_smul, smul_one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul, smul_assoc, one_smul, Pi.smul_apply]

theorem det_mact [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] (q : Matrix (Fin n) (Fin n) O) :
    LinearMap.det ((mact L q).restrictScalars ℤ) = Algebra.norm ℤ q.det ^ Module.finrank O L := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank O L := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := L) hr.le
  rw [← hr]
  let f : (Fin r → Fin n → O) →ₗ[O] (Fin r → Fin n → O) :=
    LinearMap.pi fun s => (Matrix.toLin' q).comp (LinearMap.proj s)
  have hf : LinearMap.det f = q.det ^ r := by
    simp [f, LinearMap.det_pi]
  let i : (Fin r → Fin n → O) →ₗ[O] (Fin n → L) :=
    { toFun c j := ∑ s, c s j • v s
      map_add' c d := by ext j; simp [add_smul, Finset.sum_add_distrib]
      map_smul' a c := by ext j; simp [Finset.smul_sum, mul_smul] }
  have hi : Function.Injective i := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    ext s j
    have h1 : ∑ s, c s j • v s = 0 := congrFun hc j
    exact Fintype.linearIndependent_iff.1 hv (fun s => c s j) h1 s
  rw [det_eq_of_intertwine ?_ (f.restrictScalars ℤ) _ (i.restrictScalars ℤ) hi ?_, LinearMap.det_restrictScalars, hf,
    map_pow]
  · simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [finrank_int_eq_mul_of_finite (O := O) (M := L), ← hr]; ring
  · refine LinearMap.ext fun c => funext fun j => ?_
    change ∑ b, q j b • ∑ s, c s b • v s = ∑ s, (q.mulVec (c s) j) • v s
    simp only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm

theorem card_kills [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] {P : Type} [AddCommGroup P] [Module O P] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (q g : Matrix (Fin n) (Fin n) O) (k M : ℕ) (hk : Nat.Coprime k ℓ) (hM : 0 < M)
    (hgq : g * q = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) (ev : L →ₗ[O] P)
    (hker : ∀ a, ev a = 0 ↔ ∃ b, a = M • b) (honto : ∀ w : P, M • w = 0 → ∃ a, ev a = w) :
    Nat.card {u : Fin n → P // mact P q u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L).factorization ℓ := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hℓ.one_lt.ne' (by simpa using hk)
  have hc : k * M ≠ 0 := mul_ne_zero hk0 hM.ne'
  have tf : ∀ (m : ℕ) (w : Fin n → L), m ≠ 0 → m • w = 0 → w = 0 := fun m w hm h => by
    rw [← natCast_zsmul] at h
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hm)
  have hGQ : ∀ w, mact L g (mact L q w) = (k * M) • w := fun w => by rw [mact_mul, hgq, mact_nat]
  have hdet : q.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hgq
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) h1.symm
  have hqg : q * g = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
    have h1 : (q * g - ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hgq]; simp
    have h2 := congrArg (· * q.adjugate) h1
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdet)
  have hQG : ∀ w, mact L q (mact L g w) = (k * M) • w := fun w => by rw [mact_mul, hqg, mact_nat]
  have hinj : Function.Injective ((mact L q).restrictScalars ℤ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    refine tf _ w hc ?_
    rw [← hGQ, show mact L q w = 0 from hw, map_zero]
  have hcard : Nat.card ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) =
      (Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L := by
    rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← Int.natAbs_pow, ← det_mact (L := L) q]
    congr 2
  have hfin : Finite ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet))
  rw [← hcard, ← card_primary _ ℓ hℓ]
  refine card_ker_eq ((mact L q).restrictScalars ℤ) ((mact L g).restrictScalars ℤ) (mact P q).toAddMonoidHom
    (ev.compLeft (Fin n)).toAddMonoidHom k M ℓ hk hk0 hM.ne' tf (fun w => ?_) hGQ hQG (fun w => ?_) (fun u hu => ?_)
    (fun u hu => ?_)
  · ext i
    simp [mact_apply]
  · constructor
    · intro h
      choose b hb using fun i => (hker (w i)).1 (congrFun h i)
      exact ⟨b, funext hb⟩
    · rintro ⟨b, rfl⟩
      exact funext fun i => (hker _).2 ⟨b i, rfl⟩
  · choose a ha using fun i => honto (u i) (congrFun hu i)
    exact ⟨a, funext ha⟩
  · rw [← mact_nat (O := O), ← hgq, ← mact_mul, show mact P q u = 0 from hu, map_zero]
end Mat

end GlobalTheory.TorsCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

theorem card_kills_primary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x ℓ hℓ n q g k M hk hM hgq hall
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo K x M hM).2 hall).2
  letI := ZPart.ptMod Xo (ptO Xo x)
  have := Dw.fin
  have := datum_free_int Dw
  let ev' : Dw.La →ₗ[𝓞 E] Additive (ptO Xo x ⟶ Xo.univ.t.G) :=
    { toFun a := Additive.ofMul (ev a)
      map_add' a b := congrArg Additive.ofMul (hadd a b)
      map_smul' o a := congrArg Additive.ofMul (hlin o a) }
  rw [← Dw.rank, ← TorsCount.card_kills ℓ hℓ q g k M hk hM hgq ev' (fun a => hker a) (fun w hw => honto w.toMul hw)]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Additive.ofMul) fun u => ?_)
  refine and_congr ((ZPart.kills_iff Xo q u).trans funext_iff.symm) ⟨fun h => ?_, fun ⟨j, hj⟩ b => ⟨j, congrFun hj b⟩⟩
  choose e he using h
  refine ⟨∑ b, e b, funext fun b => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  change u b ^ (ℓ ^ ∑ b, e b) = 1
  rw [hd, pow_add, pow_mul, he, one_pow]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.card_kills_primary | exact GlobalTheory.card_kills_primary | (intros; apply GlobalTheory.card_kills_primary <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ShortPrime

section Val
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

def Un (V : Type) {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x : K) : Prop := valV V x = 1

theorem Un.mul {x y : K} (hx : Un V x) (hy : Un V y) : Un V (x * y) := by
  unfold Un at *; rw [map_mul, hx, hy, _root_.one_mul]

theorem Un.inv {x : K} (hx : Un V x) : Un V x⁻¹ := by
  unfold Un at *; rw [map_inv₀, hx, inv_one]

theorem Un.pow {x : K} (hx : Un V x) (n : ℕ) : Un V (x ^ n) := by
  unfold Un at *; rw [map_pow, hx, one_pow]

theorem Un.ne {x : K} (hx : Un V x) : x ≠ 0 := by
  rintro rfl; simp [Un] at hx

theorem Un.nval {x : K} (hx : Un V x) (e : ℕ) (z : K) : nval V e (x * z) = nval V e z :=
  nval_mul_unit e hx.ne (by unfold Un at hx; simp [vV, hx]) z

theorem un_of_vV {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : vV V x = vV V y) : Un V (x * y⁻¹) := by
  unfold Un
  have h1 : WithZero.log (valV V x) = WithZero.log (valV V y) := neg_injective h
  have h2 : valV V x = valV V y := by
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h1, WithZero.exp_log (valV_ne_zero (V := V) hy)]
  rw [map_mul, map_inv₀, h2, mul_inv_cancel₀ (valV_ne_zero hy)]

theorem isUnit_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : IsUnit (k : V) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (k : V) (ℓ : V) := h.cast
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · exact absurd (isUnit_of_mul_isUnit_right h1) hl

theorem un_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : Un V (k : K) := by
  unfold Un valV
  rw [← map_natCast (algebraMap V K), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm (isUnit_of_coprime hl h)

theorem un_ordProj [CharZero K] {ℓ m : ℕ} (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : V)) (hm : m ≠ 0) :
    Un V (((ℓ ^ m.factorization ℓ : ℕ) : K) * (m : K)⁻¹) := by
  have h := (un_of_coprime (K := K) hl (Nat.coprime_ordCompl hp hm).symm).inv
  convert h using 1
  have h1 : (m : K) = ((ℓ ^ m.factorization ℓ : ℕ) : K) * ((m / ℓ ^ m.factorization ℓ : ℕ) : K) := by
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have h2 : ((ℓ ^ m.factorization ℓ : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
  generalize ((m / ℓ ^ m.factorization ℓ : ℕ) : K) = t at *
  rw [h1, mul_inv, ← _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.one_mul]

theorem le_nval_sum {J : Type} (s : Finset J) (e : ℕ) (r : EReal) (f : J → K) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, nval_zero]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans
      (nval_add e _ _)
end Val

theorem eq_one_of_coprime {G : Type} [Monoid G] {u : G} {k ℓ : ℕ} (h : Nat.Coprime k ℓ) (h1 : u ^ k = 1)
    (h2 : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) : u = 1 := by
  obtain ⟨j, hj⟩ := h2
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes (h.pow_right j) (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hj)

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l)

theorem comp_act_nat {T : Over Xo.X} (u : T ⟶ Xo.univ.t.G) (k : ℕ) : u ≫ Xo.univ.t.act.act (k : 𝓞 E) = u ^ k := by
  rw [ZhStable.act_natCast, MonObj.comp_pow, Category.comp_id]

theorem kills_pow {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (k : ℕ) : Kills Xo mu (fun b => u b ^ k) := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  intro i
  simp only [ofMul_pow, smul_comm (mu i _) k]
  rw [← Finset.smul_sum, h i, smul_zero]

theorem kills_mul {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (nu : Matrix (Fin n) (Fin n) (𝓞 E)) : Kills Xo (nu * mu) u := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  exact h.mul nu

theorem nat_mul_bar (k : ℕ) : (k : 𝓞 E) * H.bar (k : 𝓞 E) = ((k ^ 2 : ℕ) : 𝓞 E) := by
  rw [map_natCast]; push_cast; ring

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem moves_comm {k : ℕ} (hk : Odd k) {u t : ptO Xo x ⟶ Xo.univ.t.G} {m ℓ : ℕ} (hu : u ^ k = 1) (ht : t ^ k = 1)
    (hc : Nat.Coprime m ℓ) (hul : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) (htm : t ^ m = 1) {A A' B B' : SecN Xo x k}
    (h1 : Moves Xo u A A') (h2 : Moves Xo t A B) (h3 : Moves Xo t A' B') : Moves Xo u B B' := by
  obtain ⟨j, hj⟩ := hul
  have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk t u m (ℓ ^ j) ht hu (hc.pow_right j) htm hj A A' B' h1).1 h3
  rw [_root_.mul_comm] at h4
  exact (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk u t (ℓ ^ j) m hu ht (hc.pow_right j).symm hj htm A B B' h2).2 h4
end Pts

section Base
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem exists_base {N ℓ m m' : ℕ} (hN : Odd N) (s : SecN Xo x 1) (a' t : ptO Xo x ⟶ Xo.univ.t.G)
    (ha' : a' ^ (N ^ 2) = 1) (ht : t ^ (N ^ 2) = 1) (hm : Nat.Coprime m ℓ) (hm' : Nat.Coprime m' ℓ)
    (ham : a' ^ m = 1) (htm : t ^ m' = 1) :
    ∃ F₀ : SecN Xo x (N ^ 2), Reach Xo s (N ^ 2) F₀ ∧
      (∀ u : ptO Xo x ⟶ Xo.univ.t.G, (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u F₀ F₀) ∧
      ∀ (a : ptO Xo x ⟶ Xo.univ.t.G) F, (∃ j : ℕ, a ^ (ℓ ^ j) = 1) → a ^ (N ^ 2) = 1 →
        IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (a * a') t F → Moves Xo a F₀ (sqN Xo N F) := by
  have hN2 : Odd (N ^ 2) := hN.pow
  obtain ⟨G₀, hG₀, hG₀u⟩ := GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
    (Nat.one_mul _).symm s
  obtain ⟨F₁, hF₁, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 a' ha' G₀).1
  obtain ⟨F₀, hF₀, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 t ht F₁).1
  refine ⟨F₀, ?_, fun u hu huN => ?_, fun a F ha haN hF => ?_⟩
  · exact .move _ _ _ _ (.move _ _ _ _ (.pull 1 (N ^ 2) (N ^ 2) (N : 𝓞 E) s G₀ .base (Or.inl rfl) hN2
      (nat_mul_bar N) (Nat.one_mul _).symm hG₀) hF₁) hF₀
  · have hu2 : u ^ (N ^ 2) = 1 := by rw [pow_two, pow_mul, huN, one_pow]
    have h0 : Moves Xo u G₀ G₀ := moves_of_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
      (Nat.one_mul _).symm hN2 1 u ((comp_act_nat Xo u N).trans huN) hu2 s s G₀ G₀
      (GlobalTheory.existsUnique_moves E H Dw l Xo S x 1 odd_one 1 (one_pow _) s).2 hG₀ hG₀
    exact moves_comm Xo hN2 hu2 ht hm' hu htm (moves_comm Xo hN2 hu2 ha' hm hu ham h0 hF₁ hF₁) hF₀ hF₀
  · obtain ⟨G, F₂, hG, h2, h3⟩ := ((uu_through_moves E H Dw l Xo S x N hN s).1 (a * a') t F
      (by rw [mul_pow, haN, ha', _root_.one_mul]) ht).1 hF
    obtain rfl := hG₀u G hG
    obtain ⟨j, hj⟩ := ha
    have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x _ hN2 a a' (ℓ ^ j) m haN ha' (hm.pow_right j).symm hj ham
      G F₁ F₂ hF₁).2 h2
    exact moves_comm Xo hN2 haN ht hm' ⟨j, hj⟩ htm h4 hF₀ h3

theorem exists_perm {T : Over Xo.X} {n k ℓ : ℕ} (hk : Nat.Coprime k ℓ) (mu : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} [Fintype J] (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo mu u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    ∃ π : J ≃ J, ∀ i b, a (π i) b = a i b ^ k := by
  have h1 : ∀ i, ∃ i', a i' = fun b => a i b ^ k := fun i => by
    obtain ⟨h1, h2⟩ := (ha _).1 ⟨i, rfl⟩
    exact (ha _).2 ⟨kills_pow Xo h1 k, fun b => (h2 b).imp fun j hj => by rw [pow_right_comm, hj, one_pow]⟩
  choose π hπ using h1
  have h2 : Function.Injective π := fun i i' h => hinj <| funext fun b => by
    have h3 : a i b ^ k = a i' b ^ k := by
      have := hπ i
      rw [h, hπ i'] at this
      exact (congrFun this b).symm
    obtain ⟨j, hj⟩ := ((ha _).1 ⟨i, rfl⟩).2 b
    obtain ⟨j', hj'⟩ := ((ha _).1 ⟨i', rfl⟩).2 b
    refine div_eq_one.1 (eq_one_of_coprime hk (by rw [div_pow, h3, div_self']) ⟨j + j', ?_⟩)
    rw [div_pow, pow_add, pow_mul, hj, one_pow, _root_.mul_comm, pow_mul, hj', one_pow, div_self']
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 h2), fun i b => congrFun (hπ i) b⟩

theorem card_kills {T : Over Xo.X} {n ℓ : ℕ} (p q : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    Nat.card {i : J // Kills Xo q (a i)} =
      Nat.card {u : Fin n → (T ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1} := by
  refine Nat.card_eq_of_bijective (fun i => ⟨a i.1, i.2, ((ha _).1 ⟨i.1, rfl⟩).2⟩) ⟨fun i i' h => ?_, fun u => ?_⟩
  · exact Subtype.ext (hinj (congrArg Subtype.val h))
  · obtain ⟨i, hi⟩ := (ha u.1).2 ⟨kills_mul Xo u.2.1 p, u.2.2⟩
    exact ⟨⟨i, hi ▸ u.2.1⟩, Subtype.ext hi⟩
end Base

section Core
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem one_or_four_le {N : ℕ} (hN : Odd N) : N ^ 2 = 1 ∨ 4 ≤ N ^ 2 := by
  obtain ⟨r, rfl⟩ := hN
  rcases r with _ | r
  · exact Or.inl rfl
  · exact Or.inr (le_trans (by norm_num : 4 ≤ 3 ^ 2) (Nat.pow_le_pow_left (by omega) 2))

theorem un_nrm (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) {k ℓ : ℕ} (hl : ¬ IsUnit (ℓ : T.V)) (hk : Nat.Coprime k ℓ)
    (w : (E →+* ℂ) × ℕ → ℕ) : Un T.V (io (nrm Dw c w (k : 𝓞 E))) := by
  simp only [nrm, map_natCast, Finset.prod_pow_eq_pow_sum, map_pow]
  exact (un_of_coprime hl hk).pow _

theorem ell_part (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C) (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e) (hB : ChBound C e ρ w n)
    (ℓ : ℕ) (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M)
    (β : c.F) (hβ0 : β ≠ 0) (hβ : BetaIs (Dw := Dw) c Λ β) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (hR : AllRat Xo (xOf y) (N ^ 2)) (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (hinj : Function.Injective a) (ha : ∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1))
    (F₀ : Fin n → SecN Xo (xOf y) (N ^ 2)) (F : J → Fin n → SecN Xo (xOf y) (N ^ 2))
    (hre : ∀ b, Reach Xo (sOf1 y) (N ^ 2) (F₀ b))
    (hfix : ∀ b (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F₀ b) (F₀ b))
    (hF : ∀ i b, Moves Xo (a i b) (F₀ b) (F i b)) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) := by
  letI := io.toAlgebra
  obtain ⟨A, hsim⟩ := GlobalTheory.T.exists_adapted_similitude_data_at_prime E H n Λ N M ℓ hU hL hp
  have hN : Odd N := hL.1
  have hkN : Odd (A.k * N) := A.odd.mul hN
  have hlev : (A.k * N) ^ 2 = N ^ 2 * A.k ^ 2 := by ring
  have hz := fun u hu => GlobalTheory.inZh_iff_kills_adapted E H Dw l Xo n Λ N ℓ hp hN.pos A (ptO Xo (xOf y)) u hu
  have ha' : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (A.p * A.q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) := fun u =>
    (ha u).trans (and_congr_left fun hu => (hz u hu).1)
  have hZ : ∀ i, InZh Xo Λ (A.k * N) (a i) := fun i =>
    have h := (ha' _).1 ⟨i, rfl⟩
    (hz _ h.2).2.2 h.1
  obtain ⟨π, hπ⟩ := exists_perm Xo A.cop _ a hinj ha'
  have hpull := fun G => (GlobalTheory.existsUnique_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2)
    (nat_mul_bar A.k) hlev G).exists
  choose pl hpl using hpull
  have hmv : ∀ (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G) G G', u ^ ((A.k * N) ^ 2) = 1 → Moves Xo (u ^ A.k) G G' →
      Moves Xo u (pl G) (pl G') := fun u G G' hu h =>
    moves_of_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2) (nat_mul_bar A.k) hlev
      hkN.pow _ u (comp_act_nat Xo u A.k) hu G G' _ _ h (hpl G) (hpl G')
  have hsub : Ideal.span {((A.k * N : ℕ) : 𝓞 E)} • stdLat E n ≤ Λ.La := by
    refine le_trans (Submodule.smul_mono_left ?_) (hL.2.2.trans inf_le_left)
    rw [Nat.cast_mul]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_mul_left _ _)
  have hiso := (GlobalTheory.zh_isotropic_and_half_isotropic GlobalTheory.firstFiveLaws.1 E H Dw l Xo _ (xOf y) n Λ (A.k * N) hU
    hkN.pos hsub).1
  obtain ⟨hff, -, hhom⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io A.k A.ga
    (isUnit_of_coprime hl A.cop) A.unitary A.into
  have hkN0 : ((A.k * N : ℕ) : c.F) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hkN.pos.ne')
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.sum_hv_primary_kernel_alt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl (A.k * N)
    (A.k ^ 2) (N ^ 2) A.k₁ A.p A.q ((A.k : 𝓞 E) • A.g) hkN hsim (mul_pow _ _ _) (A.cop.pow_left 2) hR A.cop₁
    (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) J a hinj ha'
    (fun i i' ε hε => hiso (a i) (a i') ε (hZ i) (hZ i') fun b => by rw [← Nat.cast_pow]; exact hε b)
    (fun b => pl (F₀ b)) (fun i b => pl (F (π i) b))
    (fun b => .pull (N ^ 2) (A.k ^ 2) _ (A.k : 𝓞 E) (F₀ b) _ (hre b)
      (one_or_four_le hN)
      A.odd.pow (nat_mul_bar A.k) hlev (hpl _))
    (fun b u hu huN => hmv u _ _ (by rw [pow_two, pow_mul, huN, one_pow]) (hfix b _
      (hu.imp fun j hj => by rw [pow_right_comm, hj, one_pow]) (by rw [← pow_mul, huN])))
    (fun i b => hmv _ _ _ ((hZ i).1 b) (by rw [← hπ]; exact hF _ _))
    P (((A.k * N : ℕ) : c.F) ^ P.totalDegree)⁻¹ hP.1
    (by rw [A.prod, hhom, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hkN0, map_one, _root_.one_mul]; exact hff)
  have hch : ∀ i, hv Xo c nab y.1 ((A.k * N) ^ 2) (fun b => pl (F (π i) b)) P =
      io (nrm Dw c w (A.k : 𝓞 E)) * hv Xo c nab y.1 (N ^ 2) (F (π i)) P := fun i =>
    GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) _ (nat_mul_bar A.k) hlev n
      (F (π i)) _ (fun b => hpl _) w P hP.1
  obtain ⟨hi1, hi2, hi3⟩ := GlobalTheory.LatticeIndex.latidx E H Dw l c n Λ N M ℓ hU hL hp A
  obtain ⟨hi4, hi5⟩ := hi3 β hβ0 hβ T io hl
  have hcnt := GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix E H Dw l Xo T.Fr (xOf y) ℓ hp n A.q ((N : 𝓞 E) • A.g) A.k₁ (N ^ 2) A.cop₁
    (pow_pos hN.pos 2) (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) hR
  rw [card_kills Xo A.p A.q a hinj ha', hcnt, hi1, Finset.sum_congr rfl fun i _ => hch i, ← Finset.mul_sum,
    Equiv.sum_comp π fun i => hv Xo c nab y.1 (N ^ 2) (F i) P] at hz2
  have hδ : io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≠ 0 := by
    refine (map_ne_zero io).2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_)
    exact (map_ne_zero (embF c τ)).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hi5)
  have u1 := un_of_vV hδ ((map_ne_zero io).2 hβ0) hi4
  have u2 := un_ordProj (K := T.Fr) hp hl hi2
  have u3 := un_nrm (Dw := Dw) c T io hl A.cop w
  have u4 := (un_of_coprime (K := T.Fr) hl A.cop).pow P.totalDegree
  rw [← (((u1.mul u2).mul u3.inv).mul u4).nval e z] at hz1
  convert hz1 using 2
  have h3 := u3.ne
  have h4 := u4.ne
  have h5 : (N : T.Fr) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN.pos.ne')
  simp only [map_mul, map_inv₀, map_pow io, map_natCast, Nat.cast_mul, mul_pow] at hz2 ⊢
  generalize (∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) = Sm at *
  generalize io (nrm Dw c w (A.k : 𝓞 E)) = ν at *
  generalize (A.k : T.Fr) ^ P.totalDegree = κ at *
  generalize (N : T.Fr) ^ P.totalDegree = ξ at *
  have h6 : Sm = κ * ξ * ν⁻¹ * ((κ * ξ)⁻¹ * (ν * Sm)) := by field_simp
  rw [h6, hz2]
  field_simp
end Core

end GlobalTheory.ShortPrime

theorem GlobalTheory.short_value_bound_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ (β : c.F), β ≠ 0 → BetaIs (Dw := Dw) c Λ β → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP z tp F hz hg
    htp hF hR ⟨m', hm', htm⟩
  letI := io.toAlgebra
  obtain ⟨J, J', _, _, a, a', σ, hinj, ha, ⟨m, hm, ham⟩, hσ, -⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hp z hz hg
  rw [← Equiv.sum_comp σ, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine GlobalTheory.ShortPrime.le_nval_sum _ _ _ _ fun i' _ => ?_
  choose F₀ h1 h2 h3 using fun b => GlobalTheory.ShortPrime.exists_base Xo hL.1 (sOf1 y) (a' i' b) (tp b) (ham i' b).2 (htp b)
    hm hm' (ham i' b).1 (htm b)
  refine GlobalTheory.ShortPrime.ell_part Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP hR J a
    hinj ha F₀ (fun i b => sqN Xo N (F (σ (i, i')) b)) h1 h2 fun i b => ?_
  obtain ⟨h4, h5⟩ := (ha _).1 ⟨i, rfl⟩
  exact h3 b _ _ (h5 b) (h4.1 b) (hσ i i' b ▸ hF _ b)
