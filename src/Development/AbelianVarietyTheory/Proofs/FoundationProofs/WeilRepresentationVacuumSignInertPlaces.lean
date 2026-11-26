module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributive
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTriple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbour
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationCommHeisenbergIntertwiner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributive
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributive
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistTriple

theorem bc_eq_one {D : D7} {T : Tor D} {N N' : ℕ} {A₁ A₂ A₃ : AddSubgroup (VC D N N')}
    (h₁ : Nice D T A₁) (h₂ : Nice D T A₂) (h₃ : Nice D T A₃) (hd : Dist A₁ A₂ A₃)
    {x y : VC D N N'} (hx : x ∈ A₂) (hy : y ∈ A₃) (hxy : y + x ∈ A₁) : bc D T y x = 1 := by
  have hm := hd x hx y hy (by rwa [add_comm])
  obtain ⟨x₁, hx₁, x₃, hx₃, rfl⟩ := AddSubgroup.mem_sup.1 hm
  have hy₃ : y + x₃ ∈ A₁ := by
    have := A₁.sub_mem hxy hx₁.1
    have e : y + (x₁ + x₃) - x₁ = y + x₃ := by abel
    rwa [e] at this
  have e1 := h₁.2.1 _ hy₃ _ hx₁.1
  rw [bc_add_left, h₂.2.1 _ hx₃.1 _ hx₁.2, mul_one] at e1
  rw [bc_add_right, e1, h₃.2.1 _ hy _ hx₃.2, mul_one]

theorem const_eq_one : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N'))
    (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  intro D T N N' A₁ A₂ A₃ e μ ht hd
  obtain ⟨r, hr, hs⟩ := GlobalTheory.T.thetaTripleConstant_eq_cocycle_sum D T N N' A₁ A₂ A₃ e μ ht
  obtain ⟨h₁, h₂, h₃, -, -, -, -, -, h8, -⟩ := ht
  have key : ∃ s : ℝ, 0 ≤ s ∧ μ * (r : ℂ) = (s : ℂ) := by
    rw [hs]
    refine finsum_induction (fun z : ℂ => ∃ s : ℝ, 0 ≤ s ∧ z = (s : ℂ)) ⟨0, le_rfl, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_nonneg ha hb, by push_cast; rfl⟩
    · intro p
      split_ifs with h
      · exact ⟨1, zero_le_one, by
          rw [bc_eq_one h₁ h₂ h₃ hd (Quotient.out p.2 : A₂).2 (Quotient.out p.1 : A₃).2 h]; simp⟩
      · exact ⟨0, le_rfl, by simp⟩
  obtain ⟨s, hs0, hμ⟩ := key
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hμ' : μ = ((s / r : ℝ) : ℂ) := by
    push_cast; rw [eq_div_iff hr', hμ]
  rw [hμ'] at h8 ⊢
  have h8' : (s / r) ^ 8 = 1 := by exact_mod_cast h8
  have := (pow_eq_one_iff_of_nonneg (div_nonneg hs0 hr.le) (by norm_num)).1 h8'
  rw [this]; simp

end GlobalTheory.DistTriple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributiveStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_one_distributive : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  first | exact @GlobalTheory.DistTriple.const_eq_one | exact GlobalTheory.DistTriple.const_eq_one | (intros; apply GlobalTheory.DistTriple.const_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrime
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.UnitaryTransvection

def tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  1 + μ • Matrix.vecMulVec w (fun i => D.host.conj (w i))

theorem tv_mulVec (D : D7) {n : ℕ} (μ : D.host.E) (w v : Fin n → D.host.E) :
    (tv D μ w).mulVec v = v + (μ * hE D v w) • w := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, hE,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cT_tv (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E) :
    cT D (tv D μ w) = tv D (D.host.conj μ) w := by
  ext i j
  simp only [cT, tv, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, conj_conj, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp only [if_true, map_one]; ring
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]; ring

theorem tv_unitary (D : D7) {n : ℕ} (μ : D.host.E) (w : Fin n → D.host.E)
    (h : μ + D.host.conj μ + μ * D.host.conj μ * hE D w w = 0) : tv D μ w * cT D (tv D μ w) = 1 := by
  rw [cT_tv]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, Matrix.one_mulVec,
    hE_add_left, hE_smul_left, add_assoc, ← add_smul]
  have : D.host.conj μ * hE D v w + μ * (hE D v w + D.host.conj μ * hE D v w * hE D w w) = 0 := by
    linear_combination hE D v w * h
  rw [this, zero_smul, add_zero]

theorem smul_mem_int {D : D7} {n : ℕ} (N : Lat D n) {c : D.host.E} (hc : IntE D c) {v : Fin n → D.host.E}
    (hv : v ∈ N) : c • v ∈ N := by
  obtain ⟨a, rfl⟩ := hc
  rw [algebraMap_smul]
  exact N.smul_mem a hv

theorem intE_nat (D : D7) (m : ℕ) : IntE D (m : D.host.E) := ⟨m, map_natCast _ m⟩

theorem gen {D : D7} {n : ℕ} (s : Matrix (Fin n) (Fin n) D.host.E) (c : D.host.E) (M N : Lat D n)
    (z : Fin n → D.host.E) (hM : ∀ y ∈ M, c • s.mulVec y ∈ N) (hz : c • s.mulVec z ∈ N) :
    ∀ v ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z}, c • s.mulVec v ∈ N := by
  intro v hv
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [Matrix.mulVec_add, smul_add]
  refine N.add_mem (hM y hy) ?_
  rw [← algebraMap_smul D.host.E a z, Matrix.mulVec_smul, smul_comm]
  exact smul_mem_int N ⟨a, rfl⟩ hz

theorem step {D : D7} {n : ℕ} (M N : Lat D n) (hMN : M ≤ N) (w y : Fin n → D.host.E) (μ : D.host.E) (m : ℕ)
    (hw : ((m : D.host.E) * μ) • w ∈ M) (hy : y ∈ N) (hi : IntE D (hE D y w)) :
    ((m * m : ℕ) : D.host.E) • (tv D μ w).mulVec y ∈ N := by
  rw [tv_mulVec, smul_add, smul_smul]
  refine N.add_mem (smul_mem_int N (intE_nat D _) hy) ?_
  have : ((m * m : ℕ) : D.host.E) * (μ * hE D y w) = ((m : D.host.E) * hE D y w) * ((m : D.host.E) * μ) := by
    push_cast; ring
  rw [this, mul_smul]
  exact smul_mem_int N (mul_mem (intE_nat D m) hi) (hMN hw)

theorem transvection : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  intro D n q P hP M b x lam m hbx hM hww hl hmq ⟨p, hp, hpl⟩ ⟨p', hp', hpl'⟩
  have hPw : ∀ a ∈ P, (a : D.host.E) • (b + x) ∈ M := by
    intro a ha
    have : a • (b + x) ∈ M := by
      rw [smul_add]; exact M.add_mem (hbx a ha).1 (hbx a ha).2
    rw [← algebraMap_smul D.host.E a (b + x)] at this
    exact this
  have hcl : (m : D.host.E) * D.host.conj lam = ((sgO D p : 𝓞 D.host.E) : D.host.E) := by
    rw [sgO_coe, ← hpl, map_mul, map_natCast]
  have h1 : ((m : D.host.E) * lam) • (b + x) ∈ M := by rw [hpl]; exact hPw p hp
  have h2 : ((m : D.host.E) * D.host.conj lam) • (b + x) ∈ M := by rw [hcl]; exact hPw _ (hP p hp)
  have h3 : ((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x) ∈ M := by rw [hpl']; exact hPw p' hp'
  have hmem : ∀ z : Fin n → D.host.E, z ∈ M ⊔ Submodule.span (𝓞 D.host.E) {z} := fun z =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hco : Nat.Coprime (m * m) q := Nat.Coprime.mul_left hmq hmq
  refine ⟨tv D lam (b + x), tv_unitary D lam _ hl, ⟨m * m, hco, ?_, ?_⟩, ⟨m * m, hco, ?_, ?_⟩⟩
  · exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h1 (hmem _) hww)
  · rw [cT_tv]
    exact gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy))
      (step M _ le_sup_left _ _ _ m h2 (hmem _) hww)
  · refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h1 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have : ((m * m : ℕ) : D.host.E) • (b + (lam * hE D b (b + x)) • (b + x)) =
        (m : D.host.E) • (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • x := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      push_cast; ring
    rw [this]
    exact Submodule.sub_mem _ (smul_mem_int _ (intE_nat D m) (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem x))
  · rw [cT_tv]
    refine gen _ _ _ _ _ (fun y hy => step M _ le_sup_left _ y _ m h2 (Submodule.mem_sup_left hy) (hM y hy)) ?_
    rw [tv_mulVec]
    have hx : hE D x (b + x) = hE D (b + x) (b + x) - hE D b (b + x) := by
      rw [hE_add_left]; ring
    have : ((m * m : ℕ) : D.host.E) • (x + (D.host.conj lam * hE D x (b + x)) • (b + x)) =
        ((m : D.host.E) + ((m : D.host.E) * D.host.conj lam) * hE D (b + x) (b + x)) •
          (((m : D.host.E) * (1 + lam * hE D b (b + x))) • (b + x)) -
          ((m * m : ℕ) : D.host.E) • b := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [hx]
      push_cast
      linear_combination (-((m : D.host.E) * m * hE D b (b + x) * (b i + x i))) * hl
    rw [this]
    refine Submodule.sub_mem _ (smul_mem_int _ ?_ (Submodule.mem_sup_left h3))
      (smul_mem_int _ (intE_nat D _) (hmem b))
    rw [hcl]
    exact add_mem (intE_nat D m) (mul_mem ⟨sgO D p, rfl⟩ hww)

end GlobalTheory.UnitaryTransvection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrimeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  first | exact @GlobalTheory.UnitaryTransvection.transvection | exact GlobalTheory.UnitaryTransvection.transvection | (intros; apply GlobalTheory.UnitaryTransvection.transvection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntSmulIntegral
universe u_1 u_2

namespace GlobalTheory.IntegerScalarIntegral

open NumberField

theorem exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple

theorem exists_int_smul_mem {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y

end GlobalTheory.IntegerScalarIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEq
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NearerNeighbour

theorem exists_step {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Finite (M ⧸ N)] (hN : N ≠ ⊤) :
    ∃ (P : Ideal R) (x : M), P.IsMaximal ∧ x ∉ N ∧ (∀ p ∈ P, p • x ∈ N) ∧
      (Module.length R (M ⧸ (N ⊔ Submodule.span R {x}))).toNat + 1 = (Module.length R (M ⧸ N)).toNat := by
  haveI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 hN
  haveI : IsArtinian R (M ⧸ N) := isArtinian_of_finite
  haveI : IsNoetherian R (M ⧸ N) := isNoetherian_of_finite R _
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R (M ⧸ N))
  haveI hs : IsSimpleModule R S := isSimpleModule_iff_isAtom.2 hS
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨x, hx⟩ := N.mkQ_surjective (e.symm 1 : S)
  have h0 : N.mkQ x ≠ 0 := by
    rw [hx]
    intro h
    have h1 : e.symm 1 = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact hP.ne_top (Ideal.Quotient.zero_eq_one_iff.1 h1.symm)
  have hmap : (N ⊔ Submodule.span R {x}).map N.mkQ = S := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, Set.image_singleton]
    refine (hS.le_iff.1 ?_).resolve_left ?_
    · rw [Submodule.span_singleton_le_iff_mem, hx]; exact (e.symm 1).2
    · rwa [Submodule.span_singleton_eq_bot]
  refine ⟨P, x, hP, fun h => h0 ((Submodule.Quotient.mk_eq_zero N).2 h), fun p hp => ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, hx, ← Submodule.coe_smul, ← map_smul]
    have : p • (1 : R ⧸ P) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hp
    rw [this, map_zero]; rfl
  · have h1 := Module.length_eq_add_of_exact S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
    have h2 := (Submodule.quotientQuotientEquivQuotient N (N ⊔ Submodule.span R {x}) le_sup_left).length_eq
    rw [hmap] at h2
    have h3 : Module.length R ((M ⧸ N) ⧸ S) ≠ ⊤ := Module.length_ne_top
    rw [← h2, h1, Module.length_eq_one R S, ENat.toNat_add (by simp) h3, add_comm]
    simp

theorem exists_prime_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P := by
  have hb : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hb
  letI := Ideal.Quotient.field P
  refine ⟨ringChar (𝓞 K ⧸ P), CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_int_smul_mem {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerScalarIntegral.main
  | exact _root_.GlobalTheory.IntegerScalarIntegral.main
  | (apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerScalarIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerScalarIntegral.main ..)

theorem exists_nearer : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  intro D n L₀ L h₀ h hne
  obtain ⟨fg₀, -, d₀⟩ := (sd_iff D L₀).1 h₀
  obtain ⟨-, sp, d⟩ := (sd_iff D L).1 h
  have hN : Submodule.comap L₀.subtype L ≠ ⊤ := by
    intro ht
    have hle : L₀ ≤ L := Submodule.comap_subtype_eq_top.1 ht
    exact hne (le_antisymm hle fun y hy => (d₀ y).2 fun x hx => (d y).1 hy x (hle hx))
  haveI : Module.Finite (𝓞 D.host.E) L₀ := Module.Finite.iff_fg.2 fg₀
  haveI : Module.Finite ℤ (L₀ ⧸ Submodule.comap L₀.subtype L) :=
    Module.Finite.trans (𝓞 D.host.E) _
  haveI : Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨m, hm, hy⟩ := exists_int_smul_mem L sp y.1
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • (Submodule.mkQ (Submodule.comap L₀.subtype L) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  obtain ⟨P, x, hP, hx, hPx, hlen⟩ := exists_step _ hN
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P hP
  refine ⟨P, q, x.1, hP, hq, hqP, x.2, ⟨hx, hPx, (d₀ x.1).1 x.2 x.1 x.2⟩, ?_⟩
  have key : Submodule.comap L₀.subtype (nbr D L x.1) =
      Submodule.comap L₀.subtype L ⊔ Submodule.span (𝓞 D.host.E) {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine Submodule.mem_sup.2 ⟨y - c • x, ?_, c • x, Submodule.mem_span_singleton.2 ⟨c, rfl⟩, sub_add_cancel _ _⟩
      have : L₀.subtype (y - c • x) = a := by
        rw [map_sub, ← hab, map_smul]; exact add_sub_cancel_right _ _
      rw [Submodule.mem_comap, this]
      exact ha.1
    · refine sup_le (fun y hy => ?_) ?_
      · exact Submodule.mem_sup_left (S := nbM D L x.1) ⟨hy, (d₀ y.1).1 y.2 x.1 x.2⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_sup_right (S := nbM D L x.1) (Submodule.mem_span_singleton_self _)
  unfold lenQ
  rw [key]
  exact hlen

end GlobalTheory.NearerNeighbour
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEqStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_neighbour_chain : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  first | exact @GlobalTheory.NearerNeighbour.exists_nearer | exact GlobalTheory.NearerNeighbour.exists_nearer | (intros; apply GlobalTheory.NearerNeighbour.exists_nearer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroup
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TrivSubgroup

variable {D : D7} {q : ℕ}

theorem zeroAt_zero : ZeroAt D q 0 := fun k =>
  ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem zeroAt_add {x y : AE D} (hx : ZeroAt D q x) (hy : ZeroAt D q y) : ZeroAt D q (x + y) := by
  intro k
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx k
  obtain ⟨m', hm', hmq', s', hs', h'⟩ := hy k
  refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hmq hmq', (m' : AE D) * s + (m : AE D) * s',
    add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
  push_cast
  linear_combination (m' : AE D) * h + (m : AE D) * h'

theorem zeroAt_mul_left (hq : q.Prime) (y : AE D) {x : AE D} (hx : ZeroAt D q x) :
    ZeroAt D q (y * x) := by
  intro k
  obtain ⟨n, hn, hy⟩ := GlobalTheory.AdelicApprox.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

def zeroIdeal (D : D7) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  add_mem' := zeroAt_add
  zero_mem' := zeroAt_zero
  smul_mem' := fun c _ hx => zeroAt_mul_left hq c hx

theorem entry_mul_mem {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hB : ∀ i j, B i j ∈ I) (i j : Fin n) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hB k j)

theorem trivAt_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧
    (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧
    ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  intro D n q hq
  refine ⟨fun i j => ?_, fun g h hg hh i j => ?_, fun g hg i j => ?_⟩
  · rw [Units.val_one, sub_self]; exact zeroAt_zero
  · have e : ((g * h : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (g : Matrix (Fin n) (Fin n) (AE D)) * ((h : Matrix (Fin n) (Fin n) (AE D)) - 1) +
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact zeroAt_add (entry_mul_mem (zeroIdeal D hq) _ _ hh i j) (hg i j)
  · have e : ((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (-((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) *
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [neg_mul, mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [← Matrix.sub_apply, e]
    exact entry_mul_mem (zeroIdeal D hq) _ _ hg i j

end GlobalTheory.TrivSubgroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroupStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialAtPrime_adelicGL_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧ (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧ ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  first | exact @GlobalTheory.TrivSubgroup.trivAt_subgroup | exact GlobalTheory.TrivSubgroup.trivAt_subgroup | (intros; apply GlobalTheory.TrivSubgroup.trivAt_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section
namespace GlobalTheory.InertSign

theorem Iop_smul (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (a : ℂ) (F : VC D N N' → ℂ) :
    Iop D T A B (a • F) = a • Iop D T A B F := by
  funext z
  simp only [Iop, U, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm a, ← smul_eq_mul a, smul_finsum]
  congr 1
  exact finsum_congr fun q => by rw [smul_eq_mul]; ring

theorem ThSp_smul {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (a : ℂ) {F : VC D N N' → ℂ}
    (h : F ∈ ThSp D T A) : a • F ∈ ThSp D T A := by
  refine ⟨h.1.const_smul a, fun x hx z => ?_⟩
  have := h.2 x hx z
  simp only [U, Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [← this]; ring

theorem moves_unique {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {L L' : Lat D n} (h : Moves D g L) (h' : Moves D g L') :
    L = L' := by
  ext x; rw [h x, h' x]

theorem sd_of_moves {D : D7} {n : ℕ} {g : GA D n} {L : Lat D n} (h : Moves D (g : GL (Fin n) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D n
  rw [moves_unique h (h1 g).1]; exact (h1 g).2

theorem moves_one (D : D7) (n : ℕ) : Moves D ((1 : GA D n) : GL (Fin n) (AE D)) (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 1).1

theorem intG_of_moves {D : D7} {n : ℕ} {g g' : GA D n} {L : Lat D n} (h : Moves D (g : GL (Fin n) (AE D)) L)
    (h' : Moves D (g' : GL (Fin n) (AE D)) L) : IntG D ((g⁻¹ * g' : GA D n) : GL (Fin n) (AE D)) := by
  obtain ⟨Lt, h1, -, h3, -⟩ := exists_lattice_of_adelic_point D n
  exact AdLattice.intG_of_mem D n _ ((h3 g g').1 ((moves_unique (h1 g).1 h).trans (moves_unique h' (h1 g').1)))

theorem eqAt_of_moves {D : D7} {n p : ℕ} (hp : p.Prime) {g : GA D n} {L : Lat D n}
    (h : Moves D (g : GL (Fin n) (AE D)) L) (ht : TrivAt D p (g : GL (Fin n) (AE D))) : EqAt D p (stdL D n) L := by
  obtain ⟨Lt, h1, -, -, -, h5⟩ := exists_lattice_of_adelic_point D n
  rw [moves_unique h (h1 g).1]; exact h5 p g hp ht

theorem suppInert_one (D : D7) (n : ℕ) : SuppInert D ((1 : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq _ => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).1

theorem suppInert_mul {D : D7} {n : ℕ} {g h : GA D n} (hg : SuppInert D (g : GL (Fin n) (AE D)))
    (hh : SuppInert D (h : GL (Fin n) (AE D))) : SuppInert D ((g * h : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq hi => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).2.1 _ _ (hg q hq hi) (hh q hq hi)

theorem suppInert_inv {D : D7} {n : ℕ} {g : GA D n} (hg : SuppInert D (g : GL (Fin n) (AE D))) :
    SuppInert D ((g⁻¹ : GA D n) : GL (Fin n) (AE D)) :=
  fun q hq hi => (GlobalTheory.T.trivialAtPrime_adelicGL_subgroup D n q hq).2.2 _ (hg q hq hi)

theorem stable_of_inert {D : D7} {q : ℕ} (hq : q.Prime) (hi : InertQ D q) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal)
    (hqP : (q : 𝓞 D.host.E) ∈ P) : ∀ a ∈ P, sgO D a ∈ P := by
  intro a ha
  have h0 : P ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have := Ideal.smul_mem_pointwise_smul D.host.conj a P ha
  rw [hi P hP.isPrime h0 hqP] at this
  exact this

theorem exists_move {D : D7} {n q : ℕ} (hq : q.Prime) (hi : InertQ D q) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal)
    (hqP : (q : 𝓞 D.host.E) ∈ P) {B : Lat D n} {x : Fin n → D.host.E} (hB : SD D B) (hx : NbD D P B x) :
    ∃ (g : GA D n) (w : Fin n → D.host.E), SuppInert D (g : GL (Fin n) (AE D)) ∧ NbD D P B w ∧
      (∀ h : GA D n, Moves D (h : GL (Fin n) (AE D)) B → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) (nbr D B x)) ∧
      (∀ h : GA D n, Moves D (h : GL (Fin n) (AE D)) (nbr D B w) →
        Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) (nbr D B w)) ∧
      (SD D (nbr D B w) → SD D (nbr D B x) → Tri D P (nbr D B w) B (nbr D B x)) := by
  have hst := stable_of_inert hq hi hP hqP
  obtain ⟨b, x', lam, m, hb, hx', hp, hθ, hw, hM, hl, hm, h1, h2⟩ := GlobalTheory.T.exists_transvection_vectors_neighbour D n q hq P hP hqP hst B x hB hx
  have hA : nbr D B (b + x') = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b + x'} := by rw [nbr, hM]
  obtain ⟨s, hs, hsA, hsB⟩ := GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime D n q P hst (nbM D B x) b x' lam m hp
    (fun y hy => by rw [← hM] at hy; exact hy.2) hw.2.2 hl hm h1 h2
  rw [← hA] at hsA
  rw [← hb, ← hx'] at hsB
  obtain ⟨g, hg, hmv⟩ := GlobalTheory.T.exists_local_component_unitary_matrix D n q hq s hs
  have hqs : ∀ (v : Fin n → D.host.E) (L : Lat D n), (∀ p ∈ P, p • v ∈ nbM D B x) →
      L = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {v} → ∀ y ∈ L, ((q : D.host.E) ^ 1) • y ∈ nbM D B x := by
    intro v L hv hL y hy
    rw [hL] at hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hc
    have e : ∀ u : Fin n → D.host.E, ((q : D.host.E) ^ 1) • u = (q : 𝓞 D.host.E) • u := by
      intro u; rw [pow_one, ← algebraMap_smul D.host.E (q : 𝓞 D.host.E) u, map_natCast]
    rw [e, smul_add, smul_comm]
    exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ (hv _ hqP))
  refine ⟨g, b + x', fun p hp hn => hg p hp (fun h => hn (h ▸ hi)), hw, fun h hh => hmv h B _ hh ⟨1, ?_, ?_⟩ hsB,
    fun h hh => hmv h _ _ hh ⟨0, by simp, by simp⟩ hsA, fun a c => ⟨a, hB, c, nbM D B x, b, x', hA, hb, hx', hp, hθ⟩⟩
  · intro y hy
    exact (le_sup_left : nbM D B x ≤ nbr D B x) (hqs b B (fun p h => (hp p h).1) hb y hy)
  · intro y hy
    exact (hqs x' _ (fun p h => (hp p h).2) hx' y hy).1

section Core

variable {D : D7} {T : Tor D} {N N' n : ℕ} (Λ : Lat D n → AddSubgroup (VC D N N'))
  (ω : GA D n → (VC D N N' → ℂ) → (VC D N N' → ℂ)) (e0 : VC D N N' → ℂ) (σ : ℂ)

theorem core (hσ : σ * σ = 1) (hnz : e0 ≠ 0) (he0 : e0 ∈ ThSp D T (Λ (stdL D n)))
    (hI : ∀ L₁ L₂, SD D L₁ → SD D L₂ → ∀ e ∈ ThSp D T (Λ L₁), Iop D T (Λ L₁) (Λ L₂) e ∈ ThSp D T (Λ L₂) ∧
      Iop D T (Λ L₂) (Λ L₁) (Iop D T (Λ L₁) (Λ L₂) e) = e)
    (hII : ∀ L, SD D L → ∀ e ∈ ThSp D T (Λ L), Iop D T (Λ L) (Λ L) e = e)
    (hline : ∀ L, SD D L → ∀ F ∈ ThSp D T (Λ L), ∀ G ∈ ThSp D T (Λ L), G ≠ 0 → ∃ c : ℂ, F = c • G)
    (hmul : ∀ g h, ω (g * h) e0 = ω g (ω h e0))
    (hsm : ∀ g L, SD D L → ∀ F ∈ ThSp D T (Λ L), ∀ a : ℂ, ω g (a • F) = a • ω g F)
    (hin : ∀ k : GA D n, IntG D (k : GL (Fin n) (AE D)) → SuppInert D (k : GL (Fin n) (AE D)) → ω k e0 = e0)
    (hth : ∀ (h : GA D n) L, Moves D (h : GL (Fin n) (AE D)) L → ω h e0 ∈ ThSp D T (Λ L))
    (heq : ∀ (g h k : GA D n) L₁ L₂ M₁ M₂, Moves D (h : GL (Fin n) (AE D)) L₁ →
      Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) L₂ → Moves D (k : GL (Fin n) (AE D)) M₁ →
      Moves D ((g * k : GA D n) : GL (Fin n) (AE D)) M₂ → ∀ F ∈ ThSp D T (Λ L₁),
        ω g (Iop D T (Λ L₁) (Λ M₁) F) = Iop D T (Λ L₂) (Λ M₂) (ω g F))
    (hbet : ∀ L₁ L₂ L₃, SD D L₁ → SD D L₂ → SD D L₃ → Bet D L₁ L₂ L₃ → ∀ e ∈ ThSp D T (Λ L₁), e ≠ 0 →
      Iop D T (Λ L₂) (Λ L₃) (Iop D T (Λ L₁) (Λ L₂) e) = Iop D T (Λ L₁) (Λ L₃) e)
    (htri : ∀ (P : Ideal (𝓞 D.host.E)) A B C, P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) →
      Tri D P A B C → ∀ e ∈ ThSp D T (Λ A), e ≠ 0 →
      Iop D T (Λ B) (Λ C) (Iop D T (Λ A) (Λ B) e) = σ • Iop D T (Λ A) (Λ C) e) :
    ∀ (h : GA D n) L, SuppInert D (h : GL (Fin n) (AE D)) → Moves D (h : GL (Fin n) (AE D)) L →
      ω h e0 = σ ^ lenQ D (stdL D n) L • Iop D T (Λ (stdL D n)) (Λ L) e0 := by
  have hsd0 : SD D (stdL D n) := sd_of_moves (moves_one D n)
  have hwd : ∀ (h₁ h₂ : GA D n) L, SuppInert D (h₁ : GL (Fin n) (AE D)) → SuppInert D (h₂ : GL (Fin n) (AE D)) →
      Moves D (h₁ : GL (Fin n) (AE D)) L → Moves D (h₂ : GL (Fin n) (AE D)) L → ω h₂ e0 = ω h₁ e0 := by
    intro h₁ h₂ L s₁ s₂ m₁ m₂
    have := hmul h₁ (h₁⁻¹ * h₂)
    rwa [mul_inv_cancel_left, hin _ (intG_of_moves m₁ m₂) (suppInert_mul (suppInert_inv s₁) s₂)] at this
  have hone : ω 1 e0 = e0 := by
    have := intG_of_moves (moves_one D n) (moves_one D n)
    rw [inv_one, one_mul] at this
    exact hin 1 this (suppInert_one D n)
  have hne : ∀ h, ω h e0 ≠ 0 := by
    intro h h0
    have h1 := hmul h⁻¹ h
    have h2 := hsm h⁻¹ _ hsd0 e0 he0 0
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone, h0, h2] at h1
    exact hnz h1
  have hstep : ∀ (q : ℕ) (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) (h : GA D n), q.Prime → InertQ D q →
      P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → NbD D P B x → SuppInert D (h : GL (Fin n) (AE D)) →
      Moves D (h : GL (Fin n) (AE D)) B → ∃ k : GA D n, SuppInert D (k : GL (Fin n) (AE D)) ∧
        Moves D (k : GL (Fin n) (AE D)) (nbr D B x) ∧ ω h e0 = σ • Iop D T (Λ (nbr D B x)) (Λ B) (ω k e0) := by
    intro q P B x h hq hi hP hqP hx sh mh
    have hB := sd_of_moves mh
    obtain ⟨g, w, sg, hw, mC, mA, htr⟩ := exists_move hq hi hP hqP hB hx
    obtain ⟨g₂, -, sg₂, -, mA₂, -⟩ := exists_move hq hi hP hqP hB hw
    have mhA := mA₂ h mh
    have shA := suppInert_mul sg₂ sh
    set hA := g₂ * h
    have hAsd := sd_of_moves mhA
    have hCsd := sd_of_moves (mC h mh)
    obtain ⟨w0, -, hw0⟩ := GlobalTheory.T.exists_traceOne_integer_conj_diff_prime_to D q hq
    have eA := hth hA _ mhA
    have hIA := hI _ _ hAsd hB _ eA
    have hIne : Iop D T (Λ (nbr D B w)) (Λ B) (ω hA e0) ≠ 0 := by
      intro h0
      have h2 := hIA.2
      have h3 := Iop_smul D T (Λ B) (Λ (nbr D B w)) 0 0
      rw [zero_smul, zero_smul] at h3
      rw [h0, h3] at h2
      exact hne hA h2.symm
    obtain ⟨c, hc⟩ := hline B hB _ (hth h B mh) _ hIA.1 hIne
    have hfix : ω g (ω hA e0) = ω hA e0 := by
      rw [← hmul]; exact hwd _ _ _ shA (suppInert_mul sg shA) mhA (mA hA mhA)
    have hC : ω (g * h) e0 = c • Iop D T (Λ (nbr D B w)) (Λ (nbr D B x)) (ω hA e0) := by
      rw [hmul, hc, hsm g B hB _ hIA.1, heq g hA h _ _ _ _ mhA (mA hA mhA) mh (mC h mh) _ eA, hfix]
    have hT := htri P _ _ _ hP (stable_of_inert hq hi hP hqP) ⟨w0, hw0 P hP.isPrime hqP⟩ (htr hAsd hCsd) _ eA (hne hA)
    have hBC : Iop D T (Λ B) (Λ (nbr D B x)) (ω h e0) = σ • ω (g * h) e0 := by
      rw [hC, hc, Iop_smul, hT, smul_comm]
    refine ⟨g * h, suppInert_mul sg sh, mC h mh, ?_⟩
    rw [← Iop_smul, ← hBC, (hI _ _ hB hCsd _ (hth h B mh)).2]
  intro h L
  induction hl : lenQ D (stdL D n) L generalizing h L with
  | zero =>
    intro sh mh
    by_cases hL : stdL D n = L
    · subst hL
      rw [pow_zero, one_smul, hII _ hsd0 _ he0, hwd 1 h _ (suppInert_one D n) sh (moves_one D n) mh, hone]
    · obtain ⟨P, q, x, -, -, -, -, -, hlen⟩ := GlobalTheory.T.self_dual_lattices_neighbour_chain D n _ L hsd0 (sd_of_moves mh) hL
      omega
  | succ k ih =>
    intro sh mh
    have hL : stdL D n ≠ L := by
      intro hL
      rw [← hL, lenQ, Submodule.comap_subtype_self, Module.length_eq_zero] at hl
      simp at hl
    obtain ⟨P, q, x, hP, hq, hqP, hx0, hx, hlen⟩ := GlobalTheory.T.self_dual_lattices_neighbour_chain D n _ L hsd0 (sd_of_moves mh) hL
    have hi : InertQ D q := by
      by_contra hi
      obtain ⟨s, hs, h1, -⟩ := eqAt_of_moves hq mh (sh q hq hi)
      have h2 := h1 x hx0
      have h3 := hx.2.1 _ hqP
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hs
      apply hx.1
      have e1 : (s : D.host.E) • x = (s : 𝓞 D.host.E) • x := by
        rw [← algebraMap_smul D.host.E (s : 𝓞 D.host.E) x, map_natCast]
      rw [e1] at h2
      have e2 : x = (u : 𝓞 D.host.E) • (s : 𝓞 D.host.E) • x + (v : 𝓞 D.host.E) • (q : 𝓞 D.host.E) • x := by
        rw [smul_smul, smul_smul, ← add_smul]
        have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
        push_cast at this
        rw [this, one_smul]
      rw [e2]
      exact add_mem (L.smul_mem _ h2) (L.smul_mem _ h3)
    obtain ⟨g, sg, mg, hg⟩ := hstep q P L x h hq hi hP hqP hx sh mh
    have hbt : Bet D (stdL D n) (nbr D L x) L := by
      refine ⟨sup_le ?_ ?_, fun y hy => (le_sup_left : nbM D L x ≤ nbr D L x) ⟨hy.2, ?_⟩⟩
      · exact le_sup_of_le_right (le_inf le_sup_left fun y hy => hy.1)
      · exact le_sup_of_le_left (le_inf ((Submodule.span_singleton_le_iff_mem _ _).2 hx0) le_sup_right)
      · exact (((sd_iff D _).1 hsd0).2.2 y).1 hy.1 x hx0
    rw [hg, ih g _ (by omega) sg mg, Iop_smul, hbet _ _ _ hsd0 (sd_of_moves mg) (sd_of_moves mh) hbt _ he0 hnz,
      smul_smul, pow_succ']

end Core

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) : δ ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  rintro rfl
  have h1 := (hL L.ω₁).2 L.ω₁_mem_lattice
  have h2 : lamOf D cc 0 ≤ ⊥ := by
    rw [lamOf, AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  exact L.indep.ne_zero 0 (by simpa using h2 h1)

end GlobalTheory.InertSign

theorem GlobalTheory.InertSign.vacuum_inert : ∀ D : D7, odd3 D := by
  intro D cc δ hc N N' _ e0 he0 W g g' L₁ L₁' sg sg' mg mg'
  have hδ := delta_ne_zero hc
  have hK : ∀ {L : Lat D N} {L' : Lat D N'}, SD D L → SD D L' → KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
    fun h h' => Or.inr ⟨_, _, h, h', rfl⟩
  obtain ⟨-, -, hII, htp⟩ := GlobalTheory.T.kernelLattices_form_selfDual_triples D cc δ hc N N'
  obtain ⟨hTT, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hc N N'
  obtain ⟨d1, d2, d3⟩ := GlobalTheory.T.thetaLattice_triples_distributive D cc δ N N'
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N'
  have hline := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N'
  have s0 : SD D (stdL D N) := sd_of_moves (moves_one D N)
  have s0' : SD D (stdL D N') := sd_of_moves (moves_one D N')
  have m1 : Moves D ((1 * 1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by rw [one_mul]; exact moves_one D N
  have m1' : Moves D ((1 * 1 : GA D N') : GL (Fin N') (AE D)) (stdL D N') := by rw [one_mul]; exact moves_one D N'
  have i1 : IntG D ((1 : GA D N) : GL (Fin N) (AE D)) := by
    have := intG_of_moves (moves_one D N) (moves_one D N)
    rwa [inv_one, one_mul] at this
  have i1' : IntG D ((1 : GA D N') : GL (Fin N') (AE D)) := by
    have := intG_of_moves (moves_one D N') (moves_one D N')
    rwa [inv_one, one_mul] at this
  have he0T := hTT _ _ s0 s0' e0 he0
  have hdist : ∀ A₁ A₂ A₃, KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → Dist A₁ A₂ A₃ →
      ∀ e ∈ ThSp D (tor0 D cc δ) (N := N) (N' := N') A₁, e ≠ 0 →
      Iop D (tor0 D cc δ) A₂ A₃ (Iop D (tor0 D cc δ) A₁ A₂ e) = Iop D (tor0 D cc δ) A₁ A₃ e := by
    intro A₁ A₂ A₃ k₁ k₂ k₃ hd e he hne
    obtain ⟨μ, hμ⟩ := htp A₁ A₂ A₃ k₁ k₂ k₃ e he hne
    have h1 := GlobalTheory.T.thetaTripleConstant_eq_one_distributive D _ N N' _ _ _ e μ hμ hd
    rw [hμ.2.2.2.2.2.2.2.2.2, h1]
    funext z; rw [one_mul]
  have htr : ∀ A₁ A₂ A₃, KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ →
      ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) →
      TriDat D (tor0 D cc δ) A₁ A₂ A₃ P r → ∀ e ∈ ThSp D (tor0 D cc δ) (N := N) (N' := N') A₁, e ≠ 0 →
      Iop D (tor0 D cc δ) A₂ A₃ (Iop D (tor0 D cc δ) A₁ A₂ e) = ((-1 : ℂ) ^ r) • Iop D (tor0 D cc δ) A₁ A₃ e := by
    intro A₁ A₂ A₃ k₁ k₂ k₃ P r hP hst ha hd e he hne
    obtain ⟨μ, hμ⟩ := htp A₁ A₂ A₃ k₁ k₂ k₃ e he hne
    have h1 := GlobalTheory.T.thetaTripleConstant_eq_neg_one_pow D _ N N' _ _ _ e μ hμ P r hP hst ha hd
    rw [hμ.2.2.2.2.2.2.2.2.2, h1]
    rfl
  have hsq : ∀ r : ℕ, (-1 : ℂ) ^ r * (-1) ^ r = 1 := fun r => by rw [← mul_pow]; simp
  have c1 := core (T := tor0 D cc δ) (fun L => La D (tor0 D cc δ) L (stdL D N')) (fun h => W.Om h 1) e0 ((-1) ^ N') (hsq _) W.nz he0
    (fun _ _ a b e he => ⟨(huni _ _ (hK a s0') (hK b s0') e he).2.1, (huni _ _ (hK a s0') (hK b s0') e he).2.2.2⟩)
    (fun _ a => hII _ (hK a s0')) (fun _ a => (hline _ (hK a s0')).1)
    (fun a b => by rw [← W.mul a b 1 1 e0 he0T, one_mul])
    (fun a L hL F hF c => W.smul a 1 c F (hTT _ _ hL s0' F hF))
    (fun k a b => W.inert k 1 a i1' b (suppInert_one D N'))
    (fun h L a => GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W h 1 1 1 _ _ _ _ (moves_one D N) (moves_one D N') (by rwa [mul_one]) m1' e0 he0)
    (fun a h k _ _ _ _ b c d e F hF => GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W a h k 1 1 1 _ _ _ _ _ _ _ _ b (moves_one D N') c m1' d
      (moves_one D N') e m1' F hF)
    (fun _ _ _ a b c d => hdist _ _ _ (hK a s0') (hK b s0') (hK c s0') (d2 _ _ _ _ a c d))
    (fun P A B C a b c d => htr _ _ _ (hK d.1 s0') (hK d.2.1 s0') (hK d.2.2.1 s0') P N' a b c
      (GlobalTheory.T.thetaTripleDiagonalData_of_selfDualNeighbourTriple D cc δ hc.1.1 hδ N N' P a b A B C d)) g L₁ sg mg
  have c2 := core (T := tor0 D cc δ) (fun L => La D (tor0 D cc δ) (stdL D N) L) (fun h => W.Om 1 h) e0 ((-1) ^ N) (hsq _) W.nz he0
    (fun _ _ a b e he => ⟨(huni _ _ (hK s0 a) (hK s0 b) e he).2.1, (huni _ _ (hK s0 a) (hK s0 b) e he).2.2.2⟩)
    (fun _ a => hII _ (hK s0 a)) (fun _ a => (hline _ (hK s0 a)).1)
    (fun a b => by rw [← W.mul 1 1 a b e0 he0T, one_mul])
    (fun a L hL F hF c => W.smul 1 a c F (hTT _ _ s0 hL F hF))
    (fun k a b => W.inert 1 k i1 a (suppInert_one D N) b)
    (fun h L a => GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W 1 1 h 1 _ _ _ _ (moves_one D N) (moves_one D N') m1 (by rwa [mul_one]) e0 he0)
    (fun a h k _ _ _ _ b c d e F hF => GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W 1 1 1 a h k _ _ _ _ _ _ _ _ (moves_one D N) b m1 c
      (moves_one D N) d m1 e F hF)
    (fun _ _ _ a b c d => hdist _ _ _ (hK s0 a) (hK s0 b) (hK s0 c) (d1 _ _ _ _ a c d))
    (fun P A B C a b c d => htr _ _ _ (hK s0 d.1) (hK s0 d.2.1) (hK s0 d.2.2.1) P N a b c
      (GlobalTheory.T.thetaTripleData_of_neighbourTriple D cc δ hc.1.1 hδ N N' P a A B C d)) g' L₁' sg' mg'
  have sL := sd_of_moves mg
  have sL' := sd_of_moves mg'
  have h1 : W.Om g g' e0 = W.Om 1 g' (W.Om g 1 e0) := by rw [← W.mul 1 g g' 1 e0 he0T, one_mul, mul_one]
  have hI1 := (huni _ _ (hK s0 s0') (hK sL s0') e0 he0).2.1
  have h2 := GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner D cc δ hc hδ N N' e0 W 1 1 g g' 1 1 _ _ _ _ _ _ _ _ (moves_one D N) (moves_one D N') m1
    (by rw [mul_one]; exact mg') mg (moves_one D N') (by rw [one_mul]; exact mg) (by rw [mul_one]; exact mg') e0 he0
  rw [h1, c1, W.smul 1 g' _ _ (hTT _ _ sL s0' _ hI1), h2, c2, Iop_smul,
    hdist _ _ _ (hK s0 s0') (hK s0 sL') (hK sL sL') (d3 _ _ _ _ s0' sL') e0 he0 W.nz]
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, La0, pow_add, pow_mul]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlacesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places : ∀ D : D7, odd3 D := by
  first | exact @GlobalTheory.InertSign.vacuum_inert | exact GlobalTheory.InertSign.vacuum_inert | (intros; apply GlobalTheory.InertSign.vacuum_inert <;> assumption)
end
