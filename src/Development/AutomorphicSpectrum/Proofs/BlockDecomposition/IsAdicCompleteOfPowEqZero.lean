module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PerfectWittMaps

theorem isAdicComplete_of_pow_eq_zero (p : ℕ) {B : Type} [CommRing B] {n : ℕ} (hn : (p : B) ^ n = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hI : (Ideal.span {(p : B)}) ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn]; simp
  have hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y := by
    intro x y h
    rw [hI] at h
    simpa [SModEq.bot] using h
  refine { haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hmn
  · exact h hmn
  · rw [hz0 _ _ (h hmn)]

theorem exists_pow_pow_eq (p : ℕ) {A : Type} [CommRing A] (h : Function.Bijective fun x : A => x ^ p)
    (k : ℕ) (a : A) : ∃ b : A, b ^ p ^ k = a := by
  induction k generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h.2 a
    obtain ⟨b, hb⟩ := ih c
    refine ⟨b, ?_⟩
    rw [pow_succ, pow_mul, hb]
    exact hc

theorem exists_lift (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] [IsAdicComplete (Ideal.span {(p : B)}) B] (J : Ideal B)
    (hpJ : (p : B) ∈ J) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) (g : A →+* B ⧸ J) :
    ∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a := by
  let φ : B ⧸ J →+* ModP B p := Ideal.Quotient.lift J
    ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by
      intro x hx
      rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ x hx)
  let σ : A →+* A := ((frobeniusEquiv A p).symm : A ≃+* A)
  let g₁ : A →+* ModP B p := φ.comp (g.comp σ)
  let G : A →+* PreTilt B p := Perfection.lift p A (ModP B p) g₁
  have hle : Ideal.span {(p : B)} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hpJ
  let res : ModP B p →+* B ⧸ J := Ideal.Quotient.factor hle
  have hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u) := fun u => rfl
  have hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p) := by
      simp [φ, frobenius_def]
    rw [this, ← hres, map_pow]
  refine ⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩
  have h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a)
      = (G a).untilt := by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
  have h3 : PreTilt.coeff 0 (G a) = g₁ a := rfl
  rw [h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]
  change res (φ (g (σ a))) = g a
  rw [hφ, ← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p A p a

theorem lift_unique (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] (J : Ideal B) (n : ℕ) (hbij : Function.Bijective fun x : A => x ^ p)
    (hn : (p : B) ^ n = 0) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)})
    (f f' : WittVector p A →+* B)
    (h : ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) =
      Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) : f = f' := by
  refine WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_
  obtain ⟨b, rfl⟩ := exists_pow_pow_eq p hbij (n + 1) a
  rw [map_pow, map_pow, map_pow]
  set u := f (WittVector.teichmuller p b)
  set v := f' (WittVector.teichmuller p b)
  have huv : u - v ∈ J := Ideal.Quotient.eq.1 (h b)
  have h1 : (p : B) ∣ u ^ p - v ^ p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow,
      ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ _ huv
  have h2 := dvd_sub_pow_of_dvd_sub h1 n
  have h0 : (p : B) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  exact h2

theorem wittVector_lift : ∀ (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] (J : Ideal B) (n : ℕ), D.Pf p A → (p : B) ^ n = 0 → (p : B) ∈ J → (∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) → ∀ g : A →+* B ⧸ J, (∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a) ∧ ∀ f f' : WittVector p A →+* B, (∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) → f = f' := by
  intro p _ A B _ _ J n hA hn hpJ hJ g
  by_cases hB : Subsingleton B
  · have hQ : Subsingleton (B ⧸ J) := (Ideal.Quotient.mk_surjective (I := J)).subsingleton
    refine ⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
               map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩,
      fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩
  · rw [not_subsingleton_iff_nontrivial] at hB
    have hu : ¬IsUnit (p : B) := IsNilpotent.not_isUnit ⟨n, hn⟩
    haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩
    haveI := isAdicComplete_of_pow_eq_zero p hn
    have hAn : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      have h1 : (1 : B) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]
      have h2 := hJ 1 h1
      rw [one_pow, Ideal.mem_span_singleton] at h2
      exact hu (isUnit_of_dvd_one h2)
    haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char
    haveI : PerfectRing A p := ⟨hA.bij⟩
    exact ⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩

end GlobalTheory.CompanionTheory.PerfectWittMaps
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubSubSmulEqZeroOfSmulEqZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TwistedUnit

theorem sub_sub_smul_eq_zero_of_smul_eq_zero {Λ N : Type} [CommRing Λ] [AddCommGroup N]
    [Module Λ N] [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c μ : Λ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (z : N) (hz : μ • z = 0) :
    γ z - z - c • z = 0 := by
  obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Λ) (M := N)
    (f := fun _ : Fin 1 => μ) (x := fun _ : Fin 1 => z) (by simpa using hz)
  choose d hd using h
  have hz' : z = ∑ j, a 0 j • y j := hx 0
  have h0 : ∀ j, μ * a 0 j = 0 := fun j => by simpa using hf j
  have hlin : ∀ j, a 0 j • (γ (y j) - y j - c • y j) = 0 := by
    intro j
    rw [hd, smul_smul, mul_comm, h0, zero_smul]
  have hsum : γ z - z - c • z = ∑ j, a 0 j • (γ (y j) - y j - c • y j) := by
    conv_lhs => rw [hz']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hlin j)

theorem smul_eq_zero_of_fixed {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (x : N) (hx : γ x = x) : μ • x = 0 := by
  have hE := sub_sub_smul_eq_zero_of_smul_eq_zero γ c μ h
  have R : ∀ n : ℕ, ∀ x, (w * ξ) • (γ x - x) = 0 → ∃ u, μ • (x - ξ ^ n • u) = 0 := by
    intro n
    induction n with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ n ih =>
      intro x hx
      obtain ⟨x', hx'⟩ := h x
      have h1 : μ • (x + (w * ξ) • x') = 0 := by
        have : μ • (x + (w * ξ) • x') = (w * ξ) • (γ x - x) := by
          subst hμ
          linear_combination (norm := module) -(w * ξ) • hx'
        rw [this, hx]
      have h2 := hE _ h1
      simp only [map_add (f := _), map_smul] at h2
      have hM : (w * ξ) • (γ x' - x') = 0 := by
        subst hμ
        linear_combination (norm := module) h2 - hx'
      obtain ⟨u, hu⟩ := ih x' hM
      refine ⟨-w • u, ?_⟩
      have : μ • (x - ξ ^ (n + 1) • (-w • u))
          = μ • (x + (w * ξ) • x') - (w * ξ) • (μ • (x' - ξ ^ n • u)) := by
        module
      rw [this, h1, hu]
      simp
  obtain ⟨n, hn⟩ := hξ
  obtain ⟨u, hu⟩ := R n x (by simp [hx])
  simpa [hn] using hu

theorem exists_mem_smul_top {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c μ : Λ) (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ x₁ ∈ 𝔞 • (⊤ : Submodule Λ N), γ x - x - c • x = μ • x₁ := by
  induction hx using Submodule.smul_induction_on' with
  | smul a ha n hn =>
    obtain ⟨n', hn'⟩ := h n
    refine ⟨a • n', Submodule.smul_mem_smul ha trivial, ?_⟩
    rw [map_smul]
    linear_combination (norm := module) a • hn'
  | add x hx y hy ihx ihy =>
    obtain ⟨x₁, hx₁, e₁⟩ := ihx
    obtain ⟨y₁, hy₁, e₂⟩ := ihy
    refine ⟨x₁ + y₁, Submodule.add_mem _ hx₁ hy₁, ?_⟩
    rw [map_add (f := _)]
    linear_combination (norm := module) e₁ + e₂

theorem exists_sub_eq_smul {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  obtain ⟨n, hn⟩ := hξ
  have P : ∀ m k : ℕ, m + k = n → ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
      ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = (μ * ξ ^ k) • x := by
    intro m
    induction m with
    | zero =>
      intro k hk x _
      have : ξ ^ k = 0 := by
        rw [show k = n by omega, hn]
      exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    | succ m ih =>
      intro k hk x hx
      obtain ⟨x₁, hx₁, e⟩ := exists_mem_smul_top γ c μ h 𝔞 x hx
      obtain ⟨y', hy', e'⟩ := ih (k + 1) (by omega) (w • x₁)
        (Submodule.smul_of_tower_mem _ w hx₁)
      have hξx : ξ • x ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ξ) hx
      refine ⟨(w * ξ ^ k) • (ξ • x) - y',
        Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hξx) hy', ?_⟩
      simp only [map_sub, map_smul]
      subst hμ
      linear_combination (norm := module) (w * ξ ^ (k + 1)) • e - e'
  simpa using P n 0 rfl x hx

theorem twisted_bijective_up_to :
    ∀ {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N] [Module.Flat Λ N]
      (γ : N →ₗ[Λ] N) (c w ξ μ : Λ), μ = c * w * ξ → IsNilpotent ξ →
      (∀ x, ∃ x', γ x - x - c • x = μ • x') →
      (∀ x, γ x = x → μ • x = 0) ∧ ∀ (𝔞 : Ideal Λ), ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
        ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  intro Λ N _ _ _ _ γ c w ξ μ hμ hξ h
  exact ⟨smul_eq_zero_of_fixed γ c w ξ μ hμ hξ h,
    fun 𝔞 x hx => exists_sub_eq_smul γ c w ξ μ hμ hξ h 𝔞 x hx⟩

end GlobalTheory.CompanionTheory.TwistedUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDetEmbMat
noncomputable section

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps
open scoped Classical

section Coord

variable {Qp Om LL BdR : Type} [Field Qp] [Field Om] [Field LL] [CommRing BdR]
  [Algebra Qp Om] [Algebra Qp LL] [Algebra Qp BdR] [Algebra Om BdR] [IsScalarTower Qp Om BdR]

def ev (σ : LL →ₐ[Qp] Om) : (Fin 1 → LL) ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift
    ((LinearMap.mul Qp BdR).comp
      (((IsScalarTower.toAlgHom Qp Om BdR).toLinearMap.comp σ.toLinearMap).comp
        (LinearMap.proj 0 : (Fin 1 → LL) →ₗ[Qp] LL)))

@[simp] theorem ev_tmul (σ : LL →ₐ[Qp] Om) (v : Fin 1 → LL) (b : BdR) :
    ev σ (v ⊗ₜ[Qp] b) = algebraMap Om BdR (σ (v 0)) * b := by
  simp [ev]

theorem ev_smul (σ : LL →ₐ[Qp] Om) (c : LL) (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (c • z) = algebraMap Om BdR (σ c) * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', mul_assoc]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

variable [FiniteDimensional Qp LL] [Algebra.IsSeparable Qp LL] [IsAlgClosed Om]


variable (Qp Om LL) in
def embBasis : Basis (LL →ₐ[Qp] Om) Qp LL :=
  (finBasis Qp LL).reindex (Fintype.equivFinOfCardEq (AlgHom.card Qp LL Om)).symm


variable (Qp Om LL) in
def embMat : Matrix (LL →ₐ[Qp] Om) (LL →ₐ[Qp] Om) Om :=
  Algebra.embeddingsMatrixReindex Qp Om (embBasis Qp Om LL) (Equiv.refl _)

theorem embMat_apply (i j : LL →ₐ[Qp] Om) : embMat Qp Om LL i j = j (embBasis Qp Om LL i) := rfl

theorem isUnit_det_embMat : IsUnit (embMat Qp Om LL).det := by
  refine isUnit_iff_ne_zero.2 fun h => ?_
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Qp Om (embBasis Qp Om LL) (Equiv.refl _)
  have h2 : algebraMap Qp Om (Algebra.discr Qp (embBasis Qp Om LL)) = 0 := by
    rw [h1]; change (embMat Qp Om LL).det ^ 2 = 0; rw [h]; simp
  exact Algebra.discr_not_zero_of_basis Qp (embBasis Qp Om LL)
    ((map_eq_zero_iff _ (algebraMap Qp Om).injective).1 h2)

def coordInv (f : (LL →ₐ[Qp] Om) → BdR) : (Fin 1 → LL) ⊗[Qp] BdR :=
  ∑ i, (fun _ => embBasis Qp Om LL i) ⊗ₜ[Qp]
    ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j

theorem ev_coordInv (f : (LL →ₐ[Qp] Om) → BdR) (k : LL →ₐ[Qp] Om) :
    ev k (coordInv f) = f k := by
  have hN : (embMat Qp Om LL)⁻¹ * embMat Qp Om LL = 1 := Matrix.nonsing_inv_mul _ isUnit_det_embMat
  have h1 : ∀ j, ∑ i, embMat Qp Om LL i k * (embMat Qp Om LL)⁻¹ j i = if j = k then 1 else 0 := fun j => by
    have := congrFun (congrFun hN j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordInv, map_sum, ev_tmul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, algebraMap Om BdR (k (embBasis Qp Om LL i)) *
      (algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j) =
      algebraMap Om BdR (if j = k then 1 else 0) * f j := fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1 j, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, embMat_apply, mul_assoc]
  simp only [h2]
  simp

theorem coordInv_add (f g : (LL →ₐ[Qp] Om) → BdR) : coordInv (f + g) = coordInv f + coordInv g := by
  simp only [coordInv, Pi.add_apply, mul_add, Finset.sum_add_distrib, tmul_add]

theorem coordInv_ev (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    coordInv (fun σ : LL →ₐ[Qp] Om => ev σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add x y hx hy =>
    nth_rw 2 [← hx]
    nth_rw 2 [← hy]
    rw [← coordInv_add]
    congr 1
    funext σ
    exact map_add (ev σ) x y
  | tmul v b =>
    have hM : embMat Qp Om LL * (embMat Qp Om LL)⁻¹ = 1 := Matrix.mul_nonsing_inv _ isUnit_det_embMat
    set a := (embBasis Qp Om LL).repr (v 0) with ha
    have hv : v 0 = ∑ k, a k • embBasis Qp Om LL k := ((embBasis Qp Om LL).sum_repr (v 0)).symm
    have h1 : ∀ i, ∑ j, (embMat Qp Om LL)⁻¹ j i * j (v 0) = algebraMap Qp Om (a i) := fun i => by
      have h2 : ∀ j : LL →ₐ[Qp] Om, j (v 0) = ∑ k, algebraMap Qp Om (a k) * embMat Qp Om LL k j := fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hv, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, Algebra.smul_def, embMat_apply]
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ k, ∑ j, (embMat Qp Om LL)⁻¹ j i * (algebraMap Qp Om (a k) * embMat Qp Om LL k j) =
          algebraMap Qp Om (a k) * (if k = i then 1 else 0) := fun k => by
        have := congrFun (congrFun hM k) i
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [h3]
      simp
    have h4 : ∀ i, ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) *
        (algebraMap Om BdR (j (v 0)) * b) = a i • b := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Qp Om BdR, ← h1, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    simp only [coordInv, ev_tmul, h4, tmul_smul]
    have h5 : v = ∑ i, a i • (fun _ : Fin 1 => embBasis Qp Om LL i) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact hv
    conv_rhs => rw [h5, sum_tmul]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem ev_injective {z w : (Fin 1 → LL) ⊗[Qp] BdR} (h : ∀ σ : LL →ₐ[Qp] Om, ev σ z = ev σ w) : z = w := by
  rw [← coordInv_ev (Om := Om) z, ← coordInv_ev (Om := Om) w]
  exact congrArg _ (funext h)

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR_iff (ρ : Representation LL G V) (z : V ⊗[Qp] BdR) :
    z ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g z = z := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_DdRE_iff (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (z : V ⊗[Qp] BdR) :
    z ∈ DdRE PD ρ τ ↔ z ∈ DdR PD ρ ∧
      ∀ c, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c z = τ c • z := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem exists_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ)
    (h : ∀ a, multV PD ρ τ a = if a = J then 1 else 0) :
    ∃ z ∈ DdRE PD ρ τ, (∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z) ∧
      z ∈ FilV PD (LL := LL) (V := V) J ∧ z ∉ FilV PD (LL := LL) (V := V) (J + 1) := by
  haveI : FiniteDimensional LL (DdRE PD ρ τ) :=
    finite_ddRE_of_multV PD ρ τ {J} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have hanti : ∀ a, FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := fun a =>
    inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1))
  have h1 : finrank LL (DdRE PD ρ τ) = 1 :=
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left) hanti
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) J h
  have hJ := h J
  rw [if_pos rfl] at hJ
  unfold multV at hJ
  have hle : finrank LL (FildR PD ρ τ J) ≤ 1 := by
    rw [← h1]; exact Submodule.finrank_mono inf_le_left
  have h2 : finrank LL (FildR PD ρ τ J) = 1 := by omega
  have h3 : finrank LL (FildR PD ρ τ (J + 1)) = 0 := by omega
  have h4 : FildR PD ρ τ J = DdRE PD ρ τ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, h2])
  haveI : FiniteDimensional LL (FildR PD ρ τ (J + 1)) := Submodule.finiteDimensional_of_le inf_le_left
  have h5 : FildR PD ρ τ (J + 1) = ⊥ := Submodule.finrank_eq_zero.1 h3
  obtain ⟨z, hz0, hz⟩ := finrank_eq_one_iff'.1 h1
  have hz1 : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ J := by rw [h4]; exact z.2
  refine ⟨z, z.2, fun w hw => ?_, hz1.2, fun hz2 => ?_⟩
  · obtain ⟨c, hc⟩ := hz ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · have : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ (J + 1) := ⟨z.2, hz2⟩
    rw [h5, Submodule.mem_bot] at this
    exact hz0 (Subtype.ext this)

theorem multV_of_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ DdRE PD ρ τ) (hgen : ∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z)
    (h1 : z ∈ FilV PD (LL := LL) (V := V) J) (h2 : z ∉ FilV PD (LL := LL) (V := V) (J + 1)) (a : ℤ) :
    multV PD ρ τ a = if a = J then 1 else 0 := by
  have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hlo : ∀ a ≤ J, FildR PD ρ τ a = LL ∙ z := fun a ha => by
    refine le_antisymm (fun w hw => ?_) ?_
    · obtain ⟨c, rfl⟩ := hgen w hw.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hz, filV_anti PD ha h1⟩
  have hhi : ∀ a, J < a → FildR PD ρ τ a = ⊥ := fun a ha => by
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨c, rfl⟩ := hgen w hw.1
    by_cases hc : c = 0
    · simp [hc]
    · refine absurd ?_ h2
      have := filV_anti PD (by omega : J + 1 ≤ a) hw.2
      simpa [hc] using (Submodule.smul_mem_iff _ hc).1 this
  have hone : finrank LL (LL ∙ z) = 1 := finrank_span_singleton hz0
  unfold multV
  rcases lt_trichotomy a J with ha | ha | ha
  · rw [hlo a ha.le, hlo (a + 1) (by omega), if_neg ha.ne]; simp
  · subst ha
    rw [hlo a le_rfl, hhi (a + 1) (by omega), if_pos rfl, hone]; simp
  · rw [hhi a ha, hhi (a + 1) (by omega), if_neg ha.ne']; simp

end Period

end GlobalTheory.CompanionTheory.DeRhamChar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansion
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.QPd

theorem exists_sub_one_pow {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] (x : B) :
    ∃ z : B, (x - 1) ^ (p - 1) = (∑ i ∈ Finset.range p, x ^ i) - (p : B) * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : ((X - 1 : (ZMod p)[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
    have h1 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
      simpa using sub_pow_char (X : (ZMod p)[X]) 1
    have h2 : (X - 1 : (ZMod p)[X]) * ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i = X ^ p - 1 :=
      mul_geom_sum _ _
    have h3 : (X - 1 : (ZMod p)[X]) ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    have h4 : (X - 1 : (ZMod p)[X]) * ((X - 1) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
      rw [mul_sub, h2, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left h3
  have hdvd : C (p : ℤ) ∣ ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i) := by
    have hmap : ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map
        (Int.castRingHom (ZMod p)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Polynomial.map_sum] using hmod
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have h5 := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) hmap
    simp only [coeff_map, coeff_zero] at h5
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using h5)
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨-aeval x g, ?_⟩
  have := congrArg (aeval x) hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_pow, aeval_X, map_one, map_sum, map_mul, aeval_C] at this
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at this
  linear_combination this

theorem not_dvd_choose {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ (a * p + c).choose c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a * p + c) (k := c)
  have h1 : (a * p + c) % p = c := by
    rw [Nat.mul_add_mod_of_lt hc] <;> simp
  have h2 : c % p = c := Nat.mod_eq_of_lt hc
  have h3 : c / p = 0 := Nat.div_eq_of_lt hc
  rw [h1, h2, h3] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans h
  have := (Nat.modEq_iff_dvd.1 h0)
  simp at this
  have h5 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h5)

theorem not_dvd_uniformBell {p : ℕ} (hp : p.Prime) (a : ℕ) : ¬ p ∣ Nat.uniformBell a p := by
  induction a with
  | zero => simpa [Nat.uniformBell_zero_left] using hp.one_lt.ne'
  | succ a ih =>
    rw [Nat.uniformBell_succ_left]
    intro h
    rcases (hp.dvd_mul).1 h with h | h
    · refine not_dvd_choose hp a (p - 1) (Nat.sub_lt hp.pos one_pos) ?_
      have h6 : a * p + (p - 1) = a * p + p - 1 := by have := hp.pos; omega
      rwa [h6]
    · exact ih h

theorem exists_inv {B : Type} [CommRing B] {p N : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B))
    (h : ¬ p ∣ N) : ∃ v : B, v * N = 1 := by
  obtain ⟨e, he⟩ := hnil
  have hc : IsCoprime (N : ℤ) ((p : ℤ) ^ e) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨s, t, hst⟩ := hc
  refine ⟨s, ?_⟩
  have := congrArg (Int.cast : ℤ → B) hst
  push_cast at this
  rw [he] at this
  simpa using this

theorem pow_dvd_factorial {p : ℕ} (hp : p.Prime) (e : ℕ) : p ^ e ∣ (p * e).factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_pow_eq_zero {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ}
    (hp : p.Prime) (hnil : IsNilpotent (p : B)) : ∃ n : ℕ, ∀ y ∈ J, y ^ n = 0 := by
  obtain ⟨e, he⟩ := hnil
  refine ⟨p * e, fun y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := pow_dvd_factorial hp e
  rw [← δ.factorial_mul_dpow_eq_pow hy, hk]
  push_cast
  rw [he]
  simp

theorem not_dvd_coeff {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial := by
  rw [Nat.choose_symm_add]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact not_dvd_uniformBell hp a h
    · exact not_dvd_choose hp a c hc h
  · exact absurd ((hp.dvd_factorial).1 h) (not_le.2 hc)

section
variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

theorem coeff_mul_dpow {p : ℕ} (hp : p.Prime) {μ w : B} (hμ : μ ∈ J) (hw : w ∈ J)
    (h : δ.dpow p μ = μ * w) (a c : ℕ) :
    ((Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial : ℕ) : B) *
        δ.dpow (a * p + c) μ = μ ^ (a + c) * δ.dpow a w := by
  have h1 : (Nat.uniformBell a p : B) * δ.dpow (a * p) μ = μ ^ a * δ.dpow a w := by
    rw [← δ.dpow_comp hp.ne_zero hμ, h, δ.dpow_mul hw]
  have h2 := δ.mul_dpow (m := a * p) (n := c) hμ
  have h3 := δ.factorial_mul_dpow_eq_pow (n := c) hμ
  push_cast
  rw [pow_add]
  linear_combination (-(Nat.uniformBell a p : B) * (c.factorial : B)) * h2 +
    (c.factorial : B) * δ.dpow c μ * h1 + μ ^ a * δ.dpow a w * h3

theorem exists_dpow_prime_eq {p : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B)) (x : B)
    (hξ : (∑ i ∈ Finset.range p, x ^ i) ∈ J) :
    ∃ w ∈ GlobalTheory.Cris.ExpBij.dpFil δ (p - 1), δ.dpow p (x ^ p - 1) = (x ^ p - 1) * w := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  simp only [Nat.add_sub_cancel] at *
  set ξ := ∑ i ∈ Finset.range (q + 1), x ^ i with hξdef
  obtain ⟨z, hz⟩ := exists_sub_one_pow hp x
  simp only [Nat.add_sub_cancel, ← hξdef] at hz
  obtain ⟨u, hu⟩ := exists_inv (N := q.factorial) hp hnil
    (fun h ↦ absurd ((hp.dvd_factorial).1 h) (by omega))
  have hμ : x ^ (q + 1) - 1 = (x - 1) * ξ := (mul_geom_sum x (q + 1)).symm
  have h2 := δ.factorial_mul_dpow_eq_pow (n := q + 1) hξ
  rw [Nat.factorial_succ] at h2
  push_cast at h2 hz
  refine ⟨δ.dpow (q + 1) ξ - z * u * ξ ^ q, ?_, ?_⟩
  · refine Ideal.sub_mem _ (GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ q)
      (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hξ _)) (Ideal.mul_mem_left _ _ ?_)
    simpa using GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hξ) q
  · rw [hμ, δ.dpow_mul hξ, pow_succ]
    linear_combination (x - 1) * δ.dpow (q + 1) ξ * hz +
      (x - 1) * z * ((q : B) + 1) * δ.dpow (q + 1) ξ * hu - (x - 1) * z * u * h2

end

theorem dpow_pow_sub_one : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  intro B _ J δ p hp hnil x hξ
  have hμJ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hξ
  obtain ⟨n, hn⟩ := exists_pow_eq_zero δ hp hnil
  obtain ⟨w, hwf, hw⟩ := exists_dpow_prime_eq δ hp hnil x hξ
  have hp2 := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hwJ : w ∈ J := GlobalTheory.Cris.ExpBij.dpFil_le δ hp1 hwf
  generalize x ^ p - 1 = μ at hμJ hw ⊢
  have key : ∀ m, ∃ b : B, (m = 1 → b = 1) ∧
      (1 ≤ m → δ.dpow m μ = μ * b ∧ b ∈ GlobalTheory.Cris.ExpBij.dpFil δ (m - 1)) ∧
      (p * (n + 2) ≤ m → b = 0) := by
    intro m
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact ⟨0, by simp, by simp, fun _ ↦ rfl⟩
      · refine ⟨1, fun _ ↦ rfl, fun _ ↦ ⟨by rw [δ.dpow_one hμJ, mul_one],
          GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ 1⟩, fun h ↦ ?_⟩
        nlinarith
    · obtain ⟨a, c, hc, rfl⟩ : ∃ a c, c < p ∧ a * p + c = m :=
        ⟨m / p, m % p, Nat.mod_lt _ hp.pos, Nat.div_add_mod' m p⟩
      obtain ⟨v, hv⟩ := exists_inv hp hnil (not_dvd_coeff hp a c hc)
      have hco := coeff_mul_dpow δ hp hμJ hwJ hw a c
      obtain ⟨k, hk⟩ : ∃ k, a + c = k + 1 := by
        refine ⟨a + c - 1, ?_⟩
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [zero_mul, zero_add] at h ⊢
          omega
        · omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      refine ⟨v * (μ ^ k * δ.dpow a w), fun h1 ↦ by omega, fun _ ↦ ⟨?_, ?_⟩, fun hM ↦ ?_⟩
      · calc δ.dpow (a * (q + 1) + c) μ
            = (v * ((Nat.uniformBell a (q + 1) * (a * (q + 1) + c).choose (a * (q + 1)) *
                c.factorial : ℕ) : B)) * δ.dpow (a * (q + 1) + c) μ := by rw [hv, one_mul]
          _ = v * (μ ^ (a + c) * δ.dpow a w) := by rw [mul_assoc, hco]
          _ = μ * (v * (μ ^ k * δ.dpow a w)) := by rw [hk, pow_succ]; ring
      · have h5 := GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ
          (GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hμJ) k)
          (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hp1 hwf a)
        have e : a * (q + 1) + c - 1 = k * 1 + a * (q + 1 - 1) := by
          rw [Nat.add_sub_cancel, Nat.mul_succ]
          omega
        rw [e]
        exact Ideal.mul_mem_left _ _ h5
      · have h6 : n + 2 ≤ a := by
          by_contra hlt
          have h7 : a + 1 ≤ n + 2 := by omega
          have h8 := Nat.mul_le_mul_left (q + 1) h7
          nlinarith
        have h9 : μ ^ k = 0 := pow_eq_zero_of_le (by omega : n ≤ k) (hn μ hμJ)
        simp [h9]
  choose ν h1 h2 h3 using key
  refine ⟨⟨n, hn _ hμJ⟩, ν, h1 1 rfl, fun m ↦ (h2 (m + 1) (by omega)).1, fun m ↦ ?_, fun m hm ↦ ?_,
    p * (n + 2), fun m hm ↦ h3 m hm⟩
  · have h := (h2 (m + 1) (by omega)).2
    rw [Nat.add_sub_cancel] at h
    exact h
  · exact ⟨n, hn _ (GlobalTheory.Cris.ExpBij.dpFil_le δ (show 1 ≤ m - 1 by omega) (h2 m (by omega)).2)⟩

end GlobalTheory.CompanionTheory.QPd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclotomicDividedPowerExpansionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_divided_power_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | exact GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one | (intros; apply GlobalTheory.CompanionTheory.QPd.dpow_pow_sub_one <;> assumption)
end
end
