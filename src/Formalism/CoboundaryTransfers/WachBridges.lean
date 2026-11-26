module

public import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds
public import Formalism.WachModuleLifts.StatementW
public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt

@[expose] public section

section -- merged from Formalism.CoboundaryTransfers.StatementBridge
noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section CL

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

variable {B : CL.W.Base p A} {η : ℕ}

variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']

end CL

section CLback

def Base.QLin {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) : Prop :=
  B.Q = B.X + (B.p : A)

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]

def toCL (B : Base ℤ_[p] A) (hp : B.p = p) (hq : B.QLin) (hφ : B.PhiX (p - 1)) :
    CL.W.Base p A where
  φA := B.φ
  γA := B.γ
  π₀ := B.X
  q := B.Q
  hq := by simpa [Base.QLin, hp] using hq
  hφ := hφ
  comm := B.comm

def WachMod.toCL {B : Base ℤ_[p] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] (W : WachMod B M D) (hp : B.p = p)
    (hq : B.QLin) (hφ : B.PhiX (p - 1)) : CL.W.WachMod (toCL B hp hq hφ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  π₀_inj := W.X_inj
  q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N
  γ_qN := W.γ_QN

end CLback

section LIFT

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]

variable {B : LIFT.Base ℓ A} {M : ℕ}

def toLIFT (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q)
    (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) : LIFT.Base ℓ A where
  φA := B.φ
  γA := B.γ
  X := B.X
  Q := B.Q
  u := u
  comm := B.comm
  φX := hφ
  γX := hγX
  γQ := by
    obtain ⟨v, hv, ⟨t, rfl⟩, hγ⟩ := hγQ
    exact ⟨t, hv, by rw [hγ, mul_comm]⟩

def WachMod.toLIFT {B : Base ℤ_[ℓ] A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] (W : WachMod B M D) (u : ℤ_[ℓ]ˣ)
    (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.WD (toLIFT B u hφ hγX hγQ) M D where
  N := W.N
  φ := W.φ
  γ := W.γ
  φ_smul := W.φ_smul
  γ_smul := W.γ_smul
  comm := W.comm
  X_inj := W.X_inj
  Q_bij := W.Q_bij
  φ_N := W.φ_N
  γ_N := W.γ_N

end LIFT

end Formalism.CoboundaryTransfers
end
end

section -- merged from Formalism.CoboundaryTransfers.GammaStableTransfers.Transfer
section -- merged from Formalism.CoboundaryTransfers.StatementTransfer
noncomputable section

namespace Formalism.CoboundaryTransfers

def UClaimU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D) (s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W.N) →
    (∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) →
    W.TorsKilled ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
      ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1))

def LemmaUU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W₀.N, ∃ z ∈ W₀.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W₀.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W₀.QInv y → B.X • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ y, W₀.QInv y → Polynomial.aeval W₀.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W₀.N → y ∈ W₀.N) →
    CokerKilled S e → RatSurj S → Lifts S ((ℓ : ℤ_[ℓ]) ^ (e + LIFT.eU ℓ M s J))

end Formalism.CoboundaryTransfers
end
end

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

section Maps

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℤ_[ℓ] A} {M : ℕ}

def homToLIFT {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.Hom (W.toLIFT u hφ hγX hγQ) (W'.toLIFT u hφ hγX hγQ) where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le

def sesToLIFT {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂} (S : SES W₀ W₁ W₂)
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.SES (W₀.toLIFT u hφ hγX hγQ) (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) where
  ι := homToLIFT S.ι u hφ hγX hγQ
  π := homToLIFT S.π u hφ hγX hγQ
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

end Maps

theorem wachLatticeUnramified_statement : LemmaUU := by
  intro ℓ _ A _ _ B M u hp hφ hγX hγQ D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK hRS
  have hCK' : LIFT.CokerKilled (sesToLIFT S u hφ hγX hγQ) e := by
    intro n hn
    have := hCK n hn
    rw [hp] at this
    exact this
  have hRS' : LIFT.RatSurj (sesToLIFT S u hφ hγX hγQ) := by
    intro y z hyz
    have := hRS y z hyz
    rw [hp] at this
    exact this
  exact LIFT.lift_LemmaU ℓ A (toLIFT B u hφ hγX hγQ) M D₀ D₁ D₂ (W₀.toLIFT u hφ hγX hγQ)
    (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) (sesToLIFT S u hφ hγX hγQ) e s J hs h2 hv
    hJ h1 h2' h3 h4 hCK' hRS'

end Formalism.CoboundaryTransfers
end
end

section -- merged from Formalism.CoboundaryTransfers.GammaStableTransfers.TorsionKilledCriterionHolds
noncomputable section

namespace Formalism.CoboundaryTransfers

theorem gammaGradedStep_holds : GradedStep := by
  intro O A _ _ _ B M D _ _ _ _ W u hu i n hn
  obtain ⟨t, ht⟩ := hu
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap O A u + B.X * t) ^ k
      = algebraMap O A (u ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap O A u + B.X * t) + algebraMap O A (u ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap O A u + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A (u ^ i) (B.X ^ i • n)]
    module

theorem gammaImageProduct_holds : GammaOnto := by
  intro O A _ _ _ B M D _ _ _ _ W u a hyp
  suffices h : ∀ j, j ≤ a → ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 j, (1 - u ^ i)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (j + 1) • z' from h a le_rfl
  intro j
  induction j with
  | zero => intro _ n hn; exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ j ih =>
    intro hj n hn
    obtain ⟨x, hx, m, hm, he⟩ := ih (by omega) n hn
    obtain ⟨n', hn', hg⟩ := hyp (j+1) (by omega) hj m hm
    refine ⟨(1 - u^(j+1)) • x - B.X ^ j • m, ?_, n', hn', ?_⟩
    · exact W.N.sub_mem (W.N.smul_of_tower_mem _ hx) (W.N.smul_mem _ hm)
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • ((1 - u^(j+1)) • x - B.X ^ j • m)
          = (1 - u^(j+1)) • (B.X • x) - B.X ^ (j+1) • m := by
        rw [smul_sub, smul_comm, smul_smul, ← pow_succ']
      rw [e1, map_sub, LinearMap.map_smul, hg]
      simp only [smul_sub, smul_add, sub_smul, one_smul]
      abel

section Claim
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

lemma aeval_stable (δ : D →ₗ[O] D) (S : Submodule O D) (hS : ∀ y ∈ S, δ y ∈ S)
    (f : Polynomial O) : ∀ y ∈ S, Polynomial.aeval δ f y ∈ S := by
  induction f using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact S.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add (f := _), LinearMap.add_apply]
    exact S.add_mem (hp y hy) (hq y hy)
  | monomial n a ih =>
    intro y hy
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS y hy)

def QS (W : WachMod B M D) : Submodule O D where
  carrier := {y | B.Q ^ M • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.Q ^ M • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.Q ^ M • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.Q ^ M • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy

lemma N_QInv (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := W.N.smul_mem _ hx

lemma QInv_smulA (W : WachMod B M D) (b : A) {y : D} (hy : W.QInv y) : W.QInv (b • y) := by
  show B.Q ^ M • (b • y) ∈ W.N
  rw [smul_comm]
  exact W.N.smul_mem b hy

lemma δ_QInv (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ y, W.QInv y → W.QInv (δ y) := by
  intro y hy
  obtain ⟨y', hy', hyy⟩ := W.γ_QN y hy
  have h3 : δ y = y' := by
    have h := W.X_inj (δ y - y') (by rw [smul_sub, h2, hyy, sub_self])
    exact sub_eq_zero.mp h
  show B.Q ^ M • δ y ∈ W.N
  rw [h3]
  exact hy'

lemma δ_N (W : WachMod B M D) (δ : D →ₗ[O] D) (h2 : ∀ y, B.X • δ y = W.γ y - y) :
    ∀ n ∈ W.N, δ n ∈ W.N := by
  intro n hn
  obtain ⟨x', hx', hxx⟩ := W.γ_N n hn
  have h3 : δ n = x' := by
    have h := W.X_inj (δ n - x') (by rw [smul_sub, h2, hxx, sub_self])
    exact sub_eq_zero.mp h
  rw [h3]
  exact hx'

lemma claim_key (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O)
    (h1 : B.PhiX k) (h1' : M ≤ k * (a + 1))
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (w : D) (hw : W.QInv w) (j : ℕ) (y z : D) (hyz : W.C1 y z)
    (hj : ((B.p : O) ^ j) • (B.X • w) = W.d1 y z) :
    Polynomial.aeval δ R (cΓ • w) ∈ W.N := by
  have δN := δ_N W δ h2
  have RN : ∀ f : Polynomial O, ∀ n ∈ W.N, Polynomial.aeval δ f n ∈ W.N :=
    fun f => aeval_stable δ (W.N.restrictScalars O) δN f
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  have Lφ : ∀ m ∈ W.N, ∃ m' ∈ W.N, W.φ (B.X ^ (a + 1) • m) = B.X ^ (a + 1) • m' := by
    intro m hm
    obtain ⟨v, hv⟩ := h1
    refine ⟨v ^ (a + 1) • B.Q ^ (k * (a + 1) - M) • (B.Q ^ M • W.φ m),
      W.N.smul_mem _ (W.N.smul_mem _ (W.φ_N m hm)), ?_⟩
    have hexp : B.Q ^ (k * (a + 1) - M) * B.Q ^ M = (B.Q ^ k) ^ (a + 1) := by
      rw [← pow_add, Nat.sub_add_cancel h1', pow_mul]
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc (B.X ^ (a + 1) * v ^ (a + 1)), hexp]
    ring
  have φπ : ∀ x ∈ W.N, W.QInv (W.φ (B.X • x)) := by
    intro x hx
    rw [W.φ_smul]; exact QInv_smulA W _ (W.φ_N x hx)
  have tf : ∀ i : ℕ, ∀ v, W.QInv v → ((B.p : O) ^ i) • v ∈ W.N → v ∈ W.N := by
    intro i
    induction i with
    | zero => intro v _ h; simpa using h
    | succ i ih =>
      intro v hv h
      apply ih v hv
      apply h4 _ ((QS W).smul_mem _ hv)
      rw [smul_smul, ← pow_succ']; exact h
  obtain ⟨hy, n, hn, hzn⟩ := hyz
  subst hzn
  obtain ⟨x, hx, z', hz', hc⟩ := h6 n hn
  obtain ⟨m', hm', hφm⟩ := Lφ z' hz'
  set Y' := cΓ • y - (W.φ (B.X • x) - B.X • x) with hY'
  have hY'Q : W.QInv Y' :=
    (QS W).sub_mem ((QS W).smul_mem _ hy) ((QS W).sub_mem (φπ x hx) (N_QInv W (W.N.smul_mem _ hx)))
  have eA : B.X • (cΓ • ((B.p : O) ^ j) • w - δ Y' - B.X ^ a • (z' - m')) = 0 := by
    have e1 : cΓ • ((B.p : O) ^ j) • (B.X • w) = cΓ • W.d1 y (B.X • n) := by rw [hj]
    have e2 : cΓ • W.d1 y (B.X • n) = (W.γ Y' - Y') + (B.X ^ (a + 1) • z' - B.X ^ (a + 1) • m') := by
      simp only [WachMod.d1, smul_sub, ← LinearMap.map_smul, hc, hY', map_sub, map_add (f := _), W.comm, hφm]
      abel
    rw [smul_sub, smul_sub, h2, smul_comm B.X cΓ, smul_comm B.X ((B.p : O) ^ j), e1, e2,
      smul_smul, ← pow_succ', smul_sub]
    abel
  have eA' : cΓ • ((B.p : O) ^ j) • w = δ Y' + B.X ^ a • (z' - m') := by
    have := W.X_inj _ eA; rw [sub_sub, sub_eq_zero] at this; exact this
  have eB : ((B.p : O) ^ j) • (cΓ • Polynomial.aeval δ R w) ∈ W.N := by
    rw [smul_comm, ← LinearMap.map_smul, ← LinearMap.map_smul, eA', map_add (f := _)]
    refine W.N.add_mem ?_ (RN R _ (W.N.smul_mem _ (W.N.sub_mem hz' hm')))
    have : Polynomial.aeval δ R (δ Y') = Polynomial.aeval δ (Polynomial.X * R) Y' := by
      rw [mul_comm, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [this]; exact h3 Y' hY'Q
  rw [LinearMap.map_smul]
  exact tf j _ ((QS W).smul_mem _ (RQ R w hw)) eB

lemma claim_fin (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a : ℕ) (cΓ : O)
    (h2 : ∀ y, B.X • δ y = W.γ y - y)
    (h6 : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z')
    (h7 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z))
    (w : D) (hw : W.QInv w) (hm : Polynomial.aeval δ R w ∈ W.N) :
    W.IsCob2 ((R.eval 0 * cΓ) • (B.X • w)) := by
  have RQ : ∀ f : Polynomial O, ∀ y, W.QInv y → W.QInv (Polynomial.aeval δ f y) :=
    fun f => aeval_stable δ (QS W) (δ_QInv W δ h2) f
  obtain ⟨R1, hR1⟩ := Polynomial.X_dvd_sub_C (p := R)
  have eD : (R.eval 0) • w = Polynomial.aeval δ R w - δ (Polynomial.aeval δ R1 w) := by
    have : R = Polynomial.C (R.coeff 0) + Polynomial.X * R1 := by rw [← hR1]; ring
    conv_rhs => rw [this]
    rw [map_add (f := _), map_mul, Polynomial.aeval_C, Polynomial.aeval_X, LinearMap.add_apply,
      Module.End.mul_apply, Polynomial.coeff_zero_eq_eval_zero, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, Module.End.one_apply]
    abel
  obtain ⟨x2, hx2, z2, hz2, hc2⟩ := h6 _ hm
  obtain ⟨z3, hz3, h73⟩ := h7 z2 hz2
  refine ⟨B.X • x2 - cΓ • Polynomial.aeval δ R1 w, B.X • (B.X ^ a • z3),
    ⟨?_, _, W.N.smul_mem _ hz3, rfl⟩, ?_⟩
  · exact (QS W).sub_mem (N_QInv W (W.N.smul_mem _ hx2)) ((QS W).smul_mem _ (RQ R1 w hw))
  · have e3 : B.X • (B.X ^ a • z3) = B.X ^ (a + 1) • z3 := by rw [smul_smul, ← pow_succ']
    simp only [WachMod.d1, e3]
    have e4 : (R.eval 0 * cΓ) • (B.X • w) = cΓ • (B.X • ((R.eval 0) • w)) := by
      rw [mul_comm, mul_smul, smul_comm (R.eval 0) B.X]
    rw [e4, eD, smul_sub, smul_sub, hc2, h73]
    simp only [h2, map_sub, LinearMap.map_smul, smul_sub]
    abel

theorem torsionKilledCriterion_holds : CoboundaryTransfer := by
  intro O A _ _ _ B M D _ _ _ _ W δ R a k cΓ h1 h1' h2 h3 h4 h5 h6 h7
    ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  rw [LinearMap.map_smul] at hk
  have RQ : W.QInv (Polynomial.aeval δ R w) :=
    aeval_stable δ (QS W) (δ_QInv W δ h2) R w hw
  exact claim_fin W δ R a cΓ h2 h6 h7 w hw (h5 _ RQ hk)

end Claim

end Formalism.CoboundaryTransfers
end
end

noncomputable section

namespace Formalism.CoboundaryTransfers

theorem lift_wach (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (hW : CokerKilled S e) (hQ : RatSurj S)
    (δ : D₀ →ₗ[O] D₀) (R : Polynomial O) (a k : ℕ) (u : O)
    (hk : B.PhiX k) (ha : M ≤ k * (a + 1))
    (hδ : ∀ y, B.X • δ y = W₀.γ y - y)
    (hR : ∀ y, W₀.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W₀.N)
    (hZ : ∀ y, W₀.QInv y → (B.p : O) • y ∈ W₀.N → y ∈ W₀.N)
    (hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • y ∈ W₀.N → y ∈ W₀.N)
    (hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n')
    (hφ : ∀ n ∈ W₀.N, ∃ z ∈ W₀.N,
      B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W₀.φ (B.X ^ (a + 1) • z)) :
    Lifts S ((B.p : O) ^ e * (R.eval 0 * ∏ i ∈ Finset.Icc 1 a, (1 - u ^ i))) :=
  cocycleLiftOfExact_holds O A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hW hQ
    (torsionKilledCriterion_holds O A B M D₀ W₀ δ R a k _ hk ha hδ hR hZ hZu
      (gammaImageProduct_holds O A B M D₀ W₀ u a hgr) hφ)

end Formalism.CoboundaryTransfers
