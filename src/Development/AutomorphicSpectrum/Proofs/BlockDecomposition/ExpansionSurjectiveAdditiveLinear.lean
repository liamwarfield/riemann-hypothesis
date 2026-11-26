module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinear
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinear
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil.Expand

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem natCast_l_acr : (l : A.Acr 1) = 0 := by
  simpa using A.pow_l_acr 1

theorem dxi_zero : A.dxi 1 0 = 1 := by
  rw [PAlg.dxi, divided_power_xi_zero, map_one]

theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = (((i + j).choose i : ℕ) : A.Acr 1) * A.dxi 1 (i + j) := by
  simp only [PAlg.dxi]
  rw [← map_mul, divided_power_xi_mul, map_mul, map_natCast]

theorem dxi_succ (m : ℕ) :
    A.dxi 1 m * A.dxi 1 1 = ((m + 1 : ℕ) : A.Acr 1) * A.dxi 1 (m + 1) := by
  rw [dxi_mul, Nat.choose_succ_self_right]

theorem dxi_one_pow (n : ℕ) : A.dxi 1 1 ^ n = (n.factorial : A.Acr 1) * A.dxi 1 n := by
  induction n with
  | zero => simp [dxi_zero]
  | succ n ih =>
    rw [pow_succ, ih, mul_assoc, dxi_succ, Nat.factorial_succ]
    push_cast
    ring

theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  have h := A.aTo1_coeff A.xi
  rw [xi_coeff_zero, toAcr_xi, map_neg] at h
  rw [← h, neg_neg]

theorem aTo1_pi_pow : A.aTo1 A.pi ^ l = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hp.pos (le_refl l)
  rw [aTo1_pi, neg_pow, dxi_one_pow, ht]
  push_cast
  rw [natCast_l_acr]
  simp

theorem exists_inv {a : ℕ} (h : ¬ l ∣ a) : ∃ m : ℕ, (m : A.Acr 1) * (a : A.Acr 1) = 1 := by
  have hp : l.Prime := Fact.out
  have hc : Nat.Coprime a l := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp.one_lt
  refine ⟨m, ?_⟩
  have e := Nat.div_add_mod (a * m) l
  rw [hm.2] at e
  have e' := congrArg (Nat.cast : ℕ → A.Acr 1) e
  push_cast at e'
  rw [natCast_l_acr, zero_mul, zero_add] at e'
  rw [mul_comm]
  exact e'.symm

theorem dxi_lq_add (q j : ℕ) (hj : j < l) :
    ∃ n : ℕ, A.dxi 1 (l * q + j) = (n : A.Acr 1) * A.dxi 1 1 ^ j * A.dxi 1 (l * q) := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨n, hn⟩ := ih (by omega)
    have hnd : ¬ l ∣ l * q + j + 1 := by
      intro h
      rw [add_assoc] at h
      have h' := (Nat.dvd_add_right (Dvd.intro q rfl)).1 h
      have := Nat.le_of_dvd (by omega) h'
      omega
    obtain ⟨m, hm⟩ := exists_inv A hnd
    refine ⟨m * n, ?_⟩
    have e := dxi_succ A (l * q + j)
    calc A.dxi 1 (l * q + (j + 1))
        = (m : A.Acr 1) * ((l * q + j + 1 : ℕ) : A.Acr 1) * A.dxi 1 (l * q + j + 1) := by
          rw [hm, one_mul]; rfl
      _ = (m : A.Acr 1) * (A.dxi 1 (l * q + j) * A.dxi 1 1) := by rw [e]; ring
      _ = _ := by rw [hn]; push_cast; ring

theorem expand_single (q : ℕ) (b : A.A) :
    A.expand (Finsupp.single q b) = A.aTo1 b * A.dxi 1 (l * q) := by
  simp [PAlg.expand]

theorem exists_dxi_eq (k : ℕ) : ∃ (b : A.A) (q : ℕ), A.dxi 1 k = A.aTo1 b * A.dxi 1 (l * q) := by
  have hp : l.Prime := Fact.out
  obtain ⟨n, hn⟩ := dxi_lq_add A (k / l) (k % l) (Nat.mod_lt _ hp.pos)
  rw [Nat.div_add_mod] at hn
  refine ⟨(n : A.A) * (-A.pi) ^ (k % l), k / l, ?_⟩
  rw [hn, map_mul, map_natCast, map_pow, map_neg, aTo1_pi, neg_neg]

theorem expand_add (c c' : ℕ →₀ A.A) : A.expand (c + c') = A.expand c + A.expand c' := by
  simp only [PAlg.expand]
  exact Finsupp.sum_add_index' (by simp) (by intro k a b; simp [add_mul])

theorem expand_smul (a : A.A) (c : ℕ →₀ A.A) : A.expand (a • c) = A.aTo1 a * A.expand c := by
  simp only [PAlg.expand]
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [smul_eq_mul, map_mul, mul_assoc]

theorem expand_surjective : Function.Surjective A.expand := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hz := mem_spanFrom_zero A z
  unfold spanFrom at hz
  change ∃ c, A.expand c = A.mkAcr 1 z
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨b, q, h⟩ := exists_dxi_eq A k
    exact ⟨Finsupp.single q b, by rw [expand_single, ← h]; rfl⟩
  | zero => exact ⟨0, by simp [PAlg.expand]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h⟩ := hx
    obtain ⟨c', h'⟩ := hy
    exact ⟨c + c', by rw [expand_add, h, h', (A.mkAcr 1).map_add]⟩
  | smul w x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨w.coeff 0 • c, ?_⟩
    rw [expand_smul, h, aTo1_coeff, Algebra.smul_def, map_mul]
    rfl

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧
    (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧
    (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧
    ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := fun A =>
  ⟨expand_surjective A, expand_add A, expand_smul A, fun k => by
    rw [map_pow, aTo1_pi_pow, zero_mul]⟩

end GlobalTheory.CompanionTheory.PerfFil.Expand
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinearStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_surjective_additive_linear : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧ (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧ (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧ ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.Expand.main | exact GlobalTheory.CompanionTheory.PerfFil.Expand.main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.Expand.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Pull1RestrictPairRestriction
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SysBC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} {P : Type} [SemilatticeInf P]

theorem exists_sec_equiv (h : IsPullback φ s' s (spMap (algebraMap R R'))) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ e : R' ⊗[R] Sec s U ≃ₗ[R'] Sec s' (φ ⁻¹ᵁ U),
      ∀ b, e (1 ⊗ₜ b) = (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b := by
  letI : Algebra (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (GlobalTheory.AbLaw.appLE_cst h.w le_rfl r).symm
  haveI hp : Algebra.IsPushout R R' (Sec s U) (Sec s' (φ ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h hU rfl)
  refine ⟨hp.out.equiv, fun b ↦ ?_⟩
  exact (hp.out.equiv_tmul 1 b).trans (one_smul _ _)

def pullSys (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Sys X' P where
  u a := ⟨φ ⁻¹ᵁ (S.u a).1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h (S.u a).2⟩
  map_inf a b := by
    change φ ⁻¹ᵁ (S.u (a ⊓ b)).1 = φ ⁻¹ᵁ (S.u a).1 ⊓ φ ⁻¹ᵁ (S.u b).1
    rw [S.map_inf]; rfl
  cover := by
    change ⨆ a, φ ⁻¹ᵁ (S.u a).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, S.cover]; rfl

def pt (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) (a : P) : Pair φ :=
  ⟨((pullSys h S).u a, S.u a), le_rfl⟩

theorem pt_mono (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    Monotone (pt h S) := fun _ _ hab ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(pullSys h S).mono hab, S.mono hab⟩)

def ptFn (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) : Pᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (pt_mono h S).functor.op

def ptRes (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    CoefMap (RingHom.id R') (OPair φ s') (OSys s' (pullSys h S)) where
  G := ptFn h S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def pullBC (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P) :
    BC (OSys s S) (OSys s' (pullSys h S)) where
  α T := secPull s s' (pt h S T.unop)
  naturality ψ b := (pairPull h.w).naturality ((ptFn h S).map ψ) b
  smul T r b := (pairPull h.w).smul (op (pt h S T.unop)) r b
  bij T := exists_sec_equiv h (S.u T.unop).2

theorem pull1_restrict_pair_pullback (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s) : (ptRes h S).pull1 ((pairPull h.w).pull1 c) =
      (pullBC h S).coef.pull1 ((resSys s S).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pull1_restrict_pair_restriction (h : IsPullback φ s' s (spMap (algebraMap R R'))) (S : Sys X P)
    (c : HO1 s') : (ptRes h S).pull1 ((pairRes φ s').pull1 c) =
      (resSys s' (pullSys h S)).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

end GlobalTheory.CompanionTheory.SysBC


open GlobalTheory.CompanionTheory.SysBC in
theorem GlobalTheory.CompanionTheory.SysBC.sysBCSt : DescentSt → LowSt → SysBCSt := by
  intro hD hL R R' _ _ _ X X' s s' φ h hs P _ S
  have hs' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hs
  refine ⟨pullSys h S, pullBC h S, fun c c' e ↦ ?_⟩
  have inj := (hL R' _ _ _ _ (resSys s' (pullSys h S)) (hD R' X' s' hs' P (pullSys h S))).1.1
  obtain ⟨x, hx⟩ := (pairRes_bijective φ s').1.2 ((pairPull h.w).pull1 c)
  have e' : x = c' := inj (by
    rw [← pull1_restrict_pair_restriction h S x, hx, pull1_restrict_pair_pullback, e])
  exact hx.symm.trans (congrArg _ e')
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescription
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescription
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

private theorem exists_factorial_mul_eq_pow' (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, m, hm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) l hp.one_lt.ne'
  have hcop : IsCoprime (((l : ℤ)) : A.W) (((m : ℤ)) : A.W) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).intCast
  obtain ⟨u, v, huv⟩ := hcop
  push_cast at huv
  have := A.completeW
  have hj : (l : A.W) ∈ (⊥ : Ideal A.W).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {(l : A.W)}) (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit ((m : A.W) * v) := by
    have h := Ideal.mem_jacobson_bot.1 hj (-u)
    convert h using 1
    linear_combination huv
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  refine ⟨e, v * t, ?_⟩
  rw [hk]
  push_cast
  linear_combination (l : A.W) ^ e * ht

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := by
  obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow' A k
  have hu : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) (k.factorial : A.W)) := by
    have h1 : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) ((l : A.W) ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit _).pow N
    rw [← hc, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [map_natCast] at hu
  unfold CrystallineSemistableComparison.PAlg.dxi0
  apply Subtype.ext
  push_cast
  unfold CrystallineSemistableComparison.dpw
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

theorem xi_mul_divided_power (r : ℕ) :
    algebraMap A.W A.Acr0 A.xi * A.dxi0 r = ((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1) := by
  have h1 := factorial_mul_divided_power_xi A 1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
  rw [← h1, divided_power_xi_mul, add_comm 1 r, Nat.choose_one_right]

theorem exists_factorial_mul_eq_pow (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l)
    (Nat.factorial_ne_zero k) (le_refl _)
  refine ⟨k.factorial.factorization l, A.sW c, ?_⟩
  have := congrArg A.sW hc
  simpa using this

theorem filtration_element_power_multiple_xi (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow A k
    refine ⟨N, A.xi ^ (k - r) * c, ?_⟩
    have h := factorial_mul_divided_power_xi A k
    calc (l : A.Acr0) ^ N * A.dxi0 k = algebraMap A.W A.Acr0 ((l : A.W) ^ N) * A.dxi0 k := by simp
    _ = algebraMap A.W A.Acr0 c * ((k.factorial : A.Acr0) * A.dxi0 k) := by
        rw [← hc, map_mul, map_natCast]; ring
    _ = algebraMap A.W A.Acr0 (A.xi ^ r * (A.xi ^ (k - r) * c)) := by
        rw [h, ← map_pow, ← map_mul]
        congr 1
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
        ring
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N1, w1, h1⟩ := hx
    obtain ⟨N2, w2, h2⟩ := hy
    refine ⟨N1 + N2, (l : A.W) ^ N2 * w1 + (l : A.W) ^ N1 * w2, ?_⟩
    calc (l : A.Acr0) ^ (N1 + N2) * (x + y)
        = (l : A.Acr0) ^ N2 * ((l : A.Acr0) ^ N1 * x) + (l : A.Acr0) ^ N1 * ((l : A.Acr0) ^ N2 * y) := by ring
    _ = _ := by
        rw [h1, h2]
        simp only [map_mul, map_add (f := _), map_pow, map_natCast]
        ring
  | smul a x _ hx =>
    obtain ⟨N, w, h⟩ := hx
    refine ⟨N, a * w, ?_⟩
    rw [Algebra.smul_def]
    calc (l : A.Acr0) ^ N * (algebraMap A.W A.Acr0 a * x)
        = algebraMap A.W A.Acr0 a * ((l : A.Acr0) ^ N * x) := by ring
    _ = _ := by
        rw [h, ← map_mul]
        congr 1
        ring

theorem filtration_element_mod_next_level (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rcases hk.eq_or_lt with h | h
    · subst h
      exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_mul, sub_zero]
      exact (mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨k, Nat.succ_le_of_lt h, rfl⟩)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, h1⟩ := hx
    obtain ⟨w2, h2⟩ := hy
    refine ⟨w1 + w2, ?_⟩
    have e : x + y - algebraMap A.W A.Acr0 (w1 + w2) * A.dxi0 r =
        (x - algebraMap A.W A.Acr0 w1 * A.dxi0 r) + (y - algebraMap A.W A.Acr0 w2 * A.dxi0 r) := by
      rw [map_add (f := _)]; ring
    rw [e]
    exact Ideal.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨w, h⟩ := hx
    refine ⟨a * w, ?_⟩
    have e : a • x - algebraMap A.W A.Acr0 (a * w) * A.dxi0 r =
        algebraMap A.W A.Acr0 a * (x - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ h

theorem divided_power_multiple_next_level_iff (r : ℕ) (w : A.W) :
    algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi} := by
  have hinj : Function.Injective (algebraMap A.W A.Acr0) := by
    intro x y h
    apply A.algebraMap_WL_injective
    exact congrArg Subtype.val h
  constructor
  · intro h
    obtain ⟨N, v, hv⟩ := filtration_element_power_multiple_xi A (r + 1) h
    have hr := factorial_mul_divided_power_xi A r
    have e1 : algebraMap A.W A.Acr0 ((l : A.W) ^ N * w * A.xi ^ r) =
        algebraMap A.W A.Acr0 (A.xi * ((r.factorial : A.W) * v) * A.xi ^ r) := by
      have e2 := congrArg (fun t => (r.factorial : A.Acr0) * t) hv
      simp only [map_mul, map_pow, map_natCast] at e2 ⊢
      linear_combination e2 - (l : A.Acr0) ^ N * algebraMap A.W A.Acr0 w * hr
    have e3 : (l : A.W) ^ N * w = A.xi * ((r.factorial : A.W) * v) :=
      (mul_cancel_right_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.1 r)).1 (hinj e1)
    have e4 : (r.factorial : A.W) * v ∈ Ideal.span {(l : A.W) ^ N} := by
      apply (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.2 N
      rw [← e3]
      exact Ideal.mem_span_singleton.2 ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e4
    rw [hy] at e3
    have e5 : w = A.xi * y := by
      apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem A.l_mem_nzd N)).1
      rw [e3]
      ring
    exact Ideal.mem_span_singleton.2 ⟨y, e5⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h
    have h2 := xi_mul_divided_power A r
    have e : algebraMap A.W A.Acr0 (A.xi * y) * A.dxi0 r =
        algebraMap A.W A.Acr0 y * (((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1)) := by
      rw [← h2, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      ((mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨r + 1, le_rfl, rfl⟩)))

theorem crystalline_filtration_graded_pieces : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ),
    (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧
    (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧
    ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W),
      (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  intro l hl A r
  exact ⟨fun z hz => filtration_element_mod_next_level A r hz, fun w => divided_power_multiple_next_level_iff A r w,
    fun z hz => filtration_element_power_multiple_xi A r hz⟩

end GlobalTheory.CompanionTheory.PerfFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescriptionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_graded_pieces_description : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ), (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧ (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧ ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenImmersionChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeChart

attribute [local instance] MvPolynomial.gradedAlgebra

instance isOpenImmersion_chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    IsOpenImmersion (chart R N j) := by
  unfold chart
  infer_instance

theorem opensRange_fst {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (j : Fin (N + 1)) :
    (pullback.fst i (chart R N j)).opensRange = i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j := by
  have hr : (chart R N j).opensRange = GlobalTheory.ProjSpace.chart R N j := Proj.opensRange_awayι _ _ _ _
  rw [← hr]
  ext x
  change x ∈ Set.range (pullback.fst i (chart R N j)) ↔ i x ∈ Set.range (chart R N j)
  rw [Scheme.Pullback.range_fst]
  rfl

theorem preimage_chart_mem {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ)
    (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N) (h : IsTautologicalLineAt D N i) (j : Fin (N + 1)) :
    i ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j ∈ 𝒱D D := by
  obtain ⟨_, s, hs, _⟩ := h
  rw [← opensRange_fst]
  refine ⟨(pullback.fst i (chart R N j)).isoOpensRange.inv ≫ s j, ?_⟩
  rw [Category.assoc, hs, Iso.inv_comp_eq]
  exact (Scheme.Hom.isoOpensRange_hom_ι _).symm

end GlobalTheory.CompanionTheory.ConeChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeWchMem

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D :=
  fun D N i h j => GlobalTheory.CompanionTheory.ConeChart.preimage_chart_mem D N i h j

end GlobalTheory.CompanionTheory.ConeWchMem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1Statement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_open_mem_cover_of_O1 : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := by
  first | exact @GlobalTheory.CompanionTheory.ConeWchMem.main | exact GlobalTheory.CompanionTheory.ConeWchMem.main | (intros; apply GlobalTheory.CompanionTheory.ConeWchMem.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReduction
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfAlg

theorem pow_mul_mem_span_iff {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (n m : ℕ) (x : R) :
    a ^ n * x ∈ Ideal.span {a ^ (n + m)} ↔ x ∈ Ideal.span {a ^ m} := by
  have hn : a ^ n ∈ nonZeroDivisors R := pow_mem ha n
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have e : a ^ n * (c * a ^ m) = a ^ n * x := by rw [← hc, pow_add]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 hn (c * a ^ m - x) (by rw [mul_sub, e, sub_self]))
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_add]; ring⟩

theorem lseq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  intro l _ A n m
  have hl : (l : A.Acr0) ∈ nonZeroDivisors A.Acr0 := A.acris_torsion_free l (Fact.out : l.Prime).ne_zero
  have mk0 : ∀ (k : ℕ) (y : A.Acr0), A.mkAcr k y = 0 ↔ y ∈ Ideal.span {(l : A.Acr0) ^ k} :=
    fun k y => Ideal.Quotient.eq_zero_iff_mem
  refine ⟨?_, ?_, ?_, fun x => pow_mul_mem_span_iff (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1 n m x⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨A.mkAcr _ y, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.red _ (A.mkAcr _ y) = 0 ↔ A.mkAcr _ y ∈ _
    rw [red_mk, mk0]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      refine Ideal.mem_span_singleton'.2 ⟨A.mkAcr _ c, ?_⟩
      rw [map_mul, map_pow, map_natCast]
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
      have e : A.mkAcr (n + m) (d * (l : A.Acr0) ^ n - y) = 0 := by
        set_option synthInstance.maxHeartbeats 400000 in
          rw [map_sub, map_mul, map_pow, map_natCast]
        exact sub_eq_zero.2 hc
      have e2 := (mk0 _ _).1 e
      have e3 : Ideal.span {(l : A.Acr0) ^ (n + m)} ≤ Ideal.span {(l : A.Acr0) ^ n} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right n m))
      have e4 := Ideal.sub_mem _ (Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ((l : A.Acr0) ^ n))) (e3 e2)
      rwa [sub_sub_cancel] at e4
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _ * A.mkAcr _ y = 0 ↔ A.red _ (A.mkAcr _ y) = 0
    rw [red_mk, mk0, ← pow_mul_mem_span_iff hl n m y, ← mk0, map_mul, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.PerfAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReductionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_annihilator_reduction : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  first | exact @GlobalTheory.CompanionTheory.PerfAlg.lseq | exact GlobalTheory.CompanionTheory.PerfAlg.lseq | (intros; apply GlobalTheory.CompanionTheory.PerfAlg.lseq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Conductor

theorem mem_chartRingQ_of_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ chartRingQ y c := by
  unfold chartRingZ at hx
  unfold chartRingQ
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv => exact mul_mem hu hv

theorem exists_conductor_section :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ),
        ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω),
          c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  classical
  intro K _ ι _ Ω _ _ y D _ hbir
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  refine ⟨∑ c : C, δ c, ∏ c : C, aeval y (F c), Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c,
    fun a τ s hs => ?_⟩
  have key : ∀ s ∈ chartLatNm y a τ, (∏ c : C, aeval y (F c)) * s ∈
      chartLatQ y ((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) 1 := by
    intro s hs c' hc'
    let c : C := ⟨c', hc'⟩
    have hx := hs c' hc'
    have hm : ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) *
          (((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) k))) =
        (∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) * Conductor.invMon y c' (∑ c : C, δ c) := by
      rw [← Conductor.prod_zpow_eq_invMon, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc' k)]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
      ring
    apply mem_chartRingQ_of_mem_chartRingZ
    rw [hm, ← Conductor.invMon_sum y c' Finset.univ δ]
    have hsplit : (∏ b : C, aeval y (F b)) * s * ((∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) *
          ∏ b : C, Conductor.invMon y c' (δ b)) =
        (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
          (aeval y (F c) * Conductor.invMon y c' (δ c) *
            (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
        ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
        Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    exact mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (hcond c _ hx)
  induction hs using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simpa using Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu

end GlobalTheory.CompanionTheory.Conductor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShiftStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_span_twist_shift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω), c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | exact GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | (intros; apply GlobalTheory.CompanionTheory.Conductor.exists_conductor_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.ChartDenom

theorem exists_nat_mul_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingQ y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * x ∈ chartRingZ y c := by
  unfold chartRingQ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin hx
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [h]
    exact intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)
  | mul u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact mul_mem hmu hnv

theorem chartLatQ_le_span_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ),
      chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  intro K _ ι _ Ω _ _ y a τ s hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y c (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hc⟩
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ := by
    intro c hc
    have e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
          ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    have h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
        ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c :=
      mul_mem (natCast_mem _ _) (hn c hc)
    exact Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)
  have h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) :=
    Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1
  have e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s := by
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.ChartDenom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNormStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_le_span_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ), chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem exists_lim_of_dvd {R : Type*} [CommRing R] (p : R) [IsAdicComplete (Ideal.span {p}) R]
    (g : ℕ → R) (hg : ∀ n, p ^ n ∣ g (n + 1) - g n) : ∃ y, ∀ n, p ^ n ∣ g n - y := by
  have chain : ∀ m k, p ^ m ∣ g (m + k) - g m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ m ∣ g (m + k + 1) - g (m + k) :=
        (pow_dvd_pow p (Nat.le_add_right m k)).trans (hg (m + k))
      have := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) g (fun {m n} hmn => by
    rw [smodEq_span_singleton_pow_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (dvd_sub_comm).1 (chain m k))
  exact ⟨L, fun n => (smodEq_span_singleton_pow_iff _ _ _ _).1 (hL n)⟩

theorem isAdicComplete_quotient {R : Type*} [CommRing R] (p ξ : R)
    [IsAdicComplete (Ideal.span {p}) R] (h : ∀ (n : ℕ) (x : R), p ^ n ∣ ξ * x → p ^ n ∣ x) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
  have hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ∀ n : ℕ, ∃ y z, a = ξ * y + p ^ n * z := by
      intro n
      have hd := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hx n)
      rw [sub_zero] at hd
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h0 : Ideal.Quotient.mk (Ideal.span {ξ}) (a - p ^ n * c') = 0 := by
        rw [map_sub, map_mul, map_pow, hc, sub_self]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact ⟨y, c', by linear_combination hy⟩
    choose y z hyz using h1
    have hy : ∀ n, p ^ n ∣ y (n + 1) - y n := fun n =>
      h n _ ⟨z n - p * z (n + 1), by linear_combination hyz n - hyz (n + 1)⟩
    obtain ⟨Y, hY⟩ := exists_lim_of_dvd p y hy
    have hz : a - ξ * Y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {p}) _ fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero]
      obtain ⟨c, hc⟩ := hY n
      exact ⟨ξ * c + z n, by linear_combination hyz n + ξ * hc⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨Y, sub_eq_zero.1 hz⟩)
  have hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun f hf => ?_⟩
    have step : ∀ (n : ℕ) (x : R), Ideal.Quotient.mk (Ideal.span {ξ}) x = f n →
        ∃ y, Ideal.Quotient.mk (Ideal.span {ξ}) y = f (n + 1) ∧ p ^ n ∣ y - x := by
      intro n x hx
      obtain ⟨c, hc⟩ := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hf (Nat.le_succ n))
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨x - p ^ n * c', ?_, ⟨-c', by ring⟩⟩
      rw [map_sub, map_mul, map_pow, hx, ← hc]
      ring
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (f 0)
    let G : ∀ n, {x : R // Ideal.Quotient.mk (Ideal.span {ξ}) x = f n} := fun n =>
      Nat.rec ⟨x0, hx0⟩ (fun n x => ⟨(step n x.1 x.2).choose, (step n x.1 x.2).choose_spec.1⟩) n
    have hG : ∀ n, p ^ n ∣ (G (n + 1)).1 - (G n).1 := fun n => (step n _ (G n).2).choose_spec.2
    obtain ⟨y, hy⟩ := exists_lim_of_dvd p (fun n => (G n).1) hG
    refine ⟨Ideal.Quotient.mk _ y, fun n => ?_⟩
    rw [smodEq_span_singleton_pow_iff]
    have := map_dvd (Ideal.Quotient.mk (Ideal.span {ξ})) (hy n)
    rwa [map_pow, map_sub, (G n).2] at this
  exact { hH, hP with }

theorem isAdicComplete_U : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  intro l _ A
  have hc := isAdicComplete_quotient (l : A.W) A.xi (fun n x hx =>
    Ideal.mem_span_singleton.1 ((GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.2 n x (Ideal.mem_span_singleton.2 hx)))
  have e : (l : A.U) = Ideal.Quotient.mk (Ideal.span {A.xi}) (l : A.W) := (map_natCast A.th l).symm
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.Untilt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untilt_adic_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | exact GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | (intros; apply GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U <;> assumption)
end
end
