module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.ConjSqrtMinusD
namespace Formalism.BasicNotions

open NumberField

variable {R : Ranks}

theorem Host.sqrtMinusD_sq (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem Host.conj_sqrtMinusD (H : Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := H.conjE_apply H.φ₀ H.sqrtMinusD
  rw [h1, map_neg]
  set z := H.φ₀ H.sqrtMinusD
  have hz : z ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.sqrtMinusD_sq]; simp
  have hre : z.re = 0 := by
    have h2 := congrArg Complex.im hz
    have h3 := congrArg Complex.re hz
    simp [pow_two] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · rw [h] at h3; nlinarith [sq_nonneg z.re]
    · norm_num at h
  apply Complex.ext <;> simp [hre]

theorem Host.exists_trace_one (H : Host R) : ∃ c : 𝓞 H.E, (c : H.E) + H.conj c = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 4 * (m : H.E) := by exact_mod_cast hm
    have hs := H.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, ?_⟩
  show c + H.conj c = 1
  simp only [c, map_div₀, map_add (f := _), map_one, H.conj_sqrtMinusD, map_ofNat]
  ring

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
noncomputable section

namespace Formalism.BasicNotions

open NumberField

theorem intCast_dvd_of_dvd_integers (E : Type) [Field E] [NumberField E] (a b : ℤ)
    (h : (b : 𝓞 E) ∣ (a : 𝓞 E)) : b ∣ a := by
  have h1 := map_dvd (Algebra.norm ℤ) h
  have ea : (a : 𝓞 E) = algebraMap ℤ (𝓞 E) a := by simp
  have eb : (b : 𝓞 E) = algebraMap ℤ (𝓞 E) b := by simp
  rw [ea, eb, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := by
    rw [RingOfIntegers.rank]; exact (Module.finrank_pos).ne'
  exact (Int.pow_dvd_pow_iff hn).1 h1

theorem dvd_norm_sub_one (E : Type) [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (π : 𝓞 E) (T M : ℕ)
    (hT : (π : E) * σ (π : E) = (T : E)) (hπ : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  rw [Ideal.mem_span_singleton] at hπ
  obtain ⟨α, hα⟩ := hπ
  have hint : IsIntegral ℤ (σ (α : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe α)
  set α' : 𝓞 E := ⟨σ (α : E), hint⟩ with hα'
  have e1 : (π : E) = 1 + (M : E) * (α : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) hα
    simp only [map_sub, map_one, map_mul, map_natCast] at this
    linear_combination this
  have e2 : σ (π : E) = 1 + (M : E) * (α' : E) := by
    have hc : (α' : E) = σ (α : E) := rfl
    rw [e1, hc]; simp
  have e3 : (T : E) - 1 = (M : E) * ((α : E) + (α' : E) + (M : E) * (α : E) * (α' : E)) := by
    rw [← hT, e2, e1]; ring
  have h5 : ((M : ℤ) : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨α + α' + (M : 𝓞 E) * α * α', ?_⟩
    apply RingOfIntegers.ext
    simp only [map_mul, map_add (f := _), map_natCast, map_intCast]
    push_cast
    exact e3
  exact intCast_dvd_of_dvd_integers E _ _ h5

namespace D7

variable (D : D7)

def modT : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2

theorem modT_dvd (u : D.what₂.Word) : (D.modT : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 := by
  obtain ⟨π, -, hT, hπ⟩ := D.T_norm u
  exact dvd_norm_sub_one D.host.E D.host.conj π _ _ hT hπ

theorem T_modEq (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD D.modT] :=
  ((Nat.modEq_iff_dvd).2 (by exact_mod_cast D.modT_dvd u)).symm

theorem T_modEq_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) : (D.mem u).A.T ≡ 1 [MOD a] :=
  (D.T_modEq u).of_dvd ha

theorem T_mod_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) (h1 : 1 < a) : (D.mem u).A.T % a = 1 := by
  have h := D.T_modEq_of_dvd u ha
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h1] at h

theorem g_dvd_modT (i : Fin 2) : D.host.g i ∣ D.modT := by
  have h : D.host.g i ∣ D.host.g 0 * D.host.g 1 := by
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  exact Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _

theorem gg_dvd_modT : (D.host.g 0 * D.host.g 1) ^ 2 ∣ D.modT := Dvd.intro_left _ rfl

theorem cond_dvd_modT : D.host.QS * D.host.q * D.host.d ∣ D.modT := Dvd.intro _ rfl

theorem q_prime : D.host.q.Prime := D.host.hyp.1

theorem d_prime : D.host.d.Prime := D.host.hyp.2.1

theorem one_lt_cond : 1 < D.host.QS * D.host.q * D.host.d := by
  have h1 := D.host.QS_pos
  have h2 := D.q_prime.pos
  have h3 := D.d_prime.two_le
  have : 1 * 1 * 2 ≤ D.host.QS * D.host.q * D.host.d := by gcongr <;> omega
  omega

theorem T_mod_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T % D.host.g i = 1 :=
  D.T_mod_of_dvd u (D.g_dvd_modT i) (D.host.g_prime i).one_lt

theorem T_mod_gg (u : D.what₂.Word) : (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 := by
  refine D.T_mod_of_dvd u D.gg_dvd_modT ?_
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have : 2 * 2 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
  nlinarith

theorem T_mod_cond (u : D.what₂.Word) : (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 :=
  D.T_mod_of_dvd u D.cond_dvd_modT D.one_lt_cond

private theorem tower_dvd_modT : 2 ^ (D.R.e + 2) ∣ D.modT :=
  D.host.tower_dvd.trans (dvd_trans ⟨D.host.q * D.host.d, by ring⟩ D.cond_dvd_modT)

theorem T_mod_four (u : D.what₂.Word) : (D.mem u).A.T % 4 = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨2 ^ D.R.e, by ring⟩ (tower_dvd_modT D)) (by norm_num)

theorem T_mod_q (u : D.what₂.Word) : (D.mem u).A.T % D.host.q = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.d, by ring⟩ D.cond_dvd_modT) D.q_prime.one_lt

theorem T_mod_d (u : D.what₂.Word) : (D.mem u).A.T % D.host.d = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.q, by ring⟩ D.cond_dvd_modT) D.d_prime.one_lt

theorem T_ne_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T ≠ D.host.g i := by
  intro h
  have h1 := D.T_mod_g u i
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_two (u : D.what₂.Word) : (D.mem u).A.T ≠ 2 := by
  have h1 := D.T_mod_four u
  omega

theorem T_ne_q (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.q := by
  intro h
  have h1 := D.T_mod_q u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_d (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.d := by
  intro h
  have h1 := D.T_mod_d u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

end D7

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataLevelD
namespace Formalism.BasicNotions

def LevelData (D : D7) :=
  letI := D.host.cmStar
  ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.DataBu
noncomputable section
namespace Formalism.BasicNotions
namespace Rows.Data
variable {R : Ranks} (D : Rows.Data R)

def iotaQ (μ : D.Tup) : D.Qsp μ →ₗ[ℂ] D.EE := (D.iota μ).domRestrict (D.Qsp μ)

theorem iotaQ_inj (μ : D.Tup) : Function.Injective (D.iotaQ μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hxQ : (x : D.Amb μ) ∈ D.V0 μ ⊓ (D.Usp μ)ᗮ := x.2
  have hU : (x : D.Amb μ) ∈ D.Usp μ := ⟨hxQ.1, hx⟩
  have h0 : inner ℂ (x : D.Amb μ) (x : D.Amb μ) = 0 := Submodule.inner_right_of_mem_orthogonal hU hxQ.2
  exact Subtype.ext (inner_self_eq_zero.mp h0)

def sec (μ : D.Tup) : D.EE →ₗ[ℂ] D.Amb μ :=
  (D.Qsp μ).subtype ∘ₗ (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)).symm.toLinearMap ∘ₗ
    ((LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto : D.EE →L[ℂ] LinearMap.range (D.iotaQ μ)).toLinearMap

theorem sec_iota (μ : D.Tup) (q : D.Amb μ) (hq : q ∈ D.Qsp μ) : D.sec μ (D.iota μ q) = q := by
  have hr : D.iota μ q ∈ LinearMap.range (D.iotaQ μ) := ⟨⟨q, hq⟩, rfl⟩
  have h1 : (LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto (D.iota μ q) = ⟨D.iota μ q, hr⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := LinearMap.range (D.iotaQ μ)) ⟨D.iota μ q, hr⟩
  have h2 : (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)) ⟨q, hq⟩ = ⟨D.iota μ q, hr⟩ := rfl
  simp only [sec, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1, ← h2, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply]

end Rows.Data

def Rows.BuDefQ {R : Ranks} (D : Rows.Data R) : Prop :=
  ∀ u (φ : D.Mu u) (x : D.EE), D.Bu u φ x = D.perCol u D.mu0 φ (D.sec D.mu0 x)

theorem D7.perCol_add (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F G : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (F + G) = D.what₂.perCol u D.what₂.mu0 φ F + D.what₂.perCol u D.what₂.mu0 φ G := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add (f := _)]

theorem D7.perCol_zero (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    D.what₂.perCol u D.what₂.mu0 φ 0 = 0 := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_zero]

end Formalism.BasicNotions
end
end

section -- merged from Formalism.LocalRingCardinality.PrincipalHermitianLattice
noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

structure RowSide (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] where

  Amb : D.what₂.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]

  Mult : D.what₂.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ D.R.m ≃ₗᵢ[ℂ] Amb μ

  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j

  Mtilde : ∀ μ, Rows.OLat D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) (Amb μ)

  cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ (Amb μ)

  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric

  eOp_tie : ∀ μ, eOp μ = (open Classical in
    if h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) then cen μ ⟨D.ntypes.e0, h⟩ else 0)

  RR : HLat D.what₂.LL
  RR_frames : ∀ v, IsUnit (RR.X v).det

  jEE : RR.V →ₛₗ[D.what₂.embLL] EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (RR.b i))) = ⊤

  jEE_norm : ∀ x : RR.V,
    Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk D.what₂.embLL) x = ‖jEE x‖

attribute [instance] RowSide.instAmb RowSide.instAmbi RowSide.instAmbf RowSide.instMult
  RowSide.instMulti RowSide.instMultf

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def downTo (μ : D.what₂.Tup) : (j : ℕ) → S.Mult μ j →ₗ[ℂ] S.Mult μ 0
  | 0 => LinearMap.id
  | j + 1 => (downTo μ j).comp (S.io μ j)

def iota (μ : D.what₂.Tup) : S.Amb μ →ₗ[ℂ] EE :=
  (S.multZero μ).toLinearEquiv.toLinearMap ∘ₗ S.downTo μ D.R.m ∘ₗ
    (S.multTop μ).symm.toLinearEquiv.toLinearMap

def V0 (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := LinearMap.range (S.eOp μ)

def Usp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ LinearMap.ker (S.iota μ)

def Qsp (μ : D.what₂.Tup) : Submodule ℂ (S.Amb μ) := S.V0 μ ⊓ (S.Usp μ)ᗮ

def LamSet (μ : D.what₂.Tup) : Set (S.Amb μ) :=
  (fun x => (S.Qsp μ).starProjection x) '' ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ)))

def RRset (μ : D.what₂.Tup) : Set EE := S.iota μ '' S.LamSet μ

def iotaQ (μ : D.what₂.Tup) : S.Qsp μ →ₗ[ℂ] EE := (S.iota μ).domRestrict (S.Qsp μ)

def RRDef : Prop :=
  ∀ x : S.RR.V, x ∈ S.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | S.jEE y ∈ S.RRset (D.what₂.muAt w)}

def AIntegral : Prop :=
  ∀ μ x, x ∈ (S.Mtilde μ).carrier → ((D.what₂.restRowsFiniteGroupCard : ℂ) • S.eOp μ x) ∈ (S.Mtilde μ).carrier

def sharp (D : D7) : RowSide D D.what₂.EE where
  Amb := D.what₂.Amb
  Mult := D.what₂.Mult
  multZero := D.what₂.multZero
  multTop := D.what₂.multTop
  io := D.what₂.io
  Mtilde := D.what₂.Mtilde
  cen := D.ntypes.cenAmb
  eOp := D.what₂.eOp
  eOp_idem := D.what₂.eOp_idem
  eOp_sa := D.what₂.eOp_sa
  eOp_tie := fun μ => by
    rw [D.nStage_trivialCharacter_compat.1 μ]; rfl
  RR := D.div.RR
  RR_frames := D.div_good.1
  jEE := D.jEE
  jEE_basis := D.jEE_basis
  jEE_norm := D.jEE_norm

end RowSide

structure BaseLevelRowSide (D : D7) where
  s : RowSide D D.what₂.EE0

namespace BaseLevelRowSide

variable {D : D7} (X : BaseLevelRowSide D)

def principalHermitianLattice : HLat D.what₂.LL := X.s.RR

end BaseLevelRowSide

def lam0 (D : D7) : ℝ := Real.log (D.what₂.restRowsFiniteGroupCard : ℝ)

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataNChoice
noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct


set_option synthInstance.maxHeartbeats 400000 in
structure NChoice (D : D7) where

  twI : D.what₂.places.Pl → D.ntw.Tw
  twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w
  sd : D.what₂.places.Pl → Bool

  Q : D.what₂.places.Pl → Finset (PlE D.host)
  k' : D.what₂.places.Pl → ℕ
  psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ

  Oe : D.what₂.places.Pl → Type
  [crOe : ∀ w, CommRing (Oe w)]
  [domOe : ∀ w, IsDomain (Oe w)]
  [dvrOe : ∀ w, IsDiscreteValuationRing (Oe w)]
  [algOe : ∀ w, Algebra (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  [algOOe : ∀ w, Algebra (D.ntw.O (twI w)) (Oe w)]
  [towOe : ∀ w, IsScalarTower (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  Oe_inj : ∀ w, Function.Injective (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))
  Oe_fin : ∀ w, Module.Finite (D.ntw.Ok (twI w) (k' w)) (Oe w)
  Oe_loc : ∀ w, IsLocalHom (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))

  embW : ∀ w, D.what₂.LL →+* FractionRing (Oe w)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (Oe w) (FractionRing (Oe w))).range

  eMt : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[embW w]
    FractionRing (Oe w) ⊗[D.ntw.Ok (twI w) (k' w)]
      D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))
  eMt_basis : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (Oe w)) (fun i => eMt w j (b i)) ∧
      Submodule.span (FractionRing (Oe w)) (Set.range fun i => eMt w j (b i)) = ⊤
  eMt_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → Submodule.span (Oe w)
      (eMt w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    Submodule.span (Oe w)
      ((TensorProduct.mk (D.ntw.Ok (twI w) (k' w)) (FractionRing (Oe w))
          (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))) 1) ''
        (D.nexp.MtLat (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))) :
          Set (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))))))

attribute [instance] NChoice.crOe NChoice.domOe NChoice.dvrOe NChoice.algOe NChoice.algOOe NChoice.towOe


set_option synthInstance.maxHeartbeats 400000 in
def NChoice.kMapE {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) :
    FractionRing (D.ntw.Ok (c.twI w) (c.k' w)) →+* FractionRing (c.Oe w) :=
  IsFractionRing.map (j := algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)) (c.Oe_inj w)

namespace NChoice

section OfOk

variable {K V : Type} [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
  [IsScalarTower K (FractionRing K) V]

def fracEquiv (K V : Type) [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
    [IsScalarTower K (FractionRing K) V] : FractionRing K ⊗[K] V ≃ₗ[FractionRing K] V :=
  haveI := isLocalizedModule_id (nonZeroDivisors K) V (FractionRing K)
  (IsLocalizedModule.isBaseChange (nonZeroDivisors K) (FractionRing K) (LinearMap.id : V →ₗ[K] V)).equiv

end OfOk


end NChoice

end Formalism.BasicNotions

end
end

section -- merged from Formalism.LocalRingCardinality.DataMink
namespace Formalism.BasicNotions

abbrev minkM (n : ℕ) : ℕ := Formalism.HermitianLatticeCounting.S6.minkowskiM n

def DGamMink (D : D7) : Prop := (D.mem D.u₀).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m)

end Formalism.BasicNotions
end

section -- merged from Formalism.LocalRingCardinality.DataGatTies
open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

namespace Formalism.BasicNotions

structure GatTies (D : D7) where

  gat_k : ∀ u w h, (D.gat u w h).P.m + 1 = D.R.k

  gat_n : ∀ u w h (v : Fin (D.gat u w h).P.nV) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    (D.gat u w h).P.n' v = orderOf (D.host.galE σ).2

  gat_pos : ∀ u w h, (Σ v : Fin (D.gat u w h).P.nV, Fin ((D.gat u w h).P.n' v)) ≃ D.what₂.Tau

  gat_step : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    ((D.eTau (gat_pos u w h ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gat_pos u w h ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE σ * D.R.cc

  gat_lam : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (i : Fin ((D.gat u w h).P.m + 1)),
    (D.gat u w h).P.lam0 v s i =
      ((D.fm u).lam 0 (gat_pos u w h ⟨v, s⟩)).w
        ⟨i.1, by have h1 := gat_k u w h; have h2 := i.2; simp only [Ranks.N]; omega⟩

end Formalism.BasicNotions
end
