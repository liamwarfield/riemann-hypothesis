module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
namespace GlobalTheory.AdIdem

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct nonZeroDivisors

section

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_integral (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  have hy : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, hm, h⟩ := hy.exists_integral_multiple
  refine ⟨(m * m).toNat, ?_, ?_⟩
  · have := mul_self_pos.2 hm
    omega
  · have h2 : (((m * m).toNat : ℕ) : E) = (m : E) * m := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (mul_self_nonneg m), Int.cast_mul]
    have h3 : IsIntegral ℤ ((m : E) * (m • y)) :=
      IsIntegral.mul (by simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := m)) h
    refine ⟨⟨_, h3⟩, ?_⟩
    rw [h2, mul_assoc, ← zsmul_eq_mul y m]
    rfl

omit [NumberField E] in
theorem mul_mem_hat {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x * y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a * b, map_mul _ _ _⟩

theorem exists_eq_one_tmul_add (z : RA F E) :
    ∃ (x : E), ∃ h ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x + h := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a y =>
    obtain ⟨d, hd, hy⟩ := exists_nat_mul_integral E y
    obtain ⟨x, b, hb, rfl⟩ := exists_eq_algebraMap_add_nsmul F d hd a
    refine ⟨x • y, b ⊗ₜ[F] ((d : E) * y), tmul_mem_adelicCompletion_of_integral F hb hy, ?_⟩
    rw [TensorProduct.add_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  | add u v hu hv =>
    obtain ⟨x, h, hh, rfl⟩ := hu
    obtain ⟨x', h', hh', rfl⟩ := hv
    refine ⟨x + x', h + h', add_mem hh hh', ?_⟩
    rw [TensorProduct.tmul_add]
    abel

theorem mem_range_of_one_tmul_mem {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    x ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext y
    exact FractionalIdeal.mem_one_iff _
  rw [← h] at hx ⊢
  exact (one_tmul_mem_adelicCompletion_fractionalIdeal_iff F 1 x).1 hx

theorem mem_hat_of_idempotent (z : RA F E) (hz : z * z = z) :
    z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨x, h, hh, hx⟩ := exists_eq_one_tmul_add F E z
  obtain ⟨N, hN, hNx⟩ := exists_nat_mul_integral E x
  have h1 : (1 : RA F E) ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  have hc : ∀ y : E, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * y) =
      N • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y : RA F E) := by
    intro y
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul]
  have hNz : N • z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    rw [hx, nsmul_add, ← hc]
    exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F hNx) (nsmul_mem hh N)
  have hpow : ∀ n : ℕ, ∃ a ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      ∃ b ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (z - h) ^ n = a + z * b := by
    intro n
    induction n with
    | zero => exact ⟨1, h1, 0, zero_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, b, hb, e⟩ := ih
      refine ⟨-(a * h), neg_mem (mul_mem_hat F E ha hh), a + b - b * h,
        sub_mem (add_mem ha hb) (mul_mem_hat F E hb hh), ?_⟩
      rw [pow_succ, e]
      linear_combination b * hz
  have hzh : z - h = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by rw [hx]; abel
  have hint : ∀ n : ℕ, (N : E) * x ^ n ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro n
    apply mem_range_of_one_tmul_mem F E
    obtain ⟨a, ha, b, hb, e⟩ := hpow n
    rw [hzh, Algebra.TensorProduct.tmul_pow, one_pow] at e
    rw [hc, e, nsmul_add, ← smul_mul_assoc]
    exact add_mem (nsmul_mem ha N) (mul_mem_hat F E hNz hb)
  have hai : IsAlmostIntegral (𝓞 E) x := by
    refine ⟨(N : 𝓞 E), mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hN.ne'), fun n => ?_⟩
    rw [Algebra.smul_def, map_natCast]
    exact hint n
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hai.isIntegral
  rw [hx]
  exact add_mem (one_tmul_mem_adelicCompletionOfElementSet F ⟨r, hr⟩) hh

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idempotent_mem_intAE : ∀ (D : D7) (z : Af D.host.F ⊗[D.host.F] D.host.E), z * z = z → z ∈ intAE D := by
  intro D z hz
  have h : intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
    unfold intAE GlobalTheory.AdLat.hat1
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      exact ⟨a, ha, x, rfl⟩
  rw [h]
  exact mem_hat_of_idempotent D.host.F D.host.E z hz

end

end GlobalTheory.AdIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeStable

noncomputable def liftFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  LinearMap.rTensor D.host.E
    (show Af D.host.F →ₗ[D.host.F] AF D.host.F from LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F))

theorem liftFin_tmul (D : D7) (α : Af D.host.F) (m : D.host.E) :
    liftFin D (α ⊗ₜ[D.host.F] m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] m := rfl

theorem mul_pair_tmul (D : D7) (w : AE D) (α : Af D.host.F) (m : D.host.E) :
    w * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = liftFin D (finPart D w * (α ⊗ₜ[D.host.F] m)) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [zero_mul, RingHom.map_zero, zero_mul, LinearMap.map_zero]
  | tmul x e =>
    change _ = liftFin D ((sndA D.host.F x ⊗ₜ[D.host.F] e) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul]
    congr 1
    exact Prod.ext (mul_zero _) rfl
  | add x y hx hy => rw [add_mul, hx, hy, RingHom.map_add (f := _), add_mul, LinearMap.map_add (f := _)]

noncomputable def liftMul (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E →+ AE D :=
  (liftFin D).toAddMonoidHom.comp (AddMonoidHom.mulRight c)

theorem smul_mem_latO (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : AE D) (hw : finPart D w ∈ intAE D) :
    ∀ u ∈ latO S T LS LT P, w • u ∈ latO S T LS LT P := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => w • u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : latO S T LS LT P ≤ (latO S T LS LT P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun y => Matrix.of fun i j => liftMul D
        (α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * HSpace.gram S k j)) y)
      fun y y' => Matrix.ext fun i j => (liftMul D _).map_add y y'
    have hle : intAE D ≤ (latO S T LS LT P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, o • a,
        Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · ext i j
        change liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _ ⊗ₜ[D.host.F] _
        rw [Algebra.TensorProduct.tmul_mul_tmul, liftFin_tmul, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * HSpace.gram S k j) : WO S T) = Φ (finPart D w) :=
      Matrix.ext fun i j => mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

end GlobalTheory.LatticeStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealLineAt

theorem exists_inverse_chart {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, GlobalTheory.FockCompare.Chart θ σ := by
  obtain ⟨ρ, h1, h2, h3⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  exact GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ h1 h2 h3


open Classical in
def ray {ι : Type} (τ : ι) (c : ℂ) : ℝ →+ (ι → ℂ) where
  toFun t := fun τ' => if τ' = τ then (t : ℂ) * c else 0
  map_zero' := by funext τ'; simp
  map_add' s t := by
    funext τ'
    simp only [Pi.add_apply]
    split_ifs <;> simp [add_mul]

theorem continuous_ray {ι : Type} (τ : ι) (c : ℂ) : Continuous (ray τ c) := by
  refine continuous_pi fun τ' => ?_
  by_cases h : τ' = τ
  · have : (fun t : ℝ => ray τ c t τ') = fun t : ℝ => (t : ℂ) * c := funext fun t => if_pos h
    rw [this]
    exact Complex.continuous_ofReal.mul continuous_const
  · have : (fun t : ℝ => ray τ c t τ') = fun _ : ℝ => (0 : ℂ) := funext fun t => if_neg h
    rw [this]
    exact continuous_const

theorem lineAt_exists (D : D7) : LineAtExists D := by
  intro θ hθ m n τ z
  obtain ⟨σ, hσ⟩ := exists_inverse_chart hθ
  let L : ℝ →+ Mx D m n :=
    { toFun := fun t => Matrix.of fun i j => σ (ray τ (z i j) t)
      map_zero' := by
        funext i j
        show σ (ray τ (z i j) 0) = 0
        rw [(ray τ (z i j)).map_zero, σ.map_zero]
      map_add' := fun s t => by
        funext i j
        show σ (ray τ (z i j) (s + t)) = σ (ray τ (z i j) s) + σ (ray τ (z i j) t)
        rw [map_add, map_add] }
  refine ⟨L, ?_, fun t => ?_, fun t τ' => ?_⟩
  · exact continuous_pi fun i => continuous_pi fun j => hσ.cont.comp (continuous_ray τ (z i j))
  · funext i j
    exact hσ.fin _
  · funext i j
    refine (hσ.comp (ray τ (z i j) t) τ').trans ?_
    by_cases h : τ' = τ
    · rw [if_pos h]
      exact if_pos h
    · rw [if_neg h]
      exact if_neg h

theorem lineAt_unique (D : D7) : LineAtUnique D := by
  intro θ hθ m n τ z L L' hL hL'
  obtain ⟨σ, hσ⟩ := exists_inverse_chart hθ
  refine AddMonoidHom.ext fun t => ?_
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ' => ?_)
  · have e1 : finPart D (L t i j) = 0 := congrFun (congrFun (hL.2.1 t) i) j
    have e2 : finPart D (L' t i j) = 0 := congrFun (congrFun (hL'.2.1 t) i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ' (infPart D (L t i j)) = θ τ' (infPart D (L' t i j)) :=
      congrFun (congrFun ((hL.2.2 t τ').trans (hL'.2.2 t τ').symm) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem lineAt_exists_unique : ∀ D : D7, LineAtExists D ∧ LineAtUnique D :=
  fun D => ⟨lineAt_exists D, lineAt_unique D⟩

end GlobalTheory.RealLineAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

variable {D : D7}

def hRat (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (y c b) * T.gram c d * x d a

def genMap (S T : HSp D) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j

def latRat (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ s ∈ LS, ∃ t ∈ LT, w = genMap S T a s t}

def finTens {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun x => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x

theorem finTens_add {m n : ℕ} (α : Af D.host.F) (M N : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (M + N) = finTens α M + finTens α N := by
  ext i j; simp [finTens, TensorProduct.tmul_add]

theorem finTens_zero {m n : ℕ} (α : Af D.host.F) :
    finTens α (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  ext i j; simp [finTens]

theorem finTens_neg {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (-M) = -finTens α M := by
  ext i j; simp [finTens, TensorProduct.tmul_neg]

theorem smul_mem_latRat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (c : 𝓞 D.host.E) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hM : M ∈ latRat S T LS LT) :
    (c : D.host.E) • M ∈ latRat S T LS LT := by
  induction hM using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨(c : D.host.E) * a, ?_, s, hs, t, ht, ?_⟩
    · exact Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    · ext i j; simp [genMap, mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem finTens_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hM : M ∈ latRat S T LS LT) : finTens α M ∈ latO S T LS LT fun _ => True := by
  induction hM using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, fun v hv => absurd trivial hv, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [finTens_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [finTens_add]; exact add_mem hx hy
  | neg x _ hx => rw [finTens_neg]; exact neg_mem hx

theorem latO_induction {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {p : WO S T → Prop} (mem : ∀ α ∈ intAf D.host.F, ∀ M ∈ latRat S T LS LT, p (finTens α M))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x))
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) : p u := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    exact mem α hα (genMap S T a s t) (AddSubgroup.subset_closure ⟨a, ha, s, hs, t, ht, rfl⟩)
  | zero => exact zero
  | add x y _ _ hx hy => exact add _ _ hx hy
  | neg x _ hx => exact neg _ hx

theorem gram_star (S : HSp D) (i j : Fin S.rank) : star (S.gram i j) = S.gram j i :=
  S.herm.eq (S.frame i) (S.frame j)

theorem gram_det_isUnit (S : HSp D) : IsUnit S.gram.det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h1 : ∑ j, v j • S.frame j = 0 := by
    apply S.nondeg.2
    intro x
    have : (S.hT.flip (∑ j, v j • S.frame j)) = 0 := by
      refine S.frame.ext fun i => ?_
      have := congrFun hv0 i
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mulVec, dotProduct, HSpace.gram, map_sum, mul_comm] using this
    exact LinearMap.congr_fun this x
  exact funext (Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h1)

theorem hRat_genMap (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    hRat S T x (genMap S T a s t) = star a * ∑ c, ∑ d, star (t c) * T.gram c d * (x *ᵥ s) d := by
  have key : ∀ e, ∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b) = s e := by
    intro e
    have : ∀ b, star (∑ k, star (s k) * S.gram k b) = (S.gram *ᵥ s) b := by
      intro b
      simp [star_sum, gram_star, Matrix.mulVec, dotProduct, mul_comm]
    simp_rw [this]
    change (S.gram⁻¹ *ᵥ (S.gram *ᵥ s)) e = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (gram_det_isUnit S), Matrix.one_mulVec]
  calc hRat S T x (genMap S T a s t)
      = ∑ e, (∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b)) *
          ∑ c, ∑ d, star a * star (t c) * T.gram c d * x d e := by
        unfold hRat genMap
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Finset.mul_sum (s := Finset.univ (α := Fin T.rank)), Matrix.of_apply, star_mul']
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    _ = _ := by
        simp_rw [key]
        simp only [Finset.mul_sum, Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring

theorem hO_finTens (S T : HSp D) (α β : Af D.host.F) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (finTens α M) (finTens β N) = (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] hRat S T M N := by
  have hp : pairA D.host.F 0 (α * β) = pairA D.host.F 0 β * pairA D.host.F 0 α := by
    exact Prod.ext (mul_zero _).symm (mul_comm _ _)
  unfold hO hRat
  simp only [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h1 : cA D (finTens β N c b) = (pairA D.host.F 0 β) ⊗ₜ[D.host.F] star (N c b) := rfl
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [h1, h2, h2, hp]
  simp [finTens, Algebra.TensorProduct.tmul_mul_tmul]

theorem trace_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem symplO_finTens (S T : HSp D) (α β : Af D.host.F) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (finTens α M) (finTens β N) = pairA D.host.F 0 (α * β * algebraMap D.host.F (Af D.host.F)
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T M N))) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplO, hO_finTens, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul]
  exact Prod.ext (zero_mul _) rfl

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, RingHom.map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  rw [symplO, hO_add_left, mul_add, map_add (f := _)]; rfl

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  rw [symplO, hO_add_right, mul_add, map_add (f := _)]; rfl

def symplHom (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (symplO S T x) (symplO_add_right S T x))
    fun x x' => AddMonoidHom.ext fun y => symplO_add_left S T x x' y

theorem symplHom_apply (S T : HSp D) (x y : WO S T) : symplHom S T x y = symplO S T x y := rfl

end GlobalTheory.LatVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) :
    IsSBHalf e Λ (halfInd e Λ) := by
  classical
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [halfInd, h])
  · have : (t + 1 • u ∈ Λ ∧ IsHalf e (t + 1 • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
      rw [one_smul, Λ.add_mem_cancel_right hu]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    simp only [halfInd, this]
  · by_contra h
    rw [one_smul] at h
    exact ht (by simp [halfInd, h])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
open NumberField IsDedekindDomain MeasureTheory Polynomial

namespace GlobalTheory.GLIntegral

section general

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def glSub (S : Subring A) : Subgroup (GL ι A) where
  carrier := {g | (∀ i j, (g : Matrix ι ι A) i j ∈ S) ∧ ∀ i j, ((g⁻¹ : GL ι A) : Matrix ι ι A) i j ∈ S}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix ι ι A) i j ∈ S := fun i j => by
      rw [Matrix.one_apply]; split_ifs
      exacts [S.one_mem, S.zero_mem]
    exact ⟨h, by simpa using h⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (ha _ _) (hb _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact S.sum_mem fun k _ => S.mul_mem (hb' _ _) (ha' _ _)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

variable [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem isOpen_glSub (S : Subring A) (hS : IsOpen (S : Set A)) :
    IsOpen (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsOpen {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hS.preimage (continuous_id.matrix_elem i j)
  exact (h.preimage Units.continuous_val).inter (h.preimage Units.continuous_coe_inv)

theorem isCompact_glSub [T2Space A] (S : Subring A) (hS : IsCompact (S : Set A)) :
    IsCompact (glSub (ι := ι) S : Set (GL ι A)) := by
  have h : IsCompact {m : Matrix ι ι A | ∀ i j, m i j ∈ S} := by
    have := isCompact_univ_pi fun _ : ι => isCompact_univ_pi fun _ : ι => hS
    have e : {m : Matrix ι ι A | ∀ i j, m i j ∈ S} =
        Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => (S : Set A) :=
      Set.ext fun m => ⟨fun hm i _ j _ => hm i j, fun hm i j => hm i trivial j trivial⟩
    rw [e]; exact this
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix ι ι A)).isCompact_preimage
    (h.prod (h.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  constructor
  · rintro ⟨h1, h1'⟩
    exact ⟨h1, _, h1', rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL ι A) : Matrix ι ι A) := MulOpposite.op_injective hm'
    rw [← this]; exact hm

end general

def intSubring (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem exists_isOpen_isCompact : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∃ U : Subgroup (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) ∧ IsCompact (U : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  intro F _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  refine ⟨glSub (intSubring F), isOpen_glSub _ ?_,
    isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral F)⟩
  exact RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

end GlobalTheory.GLIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralFinAdele

variable (F : Type) [Field F] [NumberField F]

theorem t2Space_finiteAdeleRing' : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

theorem natCast_apply (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (M : FiniteAdeleRing (𝓞 F) F) v = ((algebraMap (𝓞 F) F (M : 𝓞 F) : F) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    map_natCast (algebraMap (𝓞 F) F)]

theorem mul_apply' (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

theorem pow_apply' (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (a ^ n) v = a v ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, mul_apply', ih]

theorem eq_zero_of_forall_mul (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F,
      (∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
        a = (M : FiniteAdeleRing (𝓞 F) F) * c) : a = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  change a v = 0
  by_contra h0
  set N := Ideal.absNorm v.asIdeal with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hlt : Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) < 1 := by
    rw [natCast_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _
  have hv0 : Valued.v (a v) ≠ 0 := by simpa using h0
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
  obtain ⟨c, hc, hac⟩ := h (N ^ n) (pow_pos hNpos n)
  have hc' : Valued.v (c v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc v)
  have : Valued.v (a v) ≤ Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) ^ n := by
    conv_lhs => rw [hac]
    rw [mul_apply', Nat.cast_pow, pow_apply', map_mul, map_pow]
    exact mul_le_of_le_one_right' hc'
  exact absurd hn (not_lt.2 this)

theorem exists_nat_mul_integral (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ M : ℕ, 0 < M ∧ ∀ v, ((M : FiniteAdeleRing (𝓞 F) F) * a) v ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).2 inferInstance
  obtain ⟨m, y, hm, hmx⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 F)
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)
  refine ⟨m, Nat.pos_of_ne_zero hm, fun v => ?_⟩
  have h : (m : FiniteAdeleRing (𝓞 F) F) * a =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F y) +
        (m : FiniteAdeleRing (𝓞 F) F) * b := by
    rw [hab, ← hmx, one_smul, map_nsmul, nsmul_eq_mul, mul_add]
  rw [h]
  refine add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y) (mul_mem ?_ (hb v))
  exact natCast_apply F m v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (m : 𝓞 F)

theorem integral_finiteAdele_properties : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  refine ⟨GlobalTheory.AdeleCocompact.isCompact_integral F, fun M _ => ?_, eq_zero_of_forall_mul F,
    fun x hx => ?_, exists_nat_mul_integral F, ⟨fun a ⟨n, hn⟩ => ?_⟩⟩
  · haveI := t2Space_finiteAdeleRing' F
    have h := ((GlobalTheory.AdeleCocompact.isCompact_integral F).image
      (continuous_const_mul (M : FiniteAdeleRing (𝓞 F) F))).isClosed
    convert h using 1
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_comm]
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)
      rwa [FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact ⟨y, hy.symm⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    have : a v ^ n = 0 := by rw [← pow_apply', hn]; rfl
    exact eq_zero_of_pow_eq_zero this

end GlobalTheory.IntegralFinAdele
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiplesStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdele_compact_closed_multiples : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | exact GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties | (intros; apply GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompletedLatticeFinite

section General

variable {E : Type} [Field E] [NumberField E]

theorem exists_denom {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : E, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ (d * x i) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin n))).image fun p => p.1 p.2)
  refine ⟨(y : E), by exact_mod_cast hy0, fun x hx i => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have := hy (x i) (Finset.mem_image.2 ⟨(x, i), by simpa using hx, rfl⟩)
    simpa [zsmul_eq_mul] using this
  | zero => simpa using isIntegral_zero
  | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact hx.add hz
  | smul c x _ hx =>
    have : (y : E) * (c • x) i = (c : E) * ((y : E) * x i) := by
      change (y : E) * ((c : E) * x i) = _
      ring
    rw [this]
    exact c.isIntegral_coe.mul hx

theorem finite_of_denom (d : E) (hd : d ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ (d * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ R}.Finite := by
  have h := NumberField.Embeddings.finite_of_norm_le E ℂ ((∑ φ : E →+* ℂ, ‖φ d‖) * R)
  refine (h.preimage (f := fun x => d * x) (mul_right_injective₀ hd).injOn).subset ?_
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun φ => ?_⟩
  rw [map_mul, norm_mul]
  exact mul_le_mul (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ d‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ φ)) (hb φ) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem mem_spanSingleton_inv (d : E) (hd : d ≠ 0) (x : E) :
    x ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ d⁻¹ ↔ IsIntegral ℤ (d * x) := by
  rw [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, rfl⟩
    have : d * (z • d⁻¹) = (z : E) := by
      change d * ((z : E) * d⁻¹) = _
      field_simp
    rw [this]
    exact z.isIntegral_coe
  · intro h
    refine ⟨⟨d * x, h⟩, ?_⟩
    change d * x * d⁻¹ = x
    field_simp

end General

theorem isIntegral_star (D : D7) {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem norm_emb_le (D : D7) {x : D.host.E} {R : ℝ} (h : ∀ τ, ‖tauE D τ x‖ ≤ R) (φ : D.host.E →+* ℂ) :
    ‖φ x‖ ≤ R := by
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have := h τ
  rw [← InfinitePlace.apply] at this ⊢
  rw [← hτ]
  exact this

theorem finite_rational_points : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  classical
  intro D S T ΛS ΛT hS hT R
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS.1.fg
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT.1.fg
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  refine (Set.Finite.pi' fun _ : Fin T.rank => Set.Finite.pi' fun _ : Fin S.rank =>
    finite_of_denom d hd R).subset ?_
  rintro g ⟨⟨l, hl, hgl⟩, hb⟩ i j
  refine ⟨?_, norm_emb_le D fun τ => hb τ i j⟩
  have h1 : finPart D (incA D (g i j) - l i j) = 0 := congrFun (congrFun hgl i) j
  rw [RingHom.map_sub, sub_eq_zero] at h1
  have h2 := hlat l hl i j
  rw [← h1] at h2
  exact (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (g i j)).1 h2)

end GlobalTheory.CompletedLatticeFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rational_points_completed_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ R : ℝ, {g : Matrix (Fin T.rank) (Fin S.rank) D.host.E | (∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ((ratW T S g : WO S T) - l).map (finPart D) = 0) ∧ ∀ τ i j, ‖tauE D τ (g i j)‖ ≤ R}.Finite := by
  first | exact @GlobalTheory.CompletedLatticeFinite.finite_rational_points | exact GlobalTheory.CompletedLatticeFinite.finite_rational_points | (intros; apply GlobalTheory.CompletedLatticeFinite.finite_rational_points <;> assumption)
end
end
