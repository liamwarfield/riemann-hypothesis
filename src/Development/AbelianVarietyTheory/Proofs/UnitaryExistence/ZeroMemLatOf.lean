module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem _root_.GlobalTheory.AdLat.Scale.smul_mem_hat {L L' : Set (Fin n → E)} {a : E}
    (h : ∀ x ∈ L, a • x ∈ L')
    {z : Fin n → _root_.GlobalTheory.AdLat.RA F E} (hz : z ∈ _root_.GlobalTheory.AdLat.hat F L) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) • z ∈
      _root_.GlobalTheory.AdLat.hat F L' := by
  unfold _root_.GlobalTheory.AdLat.hat at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨b, hb, a • x, h x hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * (b ⊗ₜ[F] x i) = b ⊗ₜ[F] (a * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.AdLat.Scale

namespace GlobalTheory.AdLat

open Scale

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

private theorem fv_smul' (c : E) (v : Fin n → E) :
    _root_.GlobalTheory.AdLat.fv F (c • v) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : _root_.GlobalTheory.AdLat.RA F E) •
        _root_.GlobalTheory.AdLat.fv F v := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c * v i) =
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] v i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem smul_mem_latOf_of_smul_mem {L L' : Set (Fin n → E)} {c : E}
    (h : ∀ x ∈ L, c • x ∈ L') (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E))
    {v : Fin n → E} (hv : v ∈ _root_.GlobalTheory.AdLat.latOf F g L) :
    c • v ∈ _root_.GlobalTheory.AdLat.latOf F g L' := by
  obtain ⟨z, hz, hzv⟩ := hv
  refine ⟨_, _root_.GlobalTheory.AdLat.Scale.smul_mem_hat h hz, ?_⟩
  rw [Matrix.mulVec_smul, hzv, fv_smul']

private theorem fv_zero' :
    _root_.GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : E) = 0
  rw [TensorProduct.tmul_zero]

private theorem zero_mem_latOf' {L : Set (Fin n → E)}
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) :
    (0 : Fin n → E) ∈ _root_.GlobalTheory.AdLat.latOf F g L :=
  ⟨0, zero_mem _, by rw [Matrix.mulVec_zero, fv_zero']⟩

private theorem fv_add' (v w : Fin n → E) :
    _root_.GlobalTheory.AdLat.fv F (v + w) =
      _root_.GlobalTheory.AdLat.fv F v + _root_.GlobalTheory.AdLat.fv F w := by
  funext i
  change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (v i + w i) = _ ⊗ₜ[F] v i + _ ⊗ₜ[F] w i
  rw [TensorProduct.tmul_add]

private theorem add_mem_latOf' {L : Set (Fin n → E)}
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) {v w : Fin n → E}
    (hv : v ∈ _root_.GlobalTheory.AdLat.latOf F g L)
    (hw : w ∈ _root_.GlobalTheory.AdLat.latOf F g L) :
    v + w ∈ _root_.GlobalTheory.AdLat.latOf F g L := by
  obtain ⟨z, hz, hzv⟩ := hv
  obtain ⟨y, hy, hyw⟩ := hw
  exact ⟨z + y, add_mem hz hy, by rw [Matrix.mulVec_add, hzv, hyw, fv_add']⟩
end

theorem _root_.GlobalTheory.AdLat.scale_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (I : FractionalIdeal (𝓞 E)⁰ E) (L' : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → I ≠ 0 → L' = Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ x ∈ L, w = a • x} → ((Submodule.span (𝓞 E) {w | ∃ a ∈ I, ∃ v ∈ _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L, w = a • v} : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = _root_.GlobalTheory.AdLat.latOf F (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) L' ∧ (AddSubgroup.closure {w | ∃ a ∈ I, ∃ z ∈ (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))), w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * z i} : Set (Fin n → _root_.GlobalTheory.AdLat.RA F E)) = (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)).mulVec '' (_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E))) ∧ L'.FG ∧ Submodule.span E (L' : Set (Fin n → E)) = ⊤ := by
  intro F E _ _ _ _ _ n L g I L' hLfg hLspan hI hL'
  set G : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E) :=
    (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) with hG
  have hgen : ∀ a ∈ I, ∀ x ∈ L, a • x ∈ L' := fun a ha x hx => by
    rw [hL']
    exact Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
  have hinv : ∀ b ∈ I⁻¹, ∀ x ∈ (L' : Set (Fin n → E)), b • x ∈ (L : Set (Fin n → E)) := by
    intro b hb x hx
    rw [SetLike.mem_coe, hL'] at hx
    rw [SetLike.mem_coe]
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hw
      obtain ⟨r, hr⟩ :=
        (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hb a ha)
      rw [smul_smul, ← hr, algebraMap_smul]
      exact L.smul_mem r hy
    | zero => rw [smul_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
    | smul r w _ hw =>
      rw [← algebraMap_smul E r w, smul_comm, algebraMap_smul]
      exact L.smul_mem r hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [SetLike.mem_coe] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨a, ha, v, hv, rfl⟩ := hw
        exact smul_mem_latOf_of_smul_mem (fun x hx => hgen a ha x hx) G hv
      | zero => exact zero_mem_latOf' G
      | add x y _ _ hx hy => exact add_mem_latOf' G hx hy
      | smul r w _ hw =>
        rw [← algebraMap_smul E r w]
        refine smul_mem_latOf_of_smul_mem (fun x hx => ?_) G hw
        rw [algebraMap_smul]
        exact L'.smul_mem r hx
    · intro v hv
      let N : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E)
        {w | ∃ a ∈ I, ∃ v ∈ _root_.GlobalTheory.AdLat.latOf F G L, w = a • v}
      let S : Submodule (𝓞 E) E :=
        { carrier := {c | c • v ∈ N}
          add_mem' := fun {c d} hc hd => by
            change (c + d) • v ∈ N
            rw [add_smul]
            exact N.add_mem hc hd
          zero_mem' := by
            change (0 : E) • v ∈ N
            rw [zero_smul]
            exact N.zero_mem
          smul_mem' := fun r c hc => by
            change (r • c) • v ∈ N
            rw [smul_assoc]
            exact N.smul_mem r hc }
      have hle : (I : Submodule (𝓞 E) E) * ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
          ≤ S := Submodule.mul_le.2 fun a ha b hb => by
        change (a * b) • v ∈ N
        rw [mul_smul]
        exact Submodule.subset_span ⟨a, ha, b • v, smul_mem_latOf_of_smul_mem (hinv b hb) G hv, rfl⟩
      have h1 : (1 : E) ∈ (I : Submodule (𝓞 E) E) *
          ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
        rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
        exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
      have h2 : (1 : E) • v ∈ N := hle h1
      rwa [one_smul] at h2
  · let φ : (Fin n → _root_.GlobalTheory.AdLat.RA F E) →+ (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
      AddMonoidHom.mk' (fun z => G *ᵥ z) (Matrix.mulVec_add G)
    have himage : G.mulVec '' (_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E)) :
        Set (Fin n → _root_.GlobalTheory.AdLat.RA F E)) =
        ((_root_.GlobalTheory.AdLat.hat F (L' : Set (Fin n → E))).map φ : Set _) :=
      (AddSubgroup.coe_map φ _).symm
    rw [himage]
    congr 1
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro w ⟨a, ha, z, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) • y,
        _root_.GlobalTheory.AdLat.Scale.smul_mem_hat (fun x hx => hgen a ha x hx) hy, ?_⟩
      change G *ᵥ (_ • y) = _
      rw [Matrix.mulVec_smul]
      rfl
    · rw [AddSubgroup.map_le_iff_le_comap]
      intro z hz
      unfold _root_.GlobalTheory.AdLat.hat at hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨b, hb, w, hw, rfl⟩ := hz
        rw [SetLike.mem_coe, hL'] at hw
        rw [show w = (1 : 𝓞 E) • w from (one_smul _ _).symm]
        generalize (1 : 𝓞 E) = r
        induction hw using Submodule.span_induction generalizing r with
        | mem w hw =>
          obtain ⟨a, ha, x, hx, rfl⟩ := hw
          have hy : r • x ∈ L := L.smul_mem r hx
          have heq : (fun i => b ⊗ₜ[F] (r • a • x) i) =
              ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) •
                fun i => b ⊗ₜ[F] (r • x) i := by
            funext i
            change b ⊗ₜ[F] (r • a • x) i =
              ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * (b ⊗ₜ[F] (r • x) i)
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            congr 1
            simp only [Pi.smul_apply, smul_eq_mul, mul_smul_comm]
          change G *ᵥ (fun i => b ⊗ₜ[F] (r • a • x) i) ∈ AddSubgroup.closure _
          rw [heq, Matrix.mulVec_smul]
          exact AddSubgroup.subset_closure
            ⟨a, ha, _, ⟨_, AddSubgroup.subset_closure ⟨b, hb, r • x, hy, rfl⟩, rfl⟩, rfl⟩
        | zero =>
          have h0 : (fun i => b ⊗ₜ[F] (r • (0 : Fin n → E)) i) = 0 := by
            funext i
            simp
          rw [h0]
          exact zero_mem _
        | add x y _ _ hx hy =>
          have hxy : (fun i => b ⊗ₜ[F] (r • (x + y)) i) =
              (fun i => b ⊗ₜ[F] (r • x) i) + fun i => b ⊗ₜ[F] (r • y) i := by
            funext i
            simp [smul_add, TensorProduct.tmul_add]
          rw [hxy]
          exact add_mem (hx r) (hy r)
        | smul s w _ hw =>
          rw [smul_smul]
          exact hw (r * s)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
  · obtain ⟨d, hd, hdI⟩ := I.isFractional
    have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero hd)
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (((algebraMap (𝓞 E) E d)⁻¹ • LinearMap.id : (Fin n → E) →ₗ[E] (Fin n → E))).restrictScalars
        (𝓞 E)
    have hle : L' ≤ L.map f := by
      rw [hL', Submodule.span_le]
      rintro w ⟨a, ha, x, hx, rfl⟩
      obtain ⟨r, hr⟩ := hdI a ha
      refine ⟨r • x, L.smul_mem r hx, ?_⟩
      change (algebraMap (𝓞 E) E d)⁻¹ • (r • x) = a • x
      rw [← algebraMap_smul E r x, hr, smul_smul, Algebra.smul_def d a, inv_mul_cancel_left₀ hd0]
    exact (hLfg.map f).of_le hle
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.2 hI)
    rw [eq_top_iff, ← hLspan, Submodule.span_le]
    intro x hx
    have hax : a • x ∈ Submodule.span E (L' : Set (Fin n → E)) :=
      Submodule.subset_span (hgen a ha x hx)
    have := Submodule.smul_mem _ a⁻¹ hax
    rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this

end GlobalTheory.AdLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
open NumberField IsDedekindDomain GlobalTheory.AdLat WithZero
open scoped TensorProduct Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.AdLat

variable {F : Type} [Field F] [NumberField F]

theorem valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.intValuation (N : 𝓞 F) := by
  have h : (N : v.adicCompletion F)
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (N : 𝓞 F)) := by simp
  rw [h, ← v.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) ≤ 1 := by
  rw [valued_natCast_eq]; exact v.intValuation_le_one _

theorem valued_natCast_ne_zero (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : 0 < N) :
    Valued.v (N : v.adicCompletion F) ≠ 0 := by
  rw [valued_natCast_eq]
  exact v.intValuation_ne_zero _ (by exact_mod_cast hN.ne')

theorem exists_nat_valued_pow_le (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, Valued.v ((p ^ n : ℕ) : v.adicCompletion F) ≤ exp (-(n : ℤ)) := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, fun n => ?_⟩
  · exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · rw [valued_natCast_eq, HeightOneSpectrum.intValuation_le_pow_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) n

theorem eq_zero_of_valued_le_natCast (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F)
    (h : ∀ N : ℕ, 0 < N → Valued.v y ≤ Valued.v (N : v.adicCompletion F)) : y = 0 := by
  by_contra hy
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (γ := Valued.v y) (by simpa using hy)
  exact absurd ((h _ (pow_pos hp n)).trans (hpn n)) (not_le.2 hn)

theorem exists_limit_of_compatible (v : HeightOneSpectrum (𝓞 F)) (x : ℕ → v.adicCompletion F)
    (h : ∀ N m : ℕ, 0 < N → 0 < m →
      Valued.v (x (N * m) - x N) ≤ Valued.v (N : v.adicCompletion F)) :
    ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
      Valued.v (t - x N) ≤ Valued.v (N : v.adicCompletion F) := by
  obtain ⟨p, hp, hpn⟩ := exists_nat_valued_pow_le v
  obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit (K := F) v (fun n => x (p ^ n)) (fun m n hnm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add]
    exact (h _ _ (pow_pos hp n) (pow_pos hp k)).trans (hpn n))
  refine ⟨t, fun N hN => ?_⟩
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt (valued_natCast_ne_zero v hN)
  have h1 := (ht n).trans hn.le
  have h2 := ((h _ _ (pow_pos hp n) hN).trans (hpn n)).trans hn.le
  have h3 := h _ _ hN (pow_pos hp n)
  have e : t - x N = (t - x (p ^ n)) - (x (p ^ n * N) - x (p ^ n)) + (x (N * p ^ n) - x N) := by
    rw [mul_comm N]; ring
  rw [e]
  exact Valuation.map_add_le _ (Valuation.map_sub_le _ h1 h2) h3

theorem valued_nsmul_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : a v ∈ v.adicCompletionIntegers F) :
    Valued.v ((N • a) v) ≤ Valued.v (N : v.adicCompletion F) := by
  have : (N • a) v = N • a v := rfl
  rw [this, nsmul_eq_mul, map_mul]
  exact mul_le_of_le_one_right' ha

theorem integral_finiteAdele_complete_separated :
    ∀ (F : Type) [Field F] [NumberField F], (∀ y : FiniteAdeleRing (𝓞 F) F, (∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a) → y = 0) ∧ ∀ x : ℕ → FiniteAdeleRing (𝓞 F) F, (∀ N v, x N v ∈ v.adicCompletionIntegers F) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x (N * m) = x N + N • a) → ∃ y : FiniteAdeleRing (𝓞 F) F, ∀ N : ℕ, 0 < N → ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = x N + N • a := by
  intro F _ _
  refine ⟨fun y hy => ?_, fun x hx h => ?_⟩
  · refine DFunLike.ext _ _ fun v => ?_
    refine eq_zero_of_valued_le_natCast v (y v) fun N hN => ?_
    obtain ⟨a, ha, rfl⟩ := hy N hN
    exact valued_nsmul_le v N a (ha v)
  · have key : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t : v.adicCompletion F, ∀ N : ℕ, 0 < N →
        Valued.v (t - x N v) ≤ Valued.v (N : v.adicCompletion F) := fun v => by
      refine exists_limit_of_compatible v (fun N => x N v) fun N m hN hm => ?_
      obtain ⟨a, ha, e⟩ := h N m hN hm
      have : x (N * m) v - x N v = (N • a) v := by
        rw [e]
        exact add_sub_cancel_left (x N v) ((N • a) v)
      rw [this]
      exact valued_nsmul_le v N a (ha v)
    choose t ht using key
    have ht1 : ∀ v, t v ∈ v.adicCompletionIntegers F := fun v => by
      have h1 : Valued.v (t v - x 1 v) ≤ 1 := (ht v 1 one_pos).trans (valued_natCast_le_one v 1)
      have h2 : t v - x 1 v ∈ v.adicCompletionIntegers F := h1
      simpa using add_mem h2 (hx 1 v)
    refine ⟨⟨t, Filter.Eventually.of_forall ht1⟩, fun N hN => ?_⟩
    have hq : ∀ v, (t v - x N v) / (N : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
      fun v => by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ (ht v N hN) zero_le'
    refine ⟨⟨fun v => (t v - x N v) / (N : v.adicCompletion F),
      Filter.Eventually.of_forall hq⟩, hq, ?_⟩
    refine DFunLike.ext _ _ fun v => ?_
    change t v = x N v + N • ((t v - x N v) / (N : v.adicCompletion F))
    have hN0 : (N : v.adicCompletion F) ≠ 0 := fun h0 =>
      valued_natCast_ne_zero v hN (by rw [h0, map_zero])
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hN0]
    ring

end GlobalTheory.AdLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdIdem

theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (s : K) :
    ∃ e : K, (e = 0 ∨ e = 1) ∧ w (1 + 1) ≤ w (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : (1 + 1 : K) = (1 + s) + (1 - s) := by ring
  have h := w.map_add (1 + s) (1 - s)
  rw [← h2] at h
  rcases le_total (w (1 - s)) (w (1 + s)) with hle | hle
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [max_eq_left hle] at h
    simpa using h
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [max_eq_right hle] at h
    simpa using h

theorem local_field {K : Type*} [Field K] (h2 : (1 + 1 : K) ≠ 0) (s : K) :
    ∃ e : K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  by_cases h : 1 + s = 0
  · refine ⟨0, by simp, ?_⟩
    rw [isUnit_iff_ne_zero]
    intro h'
    apply h2
    linear_combination h + h'
  · exact ⟨1, by simp, by simpa [isUnit_iff_ne_zero] using h⟩

theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (s : FiniteAdeleRing R K) :
    ∃ e : FiniteAdeleRing R K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have hu : IsUnit (1 + 1 : FiniteAdeleRing R K) := by
    have : IsUnit (1 + 1 : K) := by
      rw [isUnit_iff_ne_zero]; norm_num
    simpa using this.map (algebraMap K (FiniteAdeleRing R K))
  rw [FiniteAdeleRing.isUnit_iff] at hu
  choose e he hv using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (s v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_, ?_⟩
  · refine FiniteAdeleRing.ext K fun v => ?_
    change e v * e v = e v
    rcases he v with h | h <;> simp [h]
  · have hval : ∀ v : HeightOneSpectrum R, Valued.v ((1 + 1 : FiniteAdeleRing R K) v) ≤
        Valued.v ((E * (1 + s) + (1 - E) * (1 - s)) v) := fun v => hv v
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun v h0 => ?_, ?_⟩
    · have := hval v
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact hu.1 v this
    · filter_upwards [hu.2, (E * (1 + s) + (1 - E) * (1 - s)).2] with v h1 h2
      exact le_antisymm h2 (h1 ▸ hval v)

theorem infinite_part (K : Type*) [Field K] [CharZero K] (s : InfiniteAdeleRing K) :
    ∃ e : InfiniteAdeleRing K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : ∀ v : InfinitePlace K, (1 + 1 : v.Completion) ≠ 0 := by
    intro v h
    have : algebraMap K v.Completion (1 + 1) = 0 := by rw [map_add (f := _), map_one]; exact h
    rw [map_eq_zero] at this
    norm_num at this
  choose e he hu using fun v : InfinitePlace K => local_field (h2 v) (s v)
  exact ⟨e, funext he, Pi.isUnit_iff.2 hu⟩

theorem exists_idem_isUnit (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F) :
    ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  obtain ⟨e₁, h₁, u₁⟩ := infinite_part F s.1
  obtain ⟨e₂, h₂, u₂⟩ := finite_part (𝓞 F) F s.2
  exact ⟨(e₁, e₂), Prod.ext h₁ h₂, Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.AdIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele : ∀ (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F), ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  first | exact @GlobalTheory.AdIdem.exists_idem_isUnit | exact GlobalTheory.AdIdem.exists_idem_isUnit | (intros; apply GlobalTheory.AdIdem.exists_idem_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant
set_option autoImplicit false

namespace GlobalTheory

open scoped TensorProduct

theorem char_eq_one_of_inverse_det_one_of_basis {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by
  classical
  let φ2 : Module.End S V →* Module.End R V :=
    { toFun := fun g => g.restrictScalars R, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let φ4 : (V ≃ₗ[R] V) →* (Q ≃ₗ[R] Q) :=
    { toFun := fun u => e.trans (u.trans e.symm)
      map_one' := by ext q; simp
      map_mul' := by intro u v; ext q; simp }
  let Φ : GL (Fin r) S →* (Q ≃ₗ[R] Q) :=
    φ4.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      ((Units.map φ2).comp (Units.map ((Matrix.toLinAlgEquiv b :
        Matrix (Fin r) (Fin r) S ≃ₐ[S] Module.End S V) : Matrix (Fin r) (Fin r) S →* Module.End S V))))
  have hdet : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [LinearMap.det_toMatrix, hf]; exact isUnit_one
  let g : GL (Fin r) S := Matrix.nonsingInvUnit _ hdet
  have hg : (g : Matrix (Fin r) (Fin r) S).det = 1 := by
    show (LinearMap.toMatrix b b f).det = 1
    rw [LinearMap.det_toMatrix, hf]
  have h1 : (ψ.comp Φ) g = 1 := generalLinearGroup_char_eq_one_of_det_eq_one S r A (ψ.comp Φ) h4 g hg
  have h2 : Φ g * k = 1 := by
    ext q
    show e.symm ((Matrix.toLinAlgEquiv b (LinearMap.toMatrix b b f)) (e (k q))) = q
    rw [show LinearMap.toMatrix b b f = LinearMap.toMatrixAlgEquiv b f from rfl,
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv, hk, LinearEquiv.symm_apply_apply]
  have h3 := congrArg ψ h2
  rw [map_mul, map_one] at h3
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, one_mul] at h3
  exact h3

private theorem free_quotient_tensor_of_projective {R : Type} [CommRing R] [IsDomain R] (L' : Type)
    [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R)
    [Finite (R ⧸ I)] : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] L') := by
  refine Module.free_of_flat_of_finrank_eq (R ⧸ I) _ (Module.finrank R L') fun P => ?_
  let := Ideal.Quotient.field P.1
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1)
    ((R ⧸ I) ⧸ P.1) L').finrank_eq]
  have h := Module.rankAtStalk_baseChange (R := R) (M := L') (S := (R ⧸ I) ⧸ P.1)
    ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h
  rw [h]
  exact (Ideal.finrank_fiber_eq_rankAtStalk (M := L') _).symm.trans (Ideal.finrank_fiber_eq_finrank _)

theorem char_eq_one_of_inverse_reduction_det_one : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  intro R _ _ L L' _ _ _ _ _ _ I _ A _ ψ t γ k h4 hsurj hinj hdet hk
  have := free_quotient_tensor_of_projective L' I
  obtain ⟨r, ⟨b⟩⟩ : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (R ⧸ I) ((R ⧸ I) ⊗[R] L')) := by
    rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
    · have := Module.subsingleton (R ⧸ I) ((R ⧸ I) ⊗[R] L')
      exact ⟨0, ⟨Module.Basis.empty _⟩⟩
    · exact ⟨_, ⟨Module.finBasis (R ⧸ I) ((R ⧸ I) ⊗[R] L')⟩⟩
  have hle : (I • ⊤ : Submodule R L) ≤ (I • ⊤ : Submodule R L').comap t := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let tb := (I • ⊤ : Submodule R L).mapQ (I • ⊤ : Submodule R L') t hle
  have tbij : Function.Bijective tb := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj a hx)
    · intro y
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a, ha⟩ := hsurj c
      exact ⟨Submodule.Quotient.mk a, ((Submodule.Quotient.eq _).mpr ha).symm⟩
  let e : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (R ⧸ I) ⊗[R] L' :=
    (LinearEquiv.ofBijective tb tbij).trans (TensorProduct.quotTensorEquivQuotSMul L' I).symm
  have he : ∀ a, e (Submodule.Quotient.mk a) = (1 : R ⧸ I) ⊗ₜ[R] t a := by
    intro a
    simp [e, tb, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have hz : ∀ x ∈ (I • ⊤ : Submodule R L'), (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    intro x hx
    have h0 : (Submodule.Quotient.mk x : L' ⧸ (I • ⊤ : Submodule R L')) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, h0, map_zero]
  refine char_eq_one_of_inverse_det_one_of_basis b e ψ h4 (LinearMap.baseChange (R ⧸ I) γ) hdet k ?_
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a', ha', hγ⟩ := hk a
  rw [← ha', he, he, LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact hz _ hγ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
noncomputable section

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

section
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def adCoord (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n) : (Fin n → RA F E) →+ RA F E where
  toFun w := ∑ i, w i * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

theorem _root_.GlobalTheory.AdLat.adCoord_tmul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (fun i => a ⊗ₜ x i) = a ⊗ₜ e.repr x b := by
  have hx : e.repr x b = ∑ i, x i * e.repr (Pi.single i 1) b := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → E) by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h],
      map_smul, Finsupp.smul_apply, smul_eq_mul]
  change ∑ i, (a ⊗ₜ x i) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx, TensorProduct.tmul_sum]

theorem _root_.GlobalTheory.AdLat.adCoord_smul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (r : _root_.GlobalTheory.AdLat.RA F E) (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (r • w) = r * _root_.GlobalTheory.AdLat.adCoord F e b w := by
  change ∑ i, (r • w) i * _ = r * ∑ i, w i * _
  simp [Finset.mul_sum, mul_assoc]

theorem _root_.GlobalTheory.AdLat.adCoord_sum (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by
  have h1 : ∀ a, _root_.GlobalTheory.AdLat.adCoord F e b (_root_.GlobalTheory.AdLat.fv F (e a)) =
      if a = b then 1 else 0 := by
    intro a
    have := _root_.GlobalTheory.AdLat.adCoord_tmul F e b 1 (e a)
    unfold _root_.GlobalTheory.AdLat.fv
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, _root_.GlobalTheory.AdLat.adCoord_smul, h1, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

theorem _root_.GlobalTheory.AdLat.mem_hat_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) := by
  intro F E _ _ _ _ _ n L e cI hL z
  constructor
  · intro hz b
    rw [← _root_.GlobalTheory.AdLat.adCoord_sum F e z b]
    have key : _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ≤
        (_root_.GlobalTheory.AdLat.hat1 F (cI b : Set E)).comap (_root_.GlobalTheory.AdLat.adCoord F e b) := by
      unfold _root_.GlobalTheory.AdLat.hat
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, x, hx, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      rw [_root_.GlobalTheory.AdLat.adCoord_tmul]
      unfold _root_.GlobalTheory.AdLat.hat1
      exact AddSubgroup.subset_closure ⟨c, hc, _, (hL x).1 hx b, rfl⟩
    exact key hz
  · intro hz
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have key : _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) ≤
        (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))).comap
          ((smulAddHom (_root_.GlobalTheory.AdLat.RA F E)
            (Fin n → _root_.GlobalTheory.AdLat.RA F E)).flip (_root_.GlobalTheory.AdLat.fv F (e a))) := by
      unfold _root_.GlobalTheory.AdLat.hat1
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, y, hy, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      have hmem : y • e a ∈ L := by
        rw [hL]
        intro a'
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using hy
        · simpa using (cI a').zero_mem
      unfold _root_.GlobalTheory.AdLat.hat
      refine AddSubgroup.subset_closure ⟨c, hc, _, hmem, ?_⟩
      funext i
      unfold _root_.GlobalTheory.AdLat.fv
      change (c ⊗ₜ[F] y) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e a i) = c ⊗ₜ[F] (y • e a) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, smul_eq_mul]
    exact key (hz a)

end GlobalTheory.AdLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIffStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → RA F E, (∑ a, z a • fv F (e a)) ∈ (hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ hat1 F (cI a : Set E) := by
  first | exact @GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | exact GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | (intros; apply GlobalTheory.AdLat.mem_hat_pseudoBasis_iff <;> assumption)
end
end
