module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import ReciprocityTheory.Chebotarev.EulerSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def fd {r : ℕ} (i : Fin r) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ :=
  fun m => g (m + Pi.single i 1) - g m

def DL {r : ℕ} (cs : List (Fin r)) (g : (Fin r → ℕ) → ℂ) : (Fin r → ℕ) → ℂ := cs.foldr fd g

def fdR {r : ℕ} (i : Fin r) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ :=
  fun x => G (x + Pi.single i 1) - G x

def DLR {r : ℕ} (cs : List (Fin r)) (G : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ := cs.foldr fdR G

def GoodAt (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) : Prop :=
  (∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) ∧
    ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single i e : Fin r → ℕ)) = 0

def BddW {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop := ∃ C : ℝ, ∀ m, |(v m : ℝ)| ≤ C

def partialSum {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m i), v (Function.update m i k)

def meanP (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  (∑ k ∈ Finset.range l, partialSum i v (Function.update m i k)) / l

def Aop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  partialSum i v (m + Pi.single i 1) - meanP l i v m

def Bop (l : ℕ) {r : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) : ℚ :=
  if m i = 0 then meanP l i v m else 0

def linF {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) : ℝ :=
  b j + ∑ i, a j i * x i

def Fr {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (β : ι → ℕ) (x : Fin r → ℝ) : ℂ :=
  ∏ j, ((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))

def sizeE {r : ℕ} (x : Fin r → ℝ) : ℝ := 1 + ∑ i, x i

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

def conePt {r : ℕ} (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : 𝓞 F := y + ∑ i, (m i : 𝓞 F) * v i


open Classical in
def coneWeight {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ℚ :=
  if conePt y v m ∈ A then (l : ℚ) - 1 else -1

theorem conePt_add_single {r : ℕ} (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) (i : Fin r) (e : ℕ) :
    conePt y v (m + (Pi.single i e : Fin r → ℕ)) = conePt y v m + (e : 𝓞 F) * v i := by
  simp only [conePt, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, add_assoc]
  congr 2
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem relIndex_mul_eq_absNorm (𝔠 𝔟 : Ideal (𝓞 F)) (hb : 𝔟 ≠ ⊥) :
    (𝔠 * 𝔟).toAddSubgroup.relIndex 𝔟.toAddSubgroup = Ideal.absNorm 𝔠 := by
  have hle : (𝔠 * 𝔟).toAddSubgroup ≤ 𝔟.toAddSubgroup := (Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right
  have h := AddSubgroup.relIndex_mul_index hle
  have e : ∀ I : Ideal (𝓞 F), I.toAddSubgroup.index = Ideal.absNorm I := fun I => by
    rw [Ideal.absNorm_apply, Submodule.cardQuot]
  rw [e, e, map_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hb)) h

theorem exists_unique_shift_mem {𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) (hl : (Ideal.absNorm 𝔠).Prime) {x v : 𝓞 F}
    (hx : x ∈ 𝔟) (hv : v ∈ 𝔟) (hv' : v ∉ 𝔠 * 𝔟) :
    ∃ e₀ < Ideal.absNorm 𝔠, ∀ e < Ideal.absNorm 𝔠, (x + (e : 𝓞 F) * v ∈ 𝔠 * 𝔟 ↔ e = e₀) := by
  classical
  haveI : Fact (Ideal.absNorm 𝔠).Prime := ⟨hl⟩
  let B := 𝔟.toAddSubgroup
  let H : AddSubgroup B := (𝔠 * 𝔟).toAddSubgroup.addSubgroupOf B
  have hcard : Nat.card (B ⧸ H) = Ideal.absNorm 𝔠 := relIndex_mul_eq_absNorm 𝔠 𝔟 hb
  haveI : Finite (B ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hl.ne_zero)
  let X : B := ⟨x, hx⟩
  let V : B := ⟨v, hv⟩
  have hz : ∀ z : B, (z : B ⧸ H) = 0 ↔ (z : 𝓞 F) ∈ 𝔠 * 𝔟 := fun z => by
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf
  have hV : (V : B ⧸ H) ≠ 0 := fun h => hv' ((hz V).1 h)
  have hord : addOrderOf (V : B ⧸ H) = Ideal.absNorm 𝔠 :=
    addOrderOf_eq_prime (by rw [← hcard]; exact card_nsmul_eq_zero') hV
  have hmem : -(X : B ⧸ H) ∈ AddSubgroup.zmultiples (V : B ⧸ H) := mem_zmultiples_of_prime_card hcard hV
  rw [← mem_multiples_iff_mem_zmultiples, mem_multiples_iff_mem_range_addOrderOf, hord] at hmem
  obtain ⟨e₀, he₀, h₀⟩ := Finset.mem_image.1 hmem
  have he₀' := Finset.mem_range.1 he₀
  refine ⟨e₀, he₀', fun e he => ?_⟩
  have hc : x + (e : 𝓞 F) * v = ((X + e • V : B) : 𝓞 F) := by simp [X, V, nsmul_eq_mul]
  rw [hc, ← hz]
  have hq : ((X + e • V : B) : B ⧸ H) = (X : B ⧸ H) + e • (V : B ⧸ H) := rfl
  have hX : (X : B ⧸ H) = -(e₀ • (V : B ⧸ H)) := by
    have h₀' : e₀ • (V : B ⧸ H) = -(X : B ⧸ H) := h₀
    rw [h₀', neg_neg]
  rw [hq, hX, neg_add_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  exact nsmul_injOn_Iio_addOrderOf (by simpa [hord] using he) (by simpa [hord] using he₀') h.symm

theorem goodWeight_coneWeight {𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) (hl : (Ideal.absNorm 𝔠).Prime) {r : ℕ} {y : 𝓞 F}
    {v : Fin r → 𝓞 F} (hy : y ∈ 𝔟) (hv : ∀ i, v i ∈ 𝔟) (hv' : ∀ i, v i ∉ 𝔠 * 𝔟) :
    GoodWeight (Ideal.absNorm 𝔠) (coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) y v) := by
  classical
  have hpt : ∀ m, conePt y v m ∈ 𝔟 := fun m =>
    𝔟.add_mem hy (𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hv i))
  refine ⟨fun m i => ?_, fun m i => ?_⟩
  · have h : ((Ideal.absNorm 𝔠 : ℕ) : 𝓞 F) * v i ∈ 𝔠 * 𝔟 := Ideal.mul_mem_mul (Ideal.absNorm_mem 𝔠) (hv i)
    have : conePt y v (m + (Pi.single i (Ideal.absNorm 𝔠) : Fin r → ℕ)) ∈ 𝔠 * 𝔟 ↔ conePt y v m ∈ 𝔠 * 𝔟 := by
      rw [conePt_add_single]
      exact Ideal.add_mem_iff_left _ h
    simp only [coneWeight, this]
  · obtain ⟨e₀, he₀, h⟩ := exists_unique_shift_mem hb hl (hpt m) (hv i) (hv' i)
    have h2 : ∀ e ∈ Finset.range (Ideal.absNorm 𝔠),
        coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) y v (m + (Pi.single i e : Fin r → ℕ)) =
          (if e = e₀ then (Ideal.absNorm 𝔠 : ℚ) else 0) - 1 := fun e he => by
      simp only [coneWeight, conePt_add_single, h e (Finset.mem_range.1 he)]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp [he₀]

theorem le_iff_mem_mul_of_span {I 𝔠 𝔟 : Ideal (𝓞 F)} (hb : 𝔟 ≠ ⊥) {x : 𝓞 F} (h : I * 𝔟 = Ideal.span {x}) :
    I ≤ 𝔠 ↔ x ∈ 𝔠 * 𝔟 := by
  rw [← Ideal.span_singleton_le_iff_mem, ← h, ← Ideal.dvd_iff_le, ← Ideal.dvd_iff_le, mul_dvd_mul_iff_right hb]

theorem ofReal_finset_prod_cpow {ι : Type} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    ∏ i ∈ S, ((f i : ℝ) : ℂ) ^ s = ((∏ i ∈ S, f i : ℝ) : ℂ) ^ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf i) (Finset.prod_nonneg fun j _ => hf j)]

def realEmbeddingsEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : (F →+* ℝ) ≃ (F →+* ℂ) :=
  Equiv.ofBijective (fun σ => Complex.ofRealHom.comp σ)
    ⟨fun σ τ h => RingHom.ext fun x => Complex.ofReal_injective (by simpa using RingHom.congr_fun h x), fun φ => by
      have hφ : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
      exact ⟨hφ.embedding, RingHom.ext fun x => by simpa using hφ.coe_embedding_apply x⟩⟩

theorem prod_real_embeddings_eq_norm [IsTotallyReal F] [Fintype (F →+* ℝ)] (x : F) :
    ∏ σ : F →+* ℝ, σ x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : F →+* ℝ, ((σ x : ℝ) : ℂ) = ∏ τ : F →ₐ[ℚ] ℂ, τ x :=
    Fintype.prod_equiv ((realEmbeddingsEquiv F).trans (RingHom.equivRatAlgHom F ℂ)) _ _ (fun σ => rfl)
  rw [Complex.ofReal_prod, h2, ← h]
  simp

theorem prod_real_embeddings_eq_absNorm [IsTotallyReal F] [Fintype (F →+* ℝ)] (x : 𝓞 F) (hx : TotPos F (x : F)) :
    ∏ σ : F →+* ℝ, σ (x : F) = ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℝ) := by
  have hpos : 0 ≤ ∏ σ : F →+* ℝ, σ (x : F) := Finset.prod_nonneg fun σ _ => (hx σ).le
  have h := prod_real_embeddings_eq_norm (x : F)
  rw [← Algebra.coe_norm_int] at h
  rw [Ideal.absNorm_span_singleton]
  rw [h] at hpos ⊢
  push_cast at hpos ⊢
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hpos]

theorem embedding_conePt {r : ℕ} (σ : F →+* ℝ) (y : 𝓞 F) (v : Fin r → 𝓞 F) (m : Fin r → ℕ) :
    σ (conePt y v m : F) = σ (y : F) + ∑ i, σ (v i : F) * (m i : ℝ) := by
  have : ((conePt y v m : 𝓞 F) : F) = (y : F) + ∑ i, (m i : F) * (v i : F) := by
    change algebraMap (𝓞 F) F (conePt y v m) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp [conePt, map_add (f := _), map_sum, map_mul, map_natCast]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_add (f := _), map_sum]
  simp [mul_comm]

theorem totPos_conePt {r : ℕ} {y : 𝓞 F} {v : Fin r → 𝓞 F} (hy : TotPos F (y : F)) (hv : ∀ i, TotPos F (v i : F))
    (m : Fin r → ℕ) : TotPos F (conePt y v m : F) := fun σ => by
  rw [embedding_conePt]
  exact add_pos_of_pos_of_nonneg (hy σ) (Finset.sum_nonneg fun i _ => mul_nonneg (hv i σ).le (Nat.cast_nonneg _))

theorem coneTerm_eq_absNorm_cpow [IsTotallyReal F] [Fintype (F →+* ℝ)] {r : ℕ} {y : 𝓞 F} {v : Fin r → 𝓞 F}
    (hy : TotPos F (y : F)) (hv : ∀ i, TotPos F (v i : F)) (s : ℂ) (m : Fin r → ℕ) :
    coneTerm (fun (σ : F →+* ℝ) i => σ (v i : F)) (fun σ => σ (y : F)) s m =
      ((Ideal.absNorm (Ideal.span {conePt y v m}) : ℕ) : ℂ) ^ (-s) := by
  have h := prod_real_embeddings_eq_absNorm (conePt y v m) (totPos_conePt hy hv m)
  have h2 := ofReal_finset_prod_cpow Finset.univ (fun σ : F →+* ℝ => σ (conePt y v m : F))
    (fun σ => (totPos_conePt hy hv m σ).le) (-s)
  rw [h, Complex.ofReal_natCast] at h2
  simp only [coneTerm, ← embedding_conePt]
  exact h2

theorem classTwist_entire : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  intro AC F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP hc hl hv'
  obtain ⟨hb, hy, hv, hr, e, he⟩ := hP
  haveI : Fintype (F →+* ℝ) := Fintype.ofEquiv _ (realEmbeddingsEquiv F).symm
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F), Embeddings.card]
  have key := fun j => AC (F →+* ℝ) (r j) (Ideal.absNorm 𝔠) (fun σ i => σ (v j i : F)) (fun σ => σ (y j : F))
    (coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl.pos
    (fun σ i => (hv j i).2 σ) (fun σ => (hy j).2 σ)
    (goodWeight_coneWeight hb hl (hy j).1 (fun i => (hv j i).1) (hv' j))
  choose T hTd hTs hTv using key
  have hN0 : Ideal.absNorm 𝔟 ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using hb
  have hNb : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hterm : ∀ (p : Σ j, (Fin (r j) → ℕ)) (s : ℂ),
      (classWeight (Ideal.absNorm 𝔠) 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * (((coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℚ) : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ (v p.1 i : F)) (fun σ => σ (y p.1 : F)) s p.2) := by
    intro p s
    have h1 : classWeight (Ideal.absNorm 𝔠) 𝔠 (e p).1 = coneWeight (Ideal.absNorm 𝔠) (𝔠 * 𝔟) (y p.1) (v p.1) p.2 := by
      have hI : (e p).1 ≤ 𝔠 ↔ conePt (y p.1) (v p.1) p.2 ∈ 𝔠 * 𝔟 := le_iff_mem_mul_of_span hb (he p)
      simp only [classWeight, coneWeight]
      by_cases h : (e p).1 ≤ 𝔠
      · rw [if_pos h, if_pos (hI.1 h)]
      · rw [if_neg h, if_neg fun h' => h (hI.2 h')]
    have h2 := he p
    have h3 : Ideal.absNorm (Ideal.span {conePt (y p.1) (v p.1) p.2}) = Ideal.absNorm (e p).1 * Ideal.absNorm 𝔟 := by
      rw [← map_mul, h2, conePt]
    have hne : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hNb]
    rw [coneTerm_eq_absNorm_cpow (hy p.1).2 (fun i => (hv p.1 i).2), h1, h3, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, Complex.cpow_neg ((Ideal.absNorm 𝔟 : ℕ) : ℂ) s]
    field_simp
  refine ⟨fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, T j s, ?_, ?_, ?_⟩
  · exact (differentiable_id.const_cpow (Or.inl hNb)).mul (Differentiable.fun_sum fun j _ => hTd j)
  · intro s hs
    rw [← e.hasSum_iff]
    beta_reduce
    rw [Finset.mul_sum]
    have h1 : ∀ j, HasSum (fun m => ((fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) ∘ e) ⟨j, m⟩)
        (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * T j s) := fun j => by
      have e1 := funext fun m => hterm ⟨j, m⟩ s
      simp only [Function.comp]
      rw [e1]
      exact (hTs j s hs).mul_left _
    refine HasSum.sigma_of_hasSum (hasSum_fintype _) h1 (Summable.of_norm ?_)
    exact (summable_sigma_of_nonneg fun _ => norm_nonneg _).2 ⟨fun j => (h1 j).summable.norm, Summable.of_finite⟩
  · intro k hk
    obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
    have hs : (1 - ((p + 1 : ℕ) : ℂ)) = -(p : ℂ) := by push_cast; ring
    have hq : ∀ j, ∃ q : ℚ, T j (-(p : ℂ)) = (q : ℂ) := fun j => hTv j p fun m => by
      refine ⟨((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℚ) ^ p, ?_⟩
      have h := prod_real_embeddings_eq_absNorm (conePt (y j) (v j) m)
        (totPos_conePt (hy j).2 (fun i => (hv j i).2) m)
      simp only [← embedding_conePt]
      rw [Finset.prod_pow, h]
      push_cast
      rfl
    choose q hq using hq
    refine ⟨((Ideal.absNorm 𝔟 : ℚ) ^ p)⁻¹ * ∑ j, q j, ?_⟩
    simp only [hs, hq]
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifferenceStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_twisted_entire_difference : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def coneOn (s : Finset V) : Set V :=
  {x | ∃ t : V → ℚ, (∀ i ∈ s, 0 < t i) ∧ x = ∑ i ∈ s, t i • i}

def SignConst (l : V →ₗ[ℚ] ℚ) (C : Set V) : Prop :=
  (∀ x ∈ C, l x = 0) ∨ (∀ x ∈ C, 0 < l x) ∨ (∀ x ∈ C, l x < 0)

inductive Tile (P : Set V) (Q : Set V → Prop) : Set V → Prop
  | empty : Tile P Q ∅
  | cone (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V)) (hP : (s : Set V) ⊆ P) (hQ : Q (coneOn s)) :
      Tile P Q (coneOn s)
  | union {A B : Set V} (hA : Tile P Q A) (hB : Tile P Q B) (hAB : Disjoint A B) : Tile P Q (A ∪ B)

def posCone (F : Type) [Field F] [NumberField F] : ConvexCone ℚ F where
  carrier := {x | TotPos F x}
  smul_mem' := by
    intro c hc x hx σ
    have h : σ (c • x) = (c : ℝ) * σ x := by
      rw [Rat.smul_def, map_mul, map_ratCast]
    rw [h]
    exact mul_pos (by exact_mod_cast hc) (hx σ)
  add_mem' := by
    intro x hx y hy σ
    rw [map_add (f := _)]
    exact add_pos (hx σ) (hy σ)

def congSubgroup {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := congUnits 𝔣
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a * b : (𝓞 F)ˣ) : 𝓞 F) - 1 = (a : 𝓞 F) * ((b : 𝓞 F) - 1) + ((a : 𝓞 F) - 1) := by
        rw [Units.val_mul]; ring
      rw [h]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hb.1) ha.1
    · have h : (((a * b : (𝓞 F)ˣ) : 𝓞 F) : F) = ((a : 𝓞 F) : F) * ((b : 𝓞 F) : F) := by
        rw [Units.val_mul]; simp
      rw [h, map_mul]
      exact mul_pos (ha.2 σ) (hb.2 σ)
  one_mem' := by
    refine ⟨by simp, fun σ => ?_⟩
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -(((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((a : 𝓞 F) - 1)) := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        linear_combination this
      rw [h]
      exact 𝔣.neg_mem (𝔣.mul_mem_left _ ha.1)
    · have h1 : (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((a : 𝓞 F) : F) = 1 := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) this
      have h2 := congrArg σ h1
      rw [map_mul, map_one] at h2
      have h3 := ha.2 σ
      by_contra hn
      have : σ (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * σ ((a : 𝓞 F) : F) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h3.le
      linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummable
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummable
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    (fun I : Ideal (𝓞 F) => CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞)
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaRayClassSummableStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_ray_class_summable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable <;> assumption)
end
end
