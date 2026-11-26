module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem summable_absNorm_rpow_neg (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 1 < r) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-r)) := by
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (r : ℂ)) (by simpa using hr))
  refine h.congr fun I => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem sum_torsion_le (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) {r : ℝ} (hr : 1 < r)
    (S : Finset ((Fin m → K) ⧸ L)) :
    ∑ x ∈ S, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
      ≤ zetaR K r := by
  classical
  set τ : (Fin m → K) ⧸ L → Ideal (𝓞 K) := fun x => Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x
    with hτ
  have hg := summable_absNorm_rpow_neg K hr
  have hfib : ∀ 𝔞 ∈ S.image τ,
      ∑ x ∈ S.filter (fun x => τ x = 𝔞), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := by
    intro 𝔞 h𝔞
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp h𝔞
    have hne : τ x₀ ≠ ⊥ := GlobalTheory.T.lattice_quotient_torsion_nonzero K m L hL x₀
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow K m L hL (τ x₀) hne
    have hN : (0 : ℝ) < (Ideal.absNorm (τ x₀) : ℝ) := by
      have : Ideal.absNorm (τ x₀) ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hc : ((S.filter (fun x => τ x = τ x₀)).card : ℝ) ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m := by
      have hinj : (S.filter (fun x => τ x = τ x₀)).card ≤
          Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} := by
        haveI := Fintype.ofFinite {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0}
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun x => ⟨x.1, fun a ha => ?_⟩) (fun x y h => ?_)
        · have hx := (Finset.mem_filter.mp x.2).2
          rw [← hx] at ha
          exact (Ideal.mem_torsionOf_iff _ _).mp ha
        · have h' : (x : (Fin m → K) ⧸ L) = y :=
            congrArg (fun z : {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} => z.1) h
          exact Subtype.ext h'
      exact_mod_cast hinj.trans hcard
    have hsum : ∑ x ∈ S.filter (fun x => τ x = τ x₀), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        = ((S.filter (fun x => τ x = τ x₀)).card : ℝ) *
          (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) := by
      rw [Finset.sum_congr rfl (g := fun _ => (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)))
        (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp
    rw [hsum]
    calc _ ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m * (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
      _ = (Ideal.absNorm (τ x₀) : ℝ) ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hN]
          congr 1
          ring
  calc ∑ x ∈ S, (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
      = ∑ 𝔞 ∈ S.image τ, ∑ x ∈ S.filter (fun x => τ x = 𝔞),
          (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r)) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem τ hx) _).symm
    _ ≤ ∑ 𝔞 ∈ S.image τ, (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := Finset.sum_le_sum hfib
    _ ≤ zetaR K r :=
        hg.sum_le_tsum _ (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_torsion (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) (r : ℝ) (hr : 1 < r) :
    Summable (fun x : (Fin m → K) ⧸ L =>
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧
    ∑' x : (Fin m → K) ⧸ L,
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ zetaR K r := by
  have hnn : ∀ x : (Fin m → K) ⧸ L,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_of_sum_le hnn (sum_torsion_le K m L hL hr)
  exact ⟨hs, hs.tsum_le_of_sum_le (sum_torsion_le K m L hL hr)⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_norm_zeta_bound : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ r : ℝ, 1 < r → Summable (fun x : (Fin m → K) ⧸ L => (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' x : (Fin m → K) ⧸ L, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) ≤ zetaR K r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp

def IsI {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x

section I

variable {K : Type} [Field K] [NumberField K]

theorem IsI.add {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x + y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o + p, by simp⟩

theorem IsI.neg {x : K} (hx : IsI x) : IsI (-x) := by
  obtain ⟨o, rfl⟩ := hx
  exact ⟨-o, by simp⟩

theorem IsI.mul {x y : K} (hx : IsI x) (hy : IsI y) : IsI (x * y) := by
  obtain ⟨o, rfl⟩ := hx
  obtain ⟨p, rfl⟩ := hy
  exact ⟨o * p, by simp⟩

theorem isI_zero : IsI (0 : K) := ⟨0, by simp⟩

theorem isI_sum {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, IsI (f i)) :
    IsI (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isI_zero : IsI (0 : K))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Kc_le_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc c ≤ Kc (c + h) := by
  intro y hy i
  have h1 : IsI ((c *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := hy i
  have h2 : IsI ((h *ᵥ fun j => algebraMap (𝓞 K) K (y j)) i) := by
    show IsI (∑ j, h i j * algebraMap (𝓞 K) K (y j))
    exact isI_sum (K := K) Finset.univ _ fun j _ => (hh i j).mul ⟨y j, rfl⟩
  have h3 := h1.add h2
  rw [Matrix.add_mulVec]
  exact h3

theorem Kc_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    Kc (c + h) = Kc c := by
  refine le_antisymm ?_ (Kc_le_add c h hh)
  have := Kc_le_add (c + h) (-h) fun a b => by simpa using IsI.neg (hh a b)
  simpa using this

theorem delta_add {n : ℕ} (c h : Matrix (Fin n) (Fin n) K) (hh : ∀ a b, IsI (h a b)) :
    delta (c + h) = delta c := by
  unfold delta
  rw [Kc_add c h hh]

theorem vec_out {m : ℕ} (t : Fin m → K) (i : Fin m) :
    IsI ((Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) : Fin m → K) i - t i) := by
  have h : Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m))
      = (Submodule.Quotient.mk t : (Fin m → K) ⧸ intVec K m) := Quotient.out_eq _
  have h2 := (Submodule.Quotient.eq _).1 h
  exact h2 i

end I

section H

variable {F E : Type} [Field F] [Field E] [Algebra F E] [NumberField E]

theorem herm_out (σ : E →ₐ[F] E) {n : ℕ} (t : hermE σ n) (a b : Fin n) :
    IsI ((Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b) := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) :
      hermE σ n ⧸ hermO σ n) = QuotientAddGroup.mk t := Quotient.out_eq _
  have h2 : IsI ((-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b) :=
    (QuotientAddGroup.eq.1 h) a b
  have h3 := h2.neg
  have e : -(-(Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)) + t).1 a b =
      (Quotient.out (QuotientAddGroup.mk t : hermE σ n ⧸ hermO σ n)).1 a b - t.1 a b := by
    simp
    ring
  rwa [e] at h3

def topB (σ : E →ₐ[F] E) {m : ℕ} (C : hermE σ (m + 1)) : hermE σ m :=
  ⟨fun a b => C.1 a.castSucc b.castSucc, fun a b => C.2 a.castSucc b.castSucc⟩

def lastCol {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) : Fin m → E :=
  fun a => C a.castSucc (Fin.last m)

theorem blk_cc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a b : Fin m) : blk σ c u d a.castSucc b.castSucc = c a b := by simp [blk]

theorem blk_cl (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (a : Fin m) : blk σ c u d a.castSucc (Fin.last m) = u a := by simp [blk]

theorem blk_lc (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (b : Fin m) : blk σ c u d (Fin.last m) b.castSucc = σ (u b) := by simp [blk]

theorem blk_ll (σ : E →ₐ[F] E) {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    blk σ c u d (Fin.last m) (Fin.last m) = d := by simp [blk]

theorem blk_sub_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (C : hermE σ (m + 1)) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E)
    (hc : ∀ a b : Fin m, IsI (c a b - C.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (u a - C.1 a.castSucc (Fin.last m)))
    (hd : IsI (d - C.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) :
    IsI (blk σ c u d i j - C.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact hd
    | cast b =>
      rw [blk_lc, ← C.2 (Fin.last m) b.castSucc, ← map_sub]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl]; exact hu a
    | cast b => rw [blk_cc]; exact hc a b

theorem herm_isI (σ : E →ₐ[F] E) (hσ : ∀ x : E, IsI x → IsI (σ x)) {m : ℕ}
    (D : hermE σ (m + 1))
    (hc : ∀ a b : Fin m, IsI (D.1 a.castSucc b.castSucc))
    (hu : ∀ a : Fin m, IsI (D.1 a.castSucc (Fin.last m)))
    (hd : IsI (D.1 (Fin.last m) (Fin.last m))) (i j : Fin (m + 1)) : IsI (D.1 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact hd
    | cast b =>
      rw [← D.2 (Fin.last m) b.castSucc]
      exact hσ _ (hu b)
  | cast a =>
    induction j using Fin.lastCases with
    | last => exact hu a
    | cast b => exact hc a b

end H

theorem isI_algebraMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {y : F} (hy : IsI y) : IsI (algebraMap F E y) := by
  obtain ⟨o, rfl⟩ := hy
  have h : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F o)) :=
    (RingOfIntegers.isIntegral_coe o).algebraMap
  exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ h⟩

theorem hermClass_blocks : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  intro F E _ _ _ _ _ σ hcm m
  obtain ⟨-, hfix, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  have hσ : ∀ x : E, IsI x → IsI (σ x) := by
    rintro x ⟨o, rfl⟩
    exact ⟨sO σ o, hsO o⟩
  have hcorner : ∀ C : hermE σ (m + 1), ∃ y : F,
      algebraMap F E y = C.1 (Fin.last m) (Fin.last m) := fun C => hfix _ (C.2 _ _)
  choose dd hdd using hcorner
  refine ⟨fun x => (QuotientAddGroup.mk (topB σ (Quotient.out x)),
    Submodule.Quotient.mk (lastCol (Quotient.out x).1),
    Submodule.Quotient.mk (fun _ => dd (Quotient.out x))), ?_, ?_⟩
  · intro x x' hxx
    obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := by simpa [Prod.ext_iff] using hxx
    have h1' := QuotientAddGroup.eq.1 h1
    have h2' := (Submodule.Quotient.eq _).1 h2
    have h3' := (Submodule.Quotient.eq _).1 h3
    rw [← Quotient.out_eq x, ← Quotient.out_eq x']
    refine QuotientAddGroup.eq.2 ?_
    refine fun i j => herm_isI σ hσ (-(Quotient.out x) + Quotient.out x') ?_ ?_ ?_ i j
    · intro a b
      exact h1' a b
    · intro a
      have : IsI (lastCol (Quotient.out x).1 a - lastCol (Quotient.out x').1 a) := h2' a
      have e := this.neg
      simpa [lastCol, add_comm, sub_eq_add_neg] using e
    · have : IsI (dd (Quotient.out x) - dd (Quotient.out x')) := h3' 0
      have e := (isI_algebraMap (E := E) this).neg
      simpa [hdd, add_comm, sub_eq_add_neg] using e
  · intro x
    dsimp only
    set C := Quotient.out x with hC
    set M := blk σ (Quotient.out (QuotientAddGroup.mk (topB σ C) : hermE σ m ⧸ hermO σ m)).1
      (Quotient.out (Submodule.Quotient.mk (lastCol C.1) : (Fin m → E) ⧸ intVec E m))
      (algebraMap F E ((Quotient.out (Submodule.Quotient.mk (fun _ => dd C) : FQ F) : Fin 1 → F) 0))
      with hM
    have hI : ∀ i j, IsI ((M - C.1) i j) := by
      intro i j
      refine blk_sub_isI σ hσ C _ _ _ ?_ ?_ ?_ i j
      · intro a b
        exact herm_out σ (topB σ C) a b
      · intro a
        exact vec_out (lastCol C.1) a
      · have h := isI_algebraMap (E := E) (vec_out (fun _ : Fin 1 => dd C) 0)
        rw [map_sub, hdd] at h
        exact h
    have := delta_add C.1 (M - C.1) hI
    rw [add_sub_cancel] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjectionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_quotient_injection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ m : ℕ, ∃ ι : (hermE σ (m + 1) ⧸ hermO σ (m + 1)) → (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F, Function.Injective ι ∧ ∀ x, delta (Quotient.out x).1 = delta (blk σ (Quotient.out (ι x).1).1 (Quotient.out (ι x).2.1) (algebraMap F E ((Quotient.out (ι x).2.2 : Fin 1 → F) 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU

variable {E : Type} [Field E] [NumberField E] {m : ℕ}

theorem fibre_bound (c : Matrix (Fin m) (Fin m) E) (b : (Fin m → E) ⧸ lam c) :
    Finite {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ∧
      Nat.card {U : (Fin m → E) ⧸ intVec E m //
        (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} ≤ delta c := by
  obtain ⟨hne, hidx⟩ := GlobalTheory.T.delta_eq_lattice_index E m c
  set H := (intVec E m).toAddSubgroup with hH
  set Kg := (lam c).toAddSubgroup with hK
  have hidx' : delta c = (H.addSubgroupOf Kg).index := hidx
  have hcard : Nat.card (Kg ⧸ H.addSubgroupOf Kg) = delta c := by
    rw [hidx']; rfl
  haveI : Finite (Kg ⧸ H.addSubgroupOf Kg) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hne)
  have hw : (Submodule.Quotient.mk (Quotient.out b) : (Fin m → E) ⧸ lam c) = b :=
    Quotient.out_eq' b
  have hmem : ∀ a : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b},
      Quotient.out a.1 - Quotient.out b ∈ Kg := by
    intro a
    have : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ lam c) =
        Submodule.Quotient.mk (Quotient.out b) := a.2.trans hw.symm
    exact (Submodule.Quotient.eq _).1 this
  let φ : {U : (Fin m → E) ⧸ intVec E m //
      (Submodule.Quotient.mk (Quotient.out U) : (Fin m → E) ⧸ lam c) = b} →
      Kg ⧸ H.addSubgroupOf Kg := fun a => QuotientAddGroup.mk ⟨_, hmem a⟩
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := QuotientAddGroup.eq.1 h
    have h2 : -(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b) ∈ H :=
      AddSubgroup.mem_addSubgroupOf.1 h1
    have h3 : Quotient.out a.1 - Quotient.out a'.1 ∈ intVec E m := by
      have h4 := neg_mem h2
      have h5 : -(-(Quotient.out a.1 - Quotient.out b) + (Quotient.out a'.1 - Quotient.out b)) =
          Quotient.out a.1 - Quotient.out a'.1 := by abel
      rw [h5] at h4
      exact h4
    apply Subtype.ext
    have h6 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) =
        Submodule.Quotient.mk (Quotient.out a'.1) := (Submodule.Quotient.eq _).2 h3
    have e1 : (Submodule.Quotient.mk (Quotient.out a.1) : (Fin m → E) ⧸ intVec E m) = a.1 :=
      Quotient.out_eq' _
    have e2 : (Submodule.Quotient.mk (Quotient.out a'.1) : (Fin m → E) ⧸ intVec E m) = a'.1 :=
      Quotient.out_eq' _
    rw [← e1, ← e2, h6]
  refine ⟨Finite.of_injective φ hφ, ?_⟩
  rw [← hcard]
  exact Nat.card_le_card_of_injective φ hφ

theorem sum_tor : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  intro E _ _ m c r hr
  obtain ⟨hs, hle⟩ := GlobalTheory.T.torsion_norm_zeta_bound E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) r hr
  have hg : ∀ x : (Fin m → E) ⧸ lam c,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
        (-((m : ℝ) + r)) := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le ((Fin m → E) ⧸ intVec E m) ((Fin m → E) ⧸ lam c)
    (fun U => Submodule.Quotient.mk (Quotient.out U)) (delta c) (fibre_bound c)
    (fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 E) ((Fin m → E) ⧸ lam c) x) : ℝ) ^
      (-((m : ℝ) + r))) hg hs
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDeltaStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sum_zeta_bound_delta : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) (a : Fin m) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) a.castSucc = (c *ᵥ y) a + u a * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

theorem blk_mulVec_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) (Fin.last m) =
      ∑ j, σ (u j) * y j + d * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

variable [NumberField E]

theorem mem_lastFib_blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y l : Fin m → 𝓞 E) (s : 𝓞 E)
    (h : ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) a + u a * algebraMap (𝓞 E) E s =
      algebraMap (𝓞 E) E (l a)) :
    (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + d * algebraMap (𝓞 E) E s) ∈
      lastFib (blk σ c u d) := by
  have hvI : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (y j))
      (algebraMap (𝓞 E) E s) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨s, by simp⟩
    · exact ⟨y a, by simp⟩
  have h1 := Submodule.mem_sup_right (S := intVec E (m + 1))
    (Submodule.mem_map_of_mem (f := (blk σ c u d).mulVecLin.restrictScalars (𝓞 E)) hvI)
  have h2 : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (l j)) 0 :
      Fin (m + 1) → E) ∈ lam (blk σ c u d) := by
    refine Submodule.mem_sup_left ?_
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨0, by simp⟩
    · exact ⟨l a, by simp⟩
  have h3 := (lam (blk σ c u d)).sub_mem h1 h2
  show LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m) _ ∈ lam (blk σ c u d)
  convert h3 using 1
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [blk_mulVec_last]
  · have hne : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
    simp [blk_mulVec_castSucc, h a, hne]

theorem one_le_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (1 : Submodule (𝓞 E) E) ≤ lastFib C := by
  intro x hx
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_sup_left (show _ ∈ intVec E (m + 1) from ?_)
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    exact ⟨o, by simp⟩
  · exact ⟨0, by simp [hi]⟩

theorem lastFib_fg {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).FG := by
  have hfg : (lam C).FG := (GlobalTheory.T.lam_is_lattice E (m + 1) C).1
  have hmap : ((lastFib C).map
      (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))).FG :=
    Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))
    (fun a b h => by simpa using congrFun h (Fin.last m)) hmap

theorem tor_decomp {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (t : 𝓞 E)
    (ht : t ∈ tor c u) :
    ∃ yo lo : Fin m → 𝓞 E, ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) a +
      u a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (lo a) := by
  have h : t • u ∈ lam c := by
    have h0 := (Ideal.mem_torsionOf_iff _ _).1 ht
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨l, hl, z, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.1 h
  choose lo hlo using hl
  choose yo hyo using hy
  refine ⟨-yo, lo, fun a => ?_⟩
  have h1 := congrFun hz a
  have hy' : (fun j => algebraMap (𝓞 E) E ((-yo) j)) = -y := by
    funext j
    simp [hyo j]
  rw [hy', Matrix.mulVec_neg, hlo a]
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply,
    Algebra.smul_def] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1
end

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  intro F E _ _ _ _ _ σ hCM m c hc u t ht ht0
  obtain ⟨hinv, hfix, hsO, hN⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hCM
  obtain ⟨yo, lo, hyl⟩ := LocalBound.tor_decomp c u t ht
  have hf0 : σ (-∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j)) =
      -∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
    have hs : ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j * σ (algebraMap (𝓞 E) E (yo j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hc]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_mul, hinv]
    rw [hs]
  obtain ⟨f, hf⟩ := hfix _ hf0
  refine ⟨f, fun d => ?_⟩
  have hT : tor c u ≠ ⊥ := fun h => ht0 (by simpa [h] using ht)
  have hsOt : sO σ t ≠ 0 := by
    intro h0
    apply ht0
    have h1 : σ (algebraMap (𝓞 E) E t) = 0 := by
      have := hsO t
      rw [h0] at this
      simpa using this.symm
    have h2 : algebraMap (𝓞 E) E t = 0 := by
      rw [← hinv (algebraMap (𝓞 E) E t), h1, map_zero]
    exact (map_eq_zero_iff _ (RingOfIntegers.coe_injective)).1 h2
  have hmem : ∀ t' ∈ tor c u, sO σ t' ∈ (tor c u).map (sO σ) :=
    fun t' h' => Ideal.mem_map_of_mem _ h'
  have h𝔱 : (tor c u).map (sO σ) ≠ ⊥ := by
    intro h0
    have := hmem t ht
    rw [h0] at this
    exact hsOt (by simpa using this)
  have hw := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) yo lo t hyl
  have hinvb : ∀ b : E, (∀ a ∈ (tor c u).map (sO σ), (a : E) * b ∈ (1 : Submodule (𝓞 E) E)) →
      b ∈ lastFib (blk σ c u (algebraMap F E d)) := by
    intro b hb
    obtain ⟨y, hy, hby⟩ := GlobalTheory.T.torsion_orthogonality_integral_solution F E σ hCM m c hc u b (fun t' h' => by
      have := hb _ (hmem t' h')
      rwa [show ((sO σ t' : 𝓞 E) : E) = σ (t' : E) from hsO t'] at this)
    choose lo' hlo' using hy
    have h1 := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) y lo' 0 (fun a => by
      rw [hlo' a]
      simp)
    have h2 := LocalBound.one_le_lastFib (blk σ c u (algebraMap F E d)) hby
    have h3 := Submodule.add_mem _ h1 h2
    have h4 : (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + algebraMap F E d * algebraMap (𝓞 E) E 0) +
        (b - ∑ j, σ (u j) * (y j : E)) = b := by
      simp only [map_zero, mul_zero, add_zero]
      exact add_sub_cancel _ _
    rwa [h4] at h3
  have hnorm := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hCM t).1
  have hkey : ((sO σ t : 𝓞 E) : E) * (∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) +
      algebraMap F E d * algebraMap (𝓞 E) E t) -
      algebraMap F E (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d) ∈ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_one.2 ⟨∑ j, sO σ (lo j) * yo j, ?_⟩
    have hsum : σ (algebraMap (𝓞 E) E t) * ∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) -
          ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hyl j, map_add (f := _), map_mul]
      ring
    have hs2 : algebraMap (𝓞 E) E (∑ j, sO σ (lo j) * yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (hsO (lo j))
    rw [hs2, show ((sO σ t : 𝓞 E) : E) = σ (algebraMap (𝓞 E) E t) from hsO t, map_add (f := _), map_mul,
      hf, hnorm]
    have hnorm' : (t : E) = algebraMap (𝓞 E) E t := rfl
    rw [hnorm']
    linear_combination -hsum
  have hmain := GlobalTheory.T.denominator_index_bound E ((tor c u).map (sO σ)) h𝔱
    (lastFib (blk σ c u (algebraMap F E d))) (LocalBound.lastFib_fg _)
    (LocalBound.one_le_lastFib _) hinvb (sO σ t) _ _ (hmem t ht) hw hkey
  rw [hN, GlobalTheory.T.denominator_norm_quadratic_extension F E hCM.2.2.1] at hmain
  rw [GlobalTheory.T.delta_block_matrix_multiplicative F E σ m c u (algebraMap F E d)]
  calc delta c * Ideal.absNorm (tor c u) ^ 2 *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2
      = delta c * Ideal.absNorm (tor c u) * (Ideal.absNorm (tor c u) *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmain
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_lower_bound_torsion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBound
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockSeriesZetaBoundStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_series_zeta_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLt
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.delta_block_series_zeta_bound F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := GlobalTheory.T.delta_block_quotient_injection F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := GlobalTheory.T.torsion_sum_zeta_bound_delta E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (GlobalTheory.T.delta_eq_lattice_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact Summable.of_finite
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLtStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow <;> assumption)
end
