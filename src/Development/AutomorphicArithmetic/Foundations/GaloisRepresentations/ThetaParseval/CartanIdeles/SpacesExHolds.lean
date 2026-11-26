module

public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.BaseEx
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem baseEx : BaseEx := by
  intro F E _ _ _ _ _ σ hc emb mα mβ
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F
  obtain ⟨a, -, ha⟩ := GlobalTheory.StdRescale.exists_isStd_mulShift F hc.1 ψ₀ hψ₀
  obtain ⟨v₁, -, ⟨τ₁⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hc ∅
  refine ⟨⟨ψ₀.mulShift (algebraMap F (AF F) a), emb, mα, mβ, ∅,
    fun v => absurd v.2 (Finset.notMem_empty _), v₁, τ₁⟩, rfl, rfl, rfl, rfl, ha, fun hu hg => ?_⟩
  exact
    { cm := hc
      galois := hg.1
      unram := hu
      std := ha
      inert := fun v w h => by
        obtain ⟨h2, h3, hd⟩ := hg.2 v w h
        exact ⟨h2, h3, PositivityTheory.Mix.psiUnr_of_not_le ha v hd⟩
      psiP := fun v hv => absurd hv (Finset.notMem_empty _) }

end UpperTheory.Gal.TP.Skew

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.IdeleStep
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.ideleStep :
    UpperTheory.Gal.TP.Skew.ConjAut → UpperTheory.Gal.TP.Skew.IdeleStep := by
  intro hconj F E _ _ _ _ _ σ hcm a
  obtain ⟨hgal, s, -, -, hss, hall, -⟩ := hconj F E σ hcm
  haveI := hgal
  haveI hcomm : IsMulCommutative Gal(E/F) := ⟨⟨fun g h => by
    rcases hall g with rfl | rfl <;> rcases hall h with rfl | rfl <;> simp⟩⟩
  obtain ⟨hFr, hEc, -, -⟩ := hcm
  let v : InfinitePlace F := Classical.arbitrary _
  have hram : infiniteLocalSymbol E v ≠ 1 := by
    rw [Ne, infiniteLocalSymbol_eq_one_iff]
    intro hun
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
    have hw' : w.comap (algebraMap F E) = v := hw
    refine InfinitePlace.not_isUnramified_iff.mpr ⟨hEc.isComplex w, ?_⟩ (hun w hw')
    rw [hw']
    exact hFr.isReal v
  obtain ⟨c, hc⟩ : ∃ c, infiniteLocalSymbol E v c ≠ 1 := by
    by_contra h
    push_neg at h
    exact hram (MonoidHom.ext h)
  have hc' : infiniteLocalSymbol E v c = s := (hall _).resolve_left hc
  have key : ∀ a' : IdeleGroup F, ideleSymbol F E a' = 1 →
      ∃ x b, ∀ w, ord w a' = ord w (diagonal F x) + ord w (ideleNorm F E b) := by
    intro a' ha'
    have hmem : a' ∈ (ideleSymbol F E).ker := ha'
    rw [ker_ideleSymbol, Subgroup.mem_sup] at hmem
    obtain ⟨y, ⟨x, rfl⟩, z, ⟨b, rfl⟩, rfl⟩ := hmem
    exact ⟨x, b, fun w => ord_mul w _ _⟩
  by_cases ha : ideleSymbol F E a = 1
  · exact key a ha
  · obtain ⟨x, b, hxb⟩ := key (a * infiniteEmbedding v c) (by
      rw [map_mul, (hall _).resolve_left ha, ideleSymbol_infiniteEmbedding, hc', hss])
    refine ⟨x, b, fun w => ?_⟩
    rw [← hxb w, ord_mul,
      mem_standardOpenSubgroup_iff_ord.mp (infiniteEmbedding_mem_standardOpenSubgroup v c) w,
      add_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.StdHerm
noncomputable section

open scoped nonZeroDivisors Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

private lemma mem_one_iff {E : Type} [Field E] [NumberField E] (y : E) :
    y ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ y := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro h
    exact ⟨⟨y, h⟩, rfl⟩

private lemma form_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (y x : Fin n → E) : form σ (1 : Matrix (Fin n) (Fin n) E) y x = ∑ i, y i * σ (x i) := by
  simp [form, dotProduct]

theorem stdHerm : StdHerm := by
  intro F E _ _ _ _ _ σ hc B hP n
  have hint : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (σ x) := fun x h =>
    h.map (σ.toRingHom.toIntAlgHom)
  have hL : ∀ y : Fin n → E, y ∈ (stdSpc F E n).L ↔ ∀ i, IsIntegral ℤ (y i) := by
    intro y
    have : (stdSpc F E n).L = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := rfl
    rw [this, Submodule.mem_pi]
    exact forall_congr' fun i => by simp only [Set.mem_univ, true_imp_iff, mem_one_iff]
  have hs : ∀ i, (Pi.single i (1 : E) : Fin n → E) ∈ (stdSpc F E n).L := fun i =>
    (hL _).2 fun j => by
      by_cases e : j = i
      · subst e
        simpa using isIntegral_one
      · simpa [Pi.single_eq_of_ne e] using isIntegral_zero
  have hJ : ∀ w, (stdSpc F E n).J.map (B.emb w).1 = 1 := by
    intro w
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [stdSpc, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  · intro w
    rw [hJ]
    refine ⟨rfl, Matrix.fromCols 1 0, ?_⟩
    ext (i | i) (j | j)
    · simp only [Matrix.mul_one]
      simp [Matrix.mul_apply, Matrix.one_apply]
      by_cases e : i = j
      · simp [e]
      · have e' : ¬ j = i := fun h => e h.symm
        simp [e, e']
    all_goals first | exact i.elim0 | exact j.elim0
  · haveI : (stdSpc F E n).L.IsLattice E := by
      refine ⟨Submodule.fg_pi fun _ => ?_, ?_⟩
      · rw [Submodule.one_eq_span]
        exact Submodule.fg_span_singleton 1
      · intro s _ h
        exact (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h
    refine ⟨?_⟩
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hs i)
  · intro y
    rw [hL]
    constructor
    · intro hy x hx
      rw [hL] at hx
      simp only [stdSpc, form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (hint _ (hx i))
    · intro h i
      have := h _ (hs i)
      simpa [stdSpc, form_one, Pi.single_apply] using this
  · intro w
    rw [hJ]
    refine ⟨by simp [stdSpc], by simp [stdSpc], fun x hx => ?_⟩
    simp only [stdSpc, Matrix.one_mulVec]
    exact (Complex.pos_iff.1 (Matrix.dotProduct_self_star_pos_iff.2 hx)).1
  · intro v
    exact absurd v.2 (by simp [hP])

end UpperTheory.Gal.TP.Skew

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.PosEx
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem posEx : PosEx := by
  intro F E _ _ _ _ _ σ hc δ hδ hs
  have key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x) := hc.2.2.2
    set z : ℂ := τ.1 δ with hz
    have hstar : star z = -z := by
      rw [hz, ← hconj, hs, map_neg]
    have hre : z.re = 0 := by
      have := congrArg Complex.re hstar
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      rw [hz]
      exact (map_ne_zero τ.1).2 hδ
    have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hre h)
    have hI : Complex.I * z = ((-z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨τ, -z.im, by linarith, hI⟩
    · refine ⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩
      · refine Eq.trans ?_ τ.2
        ext x
        simp
      · have : (τ.1.comp (σ : E →+* E)) δ = -z := by
          simp [hs, hz]
        rw [this, mul_neg, hI]
        simp
  choose emb hemb using key
  exact ⟨emb, hemb⟩

end UpperTheory.Gal.TP.Skew

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemOrd
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

private theorem le_one_of_count {E : Type} [Field E] [NumberField E] (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), 0 ≤ FractionalIdeal.count E w J) : J ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' E hJ]
  refine finprod_induction (p := fun X : FractionalIdeal (𝓞 E)⁰ E => X ≤ 1) le_rfl ?_ ?_
  · intro a b ha hb
    calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ ≤ 1 * 1 := mul_le_mul_right hb 1
      _ = 1 := one_mul 1
  · intro v
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one

private theorem mem_iff {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (y : E) (hy : y ≠ 0) : y ∈ I ↔ ∀ w, FractionalIdeal.count E w I ≤ ordE w y := by
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy
  constructor
  · intro h w
    exact FractionalIdeal.count_mono E w hs ((FractionalIdeal.spanSingleton_le_iff_mem).mpr h)
  · intro h
    have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hI)
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹ ≤ 1 := by
      refine le_one_of_count _ hJ fun w => ?_
      rw [FractionalIdeal.count_mul E w hs (inv_ne_zero hI), FractionalIdeal.count_inv]
      have := h w
      unfold ordE at this
      omega
    have h2 : FractionalIdeal.spanSingleton (𝓞 E)⁰ y ≤ I := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ y
          = (FractionalIdeal.spanSingleton (𝓞 E)⁰ y * I⁻¹) * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ 1 * I := mul_le_mul_left hle I
        _ = I := one_mul I
    exact (FractionalIdeal.spanSingleton_le_iff_mem).mp h2

private theorem attained {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) : ∃ x ∈ I, x ≠ 0 ∧ ordE w x = FractionalIdeal.count E w I := by
  by_contra hcon
  push_neg at hcon
  have hP : ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact w.ne_bot
  have hPI := mul_ne_zero hP hI
  have hle : I ≤ ((w.asIdeal : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (mem_iff _ hPI x hx0).mpr fun v => ?_
    rw [FractionalIdeal.count_mul E v hP hI]
    have h1 := (mem_iff I hI x hx0).mp hx v
    by_cases hv : v = w
    · subst hv
      rw [FractionalIdeal.count_self]
      have := hcon x hx hx0
      omega
    · rw [FractionalIdeal.count_maximal_coprime E v (Ne.symm hv)]
      omega
  have h3 := FractionalIdeal.count_mono E w hI hle
  rw [FractionalIdeal.count_mul E w hP hI, FractionalIdeal.count_self] at h3
  omega

private theorem lattice {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    (I : Submodule (𝓞 E) E).IsLattice E := by
  exact Submodule.IsLattice.of_fg E (FractionalIdeal.fg_of_isUnit I (IsUnit.mk0 I hI))

theorem UpperTheory.Gal.TP.Skew.memOrd :
    UpperTheory.Gal.TP.Skew.MemOrd := by
  intro E _ _ I hI
  exact ⟨mem_iff I hI, attained I hI, lattice I hI⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.LineSkew
noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem lineSkew : LineSkew := by
  intro F E _ _ _ _ _ σ δ 𝔞 hl B hpos hP d
  refine ⟨?skew, ?sig, ?lat, ?dual, ?cartan, ?bas⟩
  case skew =>
    intro i j
    simp only [skewSpc, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp [hl.skew]
    · simp [h, Ne.symm h]
  case bas =>
    intro v
    exact absurd v.2 (by simp [hP])
  case lat =>
    have hfg := Submodule.fg_pi (ι := Fin d) (p := fun _ => 𝔞) (fun _ => hl.lat.fg)
    haveI : Submodule.IsLattice E (skewSpc F δ 𝔞 d).L := Submodule.IsLattice.of_fg E hfg
    have ha : ∃ a : E, a ∈ 𝔞 ∧ a ≠ 0 := by
      by_contra h
      have hz : ∀ x ∈ 𝔞, x = 0 := by
        intro x hx
        by_contra hx0
        exact h ⟨x, hx, hx0⟩
      have h1 : (1 : E) ∈ 𝔞 := (hl.dual 1).2 (by
        intro x hx o
        simpa [hz x hx] using (isIntegral_zero : IsIntegral ℤ (0 : ℚ)))
      exact h ⟨1, h1, one_ne_zero⟩
    obtain ⟨a, ha, ha0⟩ := ha
    refine ⟨?_⟩
    apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    have hs : Pi.single i a ∈ (skewSpc F δ 𝔞 d).L := by
      change Pi.single i a ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞)
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
      intro j
      by_cases h : j = i
      · subst j; simpa using ha
      · simp [h]
    have hm := (Submodule.span E ((skewSpc F δ 𝔞 d).L : Set (Fin d → E))).smul_mem (x i / a) (Submodule.subset_span hs)
    simpa [← Pi.single_smul, smul_eq_mul, div_mul_cancel₀ _ ha0] using hm
  case dual =>
    intro y
    have hform : ∀ x : Fin d → E, form σ (skewSpc F δ 𝔞 d).J y x = ∑ i, y i * (δ * σ (x i)) := by
      intro x
      simp [form, skewSpc, Matrix.smul_mulVec, dotProduct, smul_eq_mul]
    have hmem : ∀ z : Fin d → E, z ∈ (skewSpc F δ 𝔞 d).L ↔ ∀ i, z i ∈ 𝔞 := by
      intro z
      show z ∈ Submodule.pi Set.univ (fun _ : Fin d => 𝔞) ↔ _
      simp [Submodule.mem_pi]
    rw [hmem]
    constructor
    · intro hy x hx o
      rw [hmem] at hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hform, Finset.mul_sum, map_sum]
      exact IsIntegral.sum _ (fun i _ => (hl.dual (y i)).1 (hy i) (x i) (hx i) o)
    · intro h i
      rw [hl.dual]
      intro x hx o
      have hs : Pi.single i x ∈ (skewSpc F δ 𝔞 d).L := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hx
        · simp [hj]
      have := h _ hs o
      rw [hform, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at this
      simpa using this
  case cartan =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    have hθ : (skewSpc F δ 𝔞 d).θ w = 1 := rfl
    rw [hM, hθ]
    refine ⟨by simp, by simp, fun x hx => ?_⟩
    have key : (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x ⬝ᵥ ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ star x = ((c * ∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
      simp [Matrix.smul_mulVec, dotProduct, Finset.mul_sum, Complex.mul_conj]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Complex.mul_conj]
      ring
    rw [key, Complex.ofReal_re]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact mul_pos hc (Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩)
  case sig =>
    intro w
    obtain ⟨c, hc, he⟩ := hpos w
    have hM : Complex.I • (skewSpc F δ 𝔞 d).J.map ⇑(B.emb w : E →+* ℂ) = (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [skewSpc, he]
      · simp [skewSpc, h]
    rw [hM]
    refine ⟨by simp, Matrix.of fun (k : Fin d) (p : Fin d ⊕ Fin 0) => Sum.elim (fun i => if k = i then (((Real.sqrt c)⁻¹ : ℝ) : ℂ) else 0) (fun z => z.elim0) p, ?_⟩
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    ext (i | i) (j | j)
    · simp [Matrix.mul_apply, Matrix.one_apply, Function.swap_def, Sum.elim]
      split_ifs with h
      · rw [map_inv₀, Complex.conj_ofReal, ← mul_inv]
        have hs : ((√c : ℝ) : ℂ) * (√c : ℂ) = c := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
        rw [hs, mul_inv_cancel₀ (by exact_mod_cast hc.ne')]
      · simp
    all_goals (first | exact i.elim0 | exact j.elim0)

end UpperTheory.Gal.TP.Skew

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdAut
open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

namespace UpperTheory.Gal.TP.Skew

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end

end UpperTheory.Gal.TP.Skew

private theorem count_le_count_galois_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  classical
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  rw [FractionalIdeal.count_coe E P hJ, FractionalIdeal.count_coe E (g • P) hgJ, Nat.cast_le,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hgJ)
      (g • P).associates_irreducible]
  have h1 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
    P.associates_irreducible).mpr le_rfl
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  refine ⟨g • c, ?_⟩
  change g • J = (g • P.asIdeal) ^ _ * g • c
  conv_lhs => rw [hc]
  rw [smul_mul', smul_pow']

private theorem count_galois_smul_eq_count {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) := by
  refine le_antisymm ?_ (count_le_count_galois_smul g P J hJ)
  have h := count_le_count_galois_smul g⁻¹ (g • P) (g • J) (fun h => hJ ((smul_eq_zero_iff_eq g).mp h))
  rwa [inv_smul_smul, inv_smul_smul] at h

private theorem count_smul_eq_of_mem_iff_inv_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (w : HeightOneSpectrum (𝓞 E))
    (I I' : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) (h : ∀ x : E, x ∈ I' ↔ (g⁻¹ : Gal(E/F)) x ∈ I) :
    FractionalIdeal.count E (g • w) I' = FractionalIdeal.count E w I := by
  obtain ⟨b, J, hb, hbJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := FractionalIdeal.ideal_factor_ne_zero hI hbJ
  have hb' : Ideal.span {b} ≠ 0 := FractionalIdeal.constant_factor_ne_zero hI hbJ
  have hspan : g • Ideal.span {b} = Ideal.span {g • b} := by
    rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hI' : I' = FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E (g • b))⁻¹ *
      ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    ext x
    rw [h, hbJ, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_singleton_mul]
    simp only [FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      have hgj : g • j ∈ g • J := by
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
        exact hj
      refine ⟨_, ⟨g • j, hgj, rfl⟩, ?_⟩
      have hx' : x = g ((g⁻¹ : Gal(E/F)) x) := by simp
      rw [hx', hx, map_mul, map_inv₀]
      rfl
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      refine ⟨_, ⟨g⁻¹ • j, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hj, rfl⟩, ?_⟩
      rw [hx, map_mul, map_inv₀]
      exact congrArg₂ (· * ·) (congrArg Inv.inv (hinv (algebraMap (𝓞 E) E b))) rfl
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  have hgb : g • Ideal.span {b} ≠ 0 := fun h => hb' ((smul_eq_zero_iff_eq g).mp h)
  rw [hI', hbJ, ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, ← hspan,
    FractionalIdeal.count_mul E (g • w) (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hgb))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hgJ),
    FractionalIdeal.count_mul E w (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb'))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_galois_smul_eq_count g w _ hb', count_galois_smul_eq_count g w J hJ]

private theorem galois_apply_mem_dual_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (h : Gal(E/F)) (y : E)
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    h y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hinv : ∀ y : E, (h⁻¹ : Gal(E/F)) (h y) = y := fun y => by simp
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
  rw [FractionalIdeal.mem_dual h1] at hy ⊢
  intro a ha
  obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  have hz := hy (algebraMap (𝓞 E) E (h⁻¹ • z)) ((FractionalIdeal.mem_one_iff _).mpr ⟨_, rfl⟩)
  rw [Algebra.traceForm_apply] at hz ⊢
  have e : Algebra.trace ℚ E (h y * algebraMap (𝓞 E) E z) =
      Algebra.trace ℚ E (y * algebraMap (𝓞 E) E (h⁻¹ • z)) := by
    rw [← Algebra.trace_eq_of_algEquiv ((h⁻¹ : Gal(E/F)).restrictScalars ℚ)
      (h y * algebraMap (𝓞 E) E z)]
    change Algebra.trace ℚ E ((h⁻¹ : Gal(E/F)) (h y * algebraMap (𝓞 E) E z)) = _
    rw [map_mul, hinv]
    rfl
  rw [e]
  exact hz

theorem UpperTheory.Gal.TP.Skew.ordAut :
    UpperTheory.Gal.TP.Skew.OrdAut := by
  intro F E _ _ _ _ _ g w
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hinv2 : ∀ y : E, g ((g⁻¹ : Gal(E/F)) y) = y := fun y => by simp
  refine ⟨fun x => ?_, ?_⟩
  · change FractionalIdeal.count E (g • w) (FractionalIdeal.spanSingleton (𝓞 E)⁰ (g x)) =
      FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)
    by_cases hx : x = 0
    · subst hx
      simp [FractionalIdeal.count_zero]
    · apply count_smul_eq_of_mem_iff_inv_mem g w
      · exact FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hx
      · intro y
        simp only [FractionalIdeal.mem_spanSingleton, Algebra.smul_def]
        constructor
        · rintro ⟨z, rfl⟩
          refine ⟨g⁻¹ • z, ?_⟩
          rw [map_mul, hinv]
          rfl
        · rintro ⟨z, hz⟩
          refine ⟨g • z, ?_⟩
          rw [← hinv2 y, ← hz, map_mul]
          rfl
  · apply count_smul_eq_of_mem_iff_inv_mem g w
    · refine FractionalIdeal.dual_ne_zero ℤ ℚ ?_
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    · intro y
      constructor
      · exact galois_apply_mem_dual_one g⁻¹ y
      · intro hy
        have := galois_apply_mem_dual_one g _ hy
        rwa [hinv2] at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.InvFun
open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.invFun :
    UpperTheory.Gal.TP.Skew.InvFun := by
  intro F E _ _ _ _ _ _ m hfin hinv
  have : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
    intro v
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext ?_⟩
    rw [HeightOneSpectrum.under_asIdeal]
    exact hl.over.symm
  choose W hW using hex
  have key : ∀ w : HeightOneSpectrum (𝓞 E), m (W (w.under (𝓞 F))) = m w := by
    intro w
    have h1 : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
    have h2 : (W (w.under (𝓞 F))).asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by conv_lhs => rw [← hW (w.under (𝓞 F)), HeightOneSpectrum.under_asIdeal]; rfl⟩
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal
      (W (w.under (𝓞 F))).asIdeal Gal(E/F)
    have h3 : W (w.under (𝓞 F)) = g • w := HeightOneSpectrum.ext hg.symm
    rw [h3, hinv]
  have hn : ∀ᶠ v in Filter.cofinite, m (W v) = 0 := by
    rw [Filter.eventually_cofinite] at hfin ⊢
    refine (hfin.image fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)).subset fun v hv => ?_
    exact ⟨W v, hv, hW v⟩
  obtain ⟨a, ha⟩ := toFractionalIdeal_surjective (K := F) (∏ᶠ v, primeIdealUnit v ^ m (W v))
  refine ⟨a, fun w => ?_⟩
  rw [toFractionalIdeal_eq_iff.1 ha, count_finprod_primeIdealUnit_zpow _ hn, key]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdEmb
open scoped nonZeroDivisors Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

theorem UpperTheory.Gal.TP.Skew.ordEmb :
    UpperTheory.Gal.TP.Skew.OrdEmb := by
  intro F E _ _ _ _ _ hu a w
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  have hc : ((ideleEmbedding F E a : IdeleGroup E) : 𝔸[E]).2 w =
      completionMap (below F w) w ((a : 𝔸[F]).2 (below F w)) := by
    rw [coe_ideleEmbedding]
    exact GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply _ w
  unfold ord
  rw [hc, valued_completionMap, he, pow_one]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.MemDual
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.memDual :
    UpperTheory.Gal.TP.Skew.MemDual := by
  intro E _ _ z
  have h0 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h0]
  constructor
  · intro h o
    have h1 := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : Algebra.trace ℚ E ((o : E) * z) = algebraMap ℤ ℚ n := hn.symm
    rw [h2]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    exact ⟨n, hn⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.ConjAut
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.conjAut :
    UpperTheory.Gal.TP.Skew.ConjAut := by
  classical
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨_, hE, h2, hconj⟩ := hσ
  haveI hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hgal : IsGalois F E := inferInstance
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hconj, hconj, star_star])
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hsq x⟩
  let s : Gal(E/F) := AlgEquiv.ofBijective σ ⟨σ.toRingHom.injective, hsurj⟩
  have hs : ∀ x, s x = σ x := fun x => rfl
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    show star τ = τ
    ext x
    have := hconj τ x
    rw [h x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  have hs1 : s ≠ 1 := fun h => hx (by rw [← hs, h]; rfl)
  have hcard : Fintype.card Gal(E/F) = 2 := by
    rw [← h2, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  refine ⟨hgal, s, hs, hs1, ?_, ?_, σ x - x, ?_, ?_⟩
  · ext y
    simp [hs, hsq]
  · intro g
    by_contra hg
    push_neg at hg
    have hle : ({1, s, g} : Finset Gal(E/F)).card ≤ Fintype.card Gal(E/F) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hs1.symm, hg.1.symm]),
      Finset.card_pair hg.2.symm, hcard] at hle
    omega
  · exact sub_ne_zero.mpr hx
  · rw [map_sub, hsq]
    abel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.OrdLine
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

private theorem ordE_neg {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    ordE w (-x) = ordE w x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold ordE
    rw [GroundTheory.Global.count_spanSingleton w hx, GroundTheory.Global.count_spanSingleton w (neg_ne_zero.2 hx),
      Valuation.map_neg]

private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) : ordE w (x * y) = ordE w x + ordE w y := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy)]

theorem UpperTheory.Gal.TP.Skew.ordLine :
    UpperTheory.Gal.TP.Skew.ConjAut → UpperTheory.Gal.TP.Skew.IdeleStep → UpperTheory.Gal.TP.Skew.OrdEmb → UpperTheory.Gal.TP.Skew.InvFun → UpperTheory.Gal.TP.Skew.OrdAut → UpperTheory.Gal.TP.Skew.OrdLine := by
  intro hCA hIS hOE hIF hOA F E _ _ _ _ _ σ hc hu
  classical
  obtain ⟨hG, s, hsσ, hs1, hss, hall, δ₀, hδ0, hδσ⟩ := hCA F E σ hc
  haveI := hG
  let m : HeightOneSpectrum (𝓞 E) → ℤ := fun w =>
    FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) - ordE w δ₀
  have hcof : ∀ᶠ w in Filter.cofinite, m w = 0 :=
    ((FractionalIdeal.finite_factors (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))).and
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 E)⁰ δ₀))).mono
      fun w h => by
        change _ - FractionalIdeal.count E w _ = 0
        rw [h.1, h.2, sub_zero]
  have hinv : ∀ (g : E ≃ₐ[F] E) w, m (g • w) = m w := by
    intro g w
    rcases hall g with hg | hg
    · rw [hg, one_smul]
    · rw [hg]
      have h1 := (hOA F E s w).1 δ₀
      have h2 := (hOA F E s w).2
      rw [hsσ, hδσ, ordE_neg] at h1
      change _ - _ = _ - _
      rw [h1, h2]
  obtain ⟨a, ha⟩ := hIF F E m hcof hinv
  obtain ⟨x, b, hxb⟩ := hIS F E σ hc a
  have hx0 : algebraMap F E (x : F) ≠ 0 :=
    (map_ne_zero (algebraMap F E)).2 x.ne_zero
  refine ⟨s, algebraMap F E (x : F) * δ₀,
    ((toFractionalIdeal b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E),
    hsσ, hss, mul_ne_zero hx0 hδ0, ?_, Units.ne_zero _, ?_⟩
  · rw [map_mul, AlgHom.commutes, hδσ, mul_neg]
  · intro w
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
      ext g
      simpa using hall g
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h1 : m w = ord (w.under (𝓞 F)) (diagonal F x) + ord (w.under (𝓞 F)) (ideleNorm F E b) :=
      (ha w).symm.trans (hxb _)
    rw [← hOE F E hu _ w, ← hOE F E hu _ w, ideleEmbedding_diagonal, ideleEmbedding_ideleNorm,
      huniv, Finset.prod_pair hs1.symm, ord_mul, one_smul, ord_smul, hsi, ord_diagonal,
      ← GroundTheory.Global.count_spanSingleton w (by simpa using x.ne_zero)] at h1
    have h3 : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰
        ((Units.map (algebraMap F E).toMonoidHom x : Eˣ) : E)) = ordE w (algebraMap F E (x : F)) := rfl
    rw [h3] at h1
    rw [ordE_mul w hx0 hδ0, count_toFractionalIdeal, count_toFractionalIdeal]
    change _ - _ = _ at h1
    linarith
end

namespace UpperTheory.Gal.TP.Skew

theorem lineEx_holds : LineEx := lineEx ordAut (ordLine conjAut (ideleStep conjAut) ordEmb invFun ordAut) memOrd memDual

theorem spacesEx_holds : SpacesEx := spacesEx_of lineEx_holds posEx stdHerm lineSkew

theorem baseEx_holds : BaseEx := baseEx

theorem skewLine_holds : SkewLine := skewLine_of spacesEx_holds baseEx_holds

end UpperTheory.Gal.TP.Skew
