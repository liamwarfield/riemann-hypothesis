module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.SumDual

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ G *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

omit [NumberField E] [StarRing E] in
theorem antiDiagonalEpsilonGram_mulVec {c : ℕ} (ε : E) (u : Fin c → E) (p : Fin c) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) p = (if p = p.rev then ε else 1) * u p.rev := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p.rev]
  · have := p.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
    rw [if_pos (by omega)]
  · intro q _ hq
    have := p.2
    simp only [antiDiagonalSignGramMatrix]
    rw [if_neg, zero_mul]
    intro h
    exact hq (Fin.ext (by rw [Fin.val_rev]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_herm (S : HSpace E) : S.gramᴴ = S.gram := by
  ext i j
  exact S.herm.eq _ _

theorem hT_eq (S : HSpace E) (x y : S.V) :
    S.hT x y = star (S.frame.equivFun x) ⬝ᵥ S.gram *ᵥ S.frame.equivFun y := by
  rw [← sum_eq_dot]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]
  ring

theorem gram_inj (S : HSpace E) (y : Fin S.rank → E) (h : S.gram *ᵥ y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := S.frame.equivFun.surjective y
  rw [S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]

theorem gram_isom (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (h : HSpace.IsIsomEmb A B ι) :
    (LinearMap.toMatrix A.frame B.frame ι)ᴴ * B.gram * LinearMap.toMatrix A.frame B.frame ι = A.gram := by
  ext i j
  rw [HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply,
    Module.Basis.equivFun_apply]

theorem selfDual_sum {n k c : ℕ} (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (G : Matrix (Fin n) (Fin n) E) (J : Matrix (Fin k) (Fin k) E) (M : Matrix (Fin n) (Fin k) E)
    (a : Matrix (Fin n) (Fin c) E) (ε : E) (hε : ε = 1 ∨ ε = -1) (hG : Gᴴ = G) (hJ : ∀ y, J *ᵥ y = 0 → y = 0)
    (h1 : Mᴴ * G * M = J) (h2 : Mᴴ * G * a = 0) (h3 : aᴴ * G * a = antiDiagonalSignGramMatrix c ε) (hr : k + c = n)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (𝔟 : Fin c → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : Submodule.IsLattice E Λ)
    (hΛd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * J i j * y j)
    (hb : ∀ p, 𝔟 p ≠ 0) (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹)
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, ∃ u : Fin c → E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u) :
    Submodule.IsLattice E L ∧
      ∀ y, y ∈ L ↔ ∀ x ∈ L, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  classical
  have h2' : aᴴ * G * M = 0 := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]
  have ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]
  have key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j =
      (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := by
    intro x v y u
    rw [sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, eM, ea]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [antiDiagonalEpsilonGram_mulVec, Pi.star_apply]; ring
  have hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1 := fun p => by
    split_ifs
    · rcases hε with rfl | rfl
      · exact ⟨1, rfl, by simp⟩
      · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  have hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩
  let f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E) := M.mulVecLin.coprod a.mulVecLin
  have hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u := fun _ _ => rfl
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    rintro ⟨y, u⟩ h
    rw [hf] at h
    have e1 := eM y u
    have e2 := ea y u
    rw [h, mulVec_zero, mulVec_zero] at e1 e2
    refine Prod.ext (hJ y e1.symm) (funext fun p => ?_)
    have e3 := congrFun e2 p.rev
    obtain ⟨e, he, hee⟩ := hsg p.rev
    rw [antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev] at e3
    have he0 : (e : E) ≠ 0 := by
      intro h0
      have : e = 0 := by exact_mod_cast h0
      rw [this] at hee; simp at hee
    exact (mul_eq_zero.1 e3.symm).resolve_left he0
  have fsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj
  refine ⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩
  · have : L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E)) := by
      ext x
      rw [hL, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, u, hu, rfl⟩
        exact ⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩
      · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
        exact ⟨y, hy, u, fun p => hu p trivial, rfl⟩
    rw [this]
    exact (hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro hy' x' hx'
    obtain ⟨y, hy, u, hu, rfl⟩ := (hL _).1 hy'
    obtain ⟨x, hx, v, hv, rfl⟩ := (hL _).1 hx'
    obtain ⟨b, hb1⟩ := (hΛd y).1 hy x hx
    have : ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := fun p => by
      obtain ⟨e, he, -⟩ := hsg p
      have := (FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)
      obtain ⟨t, ht⟩ := hst _ ((FractionalIdeal.mem_one_iff _).1 this)
      refine ⟨e * t, ?_⟩
      rw [← he, RingOfIntegers.coe_eq_algebraMap, map_mul]
      congr 1
      refine ht.trans ?_
      rw [star_mul, star_star]
    choose t ht using this
    refine ⟨b + ∑ p, t p, ?_⟩
    rw [key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]
    simp
  · obtain ⟨⟨y, u⟩, rfl⟩ := fsur y'
    rw [hf] at h ⊢
    refine (hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩
    · have := h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)
      rw [key] at this
      simpa using this
    · obtain ⟨p, rfl⟩ := Fin.rev_surjective q
      refine (hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)
      have := h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by
        by_cases hq : q = p
        · subst hq; simpa using hs
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem, rfl⟩)
      rw [key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
        (fun h => absurd (Finset.mem_univ _) h)] at this
      obtain ⟨b, hb1⟩ := this
      obtain ⟨e, he, hee⟩ := hsg p
      rw [← he] at hb1
      have hee' : (e : E) * e = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee
      obtain ⟨t, ht⟩ := hst (star s * u p.rev) ⟨e * b, by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul]
        change (e : E) * (b : E) = _
        rw [hb1]
        simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]
        rw [← mul_assoc, hee', one_mul]⟩
      refine (FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩
      rw [star_mul, star_star]

end General

theorem isSelfDualC_lat : ∀ (D : D7) (A B : HSp D) (c : ℕ) (ε : D.host.E) (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), (ε = 1 ∨ ε = -1) → IsSelfDualC A Λ → (∀ p, 𝔟 p ≠ 0) → (∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) → IsSelfDualC B (d.lat Λ 𝔟) := by
  intro D A B c ε d Λ 𝔟 hε hΛ hb hd
  exact selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A)
    (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl

end GlobalTheory.ChiGrid.SumDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blk_mul_dgM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  intro E _ _ _ a b n h w m k X
  constructor
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc]
  · apply Units.ext
    rw [Units.val_mul, blk_val, blk_val, dgM_val, dgMat, reindex_apply, reindex_apply, reindex_apply,
      submatrix_mul_equiv, fromBlocks_multiply]
    have hk : (k.2⁻¹).val * k.2.val = 1 := Units.inv_mul k.2
    simp [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_assoc, hk]

end GlobalTheory.BCT.CtLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonalStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  first | exact @GlobalTheory.BCT.CtLevel.blk_mul_dgM | exact GlobalTheory.BCT.CtLevel.blk_mul_dgM | (intros; apply GlobalTheory.BCT.CtLevel.blk_mul_dgM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem exists_ringEquiv_mem_iff_star {E : Type} [Field E] [NumberField E] [StarRing E] :
    ∃ σ : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E,
      ∀ (a : FractionalIdeal (𝓞 E)⁰ E) (x : E), x ∈ σ a ↔ star x ∈ a := by
  let τ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)
  have hτ : ∀ x : E, IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) τ x = star x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, star_div₀]
    rfl
  refine ⟨FractionalIdeal.ringEquivOfRingEquiv E E τ, fun a x => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg star (hτ y)).trans (star_star y)
    exact h.symm ▸ hy
  · exact ⟨star x, h, (hτ (star x)).trans (star_star x)⟩

theorem stairId_ne_zero_and_mem_rev_iff : ∀ (D : D7) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ (c : ℕ) (p : Fin c), stairId 𝔞 𝔞' c p ≠ 0 ∧ ∀ x, x ∈ stairId 𝔞 𝔞' c p.rev ↔ star x ∈ (stairId 𝔞 𝔞' c p)⁻¹ := by
  intro D 𝔞 𝔞' h0 h c p
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_mem_iff_star (E := D.host.E)
  have h1 : σ 𝔞 = 𝔞' := by
    ext x
    rw [hσ, h]
  have h2 : σ 𝔞' = 𝔞 := by
    ext x
    rw [hσ, h, star_star]
  have h0' : 𝔞' ≠ 0 := h1 ▸ (map_ne_zero_iff _ σ.injective).2 h0
  refine ⟨mul_ne_zero (pow_ne_zero _ h0) (inv_ne_zero (pow_ne_zero _ h0')), fun x => ?_⟩
  have h3 : σ (stairId 𝔞' 𝔞 c p.rev) = stairId 𝔞 𝔞' c p.rev := by
    unfold stairId
    rw [map_mul, map_inv₀, map_pow, map_pow, h1, h2]
  rw [← stairId_rev, ← hσ, h3]

end GlobalTheory.ChiGrid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatOpen

open IsDedekindDomain.HeightOneSpectrum

def intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, Valued.v (X i j) ≤ 1}
  add_mem' {X Y} hX hY i j := (Valued.v.map_add (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))
  zero_mem' i j := by simp
  neg_mem' {X} hX i j := by simpa using hX i j

theorem coe_intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    (intLat E w a b : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) =
      Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin b =>
        (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  ext X
  constructor
  · intro h i _ j _
    exact h i j
  · intro h i j
    exact h i trivial j trivial

theorem intMat_open_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  intro E _ _ w a b
  refine ⟨intLat E w a b, ?_, ?_, ?_⟩
  · rw [coe_intLat]
    exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ =>
      Valued.isOpen_valuationSubring _
  · rw [coe_intLat]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
      PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w
  · have hS : {X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) |
        ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1} =
        ((AddSubgroup.toSubgroup (intLat E w a b) : Subgroup _) : Set _) := by
      ext X; rfl
    unfold intMat
    rw [hS, Subgroup.closure_eq]

end GlobalTheory.IntMatOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroupStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  first | exact @GlobalTheory.IntMatOpen.intMat_open_compact | exact GlobalTheory.IntMatOpen.intMat_open_compact | (intros; apply GlobalTheory.IntMatOpen.intMat_open_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelEquivCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.FieldBC GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem isBC_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    IsBC hle (rulBC hle f) (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f) := by
  intro S _ _ _ h y
  rw [((GlobalTheory.T.ruleBaseChange_section_values_semilinear E H Dw l Xo c c' hle).1 a n f hf).2 S h y]
  simp

end Field

section Action

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : actLev c lev g f ∈ sec Xo c a n :=
  actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

end Action

section Weights

variable {D : D7}

end Weights

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} {i : Fin D.R.m}

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

section Second

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Y : RowDat T G i) (R : RealDat D A Ks)

end Second

variable [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0}


variable {O : OMDat T.toCore R i Tp tup} {Y : RowDat T G i}


end Compare

end GlobalTheory.LevelEquivCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Wsp (lam : InfinitePlace E → DomWeight n) : Type :=
  PiTensorProduct ℂ fun v : InfinitePlace E => nablaSq ℂ n (lam v)

def wAt (lam : InfinitePlace E → DomWeight n) (γ : UE E n) : Wsp lam →ₗ[ℂ] Wsp lam :=
  PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding γ.1)

def vecM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) where
  carrier := {F | (∀ (γ : UE E n) x, F (finPt γ * x) = (wAt lam γ⁻¹).dualMap (F x)) ∧
    ∀ k ∈ globLev S K', ∀ x, F (x * k) = F x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 γ x, hb.1 γ x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 γ x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def hopM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) :
    (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) :=
  levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam))) (globLev S (KL n)) (globLev S K') (globFn S f)
    LinearMap.id

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem trace_piMap {ι : Type} [Fintype ι] {M : ι → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ j, (bc c).repr (f c (bc c j)) j := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (bc c), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Fintype.prod_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem finrank_wsp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (lam : InfinitePlace E → DomWeight n) :
    (Module.finrank ℂ (Wsp lam) : ℂ) = dimW lam := by
  rw [← LinearMap.trace_id, ← PiTensorProduct.map_id, trace_piMap]
  unfold dimW
  simp

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularOfIsFundamentalDomainFinite
open scoped NNReal ENNReal
open MeasureTheory

theorem GlobalTheory.unimodular_of_isFundamentalDomain_finite : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by
  intro S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin
  haveI : SMulInvariantMeasure Γ S μS :=
    ⟨fun c s _ => by
      show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s
      exact measure_preimage_mul μS (c : S) s⟩
  have hpos : μS 𝓢 ≠ 0 := hF.measure_ne_zero (NeZero.ne μS)
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μS g

  have hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS := by
    refine hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact quasiMeasurePreserving_mul_right μS g
    · intro γ x
      show (γ : S) * x * g = (γ : S) * (x * g)
      exact mul_assoc _ _ _
  have heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢 := hF'.measure_eq hF
  have h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢 := by
    rw [show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]
    exact heq
  rw [hmap] at h2
  rw [Measure.smul_apply] at h2
  have hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    have h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢 := by
      rw [one_mul]; simpa [ENNReal.smul_def] using h2
    exact (ENNReal.mul_left_inj hpos hfin).mp h3
  rw [show (fun x : S => x * g) = fun x => x * g from rfl] at hmap
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
open MeasureTheory

namespace GlobalTheory.DefU.Petersson

theorem topology_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi

theorem exists_isOpen_isCompact_finU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩

theorem exists_compact_cover (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  classical
  obtain ⟨K, hKo, hKc⟩ := exists_isOpen_isCompact_finU E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU (E := E) (n := n)))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.DefU.Petersson

namespace GlobalTheory.DefU.Petersson


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
theorem exists_invariant_pos_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧
      (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  intro E _ _ _ n
  classical
  obtain ⟨h1, h2, h3, h4⟩ := topology_facts E n
  obtain ⟨C, hC, hcov⟩ := exists_compact_cover E n
  letI : MeasurableSpace (UA E n) := borel _
  haveI : BorelSpace (UA E n) := ⟨rfl⟩
  haveI : SecondCountableTopology (ratU E n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : TopologicalSpace.SeparableSpace (ratU E n) := inferInstance
  haveI : Countable (ratU E n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (UA E n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨𝓕, -, h𝓕'⟩ := Formalism.IndefR.Eqv.G5.fdom_exists_all (ratU E n)
  have h𝓕 := h𝓕' μ
  have hfin : μ 𝓕 < ⊤ := by
    refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro g hg
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hg⟩
  haveI hR : μ.IsMulRightInvariant :=
    GlobalTheory.unimodular_of_isFundamentalDomain_finite _ (ratU E n) μ 𝓕 hμ h𝓕 hfin.ne
  have hl : ∀ u : autU E n, ∀ γ ∈ ratU E n, ∀ g, u.1 (γ * g) = u.1 g := fun u γ hγ g => u.2.left γ hγ g
  have hI : ∀ u v : autU E n, IntegrableOn (fun g => star (u.1 g) * v.1 g) 𝓕 μ := by
    intro u v
    have hc : Continuous (fun g => star (u.1 g) * v.1 g) := u.2.cont.star.mul v.2.cont
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    simp only [hl u γ hγ, hl v γ hγ]
    exact hM c hc
  have hright : ∀ (y : UA E n) (f : UA E n → ℂ), (∀ γ ∈ ratU E n, ∀ h, f (γ * h) = f h) →
      ∫ h in 𝓕, f (h * y) ∂μ = ∫ h in 𝓕, f h ∂μ := by
    intro y f hf
    have h' : IsFundamentalDomain (ratU E n) ((fun h => h * y) '' 𝓕) μ := by
      refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
      · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
      · intro γ h
        simp [Subgroup.smul_def, mul_assoc]
    rw [h𝓕.setIntegral_eq h' (f := f) (fun γ h => hf γ γ.2 h)]
    exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
      (measurableEmbedding_mulRight y) f 𝓕).symm
  let F : autU E n → autU E n → ℂ := fun u v => ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ
  let B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x' y)]
      congr 1
      funext g
      change star (x.1 g + x'.1 g) * y.1 g = _
      simp only [star_add]
      ring)
    (fun c x y => by
      simp only [F, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext g
      change star (c * x.1 g) * y.1 g = _
      simp only [star_mul, starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x y')]
      congr 1
      funext g
      change star (x.1 g) * (y.1 g + y'.1 g) = _
      ring)
    (fun c x y => by
      simp only [F, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1
      funext g
      change star (x.1 g) * (c * y.1 g) = _
      ring)
  have hB : ∀ u v, B u v = ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ := fun _ _ => rfl
  have hre : ∀ v, B v v = ((∫ g in 𝓕, ‖v.1 g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro v
    rw [hB, ← integral_complex_ofReal]
    congr 1
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  refine ⟨B, fun u v => ?_, fun v => ?_, fun v h0 => ?_, fun k u v => ?_⟩
  · rw [hB, hB, Complex.star_def, ← integral_conj]
    congr 1
    funext g
    simp only [map_mul, map_star, starRingEnd_apply, star_star]
    ring
  · rw [hre, Complex.ofReal_re]
    exact integral_nonneg fun g => by positivity
  · rw [hre, Complex.ofReal_eq_zero] at h0
    have hi : IntegrableOn (fun g => ‖v.1 g‖ ^ 2) 𝓕 μ := by
      have := (hI v v).norm
      have e2 : (fun g => ‖star (v.1 g) * v.1 g‖) = fun g => ‖v.1 g‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 h0
    have := GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant (ratU E n) μ 𝓕 h𝓕 v.1 v.2.cont (hl v) (by
      filter_upwards [hae] with g hg
      simpa using hg)
    exact Subtype.ext (funext this)
  · rw [hB, hB]
    exact hright k (fun g => star (u.1 g) * v.1 g) fun γ hγ g => by simp only [hl u γ hγ, hl v γ hγ]

end GlobalTheory.DefU.Petersson
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonFormStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_positive_petersson_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧ (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  first | exact @GlobalTheory.DefU.Petersson.exists_invariant_pos_form | exact GlobalTheory.DefU.Petersson.exists_invariant_pos_form | (intros; apply GlobalTheory.DefU.Petersson.exists_invariant_pos_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem reads_linear_injective_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx f f' φ φ' hf hf'
  obtain ⟨-, -, hlin⟩ := thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hS hev x hx φ hf.1
  obtain ⟨hl, hinj⟩ := hlin φ' hf'.1
  obtain ⟨-, -, -, -, hp⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x
  obtain ⟨p, -, hp, -⟩ := hp hx
  refine ⟨fun a b => ⟨(hl a b).1, fun w hw => ?_⟩, fun h => hinj ?_, fun h h' e => ?_⟩
  · rw [(hl a b).2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.2 w hw, hf'.2 w hw]
    ring
  · funext z
    have h1 := hf.2 (p z) (hp z).1
    have h2 := hf'.2 (p z) (hp z).1
    rw [h, h2, (hp z).2] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  · refine theta_eq_of_real D ψ V W hψ f f' h h' fun w hw => ?_
    rw [hf.2 w hw, hf'.2 w hw, e]

theorem IsONFr.mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
    (hx : IsONFr X x) : x ∈ X.dom :=
  PIW.FdPA.orthonormal_domain r X x hx

theorem reads_linear_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx
  exact reads_linear_injective_dom D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx.mem_dom

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrameStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  first | exact @GlobalTheory.AdTh.reads_linear_injective | exact GlobalTheory.AdTh.reads_linear_injective | (intros; apply GlobalTheory.AdTh.reads_linear_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.DiagComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

theorem diag_comp (m : ObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply pullback.hom_ext
  · have h1 := m.sq.1
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (fst o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := m.sq.2
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (snd o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso (m : ObjMap o' o f) :
    LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  have h₁ : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp m.pol _ (diag_comp m).symm
  have h₂ : LBIso ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ)
      (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _)) m.φ rfl
  exact LBIso.trans (pull_isLB o'.isLB _) (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.DiagComp

namespace GlobalTheory.UPel.HT

theorem objMap_comp_diag_lbIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun m => DiagComp.diag_lbIso m⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | exact GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | (intros; apply GlobalTheory.UPel.HT.objMap_comp_diag_lbIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem ord_eq_zero_iff (E : Place c) {f : K} (hf : f ≠ 0) :
    E.ord f = 0 ↔ f ∈ E.ring ∧ f⁻¹ ∈ E.ring := by
  rw [← E.ord_nonneg_iff hf, ← E.ord_nonneg_iff (inv_ne_zero hf), E.ord_inv]
  omega

end GlobalTheory.FieldPair.Place
end
