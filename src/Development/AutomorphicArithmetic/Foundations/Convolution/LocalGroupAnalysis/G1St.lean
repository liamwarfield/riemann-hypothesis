module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.TwistedGeometricSideUnfolding
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.GaloisFixedAdelicMatricesDescend
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.P2TraceFixed
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.FirstCohomologyBoundOfBoundaryBound
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmHasse
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.FirstGeometricConditionOfProperties
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.GaloisTwistPreservesSiegelBound
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.TwistedTraceFormulaEllipticExpansion
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.StableTwistedTraceFormulaComparison

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.GinvHWCellLastMulMulVecBvecEI
open PositivityTheory.Rg.Tf.Geo

noncomputable section

open NumberField IsDedekindDomain Polynomial PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.D
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.G

private theorem map_twNorm {n : ℕ} {k R B : Type} [CommRing k] [CommRing R] [Algebra k R] [CommRing B]
    (p : B →+* R) (s : B →+* B) (τ : R ≃ₐ[k] R) (h : ∀ b, p (s b) = τ (p b)) (q : ℕ) (δ : GL (Fin n) B) :
    mapGL n p (twNorm (mapGL n s) q δ) = nm τ q (mapGL n p δ) := by
  unfold twNorm nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  clear hi
  simp only [Function.comp_apply]
  induction i with
  | zero =>
    ext a b
    rfl
  | succ i ih =>
    refine (congrArg (mapGL n p) (pow_succ_apply' (G := GL (Fin n) B) (mapGL n s) i δ)).trans ?_
    ext a b
    have := congrArg (fun g : GL (Fin n) R => τ ((g : Matrix (Fin n) (Fin n) R) a b)) ih
    refine (h _).trans (this.trans ?_)
    rw [pow_succ']
    rfl

private theorem transport {n : ℕ} {F E A B k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] [CommRing k] [Algebra F k]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (ι : A →+* B) (hι : ∀ a, e (1 ⊗ₜ a) = ι a) (φ : A →ₐ[F] k)
    (γ : GL (Fin n) F) (q : ℕ) (δ : GL (Fin n) B)
    (hδ : twNorm (mapGL n (galOf e σ)) q δ = mapGL n ι (mapGL n (algebraMap F A) γ)) :
    ∃ d, cp (nm (ext k σ) q (n := n) d) = (cp γ).map ((inc k).comp (algebraMap F E)) := by
  let ψ : E ⊗[F] A →ₐ[F] k ⊗[F] E :=
    (Algebra.TensorProduct.comm F E k).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id F E) φ)
  have hψ : ∀ x a, ψ (x ⊗ₜ a) = φ a ⊗ₜ x := fun x a => by simp [ψ]
  let p : B →+* k ⊗[F] E := (ψ : E ⊗[F] A →+* k ⊗[F] E).comp (e.symm : B →+* E ⊗[F] A)
  have hp : ∀ z, p (e z) = ψ z := fun z => by simp [p]
  have h1 : ∀ b, p (galOf e σ b) = ext k σ (p b) := by
    intro b
    obtain ⟨z, rfl⟩ := e.surjective b
    have : galOf e σ (e z) = e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) z) := by
      simp [galOf]
    rw [this, hp, hp]
    clear this
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a => simp [hψ, D.ext]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨mapGL n p δ, ?_⟩
  rw [← map_twNorm p _ _ h1, hδ, cp, cp, ← Matrix.charpoly_map]
  congr 1
  ext a b
  change p (ι (algebraMap F A _)) = inc k (algebraMap F E _)
  rw [← hι, hp, hψ, φ.commutes]
  change _ = (1 : k) ⊗ₜ[F] algebraMap F E _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.ginvH_wCell_last_mul_mulVec_bvec_eI :
    GlobalTheory.Published.HasseNorm → H1 := by
  intro _ F E _ _ _ _ _ _ σ hσ n _ _ γ hγ hinf hfin
  obtain ⟨a, ha, -⟩ := nmHasse F E σ hσ n γ hγ.separable (fun v => by
    obtain ⟨δ, hδ⟩ := hfin v
    refine transport (tensorEquiv' E v) σ (incFin E v) (fun a => ?_) (AlgHom.id F _) γ _ δ (hδ.trans ?_)
    · rw [tensorEquiv'_tmul, map_one, one_mul]
      rfl
    · congr 1) (fun v => by
    obtain ⟨δ, hδ⟩ := hinf
    refine transport (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (fun a => ?_)
      (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) v) γ _ δ (hδ.trans ?_)
    · rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    · congr 1)
  refine ⟨a, Eq.trans ?_ ha⟩
  exact map_twNorm (RingHom.id E) (σ : E →+* E) σ (fun _ => rfl) _ a
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.CharpolyFactorCoeffZeroValuationEqProd
open PositivityTheory.Rg.Tf.Geo

open Polynomial

namespace UpperTheory.ConvolutionTheory.G.TA1

private lemma ext_val {k K Γ : Type*} [Field k] [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k Γ) (f : k →+* K) :
    ∃ B : ValuationSubring K, (B.valuation.comap f).IsEquiv v := by
  obtain ⟨B, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (f.comp v.valuationSubring.subtype)
  refine ⟨B, Valuation.isEquiv_iff_val_le_one.mpr fun {x} => ?_⟩
  rw [Valuation.comap_apply, B.valuation_le_one_iff]
  refine ⟨fun hx => ?_, fun hx => h ⟨x, hx⟩⟩
  by_contra hc
  push Not at hc
  have hx0 : x ≠ 0 := by rintro rfl; simp at hc
  have hi : v x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have hu : IsUnit (((f.comp v.valuationSubring.subtype).codRestrict B.toSubring h) ⟨x⁻¹, hi.le⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, Subtype.ext (by simp [hx0])⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp (hl.1 _ hu)
  have hy' : x⁻¹ * (y : k) = 1 := congrArg Subtype.val hy
  have : (y : k) = x := by field_simp at hy'; exact hy'
  have h2 : v (y : k) ≤ 1 := y.2
  rw [this] at h2
  exact absurd hc (not_lt.mpr h2)

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n : ℕ}

private lemma prod_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → K) (h : ∀ i, w (f i) ≤ 1) (i : ι)
    (hi : w (f i) < 1) : w (∏ j, f j) < 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, map_prod]
  exact mul_lt_one_of_lt_of_le hi (Finset.prod_le_one' fun j _ => h j)

private lemma det_sub (M : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → w (M i j) < 1) : w (M.det - ∏ i, M i i) < 1 := by
  rw [Matrix.det_apply', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply,
    add_sub_cancel_left]
  refine w.map_sum_lt one_ne_zero fun σ hσ => ?_
  have hσ1 : σ ≠ 1 := Finset.ne_of_mem_erase hσ
  have : ∃ i, i < σ i := by
    by_contra hc
    push Not at hc
    apply hσ1
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i => ((σ i : Fin n) : ℕ))
      (g := fun i : Fin n => (i : ℕ)) (fun i _ => hc i)).mp (Equiv.sum_comp σ (fun i : Fin n => (i : ℕ)))
    ext i
    simpa using this i (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := this
  rw [map_mul]
  have hs : w ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact prod_lt w _ (fun j => h1 _ _) i (h2 _ _ hi)

private lemma scaled (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0) (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (i : Fin n) :
    ∃ D : K, D ≠ 0 ∧ ∀ y : K, w y = 1 →
      (w (y - u i i) = 1 → w ((Matrix.diagonal t * u).charpoly.eval (t i * y)) = w D) ∧
      (y = u i i → w ((Matrix.diagonal t * u).charpoly.eval (t i * y)) < w D) := by
  classical
  let d : Fin n → K := fun j => if w (t j) < w (t i) then t i else t j
  have hd0 : ∀ j, d j ≠ 0 := fun j => by simp only [d]; split_ifs <;> exact ht0 _
  have hwt : ∀ j, 0 < w (t j) := fun j => by simpa [pos_iff_ne_zero] using ht0 j
  have hwd : ∀ j, 0 < w (d j) := fun j => by simpa [pos_iff_ne_zero] using hd0 j
  have hdi : ∀ j, w (t i / d j) ≤ 1 := fun j => by
    rw [map_div₀, div_le_one₀ (hwd j)]
    simp only [d]; split_ifs with h
    · exact le_rfl
    · exact not_lt.mp h
  have hdj : ∀ j, w (t j / d j) ≤ 1 := fun j => by
    rw [map_div₀, div_le_one₀ (hwd j)]
    simp only [d]; split_ifs with h
    · exact h.le
    · exact le_rfl
  refine ⟨∏ j, d j, Finset.prod_ne_zero_iff.mpr fun j _ => hd0 j, fun y hy => ?_⟩
  let M : Matrix (Fin n) (Fin n) K := Matrix.of fun j l =>
    (if j = l then t i / d j * y else 0) - t j / d j * u j l
  have hM : Matrix.scalar (Fin n) (t i * y) - Matrix.diagonal t * u = Matrix.diagonal d * M := by
    ext j l
    have := hd0 j
    simp only [M, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.of_apply]
    split_ifs
    · field_simp
    · field_simp; ring
  have hb : ∀ j l, w (t j / d j * u j l) ≤ 1 := fun j l => by
    rw [map_mul]; exact mul_le_one' (hdj j) (h1 j l)
  have hM1 : ∀ j l, w (M j l) ≤ 1 := fun j l => by
    refine w.map_sub_le ?_ (hb j l)
    split_ifs
    · rw [map_mul, hy, mul_one]; exact hdi j
    · simp
  have hM2 : ∀ j l, l < j → w (M j l) < 1 := fun j l h => by
    simp only [M, Matrix.of_apply, if_neg h.ne', zero_sub, Valuation.map_neg, map_mul]
    rw [mul_comm]; exact mul_lt_one_of_lt_of_le (h2 j l h) (hdj j)
  have hMi : M i i = y - u i i := by
    have := ht0 i
    simp [M, d, this]
  have hM3 : ∀ j, j ≠ i → w (M j j) = 1 := fun j hj => by
    have hne : w (t j) ≠ w (t i) := fun h => hj (hinj h)
    simp only [M, Matrix.of_apply, if_true, d]
    split_ifs with h
    · rw [div_self (ht0 i), one_mul, w.map_sub_eq_of_lt_left, hy]
      rw [hy, map_mul, h3, mul_one, map_div₀, div_lt_one₀ (hwt i)]; exact h
    · have h' : w (t i) < w (t j) := lt_of_le_of_ne (not_lt.mp h) hne.symm
      rw [div_self (ht0 j), one_mul, w.map_sub_eq_of_lt_right, h3]
      rw [h3, map_mul, hy, mul_one, map_div₀, div_lt_one₀ (hwt j)]; exact h'
  have hD : 0 < w (∏ j, d j) := by
    simpa [pos_iff_ne_zero, Finset.prod_ne_zero_iff] using hd0
  have hk := det_sub w M hM1 hM2
  rw [Matrix.eval_charpoly, hM, Matrix.det_mul, Matrix.det_diagonal, map_mul]
  constructor
  · intro h
    have hp : w (∏ j, M j j) = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hj : j = i
      · rw [hj, hMi, h]
      · exact hM3 j hj
    have : w M.det = 1 := by
      rw [← hp] at hk ⊢
      exact w.map_eq_of_sub_lt hk
    rw [this, mul_one]
  · intro h
    have hp : ∏ j, M j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hMi, h, sub_self])
    rw [hp, sub_zero] at hk
    exact mul_lt_of_lt_one_right hD hk

private lemma exists_unit [IsAlgClosed K] (c : K) (hc : w c = 1) : ∃ y, w y = 1 ∧ w (y - c) = 1 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X * (X - C c) - 1 : K[X]) (by
    have : (X * (X - C c) - 1 : K[X]).degree = 2 := by compute_degree!
    rw [this]; decide)
  have h : w y * w (y - c) = 1 := by
    rw [← map_mul]
    have : y * (y - c) = 1 := by simpa [sub_eq_zero] using hy
    rw [this, map_one]
  have h1 : w y = 1 := by
    rcases lt_trichotomy (w y) 1 with h' | h' | h'
    · rw [w.map_sub_eq_of_lt_right (by rwa [hc]), hc, mul_one] at h; exact h
    · exact h'
    · rw [w.map_sub_eq_of_lt_left (by rwa [hc])] at h
      exact absurd h (one_lt_mul'' h' h').ne'
  exact ⟨y, h1, by simpa [h1] using h⟩

private lemma exists_root [IsAlgClosed K] (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0)
    (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (i : Fin n) :
    ∃ r ∈ (Matrix.diagonal t * u).charpoly.roots, w r = w (t i) := by
  by_contra hc
  push Not at hc
  obtain ⟨D, -, hD⟩ := scaled w t ht0 hinj u h1 h2 h3 i
  obtain ⟨y, hy, hy'⟩ := exists_unit w (u i i) (h3 i)
  have e1 := (hD y hy).1 hy'
  have e2 := (hD _ (h3 i)).2 rfl
  have key : ∀ z : K, w z = 1 → w ((Matrix.diagonal t * u).charpoly.eval (t i * z)) =
      ((Matrix.diagonal t * u).charpoly.roots.map fun r => max (w (t i)) (w r)).prod := fun z hz => by
    rw [(IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (Matrix.charpoly_monic _), map_multiset_prod,
      Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r hr => ?_
    have hz' : w (t i * z) = w (t i) := by rw [map_mul, hz, mul_one]
    rcases lt_or_gt_of_ne (hc r hr) with h | h
    · rw [Function.comp_apply, w.map_sub_eq_of_lt_left (by rwa [hz']), hz', max_eq_left h.le]
    · rw [Function.comp_apply, w.map_sub_eq_of_lt_right (by rwa [hz']), max_eq_right h.le]
  rw [key _ hy] at e1
  rw [key _ (h3 i), e1] at e2
  exact lt_irrefl _ e2

private lemma main [IsAlgClosed K] (t : Fin n → K) (ht0 : ∀ i, t i ≠ 0)
    (hinj : Function.Injective fun i => w (t i))
    (u : Matrix (Fin n) (Fin n) K) (h1 : ∀ i j, w (u i j) ≤ 1) (h2 : ∀ i j, j < i → w (u i j) < 1)
    (h3 : ∀ i, w (u i i) = 1) (p : K[X]) (hp : p.Monic) (hd : p ∣ (Matrix.diagonal t * u).charpoly) :
    ∃ J : Finset (Fin n), J.card = p.natDegree ∧ w (p.coeff 0) = w (∏ i ∈ J, t i) := by
  classical
  choose r hr hrw using exists_root w t ht0 hinj u h1 h2 h3
  have hri : Function.Injective r := fun i j h => hinj (by simp only [← hrw, h])
  have hle : (Finset.univ.val.map r) ≤ (Matrix.diagonal t * u).charpoly.roots := by
    rw [Multiset.le_iff_subset (Finset.univ.nodup.map hri)]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hr i
  have heq : (Finset.univ.val.map r) = (Matrix.diagonal t * u).charpoly.roots := by
    refine Multiset.eq_of_le_of_card_le hle ?_
    have := card_roots' (Matrix.diagonal t * u).charpoly
    simpa using this
  have hpl : p.roots ≤ Finset.univ.val.map r :=
    heq ▸ roots.le_of_dvd (Matrix.charpoly_monic _).ne_zero hd
  have hJ : p.roots = (Finset.univ.filter fun i => r i ∈ p.roots).val.map r := by
    refine (Multiset.Nodup.ext (Multiset.nodup_of_le hpl (Finset.univ.nodup.map hri))
      ((Finset.nodup _).map hri)).mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hpl hx)
      exact Multiset.mem_map.mpr ⟨i, by simpa using hx, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
      simpa using hi
  refine ⟨Finset.univ.filter fun i => r i ∈ p.roots, ?_, ?_⟩
  · rw [(IsAlgClosed.splits p).natDegree_eq_card_roots]
    conv_rhs => rw [hJ]
    rw [Multiset.card_map]; rfl
  · rw [(IsAlgClosed.splits p).coeff_zero_eq_prod_roots_of_monic hp, map_mul, map_pow, Valuation.map_neg,
      map_one, one_pow, one_mul, map_prod]
    conv_lhs => rw [hJ]
    rw [← Finset.prod_eq_multiset_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => hrw i

end UpperTheory.ConvolutionTheory.G.TA1

open UpperTheory.ConvolutionTheory.G.TA1 GroundTheory.Automorphic in
theorem UpperTheory.ConvolutionTheory.G.charpoly_factor_coeff_zero_valuation_eq_prod :
    A1 := by
  intro k _ _ _ _ n μ hμ a ha b hb p hp hd
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff k n).mp ((GLnLocal.iwahori k n).mul_mem hb ha)
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨B, hB⟩ := ext_val (ValuativeRel.valuation k) f
  have hd' : p ∣ (Matrix.diagonal (fun i => (GLnLocal.uniformizer k : k) ^ μ i) *
      ((b * a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).charpoly := by
    rwa [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Cartan.coe_diagPow,
      Matrix.mul_assoc, ← Units.val_mul] at hd
  have hπ := Cartan.uniformizer_ne_zero k
  obtain ⟨J, hJ, hv⟩ := main B.valuation (fun i => f ((GLnLocal.uniformizer k : k) ^ μ i))
    (fun i => (map_ne_zero f).mpr (zpow_ne_zero _ hπ))
    (fun i j h => by
      have h' := (hB.eq_iff).mp h
      simp only [map_zpow₀] at h'
      exact hμ (zpow_right_injective₀ (GLnLocal.valuation_uniformizer_pos k)
        (GLnLocal.valuation_uniformizer_lt_one k).ne h'))
    (((b * a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map f)
    (fun i j => (hB.le_one_iff_le_one).mpr (h1 i j))
    (fun i j h => (hB.lt_one_iff_lt_one).mpr (h2 i j h))
    (fun i => (hB.eq_one_iff_eq_one).mpr (h3 i)) (p.map f) (hp.map f) (by
      have := Polynomial.map_dvd f hd'
      rwa [← Matrix.charpoly_map, Matrix.map_mul, Matrix.diagonal_map (map_zero f)] at this)
  refine ⟨J, by rw [hJ, natDegree_map], ?_⟩
  rw [coeff_map, ← map_prod] at hv
  simp only [Cartan.coe_diagPow, Matrix.diagonal_apply_eq]
  exact (hB.eq_iff).mp hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.ClosedSubgroupCutoffExists
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    (H : Subgroup X) (hH : IsClosed (H : Set X)) :
    ∃ β : X → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, ∃ h ∈ H, β (h * x) ≠ 0) ∧
      ∀ C : Set X, IsCompact C → ∃ C' : Set X, IsCompact C' ∧
        ∀ h ∈ H, ∀ x ∈ C, β (h * x) ≠ 0 → h * x ∈ C' := by
  classical
  let K : CompactExhaustion X := (CompactExhaustion.choice X).shiftr.shiftr
  have hK0 : K 0 = ∅ := rfl
  have hK1 : K 1 = ∅ := rfl
  let S : ℕ → Set X := fun m => (H : Set X) * K m
  let O : ℕ → Set X := fun m => (H : Set X) * interior (K m)
  have hSc : ∀ m, IsClosed (S m) := fun m => hH.mul_right_of_isCompact (K.isCompact m)
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_interior.mul_left
  have hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1)) := fun m => (K.isCompact _).diff (hOo _)
  have hSO : ∀ m, S m ⊆ O (m + 1) := fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)
  have hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m) := fun m =>
    Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)
  choose f hf1 hf0 hfc hfI using fun m =>
    exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)
  have hself : ∀ m, K m ⊆ S m := fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b := fun hab =>
    Set.mul_subset_mul_left (K.subset hab)
  have hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0 := fun hNm x hx => hf0 _ (hSmono hNm hx)
  have hnn : ∀ m x, 0 ≤ f m x := fun m x => (hfI m x).1
  have hlf : LocallyFinite fun m => Function.support (f m) := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine ⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn),
      (Set.finite_lt_nat (n + 1)).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    by_contra hm
    exact hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))
  have hfin : ∀ x, (Function.support fun m => f m x).Finite := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine (Set.finite_lt_nat n).subset ?_
    intro m hm
    by_contra hmn
    exact hm (hvan (not_lt.1 hmn) x (hself _ hn))
  refine ⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf,
    fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩
  · intro x
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ n, n < Nat.find hex → x ∉ O n := fun n hn => Nat.find_min hex hn
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by
      rcases hN : Nat.find hex with _ | _ | m
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK0] at hy
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK1] at hy
      · exact ⟨m, rfl⟩
    rw [hm] at hspec
    obtain ⟨h, hh, y, hy, rfl⟩ := hspec
    have hyQ : y ∈ K (m + 2) \ O (m + 1) := by
      refine ⟨interior_subset hy, ?_⟩
      rintro ⟨h', hh', z, hz, rfl⟩
      refine hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, (mul_assoc _ _ _)⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    rw [inv_mul_cancel_left]
    have h1 : f m y ≤ ∑ᶠ m, f m y := single_le_finsum m (hfin y) (fun j => hnn j y)
    have h2 : f m y = 1 := hf1 m hyQ
    intro h0
    simp only [h0, h2] at h1
    linarith
  · intro C hC
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    refine ⟨⋃ m ∈ Finset.range N, tsupport (f m),
      (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩
    intro h hh x hx hne
    obtain ⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (finsum_eq_zero_of_forall_eq_zero hall)
    have hmN : m < N := by
      by_contra hmN
      exact hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.closedSubgroup_cutoff_exists :
    Q2 := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ν _ _ i hi
  have hH : IsClosed ((i.range : Subgroup X) : Set X) := by
    rw [MonoidHom.coe_range]; exact hi.isClosed_range
  obtain ⟨β, hβ, hβ0, hcov, hsupp⟩ := UpperTheory.ConvolutionTheory.G.exists_bump i.range hH
  have hB : ∀ C : Set X, IsCompact C → ∃ B : Set T, IsCompact B ∧
      ∀ t, ∀ x ∈ C, β (i t * x) ≠ 0 → t ∈ B := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨i ⁻¹' (C' * C⁻¹), hi.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩
    exact ⟨i t * x, h _ ⟨t, rfl⟩ x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩
  have hc : Continuous (Function.uncurry fun (x : X) (t : T) => β (i t * x)) :=
    hβ.comp ((hi.continuous.comp continuous_snd).mul continuous_fst)
  have hcx : ∀ x, Continuous fun t => β (i t * x) := fun x =>
    hβ.comp (hi.continuous.mul continuous_const)
  have hcs : ∀ x, HasCompactSupport fun t => β (i t * x) := by
    intro x
    obtain ⟨B, hBc, hB'⟩ := hB {x} isCompact_singleton
    refine HasCompactSupport.intro hBc fun t ht => ?_
    by_contra hne
    exact ht (hB' t x rfl hne)
  let D : X → ℝ := fun x => ∫ t, β (i t * x) ∂ν
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
    obtain ⟨B, hBc, hB'⟩ := hB N hNc
    have h1 : Continuous fun x => ∫ t in B, β (i t * x) ∂ν :=
      continuous_parametric_integral_of_continuous hc hBc
    refine h1.continuousAt.congr ?_
    filter_upwards [hN] with x hx
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra hne
    exact ht (hB' t x hx hne)
  have hDpos : ∀ x, 0 < D x := by
    intro x
    obtain ⟨h, ⟨t₀, rfl⟩, hne⟩ := hcov x
    exact (hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun t => hβ0 _) hne
  have hDinv : ∀ s x, D (i s * x) = D x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => β (i t * x)) s
    simpa [D, mul_assoc] using this
  refine ⟨fun x => Real.toNNReal (β x / D x),
    continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact (ENNReal.continuous_coe.comp
      (continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne'))).measurable
  · intro x
    have hint : Integrable (fun t => β (i t * x) / D x) ν :=
      ((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _
    have h1 : ∫⁻ t, ((Real.toNNReal (β (i t * id x) / D (i t * id x)) : NNReal) : ℝ≥0∞) ∂ν =
        ∫⁻ t, ENNReal.ofReal (β (i t * x) / D x) ∂ν := by
      refine lintegral_congr fun t => ?_
      simp only [id, hDinv]
      rfl
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]
    change ENNReal.ofReal (D x / D x) = 1
    rw [div_self (hDpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨C', hC', fun t x hx hne => h _ ⟨t, rfl⟩ x hx fun h0 => hne ?_⟩
    simp [h0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.ExistsKrylovDetNeZero
open PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.G.p1_holds :
    P1 :=
  _root_.UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.UnitaryGroupGeometricSideOfQuotientIdentities
open PositivityTheory.Rg.Tf.Geo

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal

private theorem UpperTheory.ConvolutionTheory.G.stage_key
    {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure]
    (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i)
    (hinj : Function.Injective i) (Λ : Subgroup T) [DiscreteTopology Λ] (Γ₀ : Subgroup X)
    [DiscreteTopology Γ₀] (hΛ : Λ.map i = Γ₀)
    (ρ : X → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1)
    (F : X → ℝ≥0∞) (hF : Measurable F) (hFi : ∀ t x, F (i t * x) = F x) :
    ∫⁻ x in fundamentalDomain Γ₀, F x ∂μ = ν (fundamentalDomain Λ) * ∫⁻ x, F x * ρ x ∂μ := by
  subst hΛ
  set D := fundamentalDomain Λ with hDdef
  set E := fundamentalDomain (Λ.map i) with hEdef
  have hD : IsFundamentalDomain Λ D ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hE : IsFundamentalDomain (Λ.map i) E μ := isFundamentalDomain_fundamentalDomain _ μ
  have hc : Continuous fun p : X × T => i p.2⁻¹ * p.1 :=
    (hi.comp continuous_snd.inv).mul continuous_fst
  have hm : Measurable fun p : X × T => ρ (i p.2⁻¹ * p.1) := hρ.comp hc.measurable
  set ρ' : X → ℝ≥0∞ := fun x => ∫⁻ d in D, ρ (i d⁻¹ * x) ∂ν with hρ'
  have hρ'm : Measurable ρ' := hm.lintegral_prod_right'
  have hinv : ∀ x, ∫⁻ d, ρ (i d⁻¹ * x) ∂ν = 1 := fun x => by
    rw [← hρ1 x]
    exact lintegral_inv_eq_self (fun t => ρ (i t * x))
  have hsum : ∀ x, ∑' l : Λ, ρ' (i l * x) = 1 := fun x => by
    rw [← hinv x, hD.lintegral_eq_tsum']
    refine tsum_congr fun l => ?_
    simp only [hρ']
    refine lintegral_congr fun d => ?_
    simp [Subgroup.smul_def, mul_assoc]
  have hunf : ∫⁻ x, F x * ρ' x ∂μ = ∫⁻ x in E, F x ∂μ := by
    rw [hE.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun x => ?_
      rw [← (Subgroup.equivMapOfInjective Λ i hinj).toEquiv.tsum_eq]
      have : ∀ l : Λ, F ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) *
          ρ' ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) = F x * ρ' (i l * x) := fun l => by
        have h : (Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x = i l * x := rfl
        rw [h, hFi]
      simp only [this]
      rw [ENNReal.tsum_mul_left, hsum, mul_one]
    · intro g
      exact ((hF.mul hρ'm).comp (measurable_const_smul g)).aemeasurable
  have hfub : ∫⁻ x, F x * ρ' x ∂μ = ν D * ∫⁻ x, F x * ρ x ∂μ := by
    have h1 : ∀ x, F x * ρ' x = ∫⁻ d in D, F x * ρ (i d⁻¹ * x) ∂ν := fun x => by
      have hd : Measurable fun d : T => ρ (i d⁻¹ * x) :=
        hρ.comp ((hi.comp continuous_inv).mul continuous_const).measurable
      rw [lintegral_const_mul _ hd]
    simp only [h1]
    rw [lintegral_lintegral_swap]
    · have h2 : ∀ d : T, ∫⁻ x, F x * ρ (i d⁻¹ * x) ∂μ = ∫⁻ x, F x * ρ x ∂μ := fun d => by
        rw [← lintegral_mul_left_eq_self (fun y => F y * ρ y) (i d⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hFi]
      simp only [h2]
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · exact ((hF.comp measurable_fst).mul hm).aemeasurable
  rw [← hunf, hfub]

theorem UpperTheory.ConvolutionTheory.G.unitaryGroupGeometricSide_of_quotient_identities :
    Q1 → Q2 → U2 := by
  intro hQ1 hQ2 X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ _ i hi Λ _ Γ₀ _ hΛ hvol Φ hΦc hΦi hint
  have hD : IsFundamentalDomain Λ (fundamentalDomain Λ) ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hvolD : quotientMeasure Λ ν Set.univ = ν (fundamentalDomain Λ) := quotientMeasure_univ ν hD
  have hD0 : ν (fundamentalDomain Λ) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hΦm : Measurable Φ := hΦc.measurable
  have hic : Continuous i := hi.continuous
  have hout : ∀ g, Φ (Quotient.out (RightCosetSpace.mk Γ₀ g)) = Φ g := fun g => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk Γ₀ g))
    have hγm : (γ : X) ∈ Λ.map i := hΛ ▸ γ.2
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 hγm
    rw [← hγ, Subgroup.smul_def, smul_eq_mul, ← ht, hΦi]
  have key := fun ρ hρ hρ1 F hF hFi =>
    UpperTheory.ConvolutionTheory.G.stage_key μ ν i hic hi.injective Λ Γ₀ hΛ ρ hρ hρ1 F hF hFi
  have hEfin : ∫⁻ x in fundamentalDomain Γ₀, ‖Φ x‖ₑ ∂μ < ⊤ := by
    have h := hint.2
    rw [HasFiniteIntegral, lintegral_quotientMeasure] at h
    simpa only [hout] using h
  have hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ => by
    have h := key ρ hρ.1 hρ.2 (fun x => ‖Φ x‖ₑ) hΦm.enorm (fun t x => by simp only [hΦi])
    rw [h] at hEfin
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hD0] at hEfin
    exact lt_irrefl _ hEfin
  refine ⟨?_, hfin⟩
  obtain ⟨ρ₀, hρc, hρn, -⟩ := hQ2 X T ν i hi
  have e1 := hQ1 X X T μ ν (MonoidHom.id X) i measurable_id hic Φ (fun x => (ρ₀ x : ℝ≥0∞)) hΦm hΦi hρn (hfin _ hρn)
  have hmeas : (μ.restrict (fundamentalDomain Γ₀)).map Φ =
      (ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))).map Φ := by
    rw [Measure.ext_iff_lintegral]
    intro f hf
    have hw : ∫⁻ a, f (Φ a) ∂μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)) =
        ∫⁻ a, f (Φ a) * (ρ₀ a : ℝ≥0∞) ∂μ := by
      rw [show (fun a => f (Φ a)) = f ∘ Φ from rfl,
        lintegral_withDensity_eq_lintegral_mul μ hρn.1 (hf.comp hΦm)]
      exact lintegral_congr fun a => mul_comm _ _
    rw [lintegral_map hf hΦm, lintegral_map hf hΦm, lintegral_smul_measure, hw, smul_eq_mul]
    exact key _ hρn.1 hρn.2 (fun x => f (Φ x)) (hf.comp hΦm) (fun t x => by simp only [hΦi])
  have hq : ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ∫ g in fundamentalDomain Γ₀, Φ g ∂μ := by
    rw [integral_quotientMeasure]
    simp only [hout]
  have hz : ∫ g in fundamentalDomain Γ₀, Φ g ∂μ =
      ∫ x, Φ x ∂(ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))) := by
    have h1 : ∀ m : Measure X, ∫ z, z ∂(m.map Φ) = ∫ x, Φ x ∂m := fun m =>
      integral_map hΦm.aemeasurable aestronglyMeasurable_id
    rw [← h1, ← h1, hmeas]
  rw [hq, hz, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hρn.1
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top), hvolD, Complex.real_smul]
  congr 1
  have e2 : quotInt μ id i ν Φ = ∫ x, Φ x * (((ρ₀ x : ℝ≥0∞)).toReal : ℂ) ∂μ := e1
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.real_smul, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.EllipticCentralizerQuotientCompact
open PositivityTheory.Rg.Tf.Geo
open NumberField IsDedekindDomain Matrix Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup
open PositivityTheory.Rg.Tf.Core
open scoped NumberField.AdeleRing Pointwise

private def krylovMatrixOfRowVector {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun k => x ᵥ* M ^ (k : ℕ)

private theorem vecMul_krylov {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (x c : Fin n → R) :
    c ᵥ* krylovMatrixOfRowVector M x = x ᵥ* ∑ k : Fin n, c k • M ^ (k : ℕ) := by
  rw [Matrix.vecMul_sum, Matrix.vecMul_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.vecMul_smul]
  rfl

private theorem krylov_mul_commute {R : Type*} [CommRing R] {n : ℕ} {M t : Matrix (Fin n) (Fin n) R} (h : Commute M t)
    (x : Fin n → R) : krylovMatrixOfRowVector M x * t = krylovMatrixOfRowVector M (x ᵥ* t) := by
  ext k j
  have : (krylovMatrixOfRowVector M x * t) k j = ((x ᵥ* M ^ (k : ℕ)) ᵥ* t) j := rfl
  rw [this, vecMul_vecMul, (h.pow_left k).eq, ← vecMul_vecMul]
  rfl

private theorem krylov_map_alt {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : (krylovMatrixOfRowVector M x).map f = krylovMatrixOfRowVector (M.map f) (f ∘ x) := by
  ext k j
  have h : (M.map f) ^ (k : ℕ) = (M ^ (k : ℕ)).map f := by
    simpa using (map_pow f.mapMatrix M k).symm
  change f ((x ᵥ* M ^ (k : ℕ)) j) = ((f ∘ x) ᵥ* (M.map f) ^ (k : ℕ)) j
  rw [h, RingHom.map_vecMul]

private theorem krylov_det_ne_zero {F : Type*} [Field F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : Irreducible M.charpoly) {x : Fin n → F} (hx : x ≠ 0) : (krylovMatrixOfRowVector M x).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  rw [vecMul_krylov] at hc0
  set p : F[X] := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp
  have hpa : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hp, map_sum, Algebra.smul_def]
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hp0 : p ≠ 0 := by
    intro h
    apply hc
    funext k
    have := congrArg (fun q : F[X] => q.coeff k) h
    simpa [hp, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using this
  have hnd : ¬ M.charpoly ∣ p := by
    intro hd
    have := degree_le_of_dvd hd hp0
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
    exact absurd hdeg (not_lt.2 this)
  obtain ⟨a, b, hab⟩ := (hM.coprime_iff_not_dvd).2 hnd
  have h1 := congrArg (aeval M) hab
  rw [map_add (f := _), map_mul, Matrix.aeval_self_charpoly, mul_zero, zero_add, mul_comm b p, map_mul, map_one, hpa] at h1
  apply hx
  rw [← vecMul_one x, ← h1, ← vecMul_vecMul, hc0, zero_vecMul]

private theorem commute_of_krylov_unit {R : Type*} [CommRing R] {n : ℕ} {M s t : Matrix (Fin n) (Fin n) R} {x : Fin n → R}
    (hx : IsUnit (krylovMatrixOfRowVector M x)) (hs : Commute M s) (ht : Commute M t) : Commute s t := by
  obtain ⟨u, hu⟩ := hx
  set c : Fin n → R := (x ᵥ* t) ᵥ* (↑u⁻¹ : Matrix (Fin n) (Fin n) R) with hc
  set q : Matrix (Fin n) (Fin n) R := ∑ k : Fin n, c k • M ^ (k : ℕ) with hq
  have h1 : x ᵥ* q = x ᵥ* t := by
    rw [hq, ← vecMul_krylov, hc, ← hu, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hMq : Commute M q :=
    Commute.sum_right _ _ _ fun k _ => ((Commute.refl M).pow_right k).smul_right _
  have h2 : t = q := by
    have : (u : Matrix (Fin n) (Fin n) R) * t = u * q := by
      rw [hu, krylov_mul_commute ht, krylov_mul_commute hMq, h1]
    exact (Units.mul_right_inj u).1 this
  rw [h2]
  exact Commute.sum_right _ _ _ fun k _ => (hs.symm.pow_right k).smul_right _

private theorem adelic_hadamard_inequality {K : Type*} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤
      ∏ i, adelicNorm ((Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  classical
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact g
  have hk1 := mem_normOneGL.1 (maxCompact_le_normOneGL hk)
  have hu := isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det K n b = ∏ i, (hu i).unit := by
    refine Units.ext ?_
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    rfl
  rw [map_mul, map_mul, Positive.val_mul, hk1, mul_one, hdet, map_prod, coe_finset_prod_pos]
  refine Finset.prod_le_prod₀ (fun i _ => (ideleModule K (hu i).unit).2.le) fun i _ => ?_
  rw [Units.val_mul, ← vecMul_vecMul, adelicNorm_vecMul_maxCompact _ hk, ← adelicNorm_single_units i]
  have he : (Pi.single i (((hu i).unit : IdeleGroup K) : 𝔸[K]) : Fin n → 𝔸[K]) =
      (((hu i).unit : IdeleGroup K) : 𝔸[K]) • (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have key := adelicNorm_le_of_local ((hasFiniteContent_single_one (K := K) i).smul (hu i).unit)
    ((hasFiniteContent_single_one (K := K) i).vecMul b) (fun _ => 1) (fun _ => 1) ∅ (fun w => ?_)
    (fun _ _ => rfl) (fun v => ?_)
  · rw [he]
    simpa using key
  · rw [one_mul, infComp_smul, euclidNorm_smul]
    have h1 : euclidNorm (infComp w (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])) = 1 := by
      rw [← euclidNorm_pi_single_one (E := w.Completion) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [infComp]
      · simp [infComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_euclidNorm (infComp w ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i
  · rw [one_mul, finComp_smul, norm_smul]
    have h1 : ‖finComp v (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K])‖ = 1 := by
      rw [← norm_pi_single_one (E := v.adicCompletion K) i]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [finComp]
      · simp [finComp, Pi.single_eq_of_ne hj]; rfl
    rw [h1, mul_one, single_one_vecMul]
    exact norm_le_pi_norm (finComp v ((b : Matrix (Fin n) (Fin n) 𝔸[K]).row i)) i

private theorem centralizer_compact_fundamental {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {γ : G} (hγ : γ ∈ Γ) {D : Set G} (hD : IsCompact D)
    (h : ∀ t : Subgroup.centralizer {γ}, ∃ g ∈ Γ, ∃ y ∈ D, (t : G) = g * y) :
    ∃ C : Set (Subgroup.centralizer {γ}), IsCompact C ∧ ∀ t : Subgroup.centralizer {γ},
      ∃ g : Subgroup.centralizer {γ}, (g : G) ∈ Γ ∧ ∃ y ∈ C, t = g * y := by
  classical
  have hE : IsCompact ((fun y : G => y * γ * y⁻¹) '' D) := hD.image (by fun_prop)
  have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have hfin : ((fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G)).Finite := by
    have h1 : IsCompact (Subtype.val ⁻¹' ((fun y : G => y * γ * y⁻¹) '' D) : Set Γ) :=
      hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hE
    refine (h1.finite_of_discrete.image Subtype.val).subset ?_
    rintro z ⟨hz, hzΓ⟩
    exact ⟨⟨z, hzΓ⟩, hz, rfl⟩
  have hr : ∀ δ : G, ∃ r ∈ Γ, (∃ g ∈ Γ, g⁻¹ * γ * g = δ) → r⁻¹ * γ * r = δ := fun δ => by
    by_cases hδ : ∃ g ∈ Γ, g⁻¹ * γ * g = δ
    · obtain ⟨g, hg, hg'⟩ := hδ
      exact ⟨g, hg, fun _ => hg'⟩
    · exact ⟨1, one_mem _, fun h => absurd h hδ⟩
  choose r hrΓ hr using hr
  have hC : IsCompact (⋃ δ ∈ (fun y : G => y * γ * y⁻¹) '' D ∩ (Γ : Set G), (fun y => r δ * y) '' D) :=
    hfin.isCompact_biUnion fun δ _ => hD.image (by fun_prop)
  have hZ : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G) := by
    have : ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {x | x * γ = γ * x} := by
      ext x
      exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  refine ⟨Subtype.val ⁻¹' _, hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun t => ?_⟩
  obtain ⟨g, hg, y, hy, hty⟩ := h t
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have hδ : g⁻¹ * γ * g = y * γ * y⁻¹ := by
    rw [hty] at ht
    calc g⁻¹ * γ * g = g⁻¹ * (γ * (g * y)) * y⁻¹ := by group
      _ = y * γ * y⁻¹ := by rw [← ht]; group
  have hr1 := hr _ ⟨g, hg, hδ⟩
  set ρ := r (y * γ * y⁻¹) with hρ
  have hz : g * ρ⁻¹ ∈ Subgroup.centralizer {γ} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * ρ⁻¹ * γ = g * (ρ⁻¹ * γ * ρ) * ρ⁻¹ := by group
      _ = γ * (g * ρ⁻¹) := by rw [hr1, ← hδ]; group
  refine ⟨⟨_, hz⟩, mul_mem hg (inv_mem (hrΓ _)), (⟨_, hz⟩ : Subgroup.centralizer {γ})⁻¹ * t, ?_, by group⟩
  refine Set.mem_biUnion (x := y * γ * y⁻¹) ⟨⟨y, hy, rfl⟩, ?_⟩ ⟨y, hy, ?_⟩
  · rw [← hδ]
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  · change ρ * y = (g * ρ⁻¹)⁻¹ * (t : G)
    rw [hty]; group

theorem UpperTheory.ConvolutionTheory.G.elliptic_centralizer_quotient_compact :
    N4 := by
  intro F _ _ n γ γ₁ hγ hirr
  set M : Matrix (Fin n) (Fin n) 𝔸[F] := Units.val (AdelicGLn.diagonal F n γ) with hM
  have hcom : ∀ t : Subgroup.centralizer {γ₁},
      Commute M (((t : G1 F n) : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) := fun t => by
    have ht : (t : G1 F n) * γ₁ = γ₁ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have := congrArg (fun z : G1 F n => ((z : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F])) ht
    simp only [Subgroup.coe_mul, Units.val_mul, hγ] at this
    exact this.symm
  have hK : ∀ x : Fin n → F, x ≠ 0 → ∃ κ : GL (Fin n) F,
      ((AdelicGLn.diagonal F n κ : AdelicGLn.AdelicGL F n) : Matrix (Fin n) (Fin n) 𝔸[F]) =
        krylovMatrixOfRowVector M (ratVec x) := fun x hx =>
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (krylov_det_ne_zero hirr hx),
      krylov_map_alt (algebraMap F 𝔸[F]) _ x⟩
  have hn : 0 < n := by
    have := hirr.natDegree_pos
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  constructor
  · intro s t
    obtain ⟨κ, hκ⟩ := hK (Pi.single ⟨0, hn⟩ 1) (by simp)
    have := commute_of_krylov_unit (hκ ▸ Units.isUnit _) (hcom s) (hcom t)
    exact Subtype.ext (Subtype.ext (Units.ext this.eq))
  obtain ⟨P, hP, hPle⟩ := exists_adelicNorm_vecMul_le_mul
    (Set.finite_range fun k : Fin n => AdelicGLn.diagonal F n γ ^ (k : ℕ)).isCompact
  obtain ⟨D, hD, hD'⟩ := exists_isCompact_forall_of_pos_le_height (K := F) (n := n) (inv_pos.2 hP)
  refine centralizer_compact_fundamental (Gam F n) (show (γ₁ : AdelicGLn.AdelicGL F n) ∈ AdelicGLn.rationalGL F n from ⟨γ, hγ.symm⟩)
    (isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hD) fun t => ?_
  set τ : AdelicGLn.AdelicGL F n := ((t : G1 F n) : AdelicGLn.AdelicGL F n) with hτ
  have hτ1 : τ ∈ normOneGL (K := F) (n := n) := (t : G1 F n).2
  have hht : ∀ x : Fin n → F, x ≠ 0 → P⁻¹ ≤ height τ x := fun x hx => by
    obtain ⟨κ, hκ⟩ := hK x hx
    have h1 := adelic_hadamard_inequality (AdelicGLn.diagonal F n κ * τ)
    rw [mem_normOneGL.1 (mul_mem (rationalGL_le_normOneGL ⟨κ, rfl⟩) hτ1), Units.val_mul, hκ,
      krylov_mul_commute (hcom t)] at h1
    have h2 : ∏ i : Fin n, adelicNorm ((Pi.single i (1 : 𝔸[F]) : Fin n → 𝔸[F]) ᵥ*
        krylovMatrixOfRowVector M (ratVec x ᵥ* (τ : Matrix (Fin n) (Fin n) 𝔸[F]))) ≤ ∏ _i : Fin n, P * height τ x := by
      refine Finset.prod_le_prod₀ (fun _ _ => adelicNorm_nonneg _) fun i _ => ?_
      have := hPle _ ⟨i, rfl⟩ _ (hasFiniteContent_height τ hx)
      rw [single_one_vecMul]
      rw [Units.val_pow_eq_pow_val] at this
      exact this
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 : 1 ≤ P * height τ x :=
      (one_le_pow_iff_of_nonneg (mul_nonneg hP.le (height_nonneg _ _)) hn.ne').1 (h1.trans h2)
    rw [inv_le_iff_one_le_mul₀' hP]
    exact h3
  obtain ⟨g, hg, y, hy, hgy⟩ := hD' τ hτ1 hht
  have hg1 : g ∈ normOneGL (K := F) (n := n) := rationalGL_le_normOneGL hg
  have hy1 : y ∈ normOneGL (K := F) (n := n) := by
    have : y = g⁻¹ * τ := by rw [← hgy, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hg1) hτ1
  exact ⟨⟨g, hg1⟩, hg, ⟨y, hy1⟩, hy, Subtype.ext hgy.symm⟩
end

open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.G

theorem g0 : G0 := UpperTheory.ConvolutionTheory.K.g0
theorem g1St : EllipticityFromProductFormula := firstGeometricCondition_of_properties charpoly_factor_coeff_zero_valuation_eq_prod character_column_kernels_of_block_chi_c_of_block_chi_one
theorem g2 : G2 := galois_twist_preserves_siegel_bound
theorem g3 : G3 := twisted_trace_formula_elliptic_expansion g2 twistedGeometricSide_unfolding (unitaryGroupGeometricSide_of_quotient_identities isUnit_last_join closedSubgroup_cutoff_exists) isUnit_last_join closedSubgroup_cutoff_exists monic_polynomial_is_matrix_charpoly nm_agrees_with_twisted_norm_sigmaGL galois_fixed_adelic_matrices_descend elliptic_centralizer_quotient_compact character_column_kernels_of_block_chi_c_of_block_chi_one g0
theorem g4 : G4 := stable_twisted_trace_formula_comparison isUnit_last_join closedSubgroup_cutoff_exists (orbitalIntegral_absolute_convergence isUnit_last_join closedSubgroup_cutoff_exists) galois_fixed_adelic_matrices_descend character_column_kernels_of_block_chi_c_of_block_chi_one p1_holds (p2_of p1_holds) firstCohomologyBound_of_boundaryBound (ginvH_wCell_last_mul_mulVec_bvec_eI GlobalTheory.CNorm.hasseNorm)

end UpperTheory.ConvolutionTheory.G
