module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FlagFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem coc_zero {Γ O k : Type} [Group Γ] [CommRing O] [Field k] (a : O →+* k) (A B : Γ →* Oˣ) (f : Γ → k)
    (hf : ∀ g h, f (g * h) = a (A g) * f h + f g * a (B h)) (h : Γ) (hh : a (A h) ≠ a (B h))
    (h0 : ∀ g, f (g * h * g⁻¹) = 0) (g : Γ) : f g = 0 := by
  have h1 : f h = 0 := by simpa using h0 1
  have h2 := hf (g * h * g⁻¹) g
  have h3 : A (g * h * g⁻¹) = A h := by simp [mul_comm (A g) (A h)]
  rw [h0, h3, inv_mul_cancel_right, hf, h1] at h2
  have h4 : f g * (a (A h) - a (B h)) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hh)

private theorem conj_mem {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) [Normal ℚ F]
    (h : G F Ω) (g : G ℚ Ω) : ∃ h' : G F Ω, resQ F h' = g * resQ F h * g⁻¹ := by
  refine ⟨{ (g * resQ F h * g⁻¹).toRingEquiv with commutes' := fun x => ?_ }, rfl⟩
  have h1 := AlgEquiv.restrictNormal_commutes g⁻¹ F x
  have h2 := h.commutes ((AlgEquiv.restrictNormal g⁻¹ F) x)
  rw [h1] at h2
  show g (h (g⁻¹ (algebraMap F Ω x))) = algebraMap F Ω x
  rw [h2]
  exact g.apply_symm_apply _

private theorem ne_of_res {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k) {x y : O}
    (h : residue O x ≠ residue O y) : a x ≠ a y := by
  have h1 : IsUnit (x - y) := by
    by_contra hn
    apply h
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hn
  have h2 := (h1.map a).ne_zero
  rwa [map_sub, sub_ne_zero] at h2

private theorem flag_facts {k : Type} [Field k] (n n' r : M4 k) (hn : IsLow n) (hq : SuppM qQ n) (hn' : IsLow n')
    (hr : SuppM nP r) (h1 : r 1 1 ≠ 0) (hu : IsUp (adj n' * r * n)) :
    n' 2 1 = 0 ∧ n' 2 0 * r 0 0 = r 2 0 + r 2 2 * n 2 0 ∧ n' 1 0 * r 0 0 = r 1 0 + r 1 1 * n 1 0 + r 1 2 * n 2 0 := by
  have a21 : n 2 1 = 0 := hq 2 1 (by decide) (by decide)
  have r01 : r 0 1 = 0 := hr 0 1 (by decide) (by decide)
  have r02 : r 0 2 = 0 := hr 0 2 (by decide) (by decide)
  have r03 : r 0 3 = 0 := hr 0 3 (by decide) (by decide)
  have r13 : r 1 3 = 0 := hr 1 3 (by decide) (by decide)
  have r21 : r 2 1 = 0 := hr 2 1 (by decide) (by decide)
  have r23 : r 2 3 = 0 := hr 2 3 (by decide) (by decide)
  obtain ⟨-, d, u⟩ := hn
  obtain ⟨g', d', u'⟩ := hn'
  have a01 := u 0 1 (by decide)
  have b01 := u' 0 1 (by decide)
  have b02 := u' 0 2 (by decide)
  have b12 := u' 1 2 (by decide)
  have e21 := hu 2 1 (by decide)
  have e20 := hu 2 0 (by decide)
  have e10 := hu 1 0 (by decide)
  have g20 := congrFun (congrFun g' 2) 0
  have g10 := congrFun (congrFun g' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, a21, r01, r02, r03, r13, r21, r23, a01, b01, b02, b12, d, d', h1] at e21 e20 e10 g20 g10
  rw [e21] at e20 g20
  refine ⟨e21, ?_, ?_⟩
  · linear_combination (r 0 0) * g20 - e20
  · linear_combination (r 0 0) * g10 - e10

theorem UpperTheory.V.Ws.goodQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ (g0 : G ℚ Ω) (s : PD Unit (G ℚ Ω) k) (s' : PD T.ι (G T.F Ω) k), LatShape D T.pr g0 a s → (∀ w ∈ roots, a ((frQ D T.pr g0).rt w g0) ≠ 1) →
      T.OverQ s s' → (T.fr ∅).IsRes a s' → ∀ W : Finset ℕ, (T.fr W).IsRes a s' ∧ s'.In nP ∧
        (Ent s'.r (-wPs) ∧ Ent s'.r wBe ∨ Fr.InV (Φ := T.fr ∅) s' ∧ Ent s'.r (-wAl)) := by
  intro Ω _ _ _ l _ c D _ T hT k _ a _ g0 s s' hs _ hov hres W
  obtain ⟨hr, hfl⟩ := hov
  have hre : ∀ g, s'.r g = s.r (resQ T.F g) := fun g => by rw [hr]; rfl
  have diag : ∀ g i, s.r g i i = a (chi D T.pr i g) := hs.res.res.diag
  have ne0 : ∀ g i, s.r g i i ≠ 0 := fun g i => by
    rw [diag]; exact ((chi D T.pr i g).isUnit.map a).ne_zero
  have low : IsLow (s.n ()) := hs.res.pair.low ()
  have low' : ∀ v, IsLow (s'.n v) := hres.pair.low

  have key : ∀ i j, i ≠ j → (∀ g h, s.r (g * h) i j = s.r g i i * s.r h i j + s.r g i j * s.r h j j) →
      (∀ g, s'.r g i j = 0) → ∀ g, s.r g i j = 0 := by
    intro i j hij hc h0
    refine coc_zero a (chi D T.pr i) (chi D T.pr j) (fun g => s.r g i j) (fun g h => by rw [hc, diag, diag])
      (resQ T.F T.g0) (ne_of_res a (hT.1.dist i j hij)) fun g => ?_
    obtain ⟨h', e⟩ := conj_mem T.F T.g0 g
    rw [← e, ← hre]
    exact h0 h'
  have z : ∀ g i j, i ≠ j → wt i j ∉ nP → s.r g i j = 0 := hs.supp
  have ff : ∀ v, ∃ g, s'.n v 2 1 = 0 ∧ s'.n v 2 0 * s.r g 0 0 = s.r g 2 0 + s.r g 2 2 * s.n () 2 0 := by
    intro v
    obtain ⟨u, g, -, hu⟩ := hfl v
    have := flag_facts (s.n ()) (s'.n v) (s.r g) low hs.flag (low' v) (hs.supp g) (ne0 g 1) hu
    exact ⟨g, this.1, this.2.1⟩
  have hq : ∀ v, SuppM qQ (s'.n v) := by
    intro v i j hij hw
    obtain ⟨g, h21, -⟩ := ff v
    have : i < j ∨ (i = 2 ∧ j = 1) := by revert i j; decide
    rcases this with h | ⟨rfl, rfl⟩
    · exact (low' v).2.2 i j h
    · exact h21
  refine ⟨⟨⟨hres.pair.mult, fun g hg => hres.pair.kill g ?_, hres.pair.nrm, hres.pair.low, hres.pair.flag, hres.pair.mu⟩,
    ⟨hres.res.diag, hres.res.char, hres.res.shape⟩, hres.cont⟩, ⟨fun g => by rw [hre]; exact hs.supp _, hq⟩, ?_⟩
  · obtain ⟨A, hA, h⟩ := hg
    exact ⟨A, fun p hp => hA p (Finset.insert_subset_insert l (Finset.empty_subset W) hp), h⟩
  rcases hs.ps with hps | ⟨hv, h20, -, hnc⟩
  · left
    constructor
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hps
      refine hg (key i j ?_ (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, i, j, hw, h⟩) g)
      · clear hg; revert i j; decide
      · have : (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by clear hg; revert i j; decide
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four]
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [z g 2 1 (by decide) (by decide), z g 2 3 (by decide) (by decide)]; ring
        · rw [z h 0 1 (by decide) (by decide), z h 2 1 (by decide) (by decide)]; ring
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hs.be
      have : i = 1 ∧ j = 2 := by clear hg; revert i j; decide
      obtain ⟨rfl, rfl⟩ := this
      refine hg (key 1 2 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 2, hw, h⟩) g)
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z h 0 2 (by decide) (by decide), z g 1 3 (by decide) (by decide)]
      ring
  · right
    have y0 : ∀ g, s.r g 2 0 = 0 := fun g => hv g 2 0 (by decide) (by decide)
    refine ⟨⟨fun g => by rw [hre]; exact hv _, fun v => ⟨hq v, fun h => ?_⟩⟩, ?_⟩
    · obtain ⟨g, -, e⟩ := ff v
      have h' : s'.n v 2 0 = 0 := h
      rw [h', y0, zero_mul, zero_add] at e
      exact mul_ne_zero (ne0 g 2) h20 e.symm
    · by_contra hn
      have x0 : ∀ g, s.r g 1 0 = 0 := by
        refine key 1 0 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 0, by decide, h⟩)
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, y0, z g 1 3 (by decide) (by decide)]
        ring
      refine hnc ⟨s.n () 1 0 / s.n () 2 0, fun g hg => ?_⟩
      obtain ⟨-, e1, e2⟩ := flag_facts (s.n ()) (s.n ()) (s.r g) low hs.flag low (hs.supp g) (ne0 g 1)
        (hs.res.pair.flag () g hg)
      rw [y0, zero_add, mul_comm] at e1
      have e3 := mul_right_cancel₀ h20 e1
      rw [x0, e3] at e2
      rw [← diag, ← diag]
      field_simp
      linear_combination -e2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ConTrace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem con_span {K Γ n : Type} [Field K] [Group Γ] [Fintype n] [DecidableEq n] [Nontrivial n]
    (σ : Γ → Matrix n n K) (hm : ∀ g h, σ (g * h) = σ g * σ h) (hs : Submodule.span K (Set.range σ) = ⊤)
    (P : Matrix n n K) (hP : IsUnit P)
    (ht : ∀ x g h, (P * σ (x * (g * h))).trace = (P * σ (x * (h * g))).trace) : False := by
  have h1 : ∀ g h, σ g * σ h = σ h * σ g := fun g h => by
    have h2 : ∀ M : Matrix n n K, (P * (M * (σ g * σ h))).trace = (P * (M * (σ h * σ g))).trace := fun M => by
      have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem M hM => obtain ⟨x, rfl⟩ := hM; simpa only [hm] using ht x g h
      | zero => simp
      | add a b _ _ ha hb => simp only [add_mul, mul_add, Matrix.trace_add, ha, hb]
      | smul c a _ ha => simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, ha]
    obtain ⟨u, rfl⟩ := hP
    ext i j
    have := h2 (((u⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) * Matrix.single j i (1 : K))
    simpa only [mul_assoc, Units.mul_inv_cancel_left, Matrix.trace_single_mul, one_smul, smul_eq_mul, one_mul] using this
  have h3 : ∀ M N : Matrix n n K, M * N = N * M := fun M N => by
    have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    have hN : N ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    induction hM, hN using Submodule.span_induction₂ with
    | mem_mem a b ha hb => obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact h1 x y
    | zero_left => simp
    | zero_right => simp
    | add_left a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | add_right a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | smul_left r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
    | smul_right r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  have := congrFun (congrFun (h3 (Matrix.single i j 1) (Matrix.single j j 1)) i) j
  simp [hij, hij.symm] at this

private def con_e : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private theorem con_block {K Γ : Type} [Field K] [Group Γ] (r : Γ →* M4 K)
    (ht : ∀ x g h, (r (x * (g * h))).trace = (r (x * (h * g))).trace) (g0 : Γ) (hg : Squarefree (r g0).charpoly) :
    ¬ BlockExt r := by
  rintro ⟨h0, hs, -⟩
  have z : ∀ g (i j : Fin 2), r g (ixA i) (ixB j) = 0 := fun g i j => h0 g _ _ (by revert i j; decide)
  obtain ⟨A, hA⟩ : ∃ A : Γ → Matrix (Fin 2) (Fin 2) K, A = fun g => (r g).submatrix ixA ixA := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Γ → Matrix (Fin 2) (Fin 2) K, B = fun g => (r g).submatrix ixB ixB := ⟨_, rfl⟩
  rw [← hB] at hs
  have fb : ∀ g, (r g).submatrix con_e con_e = Matrix.fromBlocks (A g) 0 ((r g).submatrix ixB ixA) (B g) := fun g => by
    subst hA hB
    ext (i | i) (j | j)
    · rfl
    · exact z g i j
    · rfl
    · rfl
  have mAB : ∀ g h, A (g * h) = A g * A h ∧ B (g * h) = B g * B h := fun g h => by
    have h1 := fb (g * h)
    rw [map_mul, ← Matrix.submatrix_mul_equiv _ _ _ con_e, fb, fb, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1
    obtain ⟨h2, -, -, h3⟩ := h1
    rw [Matrix.zero_mul, add_zero] at h2
    rw [Matrix.mul_zero, zero_add] at h3
    exact ⟨h2.symm, h3.symm⟩
  have mA := fun g h => (mAB g h).1
  have mB := fun g h => (mAB g h).2
  have tr : ∀ g, (r g).trace = (A g).trace + (B g).trace := fun g => by
    subst hA hB
    rw [Matrix.trace, ← Equiv.sum_comp con_e, Fintype.sum_sum_type]
    rfl
  have cp : (r g0).charpoly = (A g0).charpoly * (B g0).charpoly := by
    rw [← Matrix.charpoly_fromBlocks_zero₁₂, ← fb, ← Matrix.charpoly_reindex con_e.symm]
    rfl
  have ev : ∀ M : Matrix (Fin 2) (Fin 2) K, aeval M (A g0).charpoly = M * M - (A g0).trace • M + (A g0).det • 1 := fun M => by
    rw [Matrix.charpoly_fin_two]
    simp [Algebra.algebraMap_eq_smul_one, sq]
  have hU : IsUnit (aeval (B g0) (A g0).charpoly) := by
    rw [cp] at hg
    obtain ⟨u, v, huv⟩ := (IsRelPrime.of_squarefree_mul hg).isCoprime
    have := congrArg (aeval (B g0)) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact IsUnit.of_mul_eq_one_right _ this
  have key : ∀ y, (aeval (B g0) (A g0).charpoly * B y).trace =
      (r (g0 * g0 * y)).trace - (A g0).trace * (r (g0 * y)).trace + (A g0).det * (r y).trace := fun y => by
    have h1 : (aeval (A g0) (A g0).charpoly * A y).trace = 0 := by rw [Matrix.aeval_self_charpoly]; simp
    rw [ev] at h1 ⊢
    simp only [tr, mA, mB, add_mul, sub_mul, smul_mul_assoc, one_mul, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul] at h1 ⊢
    linear_combination -h1
  refine con_span B mB hs _ hU fun x g h => ?_
  rw [key, key, ht x, ← mul_assoc g0 x, ← mul_assoc g0 x, ht (g0 * x), ← mul_assoc _ x, ← mul_assoc _ x, ht (g0 * g0 * x)]

private theorem con_trace {K : Type} [Field K] [IsAlgClosed K] {l : ℕ} [Fact l.Prime] [CharP K l] (V : ValuationSubring K)
    (M : M4 V) (d : Fin 4 → V) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hd : ∀ i, d i ^ m = 1)
    (hr : ∀ i, M i i - d i ∈ maximalIdeal V)
    (hc : ((M.map V.subtype) ^ N).charpoly = ∏ i, (X - C ((d i : K) ^ N))) : M.trace = ∑ i, d i := by
  haveI : CharP V l := RingHom.charP V.subtype Subtype.val_injective l
  letI : Algebra (ZMod l) V := ZMod.algebra V l
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let φ : V →ₐ[ZMod l] K := { V.subtype with commutes' := fun x => RingHom.congr_fun (RingHom.ext_zmod (V.subtype.comp (algebraMap _ _)) (algebraMap _ _)) x }
  have hdi : ∀ i, IsIntegral (ZMod l) (d i : K) := fun i => IsIntegral.of_pow hm (by
    have : (d i : K) ^ m = 1 := by exact_mod_cast congrArg Subtype.val (hd i)
    rw [this]; exact isIntegral_one)
  have h1 : IsIntegral (ZMod l) (M.map V.subtype).trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun x hx => IsIntegral.of_pow hN ?_
    have h2 : x ∈ spectrum K (M.map V.subtype) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hx)
    have h3 := Matrix.mem_spectrum_iff_isRoot_charpoly.1 (spectrum.pow_mem_pow _ N h2)
    rw [hc, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at h3
    obtain ⟨i, -, hi⟩ := h3
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    rw [hi]; exact (hdi i).pow N
  have h4 : IsIntegral (ZMod l) (M.trace - ∑ i, d i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← isIntegral_algHom_iff φ Subtype.val_injective, map_sub, map_sum]
    refine IsIntegral.sub ?_ (IsIntegral.sum _ fun i _ => hdi i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace, map_sum]
    exact h1
  have h5 : M.trace - ∑ i, d i ∈ maximalIdeal V := by
    rw [Matrix.trace, ← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun i _ => hr i
  by_contra hne
  exact h5 (h4.isUnit (sub_ne_zero.2 hne))

private theorem con_kill {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) [CharP 𝔞.K l] (c : Coef l) (x y : c.O)
    (h : residue c.O x = residue c.O y) : 𝔞.a c x = 𝔞.a c y := by
  haveI : CharP 𝔞.V l := RingHom.charP 𝔞.V.subtype Subtype.val_injective l
  have h1 : RingHom.ker (𝔞.a c) ≠ ⊥ := fun h0 => by
    have h2 : (l : c.O) ∈ RingHom.ker (𝔞.a c) := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h0, Ideal.mem_bot] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  have h3 : RingHom.ker (𝔞.a c) = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal h1)
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, h3]
  exact Ideal.Quotient.eq.1 h

private theorem con_const {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} {ι : PadicAlgCl l ≃+* ℂ} {𝔞 : Amb l} [CharP 𝔞.K l] {r : G ℚ Ω →* M4 𝔞.V} (hp : ProMod D ι 𝔞 r) :
    ∃ T : Tower D, T.Ok ∧ ∀ g : G T.F Ω, (mapRep 𝔞.toK r (resQ T.F g)).charpoly =
      ∏ i, (X - C (𝔞.toK (𝔞.a c (chi D T.pr i (resQ T.F g))))) := by
  obtain ⟨T, c', h, Y, J, y, r₁, ⟨hok, -⟩, -, hpm, hy, -, hJ, ⟨u, hu⟩, -, hr, hψ⟩ := hp
  refine ⟨T, hok, fun g => ?_⟩
  obtain ⟨n, hn⟩ := hpm.fin
  have hy' : ∀ x, (y.comp (algebraMap Y.B Y.A)) (algebraMap c'.O Y.B x) = 𝔞.a c' x := fun x => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← hy, RingHom.comp_apply]
  have h1 : maximalIdeal Y.B ^ n ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) := by
    refine hn.trans (sup_le (sup_le (fun b hb => hJ b hb) ?_) ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, hy', ← map_zero (𝔞.a c')]
      exact con_kill 𝔞 c' _ _ (by rw [map_zero, residue_eq_zero_iff]; exact hx)
    · rw [Ideal.span_le]
      rintro _ ⟨v, i, s, hs, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, RingHom.comp_apply, Y.ψ_map v i s (Ine_le_Dec _ hs),
        hψ v i s hs, sub_eq_zero, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have h2 := congrFun (congrFun (hok.ineL _ (T.ovl v) s hs) i) i
      rw [Matrix.one_apply_eq] at h2
      rw [map_one, ← h2]
      simp [Raw.rbar, Raw.r0, diagRep]
  have h2 : maximalIdeal Y.B ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    (RingHom.ker_isPrime _).le_of_pow_le h1
  have h3 : RingHom.ker (res c'.O Y.B : Y.B →+* ResidueField c'.O) ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    fun x hx => h2 ((res_eq_zero_iff c'.O Y.B x).1 hx)
  have hsurj : Function.Surjective (res c'.O Y.B : Y.B →+* ResidueField c'.O) := fun z => by
    obtain ⟨x, rfl⟩ := residue_surjective z
    exact ⟨algebraMap _ _ x, (res c'.O Y.B).commutes x⟩
  let j : ResidueField c'.O →+* 𝔞.V := RingHom.liftOfSurjective _ hsurj ⟨_, h3⟩
  have hj : j.comp (res c'.O Y.B : Y.B →+* ResidueField c'.O) = y.comp (algebraMap Y.B Y.A) :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  have hj' : ∀ x, j (residue c'.O x) = 𝔞.a c' x := fun x => by
    rw [← hy', ← hj, RingHom.comp_apply]
    exact congrArg j ((res c'.O Y.B).commutes x).symm
  have h4 : (r₁ (resQ T.F g)).charpoly = ∏ i, (X - C (𝔞.a c (chi D T.pr i (resQ T.F g)))) := by
    have h5 : r₁ (resQ T.F g) = (Y.P.r g).map y := DFunLike.congr_fun hr g
    rw [h5, Matrix.charpoly_map, ← Y.cp_map, Polynomial.map_map, ← hj, ← Polynomial.map_map, Y.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj']
    exact congrArg (fun t => X - C t) (𝔞.compat c c' h _)
  have h6 : mapRep 𝔞.toK r₁ (resQ T.F g) = (r₁ (resQ T.F g)).map 𝔞.toK := rfl
  have h7 := congrArg Matrix.charpoly (hu (resQ T.F g))
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, h6, Matrix.charpoly_map, h4, Polynomial.map_prod] at h7
  rw [← h7]
  simp only [Polynomial.map_sub, map_X, map_C]

theorem UpperTheory.V.Ws.con :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l), CharP 𝔞.K l → ∀ r u, KPair D 𝔞 r u → ProMod D ι 𝔞 r → ¬ Star (mapRep 𝔞.toK r) := by
  intro Ω _ _ _ l _ c D _ ι 𝔞 hch r u hk hp
  obtain ⟨T, hok, hc⟩ := con_const hp
  have hlab : Function.Bijective (lab T.pr) := by cases T.pr <;> decide
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsGalois ℚ Ω := {}
  have htr : ∀ g, (r g).trace = ∑ i, 𝔞.a c (D.ps i g) := fun g => by
    have hi : T.F.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact Module.finrank_pos.ne'
    obtain ⟨N, hN, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
    obtain ⟨g', hg'⟩ : ∃ g' : G T.F Ω, resQ T.F g' = g ^ N := ⟨T.F.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
    refine con_trace (l := l) 𝔞.V (r g) _ (Nat.card (ResidueField c.O)ˣ) N Nat.card_pos hN (fun i => ?_) (fun i => ?_) ?_
    · rw [← map_pow, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have := congrArg Units.val (pow_card_eq_one' (x := Units.map (residue c.O : c.O →* ResidueField c.O) (D.ps i g)))
      rw [Units.val_pow_eq_pow_val] at this
      rw [map_pow, map_one]
      exact this
    · simpa [Raw.r0, diagRep] using hk.red g i i
    · have h1 := hc g'
      rw [hg', map_pow] at h1
      refine h1.trans ?_
      refine Eq.trans ?_ (hlab.prod_comp _)
      simp [chi]
  have ht : ∀ x g h, (mapRep 𝔞.toK r (x * (g * h))).trace = (mapRep 𝔞.toK r (x * (h * g))).trace := fun x g h => by
    have h1 : ∀ y, (mapRep 𝔞.toK r y).trace = 𝔞.toK (r y).trace := fun y => by simp [Matrix.trace]
    rw [h1, h1, htr, htr]
    simp only [map_mul, mul_comm (D.ps _ g) (D.ps _ h)]
  rintro (h | h)
  · exact con_span (mapRep 𝔞.toK r) (map_mul _) h 1 isUnit_one (by simpa only [one_mul] using ht)
  · refine con_block _ ht (resQ T.F T.g0) ?_ h
    rw [hc]
    refine (separable_prod_X_sub_C_iff.2 fun i j hij => ?_).squarefree
    by_contra hne
    have h1 : 𝔞.a c (chi D T.pr i (resQ T.F T.g0) - chi D T.pr j (resQ T.F T.g0) : c.O) = 0 := by
      rw [map_sub, sub_eq_zero]; exact Subtype.val_injective hij
    refine hok.dist i j hne (Ideal.Quotient.eq.2 fun hu => ?_)
    exact not_isUnit_zero (h1 ▸ hu.map (𝔞.a c))
end
