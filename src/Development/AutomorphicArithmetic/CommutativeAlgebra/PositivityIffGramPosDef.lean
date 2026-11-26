module

public import Development.AutomorphicArithmetic.RealSpanData.RealData

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PzIffPos
noncomputable def UpperTheory.Reformulated.B.Qh60.Pz :
    {R : Type} → [inst : Ring R] → [Algebra ℝ R] → R → Prop :=
    fun {R : Type} [Ring R] [Algebra ℝ R] (t : R) ↦
      ∃ (s : Finset ℝ),
        (∀ l ∈ s, (0 : ℝ) < l) ∧
          (Polynomial.aeval t : Polynomial ℝ → R) (∏ l ∈ s, (Polynomial.X - (Polynomial.C : ℝ → Polynomial ℝ) l)) = (0 : R)

private theorem UpperTheory.Reformulated.B.Qh60.aux {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ x : W, x ≠ 0 → 0 < inner ℝ (T x) x := by
  classical
  have hn : Module.finrank ℝ W = Module.finrank ℝ W := rfl
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have hev : ∀ i, Module.End.HasEigenvector T (μ i) (b i) := fun i => by
    simpa using hT.hasEigenvector_eigenvectorBasis hn i
  have happ : ∀ i, T (b i) = μ i • b i := fun i => (hev i).apply_eq_smul
  have hne : ∀ i, b i ≠ 0 := fun i => (hev i).2
  have haev : ∀ (s : Finset ℝ) i,
      (Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))) (b i)
        = (∏ l ∈ s, (μ i - l)) • b i := fun s i => by
    rw [Module.End.aeval_apply_of_hasEigenvector (hev i)]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨s, hs, h0⟩ x hx
    have hpos : ∀ i, 0 < μ i := fun i => by
      have h1 := haev s i
      rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
      obtain ⟨l, hl, h2⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_right (hne i))
      rw [sub_eq_zero.1 h2]
      exact hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (b i), happ i, real_inner_smul_right, real_inner_comm (b i) x]
      ring
    have hex : ∃ i, inner ℝ (b i) x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← b.sum_repr' x]
      simp [hc]
    obtain ⟨i, hi⟩ := hex
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hpos i) (by positivity)⟩
  · intro h
    refine ⟨Finset.univ.image μ, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      have h1 := h (b i) (hne i)
      rw [happ i, real_inner_smul_left] at h1
      exact (pos_iff_pos_of_mul_pos h1).2 (real_inner_self_pos.2 (hne i))
    · refine b.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, haev, LinearMap.zero_apply,
        Finset.prod_eq_zero (Finset.mem_image_of_mem μ (Finset.mem_univ i)) (sub_self _), zero_smul]

theorem UpperTheory.Reformulated.B.Qh60.Pz_iff_pos :
    ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : _root_.Module ℝ W] [FiniteDimensional ℝ W] (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ),
      (∀ (x y : W), ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) y : W → ℝ) x) →
        (∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) x) →
          ∀ (T : Module.End ℝ W),
            (∀ (x y : W),
                ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) ((T : W → W) y)) →
              (UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) x) := by
  intro W _ _ _ Q hsymm hpos T hT
  let c : InnerProductSpace.Core ℝ W :=
    { inner := fun x y => Q x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hpos x h).ne' hx }
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ c
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore c.toCore
  exact UpperTheory.Reformulated.B.Qh60.aux T (fun x y => hT x y)
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def Pz {R : Type} [Ring R] [Algebra ℝ R] (t : R) : Prop :=
  ∃ s : Finset ℝ, (∀ l ∈ s, 0 < l) ∧
    Polynomial.aeval t (∏ l ∈ s, (Polynomial.X - Polynomial.C l)) = 0

private theorem Pz_map_iff {R R' : Type} [Ring R] [Algebra ℝ R] [Ring R'] [Algebra ℝ R']
    (f : R →ₐ[ℝ] R') (hf : Function.Injective f) (t : R) : Pz (f t) ↔ Pz t := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, hf ?_⟩
    rw [← Polynomial.aeval_algHom_apply, h, map_zero]
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [Polynomial.aeval_algHom_apply, h, map_zero]

private theorem Pz_pi {I M : Type} [Fintype I] [Ring M] [Algebra ℝ M] (t : I → M) :
    Pz t ↔ ∀ i, Pz (t i) := by
  constructor
  · rintro ⟨s, hs, h⟩ i
    refine ⟨s, hs, ?_⟩
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t
      (∏ l ∈ s, (Polynomial.X - Polynomial.C l))
    rw [h, map_zero] at this
    exact this
  · intro h
    choose s hs h0 using h
    refine ⟨Finset.univ.biUnion s, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hl
      exact hs i l hi
    · funext i
      have hsub : s i ⊆ Finset.univ.biUnion s := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : I => M) i) t
        (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l))
      have e : Polynomial.aeval (t i) (∏ l ∈ Finset.univ.biUnion s, (Polynomial.X - Polynomial.C l)) = 0 := by
        rw [← Finset.prod_sdiff hsub, map_mul, h0 i, mul_zero]
      exact this.symm.trans e

private theorem Pz_iff_pos {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsym : ∀ x y, Q x y = Q y x) (hpos : ∀ x, x ≠ 0 → 0 < Q x x)
    (T : Module.End ℝ W) (hT : ∀ x y, Q (T x) y = Q x (T y)) :
    Pz T ↔ ∀ x, x ≠ 0 → 0 < Q (T x) x :=
  _root_.UpperTheory.Reformulated.B.Qh60.Pz_iff_pos Q hsym hpos T hT

private theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : ℝ) (c : C) (v : V) :
    actOn rep ℝ (r ⊗ₜ c) (s ⊗ₜ v) = (r * s) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one]
  change r • (((1 : Module.End ℝ (ℝ ⊗[ℚ] V))) ((rep c).baseChange ℝ (s ⊗ₜ v))) = _
  rw [LinearMap.baseChange_tmul, Module.End.one_apply, TensorProduct.smul_tmul', smul_eq_mul]

private theorem actOn_inj {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) :
    Function.Injective (actOn rep ℝ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  let B := Module.Free.chooseBasis ℚ ℝ
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left B x
  have hc : c = 0 := by
    ext i
    apply hrep
    rw [Finsupp.zero_apply, map_zero]
    refine LinearMap.ext fun v => ?_
    have h1 : actOn rep ℝ (c.sum fun i n => B i ⊗ₜ[ℚ] n) ((1 : ℝ) ⊗ₜ[ℚ] v) = 0 := by rw [hx]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum, LinearMap.sum_apply] at h1
    simp only [actOn_tmul, _root_.mul_one] at h1
    have h2 : ((c.mapRange (fun y => rep y v) (by simp)).sum fun i n => B i ⊗ₜ[ℚ] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h1
    have h3 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h2
    simpa using DFunLike.congr_fun h3 i
  simp [hc]

private theorem bc_anti {R A M : Type} [CommRing R] [CommRing A] [AddCommGroup M] [Algebra R A]
    [Module R M] (B : LinearMap.BilinForm R M) (h : ∀ x y, B x y = -B y x) (x y : A ⊗[R] M) :
    B.baseChange A x y = -B.baseChange A y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd]; ring
    | tmul a' m' =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h m m', neg_smul,
        mul_comm]

private theorem E_anti {p : ℕ} [Fact p.Prime] (D : Datum p) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ x y = -(D.EF.baseChange ℚ).baseChange ℝ y x := by
  have h0 : ∀ x y, D.EF x y = -D.EF y x := by
    intro x y
    have := D.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt] at this
    linarith
  exact bc_anti _ (bc_anti _ h0) x y

private theorem E_adj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    (b : ℝ ⊗[ℚ] G.C) (x y : ℝ ⊗[ℚ] VQ D) :
    (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) y =
      (D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ (starT G.star ℝ b).unop y) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add b b' h h' => simp only [map_add (f := _), LinearMap.add_apply, MulOpposite.unop_add, h, h']
  | tmul r c =>
    rw [starT_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
    | tmul s v =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
      | tmul t w =>
        have h := L.adj c v w
        rw [show sh G c = (G.star c).unop from rfl] at h
        rw [actOn_tmul, actOn_tmul, LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, h]
        congr 1
        ring

private theorem herm_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (x y : Fin n → ℂ) : star (star x ⬝ᵥ A *ᵥ y) = star y ⬝ᵥ A *ᵥ x := by
  rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]

private theorem Pz_matrix {n : ℕ} (H M : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hS : (H * M).IsHermitian) : Pz M ↔ (H * M).PosDef := by
  let π : Matrix (Fin n) (Fin n) ℂ →ₐ[ℝ] Module.End ℝ (Fin n → ℂ) :=
    AlgHom.ofLinearMap
      { toFun := fun m => (Matrix.mulVecLin m).restrictScalars ℝ
        map_add' := fun a b => LinearMap.ext fun x => by simp [Matrix.add_mulVec]
        map_smul' := fun r a => LinearMap.ext fun x => by simp [Matrix.smul_mulVec] }
      (LinearMap.ext fun x => by simp)
      (fun a b => LinearMap.ext fun x => by
        change (a * b) *ᵥ x = a *ᵥ (b *ᵥ x)
        rw [Matrix.mulVec_mulVec])
  have hπ : ∀ m x, π m x = m *ᵥ x := fun _ _ => rfl
  have hπi : Function.Injective π := fun a b hab =>
    Matrix.mulVec_injective (funext fun x => by rw [← hπ, ← hπ, hab])
  have hHh : H.IsHermitian := (Matrix.posDef_iff_dotProduct_mulVec.1 hH).1
  let Q : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star x ⬝ᵥ (H *ᵥ y)).re)
      (fun x x' y => by simp [star_add, add_dotProduct])
      (fun r x y => by simp [smul_dotProduct, star_smul])
      (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun r x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
  have hQ : ∀ x y, Q x y = (star x ⬝ᵥ (H *ᵥ y)).re := fun _ _ => rfl
  have hsym : ∀ x y, Q x y = Q y x := by
    intro x y
    rw [hQ, hQ, ← herm_conj H hHh y x]
    simp
  have hpos : ∀ x, x ≠ 0 → 0 < Q x x := fun x hx => by
    have := (Complex.lt_def.1 ((Matrix.posDef_iff_dotProduct_mulVec.1 hH).2 hx)).1
    rw [hQ]
    simpa using this
  have hT : ∀ x y, Q (π M x) y = Q x (π M y) := by
    intro x y
    rw [hQ, hQ, hπ, hπ, Matrix.mulVec_mulVec, ← herm_conj _ hS y x, ← Matrix.mulVec_mulVec,
      herm_conj H hHh, ← herm_conj H hHh, ← herm_conj H hHh]
  rw [← Pz_map_iff π hπi M, Pz_iff_pos Q hsym hpos (π M) hT, Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hS, fun x hx => ?_⟩
    have h1 := h x hx
    rw [hsym, hQ, hπ, Matrix.mulVec_mulVec] at h1
    have h2 := herm_conj _ hS x x
    refine Complex.lt_def.2 ⟨by simpa using h1, ?_⟩
    simpa using (Complex.conj_eq_iff_im.1 h2).symm
  · rintro ⟨-, h⟩ x hx
    rw [hsym, hQ, hπ, Matrix.mulVec_mulVec]
    simpa using (Complex.lt_def.1 (h hx)).1

theorem UpperTheory.positivity_iff_gram_posDef :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (b : ℝ ⊗[ℚ] G.C), (starT G.star ℝ b).unop = -b → ((∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) x) ↔ ∀ v' : InfinitePlace G.F, ((if v'.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I) • (G.gram v' * G.psiR v' b)).PosDef) := by
  intro p _ D G L b hb
  obtain ⟨J, hJJ, hJs, hJp, hJv⟩ := L.orient
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : FiniteDimensional ℝ (ℝ ⊗[ℚ] VQ D) := inferInstance
  let a : ℝ ⊗[ℚ] G.C := -(J * b)
  have hJa : J * a = b := by
    change J * -(J * b) = b
    rw [_root_.mul_neg, ← _root_.mul_assoc, hJJ, neg_mul, _root_.one_mul, neg_neg]
  have adjJ : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y =
      -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ J y) := fun x y => by
    rw [E_adj, hJs, map_neg, LinearMap.neg_apply, map_neg]
  have adjb : ∀ x y, (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) y =
      -(D.EF.baseChange ℚ).baseChange ℝ x (actOn L.rep ℝ b y) := fun x y => by
    rw [E_adj, hb, map_neg, LinearMap.neg_apply, map_neg]
  have hJaX : ∀ x, actOn L.rep ℝ J (actOn L.rep ℝ a x) = actOn L.rep ℝ b x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, hJa]
  let Q : (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ :=
    LinearMap.comp (show (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] (ℝ ⊗[ℚ] VQ D) →ₗ[ℝ] ℝ from (D.EF.baseChange ℚ).baseChange ℝ)
      (actOn L.rep ℝ J)
  have hQ : ∀ x y, Q x y = (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ J x) y := fun _ _ => rfl
  have hsym : ∀ x y, Q x y = Q y x := fun x y => by
    rw [hQ, hQ, adjJ, E_anti D x, neg_neg]
  have hT : ∀ x y, Q (actOn L.rep ℝ a x) y = Q x (actOn L.rep ℝ a y) := fun x y => by
    rw [hQ, hQ, hJaX, adjJ, hJaX, adjb]
  have hL : (∀ x : ℝ ⊗[ℚ] VQ D, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn L.rep ℝ b x) x) ↔ Pz a := by
    rw [← Pz_map_iff (actOn L.rep ℝ) (actOn_inj L.rep L.rep_inj) a, Pz_iff_pos Q hsym hJp _ hT]
    simp only [hQ, hJaX]
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : Function.Injective Ψ := G.psiR_pi_bijective.1
  rw [hL, ← Pz_map_iff Ψ hΨ a, Pz_pi]
  refine forall_congr' fun v => ?_
  set c : ℂ := if v.embedding (L.e D.ω) = D.ρc then -Complex.I else Complex.I with hc
  have hcs : star c = -c := by
    rw [hc]
    split_ifs <;> simp
  set h := G.gram v with hh
  set X := G.psiR v J with hX
  set Y := G.psiR v b with hY
  have hXX : X * X = -1 := by
    rw [hX, ← map_mul, hJJ, map_neg, map_one]
  have hM : Ψ a v = -(X * Y) := by
    change G.psiR v (-(J * b)) = _
    rw [map_neg, map_mul]
  have hHM : (c • (h * X)) * Ψ a v = c • (h * Y) := by
    rw [hM, smul_mul_assoc, _root_.mul_neg, _root_.mul_assoc, ← _root_.mul_assoc X X Y, hXX]
    simp
  have hhh : hᴴ = h := G.gram_herm v
  have hinv : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (G.gram_det v))
  have hYs : h * (-Y) = Yᴴ * h := by
    have h1 := GlobalTheory.LKMid.psiR_starT G v b
    rw [hb, map_neg] at h1
    rw [h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hinv, _root_.one_mul]
  have hSh : (c • (h * Y)).IsHermitian := by
    change (c • (h * Y))ᴴ = _
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hhh, ← hYs, hcs]
    simp
  rw [← hHM] at hSh ⊢
  exact Pz_matrix _ _ (hJv v) hSh
