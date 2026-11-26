module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import ReciprocityTheory.SemistableReduction.SemiDegSt
public import ReciprocityTheory.SemistableReduction.SemiDegCE
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoeEqSpanDetOfIntVecLe
namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors

theorem relIndex_eq_of_hom {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup M'} (f : M →+ M')
    (hf : ∀ v ∈ A₂, f v ∈ B₂) (hker : ∀ v ∈ A₂, f v ∈ B₁ ↔ v ∈ A₁)
    (hsurj : ∀ u ∈ B₂, ∃ v ∈ A₂, u - f v ∈ B₁) : A₁.relIndex A₂ = B₁.relIndex B₂ := by
  have h1 : A₁ ⊓ A₂ = B₁.comap f ⊓ A₂ := by
    ext v
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    exact ⟨fun h => ⟨(hker v h.2).2 h.1, h.2⟩, fun h => ⟨(hker v h.2).1 h.1, h.2⟩⟩
  have h2 : B₁ ⊔ A₂.map f = B₁ ⊔ B₂ := by
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left fun u hu => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hf v hv
    · obtain ⟨v, hv, h⟩ := hsurj u hu
      exact AddSubgroup.mem_sup.2 ⟨_, h, f v, ⟨v, hv, rfl⟩, sub_add_cancel _ _⟩
  rw [← AddSubgroup.inf_relIndex_right, h1, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_left, h2,
    AddSubgroup.relIndex_sup_left]

theorem relIndex_pi_univ {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (L' L : ∀ i, AddSubgroup (G i)) :
    (AddSubgroup.pi Set.univ L').relIndex (AddSubgroup.pi Set.univ L) =
      ∏ i, (L' i).relIndex (L i) := by
  let f : (AddSubgroup.pi Set.univ L) →+ (∀ i, L i ⧸ (L' i).addSubgroupOf (L i)) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y =>
    ⟨⟨fun i => (y i).out, fun i _ => (y i).out.2⟩, funext fun i => (y i).out_eq⟩
  have hc : (AddSubgroup.pi Set.univ L').addSubgroupOf (AddSubgroup.pi Set.univ L) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    refine forall_congr' fun i => ?_
    change _ ↔ (QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ :
      L i ⧸ (L' i).addSubgroupOf (L i)) = 0
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem card_eq_relIndex_of_reps {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun y : R => (QuotientAddGroup.mk ⟨y, hR y y.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨?_, ?_⟩
  · intro y y' h
    have h1 : (y : M) - y' ∈ A := by
      simpa [AddSubgroup.mem_addSubgroupOf] using QuotientAddGroup.eq_iff_sub_mem.1 h
    exact Subtype.ext ((hR' y (hR y y.2)).unique ⟨y.2, by simp⟩ ⟨y'.2, h1⟩)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, ⟨hr, h⟩, -⟩ := hR' y y.2
    refine ⟨⟨r, hr⟩, (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm⟩
    simpa [AddSubgroup.mem_addSubgroupOf] using h

theorem exists_reps_of_relIndex_ne_zero {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : A.relIndex B ≠ 0) :
    ∃ R : Finset M, (∀ y ∈ R, y ∈ B) ∧ ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A := by
  classical
  haveI : Fintype (B ⧸ A.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => (q.out : M), ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact q.out.2
  · have key : ∀ q : B ⧸ A.addSubgroupOf B,
        y - (q.out : M) ∈ A ↔ QuotientAddGroup.mk ⟨y, hy⟩ = q := fun q => by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      simp [AddSubgroup.mem_addSubgroupOf]
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key q).1 h]

section Period

variable {E : Type} [Field E] [NumberField E]

end Period

section Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Index

section Modulus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable [IsGalois ℚ E]

variable {K : Type*} [Field K] [Algebra E K]

end Modulus

section IndexIdeal

open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_coe_eq_span_det_of_intVec_le (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ :=
    ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.lattice_split K n X hfg hstd
  let CF : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  refine ⟨∏ i, CF i, ?_, ?_⟩
  · rw [coe_prod_frac]
    change ∏ i, C i = _
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [prod_eq_span_prod]
      refine Submodule.span_mono fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine ⟨fun i => t i • z i, fun i => smul_mem_of_split hin i (ht i), ?_⟩
      have : (Matrix.of fun i => t i • z i) = Matrix.diagonal t * rowMat z := by
        ext i j
        simp [rowMat, Matrix.diagonal_mul]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, Matrix.det_diagonal, mul_one]
    · rintro _ ⟨v, hv, rfl⟩
      choose T hT hTv using fun i => hdec (v i) (hv i)
      have : Matrix.of v = Matrix.of T * rowMat z := by
        ext i j
        rw [Matrix.of_apply, hTv i]
        simp [rowMat, Matrix.mul_apply, Finset.sum_apply]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, mul_one, ← Matrix.det_transpose]
      exact det_mem_prod_sub C _ fun i j => hT j i
  · rw [hidx, map_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)

theorem exists_coe_eq_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by
  classical
  choose d hd0 hd using fun k : Fin n => exists_smul_mem_of_mem_span_fraction (K := K) Λ
    (Pi.single k (1 : K)) (hsp ▸ Submodule.mem_top)
  set δ : K := algebraMap (𝓞 K) K (∏ k, d k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ, Finset.prod_ne_zero_iff] using hd0
  let μ : (Fin n → K) →ₗ[𝓞 K] (Fin n → K) := (LinearMap.lsmul K _ δ).restrictScalars (𝓞 K)
  have hμ : ∀ x, μ x = δ • x := fun _ => rfl
  have hinj : Function.Injective μ := smul_right_injective _ hδ0
  have hsurj : Function.Surjective μ := fun x => ⟨δ⁻¹ • x, by rw [hμ, smul_inv_smul₀ hδ0]⟩
  have hstd : intVec K n ≤ Λ.comap μ := by
    intro x hx
    choose c hc using fun k => Submodule.mem_one.1 (mem_intVec.1 hx k)
    have : x = ∑ k, c k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, hμ, hδ, algebraMap_smul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Λ.smul_mem _ (hd k)
  have key : ∀ Y : Submodule (𝓞 K) (Fin n → K), Λ ≤ Y → Y.FG →
      ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Y) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex
        (Y.comap μ).toAddSubgroup : ℚ) = |Algebra.norm ℚ (δ ^ n)| := by
    intro Y hY hYfg
    obtain ⟨J, hJ, hN⟩ := exists_coe_eq_span_det_of_intVec_le (Y.comap μ)
      (Submodule.fg_of_fg_map_injective μ hinj
        (by rwa [Submodule.map_comap_eq_of_surjective hsurj]))
      (hstd.trans (Submodule.comap_mono hY))
    refine ⟨FractionalIdeal.spanSingleton _ (δ ^ n) * J, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, hJ, Submodule.span_mul_span,
        Set.singleton_mul]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨δ • v, hv, ?_⟩
        change _ = (δ • Matrix.of v).det
        rw [Matrix.det_smul, Fintype.card_fin]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨_, ⟨δ⁻¹ • v, fun i => ?_, rfl⟩, ?_⟩
        · rw [Submodule.mem_comap, hμ, Pi.smul_apply, smul_inv_smul₀ hδ0]
          exact hv i
        · change _ * (δ⁻¹ • Matrix.of v).det = _
          rw [Matrix.det_smul, Fintype.card_fin, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hδ0)]
    · rw [map_mul, mul_assoc, hN, mul_one, FractionalIdeal.absNorm_span_singleton]
  obtain ⟨J, hJ, hN⟩ := key Λ le_rfl (hfg.of_le hle)
  obtain ⟨J', hJ', hN'⟩ := key Λ' hle hfg
  have hn0 : |Algebra.norm ℚ (δ ^ n)| ≠ 0 :=
    abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (pow_ne_zero _ hδ0))
  have hidx : (Λ.comap μ).toAddSubgroup.relIndex (Λ'.comap μ).toAddSubgroup =
      Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup := by
    change (Λ.toAddSubgroup.comap μ.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.comap μ.toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have htower := AddSubgroup.relIndex_mul_relIndex (intVec K n).toAddSubgroup
    (Λ.comap μ).toAddSubgroup (Λ'.comap μ).toAddSubgroup hstd (Submodule.comap_mono hle)
  refine ⟨J, J', ?_, ?_, hJ, hJ', ?_⟩
  · rintro rfl
    rw [map_zero, zero_mul] at hN
    exact hn0 hN.symm
  · rintro rfl
    rw [map_zero, zero_mul] at hN'
    exact hn0 hN'.symm
  · rw [← htower, hidx, Nat.cast_mul, ← hN] at hN'
    refine mul_right_cancel₀ (right_ne_zero_of_mul (hN ▸ hn0)) ?_
    linear_combination -hN'

attribute [local instance] extModR

end IndexIdeal

section Main

open ReciprocityTheory.PGsh

attribute [local instance] extModR

end Main

end GlobalTheory.TensorLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelTupleSumEqRational
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.LevelTupleSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Gen (Λ : Submodule (𝓞 E) (Fin r → E)) (t : Fin r → Fin r → E) : Prop :=
  (∀ j, (25 : E) • t j ∈ Λ) ∧
    ∀ u ∈ Λ, ∃ c : Fin r → 𝓞 E, ∃ y ∈ Λ, u = ∑ j, (c j : E) • ((25 : E) • t j) + (5 : E) • y

omit [IsCMField E] in
theorem coe_smul_mem (Λ : Submodule (𝓞 E) (Fin r → E)) (c : 𝓞 E) {v : Fin r → E} (hv : v ∈ Λ) :
    (c : E) • v ∈ Λ := Λ.smul_mem c hv

omit [IsCMField E] in
theorem nat_smul_mem (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) {v : Fin r → E} (hv : v ∈ Λ) :
    (n : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv n

omit [IsCMField E] in
theorem Gen.of_sub {Λ : Submodule (𝓞 E) (Fin r → E)} {t t' : Fin r → Fin r → E} (h : Gen Λ t)
    (hs : ∀ j, t j - t' j ∈ Λ) : Gen Λ t' := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · have h1 : (25 : E) • (t j - t' j) ∈ Λ := by simpa using nat_smul_mem Λ 25 (hs j)
    have : (25 : E) • t' j = (25 : E) • t j - (25 : E) • (t j - t' j) := by module
    rw [this]
    exact Λ.sub_mem (h.1 j) h1
  · obtain ⟨c, y, hy, rfl⟩ := h.2 u hu
    refine ⟨c, y + ∑ j, (c j : E) • ((5 : E) • (t j - t' j)), Λ.add_mem hy (Λ.sum_mem fun j _ =>
      coe_smul_mem Λ _ (by simpa using nat_smul_mem Λ 5 (hs j))), ?_⟩
    rw [smul_add, Finset.smul_sum, add_comm ((5 : E) • y), ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    module

omit [IsCMField E] in
theorem exists_finite_res (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ S : Set (Fin r → E), S.Finite ∧ ∀ v, (25 : E) • v ∈ Λ → ∃ s ∈ S, v - s ∈ Λ := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ (n := 25) (by norm_num)
  refine ⟨Set.range fun q : Λ ⧸ (nsmulAddMonoidHom (α := Λ) 25).range =>
    (25 : E)⁻¹ • ((q.out : Λ) : Fin r → E), Set.finite_range _, fun v hv => ?_⟩
  obtain ⟨⟨z, y, hy⟩, hz⟩ := QuotientAddGroup.mk_out_eq_mul (nsmulAddMonoidHom (α := Λ) 25).range ⟨_, hv⟩
  refine ⟨_, ⟨QuotientAddGroup.mk ⟨_, hv⟩, rfl⟩, ?_⟩
  simp only [hz]
  subst hy
  have : v - (25 : E)⁻¹ • ((25 : E) • v + (25 : ℕ) • (y : Fin r → E)) = -(y : Fin r → E) := by
    rw [← Nat.cast_smul_eq_nsmul E, Nat.cast_ofNat, ← smul_add, inv_smul_smul₀ (by norm_num)]
    abel
  simp only [nsmulAddMonoidHom_apply, Submodule.coe_add, AddSubmonoidClass.coe_nsmul]
  rw [this]
  exact Λ.neg_mem y.2

omit [IsCMField E] in
theorem exists_reps (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ 𝒯 : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯, Gen Λ t) ∧
      ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ := by
  obtain ⟨S, hS, hres⟩ := exists_finite_res Λ hΛ
  let ρ : (Fin r → E) → (Fin r → E) := fun v => (Submodule.Quotient.mk (p := Λ) v).out
  have hρ : ∀ v, v - ρ v ∈ Λ := fun v => (Submodule.Quotient.eq Λ).1 (Submodule.Quotient.mk_out _).symm
  have hρe : ∀ v w, v - w ∈ Λ → ρ v = ρ w := fun v w h => by
    simp only [ρ, (Submodule.Quotient.eq Λ).2 h]
  have hfin : {t : Fin r → Fin r → E | Gen Λ t ∧ ∀ j, ρ (t j) = t j}.Finite := by
    refine (Set.Finite.pi' fun _ : Fin r => hS.image ρ).subset ?_
    rintro t ⟨hg, ht⟩ j
    obtain ⟨s, hs, h⟩ := hres _ (hg.1 j)
    exact ⟨s, hs, by rw [← hρe _ _ h, ht]⟩
  refine ⟨hfin.toFinset, fun t ht => (hfin.mem_toFinset.1 ht).1, fun t ht => ⟨fun j => ρ (t j),
    ⟨hfin.mem_toFinset.2 ⟨ht.of_sub fun j => hρ _, fun j => (hρe _ _ (hρ _)).symm⟩, fun j => hρ _⟩, ?_⟩⟩
  rintro t' ⟨h1, h2⟩
  funext j
  rw [hρe _ _ (h2 j), (hfin.mem_toFinset.1 h1).2 j]

theorem torus_r {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) : A.T.r = r := by
  obtain ⟨τ⟩ : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := A.T.dim_conj τ.1
  rw [A.dim_pos τ, A.dim_neg τ] at h
  have := X.p0_le
  omega

theorem map_injective {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x) :
    Function.Injective A.φ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have : Nonempty X.Ψ := Fintype.card_pos_iff.1 (QuadraticCoefficientForms.card_Psi_pos (X := X))
  have h := TorusAtDataPf.norm_sq_eq X x A v
  have hpos : 0 < ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    refine Finset.sum_pos (fun τ _ => mul_pos ?_ ?_) Finset.univ_nonempty
    · have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).2 X.ξ0_ne
      unfold Data.c
      positivity
    · refine X.maj_pos hx τ fun h0 => hne (funext fun a => ?_)
      exact (map_eq_zero τ.1).1 (congrFun h0 a)
  rw [← h, hv] at hpos
  simp at hpos

theorem map_nat_smul {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (n : ℕ) (v : Fin r → E) :
    A.φ ((n : E) • v) = (n : ℂ) • A.φ v := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem map_five {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (v : Fin r → E) :
    A.φ ((5 : E) • v) = (5 : ℂ) • A.φ v := by
  simpa only [Nat.cast_ofNat] using map_nat_smul A 5 v

theorem map_twentyfive {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (v : Fin r → E) :
    A.φ ((25 : E) • v) = ((5 : ℂ) ^ 2) • A.φ v := by
  rw [show (5 : ℂ) ^ 2 = 25 by norm_num]
  simpa only [Nat.cast_ofNat] using map_nat_smul A 25 v

theorem map_mem_iff {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x) (v : Fin r → E) :
    A.φ v ∈ A.T.L ↔ v ∈ X.Λ := by
  rw [A.lat]
  exact ⟨fun ⟨w, hw, h⟩ => map_injective hx A h ▸ hw, fun h => ⟨v, h, rfl⟩⟩

theorem gen_iff {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (t : Fin r → Fin r → E) :
    Gen X.Λ t ↔ (∀ j, ((5 : ℂ) ^ 2) • A.φ (t j) ∈ A.T.L) ∧ ∀ z ∈ A.T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ A.T.L,
      z = ∑ j, act (c j) (((5 : ℂ) ^ 2) • A.φ (t j)) + (5 : ℂ) • y := by
  have key : ∀ (c : Fin r → 𝓞 E) (y : Fin r → E),
      A.φ (∑ j, (c j : E) • ((25 : E) • t j) + (5 : E) • y) =
        ∑ j, act (c j) (((5 : ℂ) ^ 2) • A.φ (t j)) + (5 : ℂ) • A.φ y := by
    intro c y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_five]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [A.act_eq, map_twentyfive]
  refine and_congr (forall_congr' fun j => by rw [← map_twentyfive, map_mem_iff hx]) ⟨fun h z hz => ?_, fun h u hu => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (A.lat z).1 hz
    obtain ⟨c, y, hy, rfl⟩ := h u hu
    exact ⟨c, A.φ y, (map_mem_iff hx A y).2 hy, key c y⟩
  · obtain ⟨c, y, hy, e⟩ := h _ ((map_mem_iff hx A u).2 hu)
    obtain ⟨w, hw, rfl⟩ := (A.lat y).1 hy
    exact ⟨c, w, hw, map_injective hx A (by rw [key, e])⟩

theorem sum_eq {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen X.Λ t)
    (h2 : ∀ t, Gen X.Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ X.Λ) (n : ℕ) (hn : n = r) :
    (∑ᶠ (a : Fin n → Vsp A.T.dim) (_ : a ∈ {a : Fin n → Vsp A.T.dim |
      (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧
        ∀ x ∈ A.T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ A.T.L,
          x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}),
      ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) =
      ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s := by
  subst hn
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun t j => ZSpan.fract A.T.b (A.φ (t j))) ⟨?_, ?_, ?_⟩ ?_
  · intro t ht
    have hl : ∀ j, ∃ v ∈ X.Λ, A.φ v = (ZSpan.floor A.T.b (A.φ (t j)) : Vsp A.T.dim) := fun j =>
      (A.lat _).1 (ZSpan.floor A.T.b (A.φ (t j))).2
    choose v hv hv' using hl
    have e : ∀ j, ZSpan.fract A.T.b (A.φ (t j)) = A.φ (t j - v j) := fun j => by
      rw [ZSpan.fract_apply, map_sub, hv']
    refine ⟨fun j => ZSpan.fract_mem_fundamentalDomain _ _, ?_⟩
    simp only [e]
    exact (gen_iff hx A _).1 ((h1 t ht).of_sub fun j => by simpa using hv j)
  · intro t ht t' ht' h
    refine ((h2 t (h1 t ht)).unique ⟨ht, fun j => by simp⟩ ⟨ht', fun j => ?_⟩)
    have := (ZSpan.fract_eq_fract A.T.b _ _).1 (congrFun h j).symm
    rw [← map_mem_iff hx A, map_sub, sub_eq_neg_add]
    exact this
  · rintro a ⟨ha, hb, hc⟩
    choose v hv hv' using fun j => (A.lat _).1 (hb j)
    have e : ∀ j, A.φ ((25 : E)⁻¹ • v j) = a j := fun j => by
      have h5 : ((5 : ℂ) ^ 2) ≠ 0 := by norm_num
      refine smul_right_injective _ h5 ?_
      simp only
      rw [← map_twentyfive, smul_inv_smul₀ (by norm_num), hv']
    have hg : Gen X.Λ fun j => (25 : E)⁻¹ • v j := (gen_iff hx A _).2 (by simp only [e]; exact ⟨hb, hc⟩)
    obtain ⟨t', ⟨ht', hs⟩, -⟩ := h2 _ hg
    refine ⟨t', ht', funext fun j => ?_⟩
    show ZSpan.fract A.T.b (A.φ (t' j)) = a j
    rw [← (ZSpan.fract_eq_self (b := A.T.b)).2 (ha j), ZSpan.fract_eq_fract, ← e j, ← sub_eq_neg_add, ← map_sub]
    exact (map_mem_iff hx A _).2 (hs j)
  · intro t _
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    have := pointwiseNormSq_add_period A.T (n := 1) A.s_mem
      (γ := fun _ => (ZSpan.floor A.T.b (A.φ (t j)) : Vsp A.T.dim)) (fun _ => (ZSpan.floor A.T.b (A.φ (t j))).2)
      (fun _ => ZSpan.fract A.T.b (A.φ (t j)))
    rw [← this]
    congr 1
    funext k
    simp [ZSpan.fract_apply]

end GlobalTheory.LevelTupleSum
end
