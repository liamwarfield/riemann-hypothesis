module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingCount
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpan
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DiscOver

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def gram (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (w : ι → Fin n → E) :
    Matrix ι ι E := Matrix.of fun a b => hf L Hm (w b) (w a)

def comb {n m : ℕ} (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • w i

theorem hf_addl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smull (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_addr (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smulr (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_suml (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i, t i • w i) y = ∑ i, t i * hf L Hm (w i) y := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_addl, hf_smull, ih]

theorem hf_sumr (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i, t i • w i) = ∑ i, L.cj (t i) * hf L Hm y (w i) := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_addr, hf_smulr, ih]

theorem gram_comb (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gram L Hm (comb w A) = cT L A * (gram L Hm w * A) := by
  ext a b
  simp only [gram, comb, Matrix.of_apply, hf_sumr, hf_suml, Matrix.mul_apply, cT]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := by ext i j; rfl
  rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl

theorem comb_comb {n m : ℕ} (w : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    comb (comb w A) B = comb w (A * B) := by
  funext j
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem comb_one {n m : ℕ} (w : Fin m → Fin n → E) : comb w 1 = w := by
  funext j
  simp [comb, Matrix.one_apply, ite_smul]

theorem sum_comb {n m : ℕ} (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) (s : Fin m → E) :
    ∑ j, s j • comb w A j = ∑ i, (A.mulVec s) i • w i := by
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem hf_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (a : Fin m) :
    hf L Hm (∑ i, t i • w i) (w a) = ((gram L Hm w).mulVec t) a := by
  rw [hf_suml]
  simp only [gram, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem li_of_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (hu : IsUnit (gram L Hm w).det) : LinearIndependent E w := by
  rw [Fintype.linearIndependent_iff]
  intro t ht
  have h0 : (gram L Hm w).mulVec t = 0 := by
    funext a
    rw [← hf_gram, ht]; simp [hf]
  have h1 : t = (gram L Hm w)⁻¹.mulVec ((gram L Hm w).mulVec t) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  intro i
  rw [h1, h0]; simp

theorem mem_spanO (L : LocE F E) {n m : ℕ} (w : Fin m → Fin n → E) (x : Fin n → E) :
    x ∈ Submodule.span L.O (Set.range w) ↔ ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • w i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun i => s i, fun i => (s i).2, hs⟩
  · rintro ⟨s, h, hs⟩
    exact ⟨fun i => ⟨s i, h i⟩, hs⟩

theorem dual_iff (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (hu : IsUnit (gram L Hm w).det) (x : Fin n → E) :
    (x ∈ Submodule.span E (Set.range w) ∧ ∀ a, hf L Hm x (w a) ∈ L.O) ↔
      x ∈ Submodule.span L.O (Set.range (comb w (gram L Hm w)⁻¹)) := by
  rw [mem_spanO, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨⟨t, rfl⟩, h⟩
    refine ⟨(gram L Hm w).mulVec t, fun a => ?_, ?_⟩
    · rw [← hf_gram]; exact h a
    · rw [sum_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · rintro ⟨s, hs, rfl⟩
    rw [sum_comb]
    refine ⟨⟨_, rfl⟩, fun a => ?_⟩
    rw [hf_gram, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    exact hs a

theorem det_mem (O : Subring E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (h : ∀ i j, A i j ∈ O) :
    A.det ∈ O := by
  have : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : O)) := by ext i j; rfl
  rw [this, ← RingHom.map_det]
  exact Subtype.property _

theorem adj_mem (O : Subring E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (h : ∀ i j, A i j ∈ O)
    (i j : Fin m) : A.adjugate i j ∈ O := by
  have : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : O)) := by ext i j; rfl
  rw [this, ← RingHom.map_adjugate]
  exact Subtype.property _

theorem disc_fin [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m : ℕ}
    (v : Fin m → Fin n → E) (c : F) (hc : c ≠ 0) (hG : (gram L Hm v).det = algebraMap F E c)
    (Mh Md : Submodule L.O (Fin n → E)) (h1 : Submodule.span L.O (Set.range v) ≤ Mh)
    (h2 : ∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v))
    (h3 : ∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O)
    (h4 : ∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) :
    0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup *
      ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 =
      resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧
      (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧
      ∃ b : Fin m → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  obtain ⟨-, hcj, -, hPIR, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨hadd, -, hpos, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hcu : IsUnit (algebraMap F E c) := (IsUnit.mk0 c hc).map _
  have hu : IsUnit (gram L Hm v).det := hG ▸ hcu
  have hv : ∀ a, v a ∈ Mh := fun a => h1 (Submodule.subset_span ⟨a, rfl⟩)
  have hle : Mh ≤ Submodule.span L.O (Set.range (comb v (gram L Hm v)⁻¹)) := fun x hx =>
    (dual_iff L Hm v hu x).1 ⟨h2 x hx, fun a => h3 x hx _ (hv a)⟩
  have hfg : Mh.FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have hsp : Submodule.span E (Mh : Set (Fin n → E)) = Submodule.span E (Set.range v) := by
    apply le_antisymm
    · exact Submodule.span_le.2 h2
    · apply Submodule.span_mono; rintro _ ⟨a, rfl⟩; exact hv a
  obtain ⟨b, hb, hMh⟩ := GlobalTheory.OrderBasis.order_basis L v (li_of_gram L Hm v hu) Mh hfg hsp
  have hbm : ∀ a, b a ∈ Mh := fun a => hMh ▸ Submodule.subset_span ⟨a, rfl⟩
  have hA : ∀ j, ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • b i = v j := fun j =>
    (mem_spanO L b _).1 (hMh ▸ hv j)
  choose s hs hsv using hA
  set A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => s j i with hAdef
  have hvA : v = comb b A := by funext j; exact (hsv j).symm
  have hdet : (gram L Hm b).det * (A.det * L.cj A.det) = algebraMap F E c := by
    rw [← hG, hvA, gram_comb, Matrix.det_mul, Matrix.det_mul, det_cT]; ring
  obtain ⟨-, -, cA, hcA⟩ := hcj A.det (det_mem _ A fun i j => hs j i)
  have hprod : IsUnit ((gram L Hm b).det * (A.det * L.cj A.det)) := hdet ▸ hcu
  have hub : IsUnit (gram L Hm b).det := isUnit_of_mul_isUnit_left hprod
  have hnt : Nontrivial E := by
    have := L.free
    exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcA0 : (cA : F) ≠ 0 := by
    intro h0
    have := isUnit_of_mul_isUnit_right hprod
    rw [hcA, h0, map_zero] at this
    exact not_isUnit_zero this
  set c0 : F := c / cA with hc0def
  have hc0 : c0 ≠ 0 := div_ne_zero hc hcA0
  have hcc : c = c0 * cA := by rw [hc0def]; field_simp
  have hdb : (gram L Hm b).det = algebraMap F E c0 := by
    have hAu : IsUnit (algebraMap F E cA) := (IsUnit.mk0 _ hcA0).map _
    apply hAu.mul_right_cancel
    rw [← map_mul, ← hcc, ← hdet, hcA]
  have hc0int : c0 ∈ 𝒪[F] := (hint c0).1
    (hdb ▸ det_mem _ _ fun i j => h3 _ (hbm j) _ (hbm i))
  have hv0 := (hpos c0 hc0).2 hc0int
  have hvA0 := (hpos cA hcA0).2 cA.2
  have hvc : vE L ϖ (algebraMap F E c) = vE L ϖ (algebraMap F E c0) + vE L ϖ (algebraMap F E cA) := by
    rw [← hadd c0 cA hc0 hcA0, ← hcc]
  have hspb : Submodule.span E (Set.range b) = Submodule.span E (Set.range v) := by
    rw [← hsp, hMh, Submodule.span_span_of_tower]
  have hMd : Md = Submodule.span L.O (Set.range (comb b (gram L Hm b)⁻¹)) := by
    ext x
    rw [h4, ← dual_iff L Hm b hub, hspb]
    refine and_congr_right fun _ => ⟨fun h a => h _ (hbm a), fun h y hy => ?_⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L b _).1 (hMh ▸ hy)
    rw [hf_sumr]
    exact L.O.sum_mem fun i _ => L.O.mul_mem (hcj _ (ht i)).1 (h i)
  have hbd : b = comb (comb b (gram L Hm b)⁻¹) (gram L Hm b) := by
    rw [comb_comb, Matrix.nonsing_inv_mul _ hub, comb_one]
  have hud : IsUnit (gram L Hm (comb b (gram L Hm b)⁻¹)).det := by
    rw [gram_comb, Matrix.mul_nonsing_inv _ hub, mul_one, det_cT]
    exact (Matrix.isUnit_nonsing_inv_det _ hub).map _
  have hMM : Mh ≤ Md := fun x hx => (h4 x).2 ⟨h2 x hx, h3 x hx⟩
  obtain ⟨-, -, e1⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hb A cA hcA0 hcA Mh
    (Submodule.span L.O (Set.range v)) hMh (by rw [hvA]; rfl)
  obtain ⟨-, -, e2⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ _ (li_of_gram L Hm _ hud) (gram L Hm b) (c0 * c0)
    (mul_ne_zero hc0 hc0) (by rw [hdb, AlgEquiv.commutes, map_mul]) Md Mh hMd
    (by rw [hMh]; exact congrArg (fun w => Submodule.span L.O (Set.range w)) hbd)
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono h1)] at e1
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono hMM), hadd c0 c0 hc0 hc0] at e2
  refine ⟨by omega, ?_, ?_, _, hMd⟩
  · obtain ⟨k0, hk0⟩ := Int.eq_ofNat_of_zero_le hv0
    obtain ⟨kA, hkA⟩ := Int.eq_ofNat_of_zero_le hvA0
    rw [hvc, hk0, hkA]
    rw [hkA] at e1
    rw [hk0] at e2
    have : ((k0 : ℤ) + kA).toNat = k0 + kA := by omega
    rw [this]
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [e1, e2, ← Nat.cast_add, zpow_natCast, zpow_natCast]
    push_cast
    ring
  · intro x hx
    have hx' := (dual_iff L Hm v hu x).1 ⟨((h4 x).1 hx).1, fun a => ((h4 x).1 hx).2 _ (hv a)⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L _ _).1 hx'
    have hadj : algebraMap F E c • (gram L Hm v)⁻¹ = (gram L Hm v).adjugate := by
      rw [← hG, Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]
    rw [sum_comb, mem_spanO]
    refine ⟨(gram L Hm v).adjugate.mulVec t, fun i => ?_, ?_⟩
    · simp only [Matrix.mulVec, dotProduct]
      exact L.O.sum_mem fun j _ => L.O.mul_mem
        (adj_mem _ (gram L Hm v) (fun i j => h3 _ (hv j) _ (hv i)) i j) (ht j)
    · rw [← hadj, Matrix.smul_mulVec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; rfl

theorem disc_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ ϖ hϖ ι _ _ v c hc hG Mh Md h1 h2 h3 h4
  let e := (Fintype.equivFin ι).symm
  have hr : Set.range (v ∘ e) = Set.range v := e.surjective.range_comp v
  have hG' : (gram L Hm (v ∘ e)).det = algebraMap F E c := by
    rw [← hG, ← Matrix.det_submatrix_equiv_self e]; rfl
  have := disc_fin L Hm ϖ hϖ (v ∘ e) c hc hG' Mh Md (by rwa [hr]) (by rwa [hr]) h3 (by rwa [hr])
  rw [hr] at this
  obtain ⟨a1, a2, a3, b, hb⟩ := this
  exact ⟨a1, a2, a3, b ∘ e.symm, by rw [e.symm.surjective.range_comp b]; exact hb⟩

end GlobalTheory.DiscOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpanStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_discriminantModule_integralOverlattice_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.DiscOver.disc_overlattice | exact GlobalTheory.DiscOver.disc_overlattice | (intros; apply GlobalTheory.DiscOver.disc_overlattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingCount
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Gluing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem encard_le [IsNonarchimedeanLocalField F] [CharZero F] {L : LocE F E} {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHermND L Hm) {m : ℕ} {y : Fin m → Fin n → E}
    (hy : LinearIndependent E y) {Y : Submodule E (Fin n → E)}
    (hY : Submodule.span E (Set.range y) = Y) (hc : Y ⊔ perp L Hm Y = ⊤)
    (Mh Λ₀ Md : Submodule L.O (Fin n → E))
    (hMd : ∀ x, x ∈ Md ↔ x ∈ Y ∧ ∀ z ∈ Mh, hf L Hm x z ∈ L.O)
    {ι : Type} [Fintype ι] (b : ι → Fin n → E) (hb : Md = Submodule.span L.O (Set.range b))
    (hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0) :
    {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀}.encard ≤
      ((Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card ι : ℕ) : ℕ∞) := by
  set T := {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  have hsym : ∀ x v, hf L Hm x v ∈ L.O → hf L Hm v x ∈ L.O := fun x v hx => by
    rw [← DualInter.cj_hf h]
    exact GlobalTheory.UnramOrder.cj_mem L hx
  have hM : ∀ Λ ∈ T, ∀ x, x ∈ Mh ↔ x ∈ Λ ∧ x ∈ Y := fun Λ hΛ x => by
    rw [← hΛ.2.1]; rfl
  have h0 : ∀ Λ ∈ T, ∀ x, x ∈ Λ₀ ↔ x ∈ Λ ∧ x ∈ perp L Hm Y := fun Λ hΛ x => by
    rw [← hΛ.2.2]; rfl
  have hproj : ∀ Λ ∈ T, ∀ l ∈ Λ, ∀ w ∈ perp L Hm Y, l - w ∈ Y → l - w ∈ Md := by
    intro Λ hΛ l hl w hw hlw
    refine (hMd _).2 ⟨hlw, fun z hz => ?_⟩
    have hz' := (hM Λ hΛ z).1 hz
    rw [DualInter.sub_l, hw z hz'.2, sub_zero]
    exact (hΛ.1.2 z).2 hz'.1 l hl
  have hbM : ∀ i, b i ∈ Md := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlift : ∀ Λ : T, ∀ i, ∃ a ∈ Λ.1, a - b i ∈ perp L Hm Y ∧
      ∃ c ∈ Λ₁, c - (a - b i) ∈ Y := by
    intro Λ i
    obtain ⟨-, -, h3, -⟩ := DualInter.dual_inter L Hm h Λ.1 Λ.2.1 m y hy
    obtain ⟨-, h2, -, -⟩ := DualInter.dual_inter L Hm h Λ₁ hΛ₁.1 m y hy
    rw [hY] at h2 h3
    obtain ⟨a, ha, hab⟩ := (h3 (b i)).1 fun x hx hxY =>
      hsym _ _ (((hMd _).1 (hbM i)).2 x ((hM _ Λ.2 x).2 ⟨hx, hxY⟩))
    obtain ⟨c, hc, hca⟩ := (h2 (a - b i)).1 fun x hx hxY => by
      rw [DualInter.sub_r, hxY _ ((hMd _).1 (hbM i)).1, sub_zero]
      exact (Λ.2.1.2 a).2 ha x ((h0 _ Λ.2 x).1 ((h0 _ hΛ₁ x).2 ⟨hx, hxY⟩)).1
    exact ⟨a, ha, by simpa using (perp L Hm Y).neg_mem hab, c, hc, by simpa using Y.neg_mem hca⟩
  choose a ha hab c hc1 hca using hlift
  have hle : ∀ Λ Λ' : T, (∀ i, a Λ i ∈ Λ'.1) → Λ.1 ≤ Λ'.1 := by
    intro Λ Λ' hi l hl
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : l ∈ Y ⊔ perp L Hm Y)
    have hu' : l - w = u := by rw [← huw]; simp
    have h1 := hproj _ Λ.2 l hl w hw (hu' ▸ hu)
    rw [hb] at h1
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : l - ∑ i, s i • a Λ i ∈ Λ₀ := by
      refine (h0 _ Λ.2 _).2 ⟨Λ.1.sub_mem hl (Λ.1.sum_mem fun i _ => Λ.1.smul_mem _ (ha Λ i)), ?_⟩
      have : l - ∑ i, s i • a Λ i = w - ∑ i, s i • (a Λ i - b i) := by
        simp only [smul_sub, Finset.sum_sub_distrib, hs]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (s i : E) (hab Λ i))
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1
      (Λ'.1.sum_mem (t := Finset.univ) fun i _ => Λ'.1.smul_mem (s i) (hi i))
    rwa [sub_add_cancel] at h3
  let Q := Md.toAddSubgroup ⧸ Mh.toAddSubgroup.addSubgroupOf Md.toAddSubgroup
  have hQ : Nat.card Q = Mh.toAddSubgroup.relIndex Md.toAddSubgroup := rfl
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hN)
  let Φ : T → ι → Q := fun Λ i =>
    QuotientAddGroup.mk ⟨c Λ i - (a Λ i - b i), hproj _ hΛ₁ _ (hc1 Λ i) _ (hab Λ i) (hca Λ i)⟩
  have key : ∀ Λ Λ' : T, Φ Λ = Φ Λ' → ∀ i, a Λ i ∈ Λ'.1 := by
    intro Λ Λ' he i
    have h1 : -(c Λ i - (a Λ i - b i)) + (c Λ' i - (a Λ' i - b i)) ∈ Mh :=
      QuotientAddGroup.eq.1 (congrFun he i)
    have h2 : a Λ i - a Λ' i ∈ Λ₀ := by
      refine (h0 _ hΛ₁ _).2 ⟨?_, ?_⟩
      · have := Λ₁.add_mem ((hM _ hΛ₁ _).1 h1).1 (Λ₁.sub_mem (hc1 Λ i) (hc1 Λ' i))
        convert this using 1; abel
      · have := (perp L Hm Y).sub_mem (hab Λ i) (hab Λ' i)
        convert this using 1; abel
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1 (ha Λ' i)
    rwa [sub_add_cancel] at h3
  have hinj : Function.Injective Φ := fun Λ Λ' he =>
    Subtype.ext (le_antisymm (hle _ _ (key _ _ he)) (hle _ _ (key _ _ he.symm)))
  have : Finite T := Finite.of_injective Φ hinj
  have h4 := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card (α := ι)] at h4
  rw [← (Set.toFinite T).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem gluing_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp Mh Λ₀ hM
  rcases {Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧
    Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hM
  obtain ⟨⟨c, hc0, hca, hdet⟩, -, hsp⟩ := GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hMh : ∀ x, x ∈ Mh ↔ x ∈ Λ₁ ∧ x ∈ S.ME := fun x => by rw [← hΛ₁.2.1]; rfl
  let Md : Submodule L.O S.V :=
    { carrier := {x | x ∈ S.ME ∧ ∀ z ∈ Mh, hf L S.Hm x z ∈ L.O}
      zero_mem' := ⟨S.ME.zero_mem, fun z _ => by simp [hf]⟩
      add_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨S.ME.add_mem hu hv, fun z hz => ?_⟩
        have : hf L S.Hm (u + v) z = hf L S.Hm u z + hf L S.Hm v z :=
          (DualInter.hfL L S.Hm z).map_add u v
        rw [this]
        exact L.O.add_mem (hu' z hz) (hv' z hz)
      smul_mem' := by
        rintro s u ⟨hu, hu'⟩
        refine ⟨S.ME.smul_mem (s : E) hu, fun z hz => ?_⟩
        have : hf L S.Hm (s • u) z = s * hf L S.Hm u z := DualInter.smul_l L S.Hm s u z
        rw [this]
        exact L.O.mul_mem s.2 (hu' z hz) }
  obtain ⟨-, hidx, -, b, hb⟩ := GlobalTheory.T.card_discriminantModule_integralOverlattice_span L S.Hm S.herm S.ϖ S.ϖ_irr _ c hc0 hdet Mh Md
    (by rw [Set.Sum.elim_range]; exact hM)
    (fun x hx => by rw [hsp]; exact ((hMh x).1 hx).2)
    (fun x hx z hz => (hΛ₁.1.2 z).2 ((hMh z).1 hz).1 x ((hMh x).1 hx).1)
    (fun x => by rw [hsp]; rfl)
  rw [hca] at hidx
  have hq : resQ S.ϖ ^ (2 * S.a.toNat) ≠ 0 := pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  have hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0 := fun h => hq (by rw [← hidx, h, zero_mul])
  have hNle : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≤ S.q ^ (2 * S.a.toNat) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Dvd.intro _ hidx)
  have hY : Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) = S.ME := by
    rw [finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
    have : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := Set.eq_univ_of_forall fun i => i.2
    simp only [Frames.ME, Frames.spanTo, this, Set.image_univ]
  have h1 := encard_le S.herm (hli.comp _ finSumFinEquiv.symm.injective) hY hcompl.sup_eq_top
    Mh Λ₀ Md (fun _ => Iff.rfl) b hb hN
  have h2 : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card (Fin (r + 1) ⊕ Fin (r + 1))
      ≤ S.q ^ (2 * S.a.toNat * (2 * r + 2)) := by
    rw [pow_mul, show Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 by simp; ring]
    exact Nat.pow_le_pow_left hNle _
  have h3 := h1.trans (Nat.cast_le.2 h2)
  have h4 := ENat.toENNReal_le.2 h3
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h4
  exact h4

end GlobalTheory.HL.Gluing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingCountStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_selfDual_sat_inf_W0_le_q_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  first | exact @GlobalTheory.HL.Gluing.gluing_count | exact GlobalTheory.HL.Gluing.gluing_count | (intros; apply GlobalTheory.HL.Gluing.gluing_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardGluingHomKernelsLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardGluingHomKernelsLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GluingKernels

theorem encard_le_of_param {R D β : Type} [CommRing R] [AddCommGroup D] [Module R D] [Finite D]
    (m j : ℕ) (Φ : (Fin m → D) → β) (T : Set β)
    (hT : ∀ t ∈ T, ∃ I : Submodule R D, Nat.card I = j ∧ ∃ x : Fin m → D, (∀ i, x i ∈ I) ∧ Φ x = t) :
    T.encard ≤ ((Nat.card (Submodule R D) * j ^ m : ℕ) : ℕ∞) := by
  haveI : Finite (Submodule R D) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule R D))
  let A := Σ I : {I : Submodule R D // Nat.card I = j}, (Fin m → I.1)
  let Ψ : A → β := fun a => Φ fun i => (a.2 i : D)
  have hsub : T ⊆ Ψ '' Set.univ := by
    intro t ht
    obtain ⟨I, hI, x, hx, rfl⟩ := hT t ht
    exact ⟨⟨⟨I, hI⟩, fun i => ⟨x i, hx i⟩⟩, trivial, rfl⟩
  haveI : Fintype {I : Submodule R D // Nat.card I = j} := Fintype.ofFinite _
  have hA : Nat.card A ≤ Nat.card (Submodule R D) * j ^ m := by
    have h1 : Nat.card A = ∑ I : {I : Submodule R D // Nat.card I = j}, j ^ m := by
      rw [Nat.card_sigma]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Nat.card_fun, I.2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.val_injective)
  calc T.encard ≤ (Ψ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set A).encard := Set.encard_image_le _ _
    _ = (Nat.card A : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by exact_mod_cast hA

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E}
  {r k : ℕ} (S : Frames L r k)

theorem sat_gens (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) :
    ∃ b : Fin ((r + 1) + (r + 1)) → S.V, S.sat Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨hSD, hW, -, h1, h2, hli, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  have hfg : (S.sat Λ).FG := by
    haveI : IsNoetherian L.O Λ := isNoetherian_of_fg_of_noetherian Λ hSD.1.1
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hsp := (GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S _ hW.2.2.1 _ hW.2.2.2.1).2.2
  set y := Sum.elim (S.fr d Λ) (S.fr' d Λ) with hy
  have hr : Set.range (y ∘ finSumFinEquiv.symm) = Set.range y :=
    finSumFinEquiv.symm.surjective.range_comp y
  obtain ⟨b, -, hb⟩ := GlobalTheory.OrderBasis.order_basis L (y ∘ finSumFinEquiv.symm)
    (hli.comp _ finSumFinEquiv.symm.injective) (S.sat Λ) hfg (by
      rw [hr]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro x hx
        have hx2 : x ∈ S.ME := hx.2
        rw [← hsp] at hx2
        refine (Submodule.span_le.2 ?_) hx2
        rintro _ ⟨i | i, rfl⟩
        · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
        · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
            (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      · apply Submodule.span_mono
        rintro _ ⟨i | i, rfl⟩
        · have := (h1 (r + 1) le_rfl (S.fr d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_left this.2⟩
        · have := (h2 (r + 1) le_rfl (S.fr' d Λ i)).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)
          exact ⟨this.1, Submodule.mem_sup_right this.2⟩)
  exact ⟨b, hb⟩

theorem tauRel_sum (d : S.Datum) (Λ : Submodule L.O S.V) (hΛ : S.IsTerm d Λ) {ι : Type}
    (s : Finset ι) (c : ι → L.O) (w y : ι → S.V) (h : ∀ i, S.TauRel d Λ (w i) (y i)) :
    S.TauRel d Λ (∑ i ∈ s, c i • w i) (∑ i ∈ s, c i • y i) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
  induction s using Finset.induction_on with
  | empty => simpa using ((h4 0 (Submodule.zero_mem _)).1 (Submodule.zero_mem _)).2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact h3 (c a) (c a).2 _ _ _ _ (h a) ih

theorem encard_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d C Mh j
  rcases Set.eq_empty_or_nonempty
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j} with h0 | ⟨Λ₀, h₀, hC₀, hM₀, -⟩
  · rw [h0]; simp
  obtain ⟨-, -, -, -, -, b, -, hb⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ₀ h₀
  obtain ⟨-, -, -, -, -, ⟨i₀, hi₀, hbe⟩, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  let M₀ : Submodule L.O Mh := (S.M d Λ₀).comap Mh.subtype
  have hcard : Nat.card (Mh ⧸ M₀) = S.q ^ i₀ := by
    rw [← hbe, Frames.be, hM₀]
    rfl
  haveI : Finite (Mh ⧸ M₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := sat_gens S d Λ₀ h₀
  rw [hM₀] at hg
  have hgm : ∀ i, g i ∈ Mh := fun i => by rw [hg]; exact Submodule.subset_span ⟨i, rfl⟩
  have hgen : Submodule.span L.O (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) = ⊤ := by
    have h1 : Submodule.span L.O (Set.range fun i => (⟨g i, hgm i⟩ : Mh)) = ⊤ := by
      apply Submodule.map_injective_of_injective Mh.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
      exact hg.symm
    have h2 : (Set.range fun i => M₀.mkQ ⟨g i, hgm i⟩) =
        M₀.mkQ '' Set.range fun i => (⟨g i, hgm i⟩ : Mh) := by
      rw [← Set.range_comp]; rfl
    rw [h2, ← Submodule.map_span, h1, Submodule.map_top, Submodule.range_mkQ]
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L (Mh ⧸ M₀) _ _ hgen).1
  have key := encard_le_of_param (R := L.O) (k - 1) j
    (fun x : Fin (k - 1) → Mh ⧸ M₀ =>
      (LinearMap.ker (Fintype.linearCombination L.O x)).map (Fintype.linearCombination L.O b))
    ((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) ''
      {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}) (by
    rintro _ ⟨Λ, ⟨hΛ, hC, hM, hj⟩, rfl⟩
    obtain ⟨t1, t2, -, t4, t5, -⟩ := GlobalTheory.T.exists_gluing_homomorphism_defect_group L r k S d Λ hΛ
    rw [hM] at t1 t5
    have hMM : S.M d Λ = S.M d Λ₀ := by
      have hmem : (S.fr d Λ, S.fr' d Λ) ∈ S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) := by
        have := (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
        have h2 : S.frameCls (S.fr d Λ) (S.fr' d Λ) = S.frameCls (S.fr d Λ₀) (S.fr' d Λ₀) :=
          hC.trans hC₀.symm
        rwa [h2] at this
      exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 _ hmem).2
    have hbL : ∀ i, b i ∈ S.complementLatticeOfDatum d := fun i => by
      rw [hb]; exact Submodule.subset_span ⟨i, rfl⟩
    choose y hy hty using fun i => t1 (b i) (hbL i)
    refine ⟨((S.Ihat d Λ).comap Mh.subtype).map M₀.mkQ, ?_, fun i => M₀.mkQ ⟨y i, hy i⟩, ?_, ?_⟩
    · rw [← hj, Frames.cardI, hMM,
        ← AddSubgroup.relIndex_addSubgroupOf (L := Mh.toAddSubgroup) t5]
      have hk : (S.M d Λ₀).toAddSubgroup.addSubgroupOf Mh.toAddSubgroup =
          M₀.mkQ.toAddMonoidHom.ker := by
        ext x
        exact (Submodule.Quotient.mk_eq_zero M₀).symm
      rw [hk, AddSubgroup.relIndex_ker]
      rfl
    · intro i
      exact ⟨⟨y i, hy i⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨b i, hbL i, hty i⟩), rfl⟩
    · have hz : ∀ c : Fin (k - 1) → L.O,
          Fintype.linearCombination L.O (fun i => M₀.mkQ ⟨y i, hy i⟩) c = 0 ↔
            S.TauRel d Λ (∑ i, c i • b i) 0 := by
        intro c
        rw [t2 _ _ 0 (tauRel_sum S d Λ hΛ Finset.univ c b y hty), sub_zero, hMM,
          Fintype.linearCombination_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← map_smul, ← map_sum]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simp [M₀]
      ext w
      simp only [Submodule.mem_map, LinearMap.mem_ker, hz, Submodule.mem_inf,
        Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hL : ∑ i, c i • b i ∈ S.complementLatticeOfDatum d := by
          rw [hb]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        rw [Fintype.linearCombination_apply]
        exact ⟨(t4 _ hL.1).2 ⟨hL, hc⟩, hL.1⟩
      · rintro ⟨hw, hw0⟩
        obtain ⟨hL, ht⟩ := (t4 w hw0).1 hw
        rw [hb] at hL
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hL
        exact ⟨c, ht, Fintype.linearCombination_apply _ _ _⟩)
  have hN : Nat.card (Submodule L.O (Mh ⧸ M₀)) * j ^ (k - 1) ≤
      S.q ^ (S.a.toNat * (2 * r + 2)) * j ^ (k - 1) := by
    refine Nat.mul_le_mul_right _ (hsub.trans ?_)
    rw [hcard, ← pow_mul]
    refine Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have h3 := key.trans (Nat.cast_le.2 hN)
  have h4 := ENat.toENNReal_le.2 h3
  simpa using h4

end GlobalTheory.HL.GluingKernels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardGluingHomKernelsLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_gluingHom_kernels_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (Mh : Submodule L.O S.V) (j : ℕ), ((((fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) '' {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.sat Λ = Mh ∧ S.cardI d Λ = j}).encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) := by
  first | exact @GlobalTheory.HL.GluingKernels.encard_kernels_le | exact GlobalTheory.HL.GluingKernels.encard_kernels_le | (intros; apply GlobalTheory.HL.GluingKernels.encard_kernels_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermCount

theorem encard_le_mul {α β : Type} (s : Set α) (f : α → β) (t : Set β) (A B : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : (t.encard : ℝ≥0∞) ≤ A)
    (hB : ∀ b ∈ t, (({a | a ∈ s ∧ f a = b} : Set α).encard : ℝ≥0∞) ≤ B) :
    (s.encard : ℝ≥0∞) ≤ A * B := by
  have h1 : s ⊆ ⋃ b : t, {a | a ∈ s ∧ f a = b.1} := by
    intro a ha
    exact Set.mem_iUnion.2 ⟨⟨f a, hf a ha⟩, ha, rfl⟩
  calc (s.encard : ℝ≥0∞) = ∑' _ : s, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one s).symm
    _ ≤ ∑' _ : (⋃ b : t, {a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_mono_subtype (fun _ => (1 : ℝ≥0∞)) h1
    _ ≤ ∑' b : t, ∑' _ : ({a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => (1 : ℝ≥0∞)) _
    _ ≤ ∑' _ : t, B := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [ENNReal.tsum_set_one]
        exact hB b.1 b.2
    _ = (t.encard : ℝ≥0∞) * B := ENNReal.tsum_set_const t B
    _ ≤ A * B := by gcongr

theorem nT_cardI_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) (j : ℕ) :
    (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  unfold Frames.nT
  set s : Set (Submodule L.O S.V) := {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C} with hs
  rcases s.eq_empty_or_nonempty with he | ⟨Λ₁, hΛ₁, -, hC₁⟩
  · simp [he]
  obtain ⟨ha, -, -, hq, hH1, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₁ hΛ₁
  have hcls : S.IsCls C := hC₁ ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hΛ₁).2.2.2.2.2.2.1.1
  have hp : (S.fr d Λ₁, S.fr' d Λ₁) ∈ C :=
    hC₁ ▸ (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ₁) (S.fr' d Λ₁)).1
  have hM : ∀ Λ ∈ s, S.Mof (S.fr d Λ₁) (S.fr' d Λ₁) ≤ S.sat Λ := by
    rintro Λ ⟨hΛ, -, hC⟩
    have h1 := ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1
      (S.fr d Λ₁, S.fr' d Λ₁) (by
        have : S.frameCls (S.fr d Λ) (S.fr' d Λ) = C := hC
        rw [this]; exact hp)).2
    simp only at h1
    rw [h1]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).2.2.1
  have hmain : (s.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) *
      (((S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1)) *
        (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2))) := by
    refine encard_le_mul s S.sat _ _ _ ?_ (GlobalTheory.T.lattice_count_bound_frames L r k S C hcls _ hp ha) ?_
    · intro Λ hΛ
      refine ⟨hM Λ hΛ, fun x hx => hx.2, fun x hx y hy => ?_⟩
      exact ((GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ.1).1.2 y).2 hy.1 x hx.1
    · intro Mh hMh
      refine encard_le_mul _ (fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) _ _ _ ?_
        (GlobalTheory.T.encard_gluingHom_kernels_le L r k S d C Mh j) ?_
      · rintro Λ ⟨⟨h1, h2, h3⟩, h4⟩
        exact ⟨Λ, ⟨h1, h3, h4, h2⟩, rfl⟩
      · intro Λ₀ _
        refine le_trans ?_ (GlobalTheory.T.encard_selfDual_sat_inf_W0_le_q_pow L r k S C hcls _ hp Mh Λ₀ hMh.1)
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro Λ ⟨⟨⟨h1, -, -⟩, h4⟩, h5⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h1).1, h4, h5⟩
  refine hmain.trans ?_
  have hq' : (S.q : ℝ) ^ S.a.toNat ≤ S.Hp := by
    have : S.a = (S.a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [this, zpow_natCast] at hq
    exact hq
  have hreal : ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) * (j : ℝ) ^ (k - 1) ≤
      S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) ≤ S.Hp ^ (10 * (r + 1)) :=
          pow_le_pow_left₀ (by positivity) hq' _
      _ ≤ S.Hp ^ (12 * (r + 1)) := pow_le_pow_right₀ hH1 (by omega)
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  ring

end GlobalTheory.HL.TermCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermCountFrameClassLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTermCount_frameClass_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) C (j : ℕ), (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  first | exact @GlobalTheory.HL.TermCount.nT_cardI_le | exact GlobalTheory.HL.TermCount.nT_cardI_le | (intros; apply GlobalTheory.HL.TermCount.nT_cardI_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassGlue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs
  · rw [mul_one]
    gcongr
    exact h _
  · simp

theorem mass_le (S : Frames L r k) (d : S.Datum) (j : ℕ) :
    (S.mass d fun Λ => S.cardI d Λ = j) ≤
      ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    have hH : 1 ≤ S.Hp := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₀ h₀).2.2.2.2.1
    rw [GlobalTheory.T.hermitianMass_eq_sum_frameClasses L r k S d _ (fun h hh Λ hT hP => by
      rw [(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.1]; exact hP)]
    refine (sumCls_le S _ _ fun C => GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans ?_
    refine (mul_le_mul_left (GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S ⟨d, Λ₀, h₀⟩) _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc, ← pow_add]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH ?_) (by positivity)
    omega
  · have : (S.mass d fun Λ => S.cardI d Λ = j) = 0 := by
      unfold Frames.mass
      refine ENNReal.tsum_eq_zero.2 fun o => if_neg fun h => hex ⟨_, h.1⟩
    rw [this]
    exact zero_le

theorem finite_fibre (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) :
    {Λ | S.IsTerm d Λ ∧ S.Fr d Λ = C}.Finite := by
  have h1 : ∀ j : ℕ, {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C}.Finite := fun j => by
    have h := (GlobalTheory.T.hermitianTermCount_frameClass_le L r k S d C j).trans_lt ENNReal.ofReal_lt_top
    unfold Frames.nT at h
    rw [← Set.encard_lt_top_iff]
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  refine ((Set.finite_Iic S.a.toNat).biUnion fun i _ =>
    (Set.finite_Iic (S.q ^ i)).biUnion fun j _ => h1 j).subset ?_
  rintro Λ ⟨hT, hC⟩
  obtain ⟨i, hi, hb⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
  have h2 := (GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card L r k S d Λ hT).2.1
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq]
  exact ⟨i, by omega, S.cardI d Λ, hb ▸ h2, hT, rfl, hC⟩

theorem finite_cls (S : Frames L r k) (h : ∃ d Λ, S.IsTerm d Λ) :
    {o : MulAction.orbitRel.Quotient S.St (Set S.FrP) | S.IsIntCls o.out}.Finite := by
  have h1 := ((GlobalTheory.T.hermitianFrameClasses_total_weight_le L r k S h).trans_lt ENNReal.ofReal_lt_top).ne
  unfold Frames.sumCls at h1
  refine (ENNReal.finite_const_le_of_tsum_ne_top h1 (ε := 1) one_ne_zero).subset fun o ho => ?_
  have ho' : S.IsIntCls o.out := ho
  simp only [Set.mem_setOf_eq, if_pos ho', mul_one]
  exact ENNReal.one_le_ofReal.2 ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ ho'.1).2.2.1

theorem finite_orbits (S : Frames L r k) (d : S.Datum) :
    {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  by_cases hex : ∃ Λ, S.IsTerm d Λ
  · obtain ⟨Λ₀, h₀⟩ := hex
    refine (((finite_cls S ⟨d, Λ₀, h₀⟩).biUnion fun o _ => finite_fibre S d o.out).image
      (fun Λ => (Quotient.mk _ Λ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)))).subset ?_
    intro o ho
    have hT : S.IsTerm d o.out := ho
    let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ (S.Fr d o.out)
    obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St (S.Fr d o.out) :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
    have hA := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d _ hT h.1 h.2
    have hF : S.Fr d (h.1 • o.out) = o'.out := hA.2.2.2.2.1.trans hh
    refine ⟨h.1 • o.out, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨o', hF ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d _ hA.1).2.2.2.2.2.2.1, hA.1, hF⟩
    · refine Eq.trans ?_ (Quotient.out_eq o)
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)
  · refine Set.finite_empty.subset fun o ho => hex ⟨_, ho⟩

end GlobalTheory.HL.MassGlue

theorem GlobalTheory.HL.MassGlue.mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ d
  exact ⟨GlobalTheory.HL.MassGlue.mass_le S d, GlobalTheory.HL.MassGlue.finite_orbits S d⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFiniteStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by
  first | exact @GlobalTheory.HL.MassGlue.mass_le_and_finite | exact GlobalTheory.HL.MassGlue.mass_le_and_finite | (intros; apply GlobalTheory.HL.MassGlue.mass_le_and_finite <;> assumption)
end
