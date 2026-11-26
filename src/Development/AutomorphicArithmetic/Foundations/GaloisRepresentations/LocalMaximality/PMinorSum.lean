module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMinorSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem det_submatrix_orderEmbOfFin_eq_subtype {R : Type*} [CommRing R] {d k : ℕ}
    (B : Matrix (Fin d) (Fin d) R) (s : Finset (Fin d)) (h : s.card = k) :
    (B.submatrix (s.orderEmbOfFin h) (s.orderEmbOfFin h)).det =
      (B.submatrix (Subtype.val : s → Fin d) Subtype.val).det := by
  rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin h).toEquiv
    (B.submatrix (Subtype.val : s → Fin d) Subtype.val)]
  rfl

theorem UpperTheory.Gal.productCup_of_system.minorSum_of :
    MinorSum := by
  intro d a A
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact (det_submatrix_orderEmbOfFin_eq_subtype A S _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FixZOf
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.fixZ_of :
    ValBasic → RYBasic → FixZ := by
  intro hV hR F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A h e he
  have hmem : ∀ b ∈ rB ℂ K (xv x) {0}, algebraMap K K' b ∈ rB ℂ K' (xv x) {0} :=
    fun b hb => ((hR F K K' d x j2 h.toY0).2.2.2.1 {0} b hb).1
  let ι : rB ℂ K (xv x) {0} →ₐ[ℂ] rB ℂ K' (xv x) {0} :=
    ((IsScalarTower.toAlgHom ℂ K K').comp (rB ℂ K (xv x) {0}).val).codRestrict _ fun b => hmem b b.2
  have hι : ∀ (b : K) (hb : b ∈ rB ℂ K (xv x) {0}), (e.1.comp ι) ⟨b, hb⟩ = e.1 ⟨_, hmem b hb⟩ :=
    fun _ _ => rfl
  refine ⟨⟨e.1.comp ι, fun j => ?_⟩, ?_⟩
  · rw [hι]
    refine Eq.trans ?_ (e.2 j)
    congr 2
    exact (IsScalarTower.algebraMap_apply F K K' _).symm
  rintro v c ⟨b, hb, hbv, hzb, hz⟩
  rw [hι] at hzb
  rw [hι, hι] at hz
  have h1b := hmem b hb
  have h1bv := hmem _ hbv
  constructor
  · have hm : algebraMap K K' b * algebraMap K K' v ∈ rB ℂ K' (xv x) {0} := by
      rw [← map_mul]; exact h1bv
    refine ⟨_, h1b, hm, hzb, ?_⟩
    rw [← hz]
    congr 2
    exact (map_mul _ _ _).symm
  · have fix := (h.fx e).1 he
    obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {0}) e.1
    have v1 := fix b hb h1b
    have v2 := fix _ hbv h1bv
    obtain ⟨m1, hm1⟩ := (hev _ _).1 v1
    obtain ⟨m2, hm2⟩ := (hev _ _).1 v2
    obtain ⟨hne, hi⟩ := hinv _ _ v1 hzb
    have hv : j2 v = (j2 b)⁻¹ * j2 (b * v) := by
      rw [map_mul, inv_mul_cancel_left₀ hne]
    have hl : j2 v ∈ loc (rB ℂ K' (xv x) {0}) e.1 := by
      rw [hv]; exact mul_mem hi m2
    refine (hev _ _).2 ⟨hl, ?_⟩
    have hmul : (⟨j2 b, m1⟩ : loc (rB ℂ K' (xv x) {0}) e.1) * ⟨j2 v, hl⟩ = ⟨j2 (b * v), m2⟩ :=
      Subtype.ext (map_mul j2 b v).symm
    have := congrArg ev hmul
    rw [map_mul, hm1, hm2, hz] at this
    exact mul_left_cancel₀ hzb this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ValuationMulBis
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma UpperTheory.Gal.productCup_of_system.valuation_mul_bis (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v * w) (a * b) := by
  obtain ⟨-, ⟨ev, hev⟩, -⟩ := hV L B e
  obtain ⟨h1, ha⟩ := (hev v a).1 h
  obtain ⟨h2, hb⟩ := (hev w b).1 h'
  refine (hev (v * w) (a * b)).2 ⟨Subalgebra.mul_mem _ h1 h2, ?_⟩
  rw [← ha, ← hb, ← map_mul]
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_unique (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e v b) : a = b := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_mem (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {b : L} (hb : b ∈ B) : Val B e b (e ⟨b, hb⟩) :=
  (hV L B e).2.2.1 ⟨b, hb⟩

theorem UpperTheory.Gal.productCup_of_system.ptT_of :
    LocEq → ValBasic → RYBasic → PtT := by
  intro hLoc hV hRY
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY I J i hi j hj e hv
  have hr : ∀ l, (sysY x j2 d).r n10 (gT x j2) i j l =
      algebraMap F K' (x l.succ) / algebraMap F K' (x i) := by
    intro l
    simp [Sys.r, Sys.u, gT, sysY, n10, div_eq_mul_inv]
  have hw : ∀ a b, (((sysY x j2 d).X a * ((sysY x j2 d).X b)⁻¹ : K'ˣ) : K') =
      algebraMap F K' (x a) / algebraMap F K' (x b) := by
    intro a b
    simp [sysY, div_eq_mul_inv]
  have hxne : ∀ a, algebraMap F K' (x a : F) ≠ 0 := fun a => (map_ne_zero _).2 (x a).ne_zero
  have h1 : Val (RY (xv x) j2 I J) e 1 1 := by
    have h1v := valuation_mem hV (RY (xv x) j2 I J) e (one_mem (RY (xv x) j2 I J))
    have h1' : (⟨1, one_mem _⟩ : RY (xv x) j2 I J) = 1 := rfl
    rw [h1', map_one] at h1v
    exact h1v
  have hv' : ∀ l : Fin d, Val (RY (xv x) j2 I J) e
      (algebraMap F K' (x l.succ) / algebraMap F K' (x i)) 0 := fun l => hr l ▸ hv l
  have hi0 : i = 0 := by
    by_contra h
    have hvi := hv' (i.pred h)
    rw [Fin.succ_pred, div_self (hxne i)] at hvi
    exact zero_ne_one (valuation_unique hV _ e hvi h1)
  subst hi0
  have hI : I = {0} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun i' hi' => ?_⟩
    by_contra h
    have hgood := (hRY F K K' d x j2 hY).2.1 d
    have hm := hgood.memX I J ⟨j, hj⟩ i' hi' 0
    rw [hw] at hm
    have hval := valuation_mem hV (RY (xv x) j2 I J) e hm
    have hprod := valuation_mul_bis hV _ e (hv' (i'.pred h)) hval
    rw [Fin.succ_pred, zero_mul] at hprod
    have hone : algebraMap F K' (x i') / algebraMap F K' (x 0) *
        (algebraMap F K' (x 0) / algebraMap F K' (x i')) = 1 := by
      rw [div_mul_div_comm, mul_comm (algebraMap F K' (x i')),
        div_self (mul_ne_zero (hxne 0) (hxne i'))]
    rw [hone] at hprod
    exact zero_ne_one (valuation_unique hV _ e hprod h1)
  obtain ⟨e0, hloc, hval⟩ := hLoc F K K' d x j2 hY I J 0 hi e
  refine ⟨⟨e0, fun l => ?_⟩, hI, hloc, hval⟩
  have ht := tco_mem ℂ K' (xv x) l
  have h0 := (hval _ _).1 (hv' l)
  rw [← map_div₀] at h0
  have hm := valuation_mem hV _ e0 ht
  exact valuation_unique hV _ e0 hm h0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem dt_eq (b : Module.Basis (Fin d) K Ω[K⁄ℂ]) (hb : ∀ j, b j = D ℂ K (tt K x j)) (S : Finset (Fin d)) :
    dtS K x S = b.ExteriorAlgebra S := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : S.card = S.card)]
  simp only [dtS, ExteriorAlgebra.ιMulti_family]
  congr 1
  ext a
  simp [hb, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private theorem dt_univ : dtS K x Finset.univ = ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
  have h : (Finset.univ : Finset (Fin d)).card = d := by simp
  have key : ∀ (n : ℕ) (hn : (Finset.univ : Finset (Fin d)).card = n) , n = d →
      (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (tt K x ((Finset.univ : Finset (Fin d)).orderEmbOfFin hn a))) =
      ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
    intro n hn e
    subst e
    congr 1
    ext a
    have : (Finset.univ : Finset (Fin n)).orderEmbOfFin hn a = a := by
      have := Finset.orderEmbOfFin_unique' (s := (Finset.univ : Finset (Fin n))) hn (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (by simp)
      rw [← this]; rfl
    rw [this]
  exact key _ rfl h

end

theorem UpperTheory.Gal.productCup_of_system.dtBasic_of :
    DtBasic := by
  intro F K _ _ _ _ _ _ d x hc τ hτ
  obtain ⟨b0, hb0⟩ := hc.exists_basis
  have hb : ∀ j, b0 j = D ℂ K (tt K x j) := hb0
  have hfun : dtS K x = b0.ExteriorAlgebra := funext (dt_eq x b0 hb)
  have hprod : algebraMap F K (omG x 0) = ∏ l, tt K x l := by
    unfold omG
    rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, one_mul, map_prod]
    rfl
  refine ⟨?_, ?_, ?_, hprod, ?_⟩
  · rw [hfun]
    exact b0.ExteriorAlgebra.linearIndependent
  · intro S
    refine Submodule.subset_span ⟨1, one_mem _, fun a => tt K x (S.orderEmbOfFin rfl a),
      fun j => tco_mem ℂ K (xv x) _, ?_⟩
    rw [one_smul]
    rfl
  · have hne : ∀ j, tt K x j ≠ 0 := fun j =>
      (map_ne_zero _).2 (div_ne_zero (x j.succ).ne_zero (x 0).ne_zero)
    have hv : vol0 ℂ K (xv x) = (∏ j, (tt K x j)⁻¹) • ExteriorAlgebra.ιMulti K d fun j => D ℂ K (tt K x j) := by
      rw [← AlternatingMap.map_smul_univ]
      rfl
    rw [dt_univ, hprod, hv, smul_smul, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j _ => mul_inv_cancel₀ (hne j), Finset.prod_const_one, one_smul]
  · have hd : ∀ S : Finset (Fin d), Disjoint (Sᶜ) S := fun S => disjoint_compl_left
    refine ⟨fun S => (Set.powersetCard.permOfDisjoint
      (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
      (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S)).sign, fun U S hUS => ?_⟩
    rw [hfun]
    split_ifs with h
    · subst h
      have e := ExteriorAlgebra.basis_mul_of_disjoint b0
        (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) (hd S)
      have hu : ((Set.powersetCard.disjUnion (s := (⟨Sᶜ, rfl⟩ : Set.powersetCard (Fin d) Sᶜ.card))
          (t := (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card)) (hd S) : Set.powersetCard (Fin d) (Sᶜ.card + S.card)) : Finset (Fin d)) = Finset.univ := by
        ext i
        simp [Set.powersetCard.disjUnion]
      rw [hu] at e
      exact e
    · have hnd : ¬ Disjoint U S := by
        intro hUd
        apply h
        have hc2 : (U ∪ S).card = Fintype.card (Fin d) := by
          rw [Finset.card_union_of_disjoint hUd, hUS, Fintype.card_fin]
        have huniv : U ∪ S = Finset.univ := (Finset.card_eq_iff_eq_univ _).1 hc2
        ext i
        have := Finset.ext_iff.1 huniv i
        have h2 : i ∈ U → i ∉ S := fun a => Finset.disjoint_left.1 hUd a
        simp at this ⊢
        tauto
      exact ExteriorAlgebra.basis_mul_of_not_disjoint b0
        (⟨U, rfl⟩ : Set.powersetCard (Fin d) U.card) (⟨S, rfl⟩ : Set.powersetCard (Fin d) S.card) hnd
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PFixLoc
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem fixLoc_key (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    (e : B →ₐ[ℂ] ℂ) {d : ℕ} (g : Fin d → Fin d → L) (A : Matrix (Fin d) (Fin d) ℂ) (t r : Fin d → L)
    (hg : ∀ m l, Val B e (g m l) (A m l)) (hdet : (1 - A).det ≠ 0)
    (hr : ∀ a, r a = t a - ∑ l, g a l * t l) :
    ∃ N : Matrix (Fin d) (Fin d) L, (∀ a l, N a l ∈ loc B e) ∧ Val B e N.det (1 - A).det ∧
      (∀ a, r a = ∑ l, N a l * t l) ∧ ∀ l, InSp (loc B e) r (t l) := by
  obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV L B e
  have hg' : ∀ m l, ∃ h : g m l ∈ loc B e, ev ⟨_, h⟩ = A m l := fun m l => (hev _ _).1 (hg m l)
  choose hmem hval using hg'
  let G : Matrix (Fin d) (Fin d) (loc B e) := fun m l => ⟨g m l, hmem m l⟩
  let N' : Matrix (Fin d) (Fin d) (loc B e) := 1 - G
  let ι : loc B e →+* L := (loc B e).val.toRingHom
  let ε : loc B e →+* ℂ := ev.toRingHom
  have hN'ε : ε.mapMatrix N' = 1 - A := by
    ext a l
    simp only [N', RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    have h1 : ε ((1 : Matrix (Fin d) (Fin d) (loc B e)) a l) = (1 : Matrix (Fin d) (Fin d) ℂ) a l := by
      by_cases h : a = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1]
    congr 1
    exact hval a l
  have hN : (ι.mapMatrix N').det = ι N'.det := (RingHom.map_det ι N').symm
  have hVal : Val B e (ι.mapMatrix N').det (1 - A).det := by
    rw [hN]
    refine (hev _ _).2 ⟨N'.det.2, ?_⟩
    have : ε N'.det = (1 - A).det := by rw [RingHom.map_det, hN'ε]
    exact this
  have hmul : ∀ a, r a = ∑ l, (ι.mapMatrix N') a l * t l := by
    intro a
    rw [hr a]
    have h2 : ∀ l, (ι.mapMatrix N') a l * t l = (if a = l then t l else 0) - g a l * t l := by
      intro l
      have h0 : (ι.mapMatrix N') a l = (if a = l then 1 else 0) - g a l := by
        show ι ((1 - G) a l) = _
        rw [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite ι, map_one, map_zero]
        rfl
      rw [h0, sub_mul, ite_mul, one_mul, zero_mul]
    simp only [h2, Finset.sum_sub_distrib]
    simp
  refine ⟨ι.mapMatrix N', fun a l => (N' a l).2, hVal, hmul, fun l => ?_⟩
  obtain ⟨hv0, hvi⟩ := hinv _ _ hVal hdet
  refine ⟨fun a => ((ι.mapMatrix N').det)⁻¹ * (ι.mapMatrix N').adjugate l a, fun a => ?_, ?_⟩
  · refine (loc B e).mul_mem hvi ?_
    rw [← RingHom.map_adjugate]
    exact (N'.adjugate l a).2
  · have h3 : (ι.mapMatrix N').mulVec t = r := by
      ext a; rw [hmul a]; rfl
    have h4 : ((ι.mapMatrix N').adjugate).mulVec r = (ι.mapMatrix N').det • t := by
      rw [← h3, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h5 := congrFun h4 l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h5
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h5, inv_mul_cancel_left₀ hv0]

theorem UpperTheory.Gal.productCup_of_system.fixLoc_of :
    ValBasic → FixLoc := by
  intro hV F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he
  have htan := hY.tan e he
  choose g hgv hgs using htan
  refine fixLoc_key hV (rB ℂ K' (xv x) {0}) e.1 g (A e) (tt K' x) _ hgv (hY.det e he) fun a => ?_
  rw [← hgs a]
  have hd : ofLex (dj (0 : Fin (d + 1)) a) = (a.succ, 0) := by
    show (Fin.succAbove 0 a, (0 : Fin (d + 1))) = _
    rw [Fin.succAbove_zero]
  have hx0 : algebraMap F K' (x 0 : F) ≠ 0 := by simp
  have hy0 : j2 (algebraMap F K (x 0 : F)) ≠ 0 := by simp
  have hmu : (sysY x j2 d).mu (dj 0 a) = algebraMap F K' (x a.succ : F) * j2 (algebraMap F K (x 0 : F))
      - algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x a.succ : F)) := by
    unfold Sys.mu
    rw [hd]
    rfl
  have hu : (((sysY x j2 d).u n11 0 0 (dj 0 a) : K'ˣ) : K') =
      algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x 0 : F)) := by
    unfold Sys.u n11
    simp only [pow_one, Units.val_mul]
    rfl
  unfold Sys.r
  rw [Units.val_inv_eq_inv_val, hu, hmu]
  simp only [tt, map_div₀]
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceMemRB
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K'] {d : ℕ}

private theorem tower_rA (y : Fin (d + 1) → F) : IsScalarTower (rA ℂ y {0}) K K' :=
  .of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)

private theorem map_mem_rB (y : Fin (d + 1) → F) {b : K} (hb : b ∈ rB ℂ K y {0}) :
    algebraMap K K' b ∈ rB ℂ K' y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact hb.algebraMap

private theorem trace_mem_rB (y : Fin (d + 1) → F) [FiniteDimensional K K'] {v : K'}
    (hv : v ∈ rB ℂ K' y {0}) : Algebra.trace K K' v ∈ rB ℂ K y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hv ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact Algebra.isIntegral_trace hv

end

theorem UpperTheory.Gal.productCup_of_system.redK_of :
    RedK := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'
  have hred := hY.red
  unfold RedFib at hred ⊢
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht
  have hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n := by
    have := congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc
    simpa only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  let b : rB ℂ K' (xv x) {0} := ⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩
  have hb : b ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0})) := by
    have hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
        (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩
      apply Subtype.ext
      simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_pow, ← hcK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)
  rw [Ideal.mem_span_range_iff_exists_fun] at hb
  obtain ⟨e, he⟩ := hb
  have key : (Module.finrank K K' : K) * (a : K) =
      ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j) := by
    have h1 := congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
      Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
      mul_comm]
  have hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0})) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubringClass.coe_natCast]
    exact key.symm
  have hpos : (Module.finrank K K' : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) *
      ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul,
      inv_mul_cancel₀ hpos, map_one, one_mul]
  rw [hA]
  exact Ideal.mul_mem_left _ _ hmem
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PValBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)

private theorem mem_loc' {v : L} : v ∈ loc B e ↔ ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B := Iff.rfl

private theorem val_indep {v : L} (b b' c c' : B) (hb : e b ≠ 0) (hb' : e b' ≠ 0)
    (h : (b : L) * v = c) (h' : (b' : L) * v = c') : e c / e b = e c' / e b' := by
  have h1 : b' * c = b * c' := Subtype.ext (by
    push_cast
    rw [← h, ← h']
    ring)
  have h2 := congrArg e h1
  rw [map_mul, map_mul] at h2
  rw [div_eq_div_iff hb hb']
  linear_combination h2

private noncomputable def evF (w : loc B e) : ℂ :=
  e ⟨_, (Classical.choose_spec ((mem_loc' B e).1 w.2)).2⟩ / e (Classical.choose ((mem_loc' B e).1 w.2))

private theorem evF_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evF B e w = e c / e b := by
  obtain ⟨hb0, hc0⟩ := Classical.choose_spec ((mem_loc' B e).1 w.2)
  unfold evF
  exact val_indep B e _ b _ c hb0 hb rfl h

private noncomputable def evH : loc B e →ₐ[ℂ] ℂ where
  toFun := evF B e
  map_one' := by
    rw [evF_eq B e 1 1 1 (by simp) (by simp)]
    simp
  map_zero' := by
    rw [evF_eq B e 0 1 0 (by simp) (by simp)]
    simp
  map_mul' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w * w') (b * b') (⟨_, h⟩ * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_mul, map_mul, mul_div_mul_comm]
  map_add' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w + w') (b * b') (b' * ⟨_, h⟩ + b * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_add, map_mul, map_mul, map_mul]
    field_simp
  commutes' r := by
    rw [evF_eq B e (algebraMap ℂ _ r) 1 (algebraMap ℂ B r) (by simp) (by simp)]
    simp

private theorem evH_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evH B e w = e c / e b :=
  evF_eq B e w b c hb h

end

theorem UpperTheory.Gal.productCup_of_system.valBasic_of :
    ValBasic := by
  intro L _ _ B e
  refine ⟨fun b hb => ⟨1, by simp, by simpa using hb⟩, ⟨evH B e, fun v c => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rintro ⟨b, hb, hbv, h1, h2⟩
    refine ⟨⟨⟨b, hb⟩, h1, hbv⟩, ?_⟩
    rw [evH_eq B e _ ⟨b, hb⟩ ⟨_, hbv⟩ h1 rfl, h2]
    field_simp
  · rintro ⟨h, rfl⟩
    obtain ⟨b, hb, hbv⟩ := (mem_loc' B e).1 h
    refine ⟨b, b.2, hbv, hb, ?_⟩
    rw [evH_eq B e ⟨v, h⟩ b ⟨_, hbv⟩ hb rfl]
    field_simp
  · intro b
    refine ⟨1, B.one_mem, by simp, by simpa using (map_one e).symm ▸ one_ne_zero, ?_⟩
    have h1 : (⟨1, B.one_mem⟩ : B) = 1 := rfl
    have h2 : (⟨1 * (b : L), by simp⟩ : B) = b := Subtype.ext (one_mul _)
    rw [h1, h2, map_one, one_mul]
  · rintro v c ⟨b, hb, hbv, h1, h2⟩ hc
    have h3 : e ⟨b * v, hbv⟩ ≠ 0 := by
      rw [h2]
      exact mul_ne_zero h1 hc
    have hv : v ≠ 0 := by
      rintro rfl
      apply h3
      have : (⟨b * 0, hbv⟩ : B) = 0 := Subtype.ext (mul_zero _)
      rw [this, map_zero]
    refine ⟨hv, ⟨b * v, hbv⟩, h3, ?_⟩
    show b * v * v⁻¹ ∈ B
    rwa [mul_inv_cancel_right₀ hv]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.POmLoc
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section OmLocAux
variable {L : Type} [Field L] [Algebra ℂ L]

private noncomputable def om1 (B : Subalgebra ℂ L) : Submodule ℂ Ω[L⁄ℂ] :=
  Submodule.span ℂ {w | ∃ b ∈ B, ∃ u ∈ B, w = b • D ℂ L u}

private lemma omB_stab (B : Subalgebra ℂ L) (q : ℕ) {r : L} (hr : r ∈ B) {m : DR ℂ L}
    (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  have h : omB ℂ L B q ≤ (omB ℂ L B q).comap (Algebra.lsmul ℂ ℂ (DR ℂ L) r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, v, hv, rfl⟩
    refine Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, ?_⟩
    simp [mul_smul]
  exact h hm

private lemma omB_mono {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) : omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma ι_mul_mem (B : Subalgebra ℂ L) (q : ℕ) {w : Ω[L⁄ℂ]} (hw : w ∈ om1 B) {y : DR ℂ L}
    (hy : y ∈ omB ℂ L B q) : ExteriorAlgebra.ι L w * y ∈ omB ℂ L B (q + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨b * c, B.mul_mem hb hc, Fin.cons u v, fun j => ?_, ?_⟩
      · exact Fin.cases hu hv j
      · rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, mul_smul, Function.comp_def, smul_comm b c]
    | zero => simp
    | add a a' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul t a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  | zero => simp
  | add a a' _ _ h h' => rw [map_add (f := _), add_mul]; exact Submodule.add_mem _ h h'
  | smul t a _ h => rw [LinearMap.map_smul_of_tower, smul_mul_assoc]; exact Submodule.smul_mem _ t h

private lemma ιMulti_mem (B : Subalgebra ℂ L) (q : ℕ) (w : Fin q → Ω[L⁄ℂ]) (hw : ∀ j, w j ∈ om1 B) :
    ExteriorAlgebra.ιMulti L q w ∈ omB ℂ L B q := by
  induction q with
  | zero =>
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.elim0, fun j => j.elim0, ?_⟩
    rw [one_smul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact ι_mul_mem B q (hw 0) (ih _ fun j => hw _)

private lemma two_mem (B : Subalgebra ℂ L) {b v : L} (hb : b ∈ B) (hv : b * v ∈ B) :
    (b ^ 2) • D ℂ L v ∈ om1 B := by
  have h : (b ^ 2) • D ℂ L v = b • D ℂ L (b * v) - (b * v) • D ℂ L b := by
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, pow_two, mul_comm b v]
    abel
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, _, hv, rfl⟩)
    (Submodule.subset_span ⟨_, hv, b, hb, rfl⟩)

private lemma common_den (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {q : ℕ} {c : L} {v : Fin q → L}
    (hc : c ∈ loc B e) (hv : ∀ j, v j ∈ loc B e) :
    ∃ b : B, e b ≠ 0 ∧ (b : L) * c ∈ B ∧ ∀ j, (b : L) * v j ∈ B := by
  obtain ⟨b0, h0, hc'⟩ := hc
  choose f hf hf' using hv
  refine ⟨b0 * ∏ j, f j, ?_, ?_, fun j => ?_⟩
  · rw [map_mul, map_prod]
    exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hf j)
  · have h := B.mul_mem (∏ j, f j).2 hc'
    convert h using 1
    push_cast
    ring
  · have h := B.mul_mem (b0 * ∏ i ∈ Finset.univ.erase j, f i).2 (hf' j)
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
    convert h using 1
    push_cast
    ring

end OmLocAux

theorem UpperTheory.Gal.productCup_of_system.omLoc_of :
    OmLoc := by
  intro L _ _ B e q
  have hle : B ≤ loc B e := fun v hv => ⟨1, by simp, by simpa using hv⟩
  refine ⟨le_antisymm ?_ ?_, fun r hr m hm => omB_stab B q hr hm, fun B' h => omB_mono h q⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨b, hb, hv⟩
    have hb0 : (b : L) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    have hinv : (b : L)⁻¹ ∈ loc B e := ⟨b, hb, by rw [mul_inv_cancel₀ hb0]; exact B.one_mem⟩
    have h := omB_stab (loc B e) q hinv (omB_mono hle q hv)
    rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, v, hv, rfl⟩
    obtain ⟨b, hb, hbc, hbv⟩ := common_den B e hc hv
    refine Submodule.subset_span ⟨b ^ (2 * q + 1), by rw [map_pow]; exact pow_ne_zero _ hb, ?_⟩
    have h1 := ιMulti_mem B q (fun j => ((b : L) ^ 2) • D ℂ L (v j)) fun j => two_mem B b.2 (hbv j)
    have h2 := omB_stab B q hbc h1
    rw [AlternatingMap.map_smul_univ, smul_smul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h2
    convert h2 using 1
    rw [smul_smul]
    congr 1
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocOne
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem locOne_nak {L : Type} [Field L] [Algebra ℂ L] (B O : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (hBO : B ≤ O) (ev : O →ₐ[ℂ] ℂ) (hunit : ∀ u : O, ev u ≠ 0 → IsUnit u)
    (hden : ∀ v : O, ∃ b : B, ev ⟨b, hBO b.2⟩ ≠ 0 ∧ (b : L) * v ∈ B)
    {d : ℕ} (t : Fin d → O) (ht : ∀ l, ev (t l) = 0)
    (hmax : ∀ v : O, ev v = 0 → ∃ a : Fin d → O, v = ∑ l, a l * t l) (v : O) :
    D ℂ L (v : L) ∈ Submodule.span O (Set.range fun l => D ℂ L (t l : L)) := by
  classical
  set I : Ideal O := RingHom.ker ev with hI
  set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN
  set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM
  have hvM : D ℂ L (v : L) ∈ M := Submodule.subset_span ⟨v, rfl⟩
  suffices hMN : M ≤ N from hMN hvM
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ B).out
    set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG
    have hB : ∀ b : B, D ℂ L (b : L) ∈ G := by
      intro b
      have hb : b ∈ Algebra.adjoin ℂ (s : Set B) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | algebraMap r => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add, map_add (f := _)]
        exact Submodule.add_mem _ hy hz
      | mul y z _ _ hy hz =>
        rw [Subalgebra.coe_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz)
          (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)
    have hGM : M = G := by
      apply le_antisymm
      · rw [hM, Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        obtain ⟨b, hb0, hbw⟩ := hden w
        obtain ⟨u, hu⟩ := hunit _ hb0
        have h1 : D ℂ L ((b : L) * (w : L)) ∈ G := hB ⟨_, hbw⟩
        rw [Derivation.leibniz] at h1
        have h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G := by
          have h4 := Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))
          convert h4 using 1
          simp [Subalgebra.smul_def]
        have h3 := Submodule.smul_mem G (↑u⁻¹ : O) h2
        rw [← hu, smul_smul, Units.inv_mul, one_smul] at h3
        exact h3
      · rw [hG, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩
    rw [hGM]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    apply hunit
    have hy0 : ev y = 0 := hy
    simp [hy0]
  · rw [hM, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := hmax (w - algebraMap ℂ O (ev w)) (by simp)
    have hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L)) := by
      have h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L) := by
        have h5 := congrArg (fun u : O => (u : L)) ha
        push_cast at h5
        linear_combination h5
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_add (f := _), Derivation.map_algebraMap, zero_add, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.leibniz]
      rfl
    show D ℂ L (w : L) ∈ _
    rw [hD]
    refine Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    · apply Submodule.mem_sup_right
      apply Submodule.smul_mem_smul
      · show ev (t l) = 0
        exact ht l
      · exact Submodule.subset_span ⟨a l, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.locOne_of :
    LocMax → ValBasic → LocOne := by
  intro hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨hle, ⟨ev, hev⟩, hbv, hinv⟩ := hVal L (rB ℂ L (xv x) {0}) e.1
  haveI := hc.smooth 0
  haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance
  have hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b := by
    intro b
    obtain ⟨h, hb⟩ := (hev _ _).1 (hbv b)
    exact hb
  have hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨h0, h1⟩ := hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu
    exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0},
      ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0} := by
    intro v
    obtain ⟨b, hb, hbv'⟩ := v.2
    exact ⟨b, by rw [hevB]; exact hb, hbv'⟩
  let t : Fin d → loc (rB ℂ L (xv x) {0}) e.1 := fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩
  have ht : ∀ l, ev (t l) = 0 := fun l =>
    (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)
  have hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1,
      v = ∑ l, a l * t l := by
    intro v h0
    obtain ⟨a, ha, hv'⟩ := hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)
    refine ⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩
    rw [hv', AddSubmonoidClass.coe_finsetSum]
    rfl
  have hmem := locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  exact ⟨fun l => c l, fun l => (c l).2, hc'.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsInv
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {A : Type} [Field A] [Algebra ℂ A]

end

end UpperTheory.Gal.productCup_of_system

private theorem stab_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro b hb m hm
  change b • m ∈ omB ℂ L B q
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨b * a, B.mul_mem hb ha, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

private theorem kos_Z_mono_of_le {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) {κ : Type} [LinearOrder κ] {M M' : Submodule ℂ E}
    (h : M ≤ M') (r : κ → S) (m : ℤ) : (kos act M r).Z m ≤ (kos act M' r).Z m := by
  intro c hc
  simp only [GlobalTheory.PD.Cx.Z, kos, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
    forall_const, true_implies, LinearMap.mem_ker] at hc ⊢
  refine ⟨fun s => ?_, hc.2⟩
  have hs := hc.1 s
  split_ifs at hs ⊢ with hcard
  · exact h hs
  · exact hs

theorem UpperTheory.Gal.productCup_of_system.yKE_of :
    LG → OmLoc → RYFT → Htpy → K1 → LocReg → ValBasic → RYBasic → YKE := by
  intro hLG hOm hFT hH hK1 hLR hVB hRB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY κ _ _ r I J hI hr
  have hact : (sysY x j2 d).act = Algebra.lsmul ℂ ℂ (DR ℂ K') := rfl
  have hM : (sysY x j2 d).M I J = omB ℂ K' (RY (xv x) j2 I J) d := rfl
  rw [hact, hM]
  haveI : Algebra.FiniteType ℂ ↥(RY (xv x) j2 I J) := hFT F K K' d x j2 hY I J hI
  set B := RY (xv x) j2 I J with hB
  have hglob : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      (∀ e : ↥B →ₐ[ℂ] ℂ, c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).B m := by
    intro m c hc
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).1 m c
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    exact hc e
  have hloc : ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) → ∃ l, r l ≠ 0 ∧ (r l)⁻¹ ∈ loc B e := by
    intro e h
    push_neg at h
    obtain ⟨l, hl⟩ := h
    obtain ⟨-, -, hval, hinv⟩ := hVB K' B e
    have hv := hval ⟨r l, hr l⟩
    have hc0 : e ⟨r l, hr l⟩ ≠ 0 := by
      intro h0
      rw [h0] at hv
      exact hl hv
    exact ⟨l, hinv _ _ hv hc0⟩
  have hle : ∀ e : ↥B →ₐ[ℂ] ℂ, omB ℂ K' B d ≤ omB ℂ K' (loc B e) d :=
    fun e => (hOm K' B e d).2.2 _ (hVB K' B e).1
  have hbad : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).Z m →
      ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m := by
    intro m c hc e h
    obtain ⟨l, hl0, hlinv⟩ := hloc e h
    have hIn : InSp (loc B e) r 1 := by
      refine ⟨fun l' => if l' = l then (r l)⁻¹ else 0, fun l' => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact hlinv
        · exact (loc B e).zero_mem
      · simp [ite_mul, hl0]
    have := hH K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
      (omB ℂ K' (loc B e) d) r (stab_lemma _ d) m c (kos_Z_mono_of_le _ (hle e) r m hc) 1 hIn
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro hyp m hm c hc
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · obtain ⟨e0, hOv, hIn⟩ := hyp e h
      have hlocEq : loc B e = loc (rB ℂ K' (xv x) {0}) e0.1 := hOv.2.1
      have hReg : Reg (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) (tt K' x) := by
        rw [hlocEq]
        exact hLR F K' d x hY.covY hY.red e0
      have hKE := hK1 K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
        (omB ℂ K' (loc B e) d) r d (tt K' x) (stab_lemma _ d) (fun l => (hVB K' B e).1 (hr l))
        hReg (fun j => by rw [hlocEq]; exact hIn j)
      exact hKE m hm (kos_Z_mono_of_le _ (hle e) r m hc)
    · exact hbad m c hc e h
  · intro m c hc hyp
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · exact hbad m c hc e h
  · intro y hy hyp
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).2 y
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · obtain ⟨l, hl0, hlinv⟩ := hloc e h
      unfold sm
      refine Submodule.mem_iSup_of_mem (r l) (Submodule.mem_iSup_of_mem (Set.mem_range_self l) ?_)
      refine Submodule.mem_map.mpr ⟨_, stab_lemma (loc B e) d _ hlinv y (hle e hy), ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel₀ hl0, map_one, Module.End.one_apply]
end
