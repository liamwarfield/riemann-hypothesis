module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2
open GlobalTheory.Mem.Chr hiding ordF HChar upF aboveF unif HChar.resFin IsChiPsi embPsi
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiIdeal

open GlobalTheory.Mem.Chr.DetOrd

section General

variable {L : Type} [Field L] [NumberField L]

theorem frac_of_mul_eq_one {A B : Submodule (𝓞 L) L} (h : A * B = 1) :
    IsFractional (𝓞 L)⁰ A ∧ ∃ k : Lˣ, (k : L) ∈ A := by
  refine ⟨FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one B h)), ?_⟩
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Submodule.bot_mul] at h
    have : (1 : L) ∈ (⊥ : Submodule (𝓞 L) L) := h ▸ Submodule.one_le.1 le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).1 this)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff A).1 hA
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordF_le_iff (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) :
    ordF w a ≤ ordF w b ↔ w.valuation L (b : L) ≤ w.valuation L (a : L) := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [neg_le_neg_iff, WithZero.log_le_log hb ha]

theorem exists_gen {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    ∃ a : Lˣ, (a : L) ∈ A ∧ ordF w a = ordSub w A ∧ ∀ x ∈ A, w.valuation L x ≤ w.valuation L (a : L) := by
  obtain ⟨⟨a, ha, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine ⟨a, ha, e, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · simp [h0]
  · have h1 := hl ⟨Units.mk0 x h0, hx, rfl⟩
    rw [← e, ordF_le_iff] at h1
    exact h1

theorem ordSub_mul {A B : Submodule (𝓞 L) L} (hA : IsFractional (𝓞 L)⁰ A) (a0 : Lˣ) (ha0 : (a0 : L) ∈ A)
    (hB : IsFractional (𝓞 L)⁰ B) (b0 : Lˣ) (hb0 : (b0 : L) ∈ B) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A * B) = ordSub w A + ordSub w B := by
  obtain ⟨a, ha, ea, hla⟩ := exists_gen hA a0 ha0 w
  obtain ⟨b, hb, eb, hlb⟩ := exists_gen hB b0 hb0 w
  rw [← ea, ← eb, ← ordF_mul']
  refine IsLeast.csInf_eq ⟨⟨a * b, Submodule.mul_mem_mul ha hb, rfl⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  rw [ordF_le_iff]
  refine Submodule.mul_induction_on (C := fun x => w.valuation L x ≤ w.valuation L ((a * b : Lˣ) : L)) hk
    (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' (hla x hx) (hlb y hy)
  · exact Valuation.map_add_le _ hx hy

theorem ordSub_one (w : HeightOneSpectrum (𝓞 L)) : ordSub w (1 : Submodule (𝓞 L) L) = 0 := by
  have h := ordSub_span_singleton w (1 : Lˣ)
  rw [Units.val_one, ← Submodule.one_eq_span] at h
  rw [h]
  simp [ordF]

theorem ordF_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') (k k' : Lˣ)
    (e : (k' : L) = c k) : ordF w' k' = ordF w k := by
  unfold ordF
  rw [e, h]

theorem ordSub_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') {A B : Submodule (𝓞 L) L}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) : ordSub w' A = ordSub w B := by
  unfold ordSub
  congr 1
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h0 : c.symm k ≠ 0 := by simp
    refine ⟨Units.mk0 _ h0, (hB _).2 (by simpa using hk), (ordF_conj h _ _ (by simp)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    have h0 : c k ≠ 0 := by simp
    exact ⟨Units.mk0 _ h0, (hB _).1 hk, ordF_conj h _ _ rfl⟩

theorem ordSub_conj_eq_neg {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w')
    {A B : Submodule (𝓞 L) L} (hB : ∀ x, x ∈ B ↔ c x ∈ A) (h1 : A * B = 1) : ordSub w' A = -ordSub w A := by
  obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one h1
  obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one ((mul_comm B A).trans h1)
  have h2 := ordSub_mul fA a ha fB b hb w
  rw [h1, ordSub_one, ← ordSub_conj h hB] at h2
  omega

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem prod_val_above (χ : HChar L) (hu : ∀ v, χ.UnrAt v) (ht : χ.TrivOn F)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) : ∏ P ∈ aboveF (L := L) F v, χ.val P = 1 := by
  have h := ht.1 v (unif v)
  have he (s : Finset (HeightOneSpectrum (𝓞 L))) :
      (∏ P ∈ s, (χ.locK P).comp (upF F)) (unif v) =
        ∏ P ∈ s, ((χ.locK P).comp (upF F)) (unif v) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih, MonoidHom.mul_apply]
  rw [HChar.resFin, he] at h
  rw [← h]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (hu P), hr, hP', ordF_unif_self, zpow_one]

theorem finprod_val_eq_one (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n : HeightOneSpectrum (𝓞 L) → ℤ) (hf : {w | n w ≠ 0}.Finite)
    (hn : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' = n w) : ∏ᶠ w, χ.val w ^ n w = 1 := by
  classical
  have hm : ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L)),
      P ∈ aboveF (L := L) F v ↔ P.under (𝓞 F) = v := fun v P => by simp [aboveF]
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s := (hf.toFinset.image fun w => w.under (𝓞 F)).biUnion (aboveF (L := L) F)), Finset.prod_biUnion]
  · refine Finset.prod_eq_one fun v hv' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
    rw [Finset.prod_congr rfl (fun P hP => by rw [hn w P ((hm _ _).1 hP)]), Finset.prod_zpow, hv, one_zpow]
  · intro v _ v' _ hne
    refine Finset.disjoint_left.2 fun P h1 h2 => hne (((hm _ _).1 h1).symm.trans ((hm _ _).1 h2))
  · intro w hw
    have : n w ≠ 0 := fun h0 => hw (by simp [h0])
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨_, Finset.mem_image.2 ⟨w, hf.mem_toFinset.2 this, rfl⟩, (hm _ _).2 rfl⟩

theorem finprod_val_add (χ : HChar L) (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite)
    (hm : {w | m w ≠ 0}.Finite) :
    ∏ᶠ w, χ.val w ^ (n w + m w) = (∏ᶠ w, χ.val w ^ n w) * ∏ᶠ w, χ.val w ^ m w := by
  simp only [zpow_add]
  exact finprod_mul_distrib (hn.subset fun w hw h0 => hw (by simp [h0])) (hm.subset fun w hw h0 => hw (by simp [h0]))

theorem finprod_val_congr (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite) (hm : {w | m w ≠ 0}.Finite)
    (h : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' - m w' = n w - m w) :
    ∏ᶠ w, χ.val w ^ n w = ∏ᶠ w, χ.val w ^ m w := by
  have hd : {w | n w - m w ≠ 0}.Finite := (hn.union hm).subset fun w hw => by
    by_contra h0
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
    exact hw (by rw [h0.1, h0.2, sub_self])
  have h1 := finprod_val_add χ _ m hd hm
  rw [finprod_val_eq_one χ hv _ hd h, one_mul] at h1
  simpa using h1

theorem finite_toNat {n : HeightOneSpectrum (𝓞 L) → ℤ} (hn : {w | n w ≠ 0}.Finite) :
    {w | ((n w).toNat : ℤ) ≠ 0}.Finite :=
  hn.subset fun w hw h0 => hw (by simp [h0])

end General

theorem phase_sq_eq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem exists_mul_conj_eq {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination hz

theorem isChi_chiId : ∀ (D : D7) (χ : HChar D.host.E), IsChiPsi D.host χ → Formalism.MainNotions.TaylorLogMetric.IsChi D (chiId χ) := by
  intro D χ hχ
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hv := prod_val_above χ hχ.unr hχ.triv hr
  have hpl := fun w w' => (under_eq_iff_conjPl c hcm.rank hcm.ne w w').1
  refine ⟨?_, ?_⟩
  · rintro A B ⟨A', hA', hA⟩ ⟨B', hB', hB⟩
    obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one hA
    obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one hB
    have nA := ordSub_finite fA a ha
    have nB := ordSub_finite fB b hb
    have nAB : {w | ordSub w A + ordSub w B ≠ 0}.Finite := (nA.union nB).subset fun w hw => by
      by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by rw [h0.1, h0.2, add_zero])
    unfold chiId
    rw [← Units.val_mul]
    congr 1
    simp only [← zpow_natCast, ordSub_mul fA a ha fB b hb]
    rw [← finprod_val_add χ _ _ (finite_toNat nA) (finite_toNat nB)]
    refine finprod_val_congr χ hv _ _ (finite_toNat nAB) ((nA.union nB).subset fun w hw => ?_) fun w w' h => ?_
    · by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by simp [h0.1, h0.2])
    · rcases hpl w w' h with rfl | h
      · rfl
      · rw [ordSub_conj_eq_neg h (fun x => (hA' x).trans (by rw [← hc]; rfl)) hA,
          ordSub_conj_eq_neg h (fun x => (hB' x).trans (by rw [← hc]; rfl)) hB]
        omega
  · letI := D.host.cmStar
    intro z
    have hcmf : IsCMField D.host.E := D.host.isCMField_hostE
    have hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
    have hinv : ∀ x, c (c x) = x := fun x => by
      rw [hc, hc, ← hcc, ← hcc, IsCMField.complexConj_apply_apply]
    have hz : (z : D.host.E) * c (z : D.host.E) = 1 := by
      rw [hc, ← bridge_star_holds D.R D.host]
      exact z.2.2
    obtain ⟨k, hk⟩ := exists_mul_conj_eq (c : D.host.E →+* D.host.E) hinv
      (by by_contra hn; push Not at hn; exact hcm.ne (AlgEquiv.ext hn)) z hz
    have hk' : (z : D.host.E) * c (k : D.host.E) = k := hk
    have z0 : (z : D.host.E) ≠ 0 := left_ne_zero_of_mul_eq_one hz
    have k0 : c (k : D.host.E) ≠ 0 := by simp
    have hu : Units.mk0 _ z0 * Units.mk0 _ k0 = k := Units.ext hk'
    have e1 := chiId_span_singleton χ (Units.mk0 _ z0)
    rw [Units.val_mk0] at e1
    have e2 : ∏ᶠ w, χ.val w ^ (ordF w (Units.mk0 _ z0)).toNat = ∏ᶠ w, χ.val w ^ ordF w k := by
      simp only [← zpow_natCast]
      refine finprod_val_congr χ hv _ _ (finite_toNat (ordF_finite _)) (ordF_finite _) fun w w' h => ?_
      rcases hpl w w' h with rfl | h
      · rfl
      · have a1 := ordF_mul' w (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a2 := ordF_mul' w' (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a3 := ordF_conj h k (Units.mk0 _ k0) rfl
        have a4 := ordF_conj h (Units.mk0 _ k0) k (hinv _).symm
        rw [hu] at a1 a2
        omega
    have e3 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hχ.unr v) k
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e3
    rw [mul_comm, mul_eq_one_iff_eq_inv] at e3
    rw [e1, e2, e3, Units.val_inv_eq_inv_val, hχ.inf k, ← Finset.prod_inv_distrib]
    refine (Fintype.prod_equiv D.eTau _ _ fun τ => ?_).symm
    congr 1
    refine (phase_sq_eq ((map_ne_zero _).2 k.ne_zero) ?_).symm
    have hcj : embPsi D.host (D.eTau τ) (D.host.conj (k : D.host.E)) =
        starRingEnd ℂ (embPsi D.host (D.eTau τ) (k : D.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
    rw [← hcj, ← hc]
    exact (map_mul (embPsi D.host (D.eTau τ)) _ _).symm.trans (congrArg _ hk')

end GlobalTheory.Mem.ChiIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.IwaCell

variable {k : Type} [Field k] {m : ℕ}

def tD (ϖ : kˣ) (a : Fin m → ℤ) : GL (Fin m) k := diagT k (Fin m) fun i => ϖ ^ a i

variable [ValuativeRel k]

def cell (ϖ : kˣ) (a : Fin m → ℤ) : Set (GL (Fin m) k) :=
  {g | ∃ u ∈ unipB k (Fin m), ∃ κ ∈ KO k (Fin m), g = u * tD ϖ a * κ}


theorem val_tD (ϖ : kˣ) (a : Fin m → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  val_diagT k _

theorem tD_add (ϖ : kˣ) (a b : Fin m → ℤ) : tD ϖ (a + b) = tD ϖ a * tD ϖ b := by
  rw [tD, tD, tD, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tD_zero (ϖ : kˣ) : tD ϖ (0 : Fin m → ℤ) = 1 := by
  rw [tD, ← map_one (diagT k (Fin m))]
  congr 1
  funext i
  simp

theorem tD_neg (ϖ : kˣ) (a : Fin m → ℤ) : tD ϖ (-a) = (tD ϖ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tD_add, neg_add_cancel, tD_zero])

theorem diag_entry (ϖ : kˣ) (s t : Fin m → ℤ) {w : GL (Fin m) k} (hw : w ∈ unipB k (Fin m)) (i : Fin m) :
    (tD ϖ s * w * tD ϖ t).val i i = ((ϖ ^ (s i + t i) : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD, val_tD, Matrix.mul_diagonal, Matrix.diagonal_mul, ((mem_unipB k).1 hw).2 i,
    mul_one, _root_.zpow_add, Units.val_mul]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd (o x ^ n) := congrArg _ h
  simpa [o, mul_comm] using h2

theorem eq_of_mem_cell {ϖ : kˣ} (hϖ : ord k ϖ = 1) {a b : Fin m → ℤ} {g : GL (Fin m) k} (ha : g ∈ cell ϖ a)
    (hb : g ∈ cell ϖ b) : a = b := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ := ha
  obtain ⟨u', hu', κ', hκ', e⟩ := hb
  have hw : u'⁻¹ * u ∈ unipB k (Fin m) := mul_mem (inv_mem hu') hu
  have hx : tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a = κ' * κ⁻¹ := by
    rw [tD_neg]
    calc (tD ϖ b)⁻¹ * (u'⁻¹ * u) * tD ϖ a = (u' * tD ϖ b)⁻¹ * (u * tD ϖ a * κ) * κ⁻¹ := by group
      _ = (u' * tD ϖ b)⁻¹ * (u' * tD ϖ b * κ') * κ⁻¹ := by rw [e]
      _ = κ' * κ⁻¹ := by group
  have hxi : (tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a)⁻¹ = tD ϖ (-a) * (u'⁻¹ * u)⁻¹ * tD ϖ b := by
    simp only [tD_neg, _root_.mul_inv_rev, inv_inv]; group
  have hK := (GlobalTheory.SplitFlip.mem_KO_iff _).1 (hx ▸ mul_mem hκ' (inv_mem hκ))
  funext i
  have h1 := hK.1 i i
  have h2 := hK.2 i i
  rw [diag_entry ϖ _ _ hw] at h1
  rw [hxi, diag_entry ϖ _ _ (inv_mem hw)] at h2
  simp only [Pi.neg_apply] at h1 h2
  set y : kˣ := ϖ ^ (-b i + a i)
  have h2' : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    have : (ϖ ^ (-a i + b i) : kˣ) = y⁻¹ := by rw [← _root_.zpow_neg]; congr 1; ring
    rwa [this] at h2
  have v1 : valuation k (y : k) ≤ 1 := h1
  have v2 : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := h2'
  have hv : valuation k (y : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at v2
    have hpos : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
    exact le_antisymm v1 ((inv_le_one₀ hpos).1 v2)
  have h3 : ord k y = 0 := by simp [ord, hv]
  rw [ord_zpow, hϖ, mul_one] at h3
  omega

end GlobalTheory.IwaCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  by_contra hne
  have hpos : 0 < ‖(χ u : ℂ)‖ := norm_pos_iff.2 (χ u).ne_zero
  have hinj := pow_right_injective₀ hpos hne
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf
  refine ((finite_image_units χ hχ).image (fun w : ℂˣ => ‖(w : ℂ)‖)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨χ (u ^ n), ⟨u ^ n, ?_, rfl⟩, ?_⟩
  · simp [Units.val_pow_eq_pow_val, map_pow, hu]
  · simp [map_pow, Units.val_pow_eq_pow_val, norm_pow]

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  intro k _ _ _ _ χ hχ
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hord : ord k ϖ = 1 := ord_eq_one hϖ
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (χ ϖ).ne_zero
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  have hlq : Real.log (resCard k : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  refine ⟨-Real.log ‖(χ ϖ : ℂ)‖ / Real.log (resCard k : ℝ), fun z => ?_⟩
  have hz : ‖(χ z : ℂ)‖ = ‖(χ ϖ : ℂ)‖ ^ ord k z := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [map_mul, Units.val_mul, norm_mul,
      GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one χ hχ _ hw, mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  have hϖabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
    refine (nabs_properties k).2.2.2.2.1 ⟨ϖ, hlt.le⟩ ϖ ?_ rfl
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one, Ideal.mem_span_singleton,
      (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  have hn : nabs k z = (resCard k : ℝ) ^ (-ord k z) := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [nabs_mul, (nabs_eq_one_iff _).2 hw, mul_one]
    have hp : nabs k (ϖ ^ ord k z) = nabs k ϖ ^ ord k z := by
      simp [nabs, map_zpow]
    rw [hp, hϖabs, _root_.inv_zpow, _root_.zpow_neg]
  rw [hz, hn, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
namespace GlobalTheory.UnrLoc

theorem fixed_ne_bot_of_mem_iSup_range :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
      {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible →
      ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X},
      f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  intro G V X _ _ _ _ _ ι _ σ hσ ρ T K f hf hf0 hfix
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  haveI : Fintype ι := Fintype.ofFinite ι

  let Y : Finset ι → Submodule ℂ X := fun t => ⨆ j ∈ t, LinearMap.range (T j).toLinearMap
  have hYst : ∀ (t : Finset ι) (g : G) (x : X), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      have : ρ g ((T j).toLinearMap v) = (T j).toLinearMap (σ g v) := by
        simp only [Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
      rw [this]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range (T j).toLinearMap) j hj)
        (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : X), x ∈ Y t → x ≠ 0 → (∀ k ∈ K, ρ k x = x) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range (T j).toLinearMap ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨y, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Subrepresentation σ :=
        ⟨(Y t).comap (T j).toLinearMap, fun g w hw => by
          rw [Submodule.mem_comap] at hw ⊢
          have : (T j).toLinearMap (σ g w) = ρ g ((T j).toLinearMap w) := by
            simp only [Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
          rw [this]
          exact hYst t g _ hw⟩
      rcases eq_bot_or_eq_top U with hU | hU
      · have hU' : (Y t).comap (T j).toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule hU
        have hvfix : ∀ k ∈ K, σ k v = v := by
          intro k hk
          have hmem : σ k v - v ∈ (Y t).comap (T j).toLinearMap := by
            rw [Submodule.mem_comap, map_sub]
            have h1 := hxfix k hk
            have h2 : (T j).toLinearMap (σ k v) = ρ k ((T j).toLinearMap v) := by
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining]
            rw [map_add (f := _)] at h1
            have h3 : (T j).toLinearMap (σ k v) - (T j).toLinearMap v = z - ρ k z := by
              rw [h2, sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t k z hz)
          rw [hU'] at hmem
          exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
        by_cases hv : v = 0
        · subst hv
          simp only [map_zero, zero_add] at hx0 hxfix hz ⊢
          exact ih z hz hx0 hxfix
        · rw [Submodule.ne_bot_iff]
          refine ⟨v, ?_, hv⟩
          intro h
          simp [hvfix _ h.2]
      · have hv : (T j).toLinearMap v ∈ Y t := by
          have : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
          rw [← hU] at this
          exact this
        exact ih _ (add_mem hv hz) hx0 hxfix
  refine key Finset.univ f ?_ hf0 hfix
  simpa [Y] using hf

end GlobalTheory.UnrLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRangesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges : ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X] {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible → ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}, f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) → GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  first | exact @GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | exact GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range | (intros; apply GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.ThetaLevel

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have h1 : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, z ^ i‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ (z ^ i).re := by
      intro i _
      have h2 := (Complex.abs_re_le_norm (z ^ i - 1)).trans_lt (h i)
      rw [Complex.sub_re, Complex.one_re, abs_lt] at h2
      linarith [h2.1]
    have h3 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h4 := h N
  rw [← geom_sum_mul, norm_mul] at h4
  rw [div_lt_iff₀ hpos] at hN
  nlinarith [h1 N]

theorem eventually_smul (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hw : GlobalTheory.Ker.IsWeak ψ S T om)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∃ c : ℂ, om p f = c • f := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  filter_upwards [GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant D ψ hψ S T μ 𝓕 hμ h𝓕 f hf] with p hp h1 h2
  obtain ⟨g, h⟩ := p
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (om (g, h) f) hf (hw.om_pres _ f hf) (fun w => by
    have e : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := GlobalTheory.AdelicLatMove.actO_actO_inv S T g h w
    have e1 := hp h1 h2 (actO S T g⁻¹ h⁻¹ w)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om (g, h)) (hw.om_pres _) (hw.om_unit μ 𝓕 hμ h𝓕 _)
      (heisO ψ S T (actO S T g⁻¹ h⁻¹ w) f) f (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf
    rw [hw.om_heis g h _ f hf, e] at e2
    simp only [e] at e1
    exact e2.trans e1.symm)
  exact ⟨c, hc⟩

theorem exists_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  intro D ψ hψ S T om hw hc f hf
  by_cases h0 : f = 0
  · exact ⟨⊤, ⊤, by simp, by simp, fun k _ _ k' _ _ => by rw [h0, map_zero]⟩
  obtain ⟨w, hw0⟩ := Function.ne_iff.1 h0
  have hw0 : f w ≠ 0 := hw0
  have hcont : Continuous fun p : GA D S × GA D T => ‖om p f w / f w - 1‖ :=
    (((hc f hf w).div_const _).sub continuous_const).norm
  have hnear : ∀ᶠ p : GA D S × GA D T in 𝓝 1, ‖om p f w / f w - 1‖ < 1 / 2 := by
    refine hcont.continuousAt.eventually_lt continuousAt_const ?_
    simp [div_self hw0]
  have hN := (eventually_smul D ψ hψ S T om hw f hf).and hnear
  obtain ⟨N, hN1, N', hN2, hsub⟩ := mem_nhds_prod_iff.1 (show _ ∈ 𝓝 ((1 : GA D S), (1 : GA D T)) from hN)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D S N hN1
  obtain ⟨U', hU', hUN'⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D T N' hN2
  refine ⟨U, U', hU, hU', fun k hk hkf k' hk' hkf' => ?_⟩
  obtain ⟨c, hcf⟩ := (hsub (Set.mk_mem_prod (hUN k hk hkf) (hUN' k' hk' hkf'))).1 hkf hkf'
  have hpow : ∀ n : ℕ, om ((k, k') ^ n) f = c ^ n • f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hcf, map_smul, ih, smul_smul, pow_succ']
  have hc1 : c = 1 := eq_one_of_pow_near fun n => by
    have h := (hsub (Set.mk_mem_prod (hUN _ (pow_mem hk n) (pow_mem hkf n))
      (hUN' _ (pow_mem hk' n) (pow_mem hkf' n)))).2
    have e : om (k ^ n, k' ^ n) f = c ^ n • f := hpow n
    rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw0] at h
    exact h
  rw [hcf, hc1, one_smul]

end GlobalTheory.Mem.ThetaLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_level_fixing_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  first | exact @GlobalTheory.Mem.ThetaLevel.exists_level | exact GlobalTheory.Mem.ThetaLevel.exists_level | (intros; apply GlobalTheory.Mem.ThetaLevel.exists_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.VB

section Generic

variable {X : Scheme.{0}} [IsIntegral X]

theorem genRank_twist {F : X.Modules} {M : LB X} (hM : M.IsLB) :
    genRank (twist F M) = genRank F :=
  have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X)
  e.finrank_eq

theorem exists_germ_ne_zero {F : X.Modules} (h : QCoh.IsGloballyGenerated F)
    (hr : genRank F ≠ 0) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := by
  obtain ⟨n, s, hs⟩ := QCoh.isGloballyGenerated_iff_spanStalks.1 h
  by_contra! H
  have : Subsingleton (genStalk F) := subsingleton_of_forall_eq 0 fun t => by
    have ht := (hs (genericPoint X)).ge (Submodule.mem_top (x := t))
    have e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) :
        (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      exact H _
    simpa using Submodule.span_mono e ht
  exact hr Module.finrank_zero_of_subsingleton

theorem mono_sectionHom {F : X.Modules} (s : Γ(F, ⊤))
    (hs : F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0) : Mono (QCoh.sectionHom s) := by
  refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  apply (QCoh.structureModuleSectionsEquiv W).injective
  have e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) •
      Twist.resM F (le_top : W ≤ ⊤) s = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact e
  have e'' := congrArg (F.presheaf.germ W _ hη) e'
  rw [QCoh.germ_smul, Twist.germ_resM, map_zero] at e''
  have := (smul_eq_zero.1 e'').resolve_right hs
  exact sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))

end Generic

variable {κ : Type} [Field κ] {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)]

theorem interNum_one_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) (hd : topologicalKrullDim Z = 1)
    {N : LB Z} (hN : N.IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G ![N] = r * interNum κ (structureModule Z) ![N] := by
  have hf := algebraMap_eq_strHom κ Z
  have hL := isLB_vecOne hN
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 : QCoh.suppDim G ≤ 0 := suppDim_le_zero hd h
    have : QCoh.suppDim G < Fintype.card (Fin 1) := h0.trans_lt (by simp)
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N] :=
      (diffVanish_chiPic_of_isProjOver (d := 1) hf G hp
        ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_one_eq_genRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z]
    [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 →
    ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB →
      interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] :=
  fun _ _ _ _ _ hp hd G _ _ hN => interNum_one_of_genRank_eq hp hd hN _ G rfl

end GlobalTheory.VB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB → interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.VB.interNum_one_eq_genRank_mul | exact GlobalTheory.VB.interNum_one_eq_genRank_mul | (intros; apply GlobalTheory.VB.interNum_one_eq_genRank_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEmbExist

variable {E : Type} [Field E] [NumberField E]

theorem isIntegral_or_isIntegral_inv (w : HeightOneSpectrum (𝓞 E)) (x : GlobalTheory.LocDict.Kbar w) :
    IsIntegral (w.adicCompletionIntegers E) x ∨ IsIntegral (w.adicCompletionIntegers E) x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl isIntegral_zero
  let K := w.adicCompletion E
  let L : IntermediateField K (GlobalTheory.LocDict.Kbar w) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hy0 : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let f : L →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w := L.val.restrictScalars _
  have hf : Function.Injective f := L.val.injective
  have key : ∀ z : L, IsIntegral (w.adicCompletionIntegers E) (z : GlobalTheory.LocDict.Kbar w) ↔
      Valued.v (Algebra.norm K z) ≤ 1 := fun z => by
    rw [← GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one E w L z]
    exact isIntegral_algHom_iff f hf
  have hyx : ((y⁻¹ : L) : GlobalTheory.LocDict.Kbar w) = x⁻¹ := by simp [y]
  have hmul : Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  rcases le_total (Valued.v (Algebra.norm K y)) 1 with h | h
  · exact Or.inl ((key y).2 h)
  · right
    rw [← hyx]
    refine (key _).2 ?_
    calc Valued.v (Algebra.norm K y⁻¹) = 1 * Valued.v (Algebra.norm K y⁻¹) := (one_mul _).symm
      _ ≤ Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) := mul_le_mul' h le_rfl
      _ = 1 := hmul

def intValRing (w : HeightOneSpectrum (𝓞 E)) : ValuationSubring (GlobalTheory.LocDict.Kbar w) where
  toSubring := (integralClosure (w.adicCompletionIntegers E) (GlobalTheory.LocDict.Kbar w)).toSubring
  mem_or_inv_mem' x := isIntegral_or_isIntegral_inv w x

theorem isIntegral_algebraMap_iff (w : HeightOneSpectrum (𝓞 E)) (e : E) :
    IsIntegral (w.adicCompletionIntegers E) (algebraMap E (GlobalTheory.LocDict.Kbar w) e) ↔
      w.valuation E e ≤ 1 := by
  let K := w.adicCompletion E
  have h1 : algebraMap E (GlobalTheory.LocDict.Kbar w) e = algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) :=
    IsScalarTower.algebraMap_apply E K _ e
  let f : K →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w :=
    (IsScalarTower.toAlgHom K K (GlobalTheory.LocDict.Kbar w)).restrictScalars _
  rw [h1, show algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) = f (algebraMap E K e) from rfl,
    isIntegral_algHom_iff f f.toRingHom.injective, IsIntegrallyClosed.isIntegral_iff (K := K)]
  have hv : Valued.v (algebraMap E K e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  constructor
  · rintro ⟨y, hy⟩
    have h := y.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v (y : K) ≤ 1 at h
    rw [show (y : K) = algebraMap E K e from hy, hv] at h
    exact h
  · intro h
    refine ⟨⟨algebraMap E K e, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]
    exact h

theorem valuation_lt_one_iff_of_mem_iff {Ω : Type} [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (hB : ∀ e : E, algebraMap E Ω e ∈ B ↔ w.valuation E e ≤ 1) (e : E) :
    B.valuation (algebraMap E Ω e) < 1 ↔ w.valuation E e < 1 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have ha : algebraMap E Ω e ≠ 0 := (map_ne_zero _).2 he
  have h1 : B.valuation (algebraMap E Ω e) < 1 ↔ ¬ B.valuation (algebraMap E Ω e⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)), not_le]
  have h2 : w.valuation E e < 1 ↔ ¬ w.valuation E e⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he)), not_le]
  rw [h1, h2, ValuationSubring.valuation_le_one_iff, hB]

end GlobalTheory.LocEmbExist

namespace GlobalTheory.LocDict

theorem exists_isLocEmb : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ ι : Ω →ₐ[E] Kbar w, IsLocEmb A w ι := by
  intro E Ω _ _ _ _ _ A w h
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[E] Kbar w := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let A₀ : ValuationSubring Ω := (GlobalTheory.LocEmbExist.intValRing w).comap ι₀.toRingHom
  have hA₀ : ∀ z, z ∈ A₀ ↔ IsIntegral (w.adicCompletionIntegers E) (ι₀ z) := fun _ => Iff.rfl
  have hE : ∀ e : E, algebraMap E Ω e ∈ A₀ ↔ w.valuation E e ≤ 1 := fun e => by
    rw [hA₀, ι₀.commutes]
    exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff w e
  have hP : IsPlaceOver A₀ w := fun x => by
    rw [GlobalTheory.LocEmbExist.valuation_lt_one_iff_of_mem_iff A₀ w hE]
    exact w.valuation_lt_one_iff_mem (K := E) x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hP h
  refine ⟨ι₀.comp (σ.symm : Ω →ₐ[E] Ω), fun z => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA₀]
  rfl

end GlobalTheory.LocDict
end
end
