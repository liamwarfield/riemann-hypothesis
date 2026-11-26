module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section Aug

variable (S : Type u) [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {n : ℕ}

def Cech.AugExact {y : Fin (n + 1) → Ω} (G : Chart y → Submodule S E) (B : Submodule S E) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ b ∈ B, (∀ _ : Cech.Idx (support y) 0, b = 0) → b = 0) ∧
  (∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G 0,
      Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Chart y => E) G (p + 1),
    Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) (p + 1) s = 0 →
      ∃ t ∈ Cech.Cdeg (fun _ : Chart y => E) G p,
        Cech.d (fun _ : Chart y => E) (Cech.idRes S E (support y)) p t = s

end Aug

section Z

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E] {r : ℕ}

def secsOnZChart (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (I : Chart x)
    (J : Chart h) : Submodule S E :=
  Submodule.span S {e | ∃ n : ℕ, xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I}

def secsOnZ (G : SubSystem S x E) (H : SubSystem S x Ω) (h : Fin (r + 1) → Ω) (J : Chart h) : Submodule S E :=
  ⨅ I : Chart x, secsOnZChart G H h I J

end Z

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def negSet (a : (Σ k, ι k) → ℤ) : ∀ k, Finset (ι k) :=
  fun k => Finset.univ.filter fun i => a ⟨k, i⟩ < 0

def blockSum (a : (Σ k, ι k) → ℤ) : K → ℤ :=
  fun k => ∑ i, a ⟨k, i⟩

def posExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (a p).toNat

def negExp (a : (Σ k, ι k) → ℤ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (-a p).toNat

theorem monomial_negExp_mem (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ)
    (h : ∀ k, negSet a k ⊆ I k) : (monomial (negExp a) (1 : S) : MRingOver S ι) ∈ KH.cellMon S I := by
  classical
  rw [monomial_eq, C_1, one_mul, Finsupp.prod]
  refine Submonoid.prod_mem _ fun p hp => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  refine ⟨p.1, p.2, h p.1 ?_, rfl⟩
  have hp' : (negExp a) p ≠ 0 := Finsupp.mem_support_iff.mp hp
  simp only [negExp, Finsupp.coe_equivFunOnFinite_symm] at hp'
  simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and]
  show a p < 0
  omega


open Classical in
def monoFrac (S : Type) [CommRing S] (I : ∀ k, Finset (ι k)) (a : (Σ k, ι k) → ℤ) :
    LocalizedModule (KH.cellMon S I) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) :=
  if h : ∀ k, negSet a k ⊆ I k then
    LocalizedModule.mk (Ideal.Quotient.mk ⊥ (monomial (posExp a) 1))
      ⟨monomial (negExp a) 1, monomial_negExp_mem S I a h⟩
  else 0

def CombCell (ι : K → Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  {I : KH.Cell K ι n // ∀ k, J k ⊆ I.1 k}

abbrev CombC (S : Type) (J : ∀ k, Finset (ι k)) (n : ℕ) : Type :=
  CombCell ι J n → S

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


open Classical in
def combD (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) :
    CombC S J n →ₗ[S] CombC S J (n + 1) :=
  LinearMap.pi fun I => ∑ k, ∑ i ∈ I.1.1 k,
    if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
        ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
      KH.faceSign I.1.1 k i • LinearMap.proj (R := S) (φ := fun _ : CombCell ι J n => S)
        ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
    else 0

def combB (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) : (n : ℕ) → Submodule S (CombC S J n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (combD S J n)

end KHFree

namespace KHFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def singOne (S : Type) [CommRing S] (J : ∀ k, Finset (ι k)) (n : ℕ) : CombC S J n :=
  fun I => if ∀ k, J k = ∅ → (I.1.1 k).card = 1 then 1 else 0


open Classical in
def embed (S : Type) [CommRing S] (a : (Σ k, ι k) → ℤ) (n : ℕ) :
    CombC S (negSet a) n →ₗ[S] KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
  LinearMap.pi fun I => if h : ∀ k, negSet a k ⊆ I.1 k then
    (LinearMap.toSpanSingleton S _ (monoFrac S I.1 a)).comp
      (LinearMap.proj (R := S) (φ := fun _ : CombCell ι (negSet a) n => S) ⟨I, h⟩)
  else 0

end KHFree

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (e : ℕ), IsSubvar y pp e →
    ∀ (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∀ᶠ c : ℕ in atTop, restrLen pp (Q'.toSubSystem.twist (twistSys k y (c : ℤ))) =
        restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZeroIdealChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ZeroIdealChartAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def chartUnion (I K : Chart x) : Chart x :=
  ⟨I.1 ∪ K.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 K.2.2⟩

theorem monos_union_split {I K : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos (I ∪ K)) :
    ∃ u ∈ monos (S := S) I, ∃ v ∈ monos (S := S) K, u * v = s := by
  unfold monos at hs
  rw [Finset.coe_union, Set.image_union, Submonoid.closure_union, Submonoid.mem_sup] at hs
  exact hs

theorem aeval_mem_twistMod {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (K : Chart x) :
    aeval x f ∈ twistMod S x (e : ℤ) K :=
  Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp, by simp⟩

theorem exists_monos_mul_mem_twistMod (I K : Chart x) (b : Ω)
    (hb : b ∈ chartRing S x (chartUnion I K)) :
    ∃ u ∈ monos (S := S) I.1, ∃ d : ℕ, u.IsHomogeneous d ∧ aeval x u * b ∈ twistMod S x (d : ℤ) K := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hb
  obtain ⟨u, hu, v, hv, rfl⟩ := monos_union_split hs
  obtain ⟨du, hdu⟩ := monos_isHomogeneous hu
  obtain ⟨dv, hdv⟩ := monos_isHomogeneous hv
  have huv0 := eval_ne_zero_of_mem_monos (chartUnion I K) hs
  have hu0 := eval_ne_zero_of_mem_monos I hu
  have hv0 := eval_ne_zero_of_mem_monos K hv
  have he : du + dv = e := (hdu.mul hdv).inj_right hse (fun h => huv0 (by rw [h, map_zero]))
  refine ⟨u, hu, du, hdu, Submodule.subset_span ⟨f, v, dv, e, hv, hf, hdv, by omega, ?_⟩⟩
  rw [map_mul]
  field_simp

theorem twistMod_mul_mem {K : Chart x} {a b : Ω} {c c' : ℤ} (ha : a ∈ twistMod S x c K)
    (hb : b ∈ twistMod S x c' K) : a * b ∈ twistMod S x (c + c') K := by
  have h := Submodule.mul_mem_mul (M := (twistSys S x c).sub K) (N := (twistSys S x c').sub K) ha hb
  rw [twistSys_sub_mul] at h
  exact h

theorem mul_mem_chartRing_union (D : SubFamily S x Ω) (I K : Chart x) (y : Ω)
    (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∀ δ ∈ D.sub (chartUnion I K), y * δ ∈ chartRing S x (chartUnion I K) := by
  intro δ hδ
  obtain ⟨a, ⟨w, hw⟩, haδ⟩ := (D.mem_iff I (chartUnion I K) Finset.subset_union_left δ).mp hδ
  have hinv : ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (a : Ω) = 1 := by
    have := congrArg Subtype.val (Units.inv_mul w)
    rw [hw] at this
    exact this
  have h1 : y * ((a : Ω) • δ) ∈ chartRing S x (chartUnion I K) :=
    chartRing_mono Finset.subset_union_left (hy _ haδ)
  have h2 : y * δ = ((↑w⁻¹ : chartRing S x (chartUnion I K)) : Ω) * (y * ((a : Ω) • δ)) := by
    rw [smul_eq_mul, mul_left_comm y, ← mul_assoc, hinv, one_mul]
  rw [h2]
  exact mul_mem (w⁻¹ : (chartRing S x (chartUnion I K))ˣ).1.2 h1

end ZeroIdealChartAux

theorem ZeroIdealChart.proof : ZeroIdealChart.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T I y hy
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul T.M T.p (T.m - T.c₁)
  have hLD : L.toSubSystem = T.D := hL
  have hsub : ∀ K, T.D.sub K = L.sub K := fun K => by rw [← hLD]

  have hsi : T.si ∈ T.D.sub I := (Submodule.mem_iInf _).mp T.si_mem I
  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy _ hsi
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * T.si * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyL : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := fun δ hδ => hy δ (by rw [hsub]; exact hδ)
  have hyU := mul_mem_chartRing_union L.toSubFamily I

  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing k x (chartUnion I p.1) := fun p =>
    hyU p.1 y hyL _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := k) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly k N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := k) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod k x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod k x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ T.J := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ (by rw [← hsub]; exact hδ))
    · rw [map_mul, ← hfz]
      ring

  refine Submodule.subset_span ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem zpow_mul_mem_tilde (M : FinGradedSub (S := S) (x := x) Ω) {I : Chart x} {i : Fin (N + 1)}
    (hi : i ∈ I.1) (c d : ℤ) {y : Ω} (hy : y ∈ M.tilde d I) : x i ^ c * y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      simp only [map_pow, aeval_X, smul_eq_mul, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      simp only [map_mul, map_pow, aeval_X, smul_eq_mul, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c * (a • y) = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]
    exact Submodule.smul_mem _ a hy

theorem tilde_eq_twist (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) (I : Chart x) :
    M.tilde c I = ((M.tildeSys 0).twist (twistSys S x c)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) * y ∈ M.tilde 0 I := by
      simpa using zpow_mul_mem_tilde M hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) * y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_mul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c * y ∈ M.tilde c I := by
      simpa using zpow_mul_mem_tilde M hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

section Generic

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]


omit [IsFractionRing S F] in
theorem exists_monos_map {I : Finset (Fin (N + 1))} {s : Poly F N} (hs : s ∈ monos I) :
    ∃ s' : Poly S N, s' ∈ monos I ∧ map (algebraMap S F) s' = s := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', mul_mem ha' hb', map_mul _ _ _⟩

theorem algebraMap_ne_zero_of_mem (F : Type u) [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] [IsFractionRing S F] {t : S} (ht : t ∈ nonZeroDivisors S) : algebraMap S Ω t ≠ 0 := by
  have : Nontrivial S := (algebraMap S F).domain_nontrivial
  rw [IsScalarTower.algebraMap_apply S F Ω]
  exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht)

theorem exists_mul_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing F x I) :
    ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hse' : s'.IsHomogeneous e := fun d hd => hse (by
    rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
  have hsum : aeval x f / aeval x (map (algebraMap S F) s') =
      ∑ d ∈ f.support, AddMonoidAlgebra.coeff f d • (aeval x (monomial d (1 : S)) / aeval x s') := by
    rw [aeval_map_algebraMap]
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def, mul_div_assoc]
  rw [hsum]
  refine Finset.sum_induction _ (fun a => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I)
    ?_ ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩ ?_
  · rintro a b ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hta)
      (mul_mem (Subalgebra.algebraMap_mem _ _) htb)
  · intro d hd
    have hmem : aeval x (monomial d (1 : S)) / aeval x s' ∈ chartRing S x I :=
      ⟨monomial d 1, s', e, hs', isHomogeneous_monomial _ (by
        rw [Finsupp.degree_eq_weight_one]; exact hf (mem_support_iff.mp hd)), hse', rfl⟩
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := S) (AddMonoidAlgebra.coeff f d)
    refine ⟨v, hv, ?_⟩
    have hv0 : algebraMap S Ω v ≠ 0 := algebraMap_ne_zero_of_mem F hv
    have : algebraMap S Ω v * (AddMonoidAlgebra.coeff f d • (aeval x (monomial d (1 : S)) / aeval x s')) =
        algebraMap S Ω u * (aeval x (monomial d (1 : S)) / aeval x s') := by
      rw [Algebra.smul_def, ← huv, map_div₀, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      field_simp
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hmem

theorem exists_mul_mem_of_mem_extend (Q : SubSystem S x Ω) (I : Chart x) {z : Ω}
    (hz : z ∈ (Q.extend F).sub I) : ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I := by
  have hS : ∀ (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I := fun t y hy => by
    rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
  refine Submodule.span_induction
    (p := fun z _ => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I) ?_ ?_ ?_ ?_ hz
  · intro z hz
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact hz⟩
  · exact ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩
  · rintro a b _ _ ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (hS t' hta) (hS t htb)
  · rintro a z _ ⟨t, ht, htz⟩
    obtain ⟨u, hu, hua⟩ := exists_mul_mem_chartRing (S := S) a.2
    refine ⟨u * t, mul_mem hu ht, ?_⟩
    have : algebraMap S Ω (u * t) * (a • z) =
        (⟨_, hua⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ _ htz

theorem span_secs_eq_secs_extend (Q : SubSystem S x Ω) :
    Submodule.span F (Q.secs : Set Ω) = (Q.extend F).secs := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf] at hz ⊢
    intro I
    exact Submodule.subset_span (hz I)
  · intro z hz
    rw [SubSystem.secs, Submodule.mem_iInf] at hz
    choose t ht htz using fun I => exists_mul_mem_of_mem_extend Q I (hz I)
    have hS : ∀ (I : Chart x) (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I :=
      fun I t y hy => by rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
    set t₀ := ∏ I, t I with ht₀
    have ht₀m : t₀ ∈ nonZeroDivisors S := prod_mem fun I _ => ht I
    have hmem : algebraMap S Ω t₀ * z ∈ Q.secs := by
      rw [SubSystem.secs, Submodule.mem_iInf]
      intro I
      rw [ht₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
        mul_assoc]
      exact hS I _ (htz I)
    have h0 : algebraMap S F t₀ ≠ 0 := by
      have : Nontrivial S := (algebraMap S F).domain_nontrivial
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht₀m
    have : z = (algebraMap S F t₀)⁻¹ • (algebraMap S Ω t₀ * z) := by
      rw [Algebra.smul_def, map_inv₀, IsScalarTower.algebraMap_apply S F Ω,
        inv_mul_cancel_left₀ ((map_ne_zero _).mpr h0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Generic

theorem FiniteSections.proof (hE : Extension.Statement.{u, w, w}) (hT : TildeTail.Statement.{u, w}) :
    FiniteSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q hx

  have tail : ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j} := by
    intro c₁
    obtain ⟨M, -, hM⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
    have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
    have hc : ∀ c : ℤ, M.tildeSys c = Q.twist (twistSys S x c) := fun c =>
      SubSystem.ext_sub fun I => by rw [← h0]; exact tilde_eq_twist M c I
    obtain ⟨n, deg, gen, hgen, hspan⟩ := hT S Ω N x M hx c₁
    refine ⟨n, deg, gen, fun j => ⟨(hgen j).1, ?_⟩, fun c hc₁ => ?_⟩
    · rw [← hc]; exact (hgen j).2
    · rw [← hc]; exact hspan c hc₁
  refine ⟨?_, tail, fun F _ _ _ _ _ => span_secs_eq_secs_extend Q.toSubSystem⟩

  obtain ⟨n, deg, gen, hgen, hspan⟩ := tail 0
  have hle : Q.secs ≤ Submodule.span S (Set.range gen) := by
    have h := hspan 0 le_rfl
    rw [SubSystem.twist_twistSys_zero] at h
    refine h.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, f, e, hf, hej, rfl⟩
    have he : e = 0 := by have := (hgen j).1; omega
    subst he
    have hfC : f = C (AddMonoidAlgebra.coeff f 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hf.totalDegree_le)
    rw [hfC, aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := isNoetherian_span_of_finite S (Set.finite_range gen)
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutComponentSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutComponent.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar (x := x) pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys (x := x) pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, IsSubvar (x := x) qq n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotAdd.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ F₃ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    (∀ I, F₃.sub I ≤ F₂.sub I) →
    eulerCharQuot k F₁.toSubSystem F₃.toSubSystem =
      eulerCharQuot k F₁.toSubSystem F₂.toSubSystem + eulerCharQuot k F₂.toSubSystem F₃.toSubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerCharQuot k
            ((F₁.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
            ((F₂.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.Away

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem homogeneousComponent_homog_mul {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

theorem span_singleton_pow_eq {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (a : A)
    (n : ℕ) : Submodule.span R {a} ^ n = Submodule.span R {a ^ n} := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Submodule.one_eq_span]
  | succ n ih => rw [pow_succ, ih, Submodule.span_mul_span, Set.singleton_mul_singleton, pow_succ]

theorem twistSys_sub (c : ℤ) (I : Chart x) : (twistSys S x c).sub I = twistMod S x c I := rfl

theorem twist_sub (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ {z | ∃ q ∈ Q.sub I, ∃ y ∈ F.sub I, z = q • y} = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨q, hq, y, hy, rfl⟩

theorem twistMod_zero (I : Chart x) : twistMod S x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem twistMod_mul (a a' : ℤ) (I : Chart x) :
    twistMod S x a I * twistMod S x a' I = twistMod S x (a + a') I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span a' I hi, twistMod_eq_span (a + a') I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, zpow_add₀ hxi]

theorem twistMod_pow (a : ℤ) (I : Chart x) (n : ℕ) :
    twistMod S x a I ^ n = twistMod S x (n * a) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero]
  | succ n ih =>
    rw [pow_succ, ih, twistMod_mul]
    congr 1
    push_cast
    ring

theorem pow_sub (Q : SubSystem S x Ω) (I : Chart x) (n : ℕ) : (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => exact (twistMod_zero I).trans (pow_zero _).symm
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [twist_sub, ih, pow_succ']

theorem div_pow_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) {h : Poly S N} {d : ℕ}
    (hh : h.IsHomogeneous d) : aeval x h / x i ^ d ∈ chartRing S x I :=
  ⟨h, X i ^ d, d, pow_mem (X_mem_monos hi) d, hh, isHomogeneous_X_pow i d, by rw [map_pow, aeval_X]⟩

theorem homogeneousComponent_mul_mem (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) {i : Fin (N + 1)}
    (hi : i ∈ I.1) {f : Poly S N} (hf : f ∈ zeroIdeal D σ) (e : ℕ) :
    ∀ δ ∈ D.sub I, aeval x (homogeneousComponent e f) * δ ∈
      Submodule.span (chartRing S x I) {σ * x i ^ e} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [zeroIdeal, Ideal.span] at hf
  induction hf using Submodule.span_induction generalizing e with
  | mem g hg =>
    obtain ⟨c, hgc, hg⟩ := hg
    intro δ hδ
    rw [homogeneousComponent_of_mem hgc]
    split_ifs with hce
    · subst hce
      obtain ⟨o, ho, heq⟩ := hg I δ hδ
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
      obtain ⟨t, rfl⟩ := ho
      rw [heq, Submodule.mem_span_singleton]
      exact ⟨t, by rw [chartRing_smul_def, chartRing_smul_def, zpow_natCast]; ring⟩
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | zero => intro δ _; rw [map_zero, map_zero, zero_mul]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    intro δ hδ
    rw [map_add (f := _), map_add (f := _), add_mul]
    exact Submodule.add_mem _ (hf e δ hδ) (hg e δ hδ)
  | smul r f _ hf =>
    intro δ hδ
    have hsum : r * f = ∑ d ∈ Finset.range (r.totalDegree + 1), homogeneousComponent d r * f := by
      rw [← Finset.sum_mul, sum_homogeneousComponent]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, hsum, map_sum, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [homogeneousComponent_homog_mul (homogeneousComponent_isHomogeneous d r) f e]
    split_ifs with hde
    · obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hf (e - d) δ hδ)
      rw [map_mul, mul_assoc, ← ht, Submodule.mem_span_singleton]
      refine ⟨⟨_, div_pow_mem_chartRing I hi (homogeneousComponent_isHomogeneous d r)⟩ * t, ?_⟩
      have hpow : x i ^ e = x i ^ d * x i ^ (e - d) := by rw [← pow_add, Nat.add_sub_cancel' hde]
      have hxd : x i ^ d ≠ 0 := pow_ne_zero _ hxi
      rw [chartRing_smul_def, chartRing_smul_def, Subalgebra.coe_mul, hpow]
      field_simp
      try ring
    · rw [map_zero, zero_mul]; exact Submodule.zero_mem _

theorem idealMod_zeroIdeal_mul_le (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) :
    idealMod (x := x) (zeroIdeal D σ) I * D.sub I ≤ Submodule.span (chartRing S x I) {σ} := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.mul_le]
  intro a ha δ hδ
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, s, e, hf, hs, hfe, hse, rfl⟩ := ha
    have h := homogeneousComponent_mul_mem D σ I hi hf e δ hδ
    rw [homogeneousComponent_of_mem hfe, if_pos rfl] at h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse,
      by rw [map_pow, aeval_X]⟩ * t, ?_⟩
    rw [chartRing_smul_def, Subalgebra.coe_mul,
      show aeval x f / aeval x s * δ = aeval x f * δ / aeval x s by ring, ← ht, chartRing_smul_def]
    field_simp
    try ring
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha

end Lemmas

theorem proof : StepThree.Away.Statement.{u, w} := by
  intro k _ Ω _ _ N x T b c hc I
  obtain ⟨i, hi⟩ := I.2.1
  have hL : ∀ I' : Chart x, T.L.sub I' = twistMod k x T.c₁ I' * T.D.sub I' := by
    intro I'
    change ((T.M.toSubSystem.pow T.p).twist (twistSys k x T.m)).sub I' =
      _ * ((T.M.toSubSystem.pow T.p).twist (twistSys k x (T.m - T.c₁))).sub I'
    rw [twist_sub, twist_sub, twistSys_sub, twistSys_sub, ← mul_assoc, twistMod_mul,
      add_sub_cancel]
  have hF : ∀ I' : Chart x, ((T.L.pow b).twist (twistSys k x c)).sub I' =
      twistMod k x (c + b * T.c₁) I' * T.D.sub I' ^ b := by
    intro I'
    rw [twist_sub, twistSys_sub, pow_sub, hL, mul_pow, twistMod_pow, ← mul_assoc, twistMod_mul]
  have hn : 0 ≤ c + b * T.c₁ :=
    add_nonneg hc (mul_nonneg (Nat.cast_nonneg b) (by linarith [T.c₁_pos]))
  obtain ⟨n, hnn⟩ := Int.eq_ofNat_of_zero_le hn

  have hy : x i ^ n * T.si ^ b ∈ ((T.L.pow b).twist (twistSys k x c)).secs := by
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    change _ ∈ ((T.L.pow b).twist (twistSys k x c)).sub I'
    rw [hF I', hnn]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _,
      isHomogeneous_X_pow i n, isHomogeneous_one _ _, by simp, by simp⟩)
      (Submodule.pow_mem_pow _ ?_ b)
    exact (Submodule.mem_iInf _).mp T.si_mem I'

  have hbound : idealMod (x := x) T.J I ^ b * ((T.L.pow b).twist (twistSys k x c)).sub I ≤
      Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
    rw [hF I, mul_left_comm, ← mul_pow]
    calc twistMod k x (c + b * T.c₁) I * (idealMod (x := x) T.J I * T.D.sub I) ^ b
        ≤ twistMod k x (c + b * T.c₁) I * Submodule.span (chartRing k x I) {T.si} ^ b := by
          gcongr
          exact idealMod_zeroIdeal_mul_le T.D T.si I
      _ = Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
          rw [twistMod_eq_span _ I hi, span_singleton_pow_eq, Submodule.span_mul_span,
            Set.singleton_mul_singleton, hnn, zpow_natCast]
  rw [Submodule.smul_le]
  intro r hr z hz
  have hr' : (r : Ω) ∈ idealMod (x := x) T.J I ^ b := by
    have hm := Submodule.mem_map_of_mem (f := (Algebra.ofId (chartRing k x I) Ω).toLinearMap) hr
    rw [Submodule.map_pow] at hm
    have hle : Submodule.map (Algebra.ofId (chartRing k x I) Ω).toLinearMap
        ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ≤
          idealMod (x := x) T.J I := by
      rintro y ⟨a, ha, rfl⟩
      exact ha
    exact pow_le_pow_left' hle b hm
  have hrz := hbound (Submodule.mul_mem_mul hr' hz)
  rw [chartRing_smul_def]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr hy) hrz

end StepThree.Away

end

end GroundTheory.Heights₂.Heights.Kleiman
end
