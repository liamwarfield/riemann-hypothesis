module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntEqOfWeightedSumEqWithSmallErrors
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpPiIInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PeriodMapIntegerVector
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSplitOfCoisotropicKer
noncomputable section

namespace GlobalTheory

namespace KerPerp

variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}

theorem exists_isotropic_section [Module.Projective O Y] {w : O} (hw : w + star w = 1) (halt : EF.IsAlt)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ s : Y →ₗ[O] L, (∀ x, y (s x) = x) ∧ ∀ x x', EF (s x) (s x') = 0 := by
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property y LinearMap.id hy
  have hs0' : ∀ x, y (s0 x) = x := fun x => LinearMap.congr_fun hs0 x
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : kerPerp hadj y ≤ LinearMap.ker y := fun t ht => hle t (mem_kerPerp.1 ht)
  obtain ⟨be, hbe_apply⟩ : ∃ be : LinearMap.BilinForm ℤ Y,
      ∀ x x', be x x' = EF (s0 x) (s0 (w • x')) :=
    ⟨EF.compl₁₂ s0.toAddMonoidHom.toIntLinearMap
      (s0.toAddMonoidHom.toIntLinearMap ∘ₗ (LinearMap.lsmul O Y w).toAddMonoidHom.toIntLinearMap),
      fun _ _ => rfl⟩
  have hbe : ∀ (a : O) x x', be (a • x) x' = be x (star a • x') := by
    intro a x x'
    rw [hbe_apply, hbe_apply, map_smul s0 a x, hadj, map_smul s0 w (star a • x'), map_smul s0 w x',
      map_smul s0 (star a) x', smul_comm]
  have hn := neg_apply_nilTo hadj hb hy hbe
  refine ⟨s0 + (kerPerp hadj y).subtype ∘ₗ nilTo hadj hb hy hbe ∘ₗ s0, fun x => ?_, fun x x' => ?_⟩
  · have h0 : y ((nilTo hadj hb hy hbe (s0 x) : L)) = 0 :=
      LinearMap.mem_ker.1 (hle' (nilTo hadj hb hy hbe (s0 x)).2)
    simp [hs0', h0]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _)]
    have h1 := hn (s0 x) (s0 x')
    have h2 := hn (s0 x') (s0 x)
    rw [hs0', hs0', hbe_apply] at h1 h2
    have h3 := isotropic hle' (nilTo hadj hb hy hbe (s0 x)).2 (nilTo hadj hb hy hbe (s0 x')).2
    have h4 := skew (s0 x) (nilTo hadj hb hy hbe (s0 x'))
    have k1 : EF (s0 x') (s0 (w • x)) = -EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x, skew, hadj]
    have k2 : EF (s0 x) (s0 x') = EF (s0 x) (s0 (w • x')) + EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x', ← map_add (EF (s0 x)), ← add_smul, hw, one_smul]
    linarith

end KerPerp

theorem exists_split_of_coisotropic_ker (O L Y : Type) [CommRing O] [StarRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module.Projective O Y] (w : O)
    (EF : LinearMap.BilinForm ℤ L) (y : L →ₗ[O] Y) (hw : w + star w = 1) (halt : ∀ x, EF x x = 0)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module O M) (EM : LinearMap.BilinForm ℤ M) (e : L ≃+ Y × (Y →+ ℤ) × M),
      Function.Bijective EM ∧ (∀ v, (e v).1 = y v) ∧
      (∀ (a : O) v x, (e (a • v)).2.1 x = (e v).2.1 (star a • x)) ∧
      (∀ (a : O) v, (e (a • v)).2.2 = a • (e v).2.2) ∧
      ∀ v v', EF v v' = (e v').2.1 (e v).1 - (e v).2.1 (e v').1 + EM (e v).2.2 (e v').2.2 := by
  obtain ⟨s, hsy, hsiso⟩ := KerPerp.exists_isotropic_section (EF := EF) (y := y) hw halt hb hadj hy hle
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : KerPerp.kerPerp hadj y ≤ LinearMap.ker y := fun t ht =>
    hle t (KerPerp.mem_kerPerp.1 ht)
  obtain ⟨E, hE⟩ : ∃ E : KerPerp.kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y,
      ∀ (t : KerPerp.kerPerp hadj y) (v : L), E t (y v) = -EF t v :=
    ⟨KerPerp.equivDual hadj hb hy, KerPerp.equivDual_apply hadj hb hy⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L →ₗ[ℤ] Module.Dual ℤ Y, ∀ v x, Φ v x = -EF v (s x) :=
    ⟨-(EF.compl₂ s.toAddMonoidHom.toIntLinearMap), fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : L →ₗ[ℤ] L, ∀ v, T v = ((E.symm (Φ v) : KerPerp.kerPerp hadj y) : L) :=
    ⟨(KerPerp.kerPerp hadj y).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ Φ,
      fun _ => rfl⟩
  have hTK : ∀ v, T v ∈ KerPerp.kerPerp hadj y := fun v => by rw [hTdef]; exact (E.symm (Φ v)).2
  have hEF : ∀ (t : KerPerp.kerPerp hadj y) w, EF t w = -E t (y w) := fun t w => by rw [hE]; ring
  have hT : ∀ v w, EF (T v) w = EF v (s (y w)) := fun v w => by
    rw [hTdef, hEF, LinearEquiv.apply_symm_apply, hΦ, neg_neg]
  have hTy : ∀ v, y (T v) = 0 := fun v => LinearMap.mem_ker.1 (hle' (hTK v))
  obtain ⟨P, hP⟩ : ∃ P : L →ₗ[ℤ] L, ∀ v, P v = v - s (y v) - T v :=
    ⟨LinearMap.id - s.toAddMonoidHom.toIntLinearMap ∘ₗ y.toAddMonoidHom.toIntLinearMap - T,
      fun _ => rfl⟩
  have hPy : ∀ v, y (P v) = 0 := fun v => by
    rw [hP, map_sub, map_sub, hsy, hTy, sub_self, sub_zero]
  have hPs : ∀ v x, EF (P v) (s x) = 0 := fun v x => by
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsiso, hT, hsy]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule O L, ∀ v, v ∈ N ↔ y v = 0 ∧ ∀ x, EF v (s x) = 0 :=
    ⟨{ carrier := {v | y v = 0 ∧ ∀ x, EF v (s x) = 0}
       add_mem' := fun {a b} ha hb => ⟨by rw [map_add (f := _), ha.1, hb.1, add_zero],
         fun x => by rw [map_add (f := _), LinearMap.add_apply, ha.2, hb.2, add_zero]⟩
       zero_mem' := ⟨map_zero y, fun x => by rw [map_zero, LinearMap.zero_apply]⟩
       smul_mem' := fun c v hv => ⟨by rw [map_smul, hv.1, smul_zero],
         fun x => by rw [hadj, ← map_smul s, hv.2]⟩ }, fun _ => Iff.rfl⟩
  have hPN : ∀ v, P v ∈ N := fun v => (hN _).2 ⟨hPy v, hPs v⟩
  have hΦN : ∀ m ∈ N, Φ m = 0 := fun m hm => LinearMap.ext fun x => by
    rw [hΦ, ((hN m).1 hm).2, neg_zero, LinearMap.zero_apply]
  have hPfix : ∀ m ∈ N, P m = m := fun m hm => by
    simp [hP, ((hN m).1 hm).1, hTdef, hΦN m hm]
  have hTsmul : ∀ (a : O) v, T (a • v) = a • T v := fun a v => hb.1 (LinearMap.ext fun w => by
    rw [hT, hadj, hadj, hT, map_smul y, map_smul s])
  have hdec : ∀ v, v = s (y v) + T v + P v := fun v => by rw [hP]; abel
  have hback : ∀ φ : Module.Dual ℤ Y, φ.toAddMonoidHom.toIntLinearMap = φ :=
    fun φ => LinearMap.ext fun _ => rfl
  let e : L ≃+ Y × (Y →+ ℤ) × N :=
    { toFun := fun v => (y v, (Φ v).toAddMonoidHom, ⟨P v, hPN v⟩)
      invFun := fun p => s p.1 + ((E.symm p.2.1.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
        (p.2.2 : L)
      left_inv := fun v => by
        show s (y v) + ((E.symm (Φ v).toAddMonoidHom.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
          P v = v
        rw [hback, ← hTdef]
        exact (hdec v).symm
      right_inv := fun p => by
        obtain ⟨a, φ, m⟩ := p
        have hyt : y ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) = 0 :=
          LinearMap.mem_ker.1 (hle' (E.symm _).2)
        have hym : y (m : L) = 0 := ((hN m).1 m.2).1
        have hyv : y (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) = a := by
          rw [map_add (f := _), map_add (f := _), hsy, hyt, hym, add_zero, add_zero]
        have hΦv : Φ (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) =
            φ.toIntLinearMap := by
          refine LinearMap.ext fun x => ?_
          rw [hΦ, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hsiso, hEF, hsy,
            LinearEquiv.apply_symm_apply, ((hN m).1 m.2).2]
          simp
        refine Prod.ext hyv (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ _ x = φ x
          rw [hΦv]
          rfl
        · show P _ = m
          rw [hP, hyv, hTdef, hΦv]
          exact (fun p q r : L => show p + q + r - p - q = r by abel) _ _ _
      map_add' := fun a b => by
        refine Prod.ext (map_add y a b) (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ (a + b) x = Φ a x + Φ b x
          rw [map_add (f := _), LinearMap.add_apply]
        · show P (a + b) = P a + P b
          exact map_add P a b }
  refine ⟨N, inferInstance, inferInstance,
    EF.compl₁₂ N.subtype.toAddMonoidHom.toIntLinearMap N.subtype.toAddMonoidHom.toIntLinearMap, e,
    ⟨?_, ?_⟩, fun v => rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    apply hb.1
    refine LinearMap.ext fun w => ?_
    have hm' : EF (m : L) (P w) = 0 := by
      simpa using LinearMap.congr_fun hm ⟨P w, hPN w⟩
    have hmN := (hN m).1 m.2
    rw [Submodule.coe_zero, map_zero, LinearMap.zero_apply, hdec w, map_add (f := _), map_add (f := _), hmN.2, hm',
      skew, hT, hmN.1, map_zero, map_zero]
    simp
  · intro g
    obtain ⟨v, hv⟩ := hb.2 (g ∘ₗ (AddMonoidHom.mk' (fun v => (⟨P v, hPN v⟩ : N))
      (fun a b => Subtype.ext (map_add P a b))).toIntLinearMap)
    refine ⟨⟨P v, hPN v⟩, LinearMap.ext fun m => ?_⟩
    have h1 : EF v m = g ⟨P m, hPN m⟩ := LinearMap.congr_fun hv m
    have h2 : (⟨P m, hPN m⟩ : N) = m := Subtype.ext (hPfix m m.2)
    have hmN := (hN m).1 m.2
    show EF (P v) m = g m
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, skew (s (y v)), hmN.2, hT, hmN.1, map_zero, map_zero]
    simp
  · intro a v x
    show Φ (a • v) x = Φ v (star a • x)
    rw [hΦ, hΦ, hadj, map_smul s]
  · intro a v
    refine Subtype.ext ?_
    show P (a • v) = a • P v
    rw [hP, hP, map_smul y, map_smul s, hTsmul, smul_sub, smul_sub]
  · intro v v'
    show EF v v' = Φ v' (y v) - Φ v (y v') + EF (P v) (P v')
    rw [hΦ, hΦ, hP, hP]
    simp only [map_sub, LinearMap.sub_apply]
    have f1 := hT v v'
    have f2 := hT v (s (y v'))
    rw [hsy] at f2
    have f3 : EF v (T v') = -EF v' (s (y v)) := by rw [skew, hT]
    have f4 : EF (s (y v)) (T v') = -EF v' (s (y (s (y v)))) := by rw [skew, hT]
    rw [hsy] at f4
    have f5 := hsiso (y v) (y v')
    have f6 : EF (T v) (T v') = 0 := KerPerp.isotropic hle' (hTK v) (hTK v')
    have f7 := skew (s (y v)) v'
    linarith

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Imports
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

namespace GlobalTheory.ComplementTypes

theorem _root_.GlobalTheory.ComplementTypes.types (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q r g g' : ℕ)
    (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ)) (hty : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty)
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = (r : ℂ) * ∑ τ : E →+* ℂ, τ (H.bar a : E) + ∑ j, ty' j (a : E)) :
    r ≤ p ∧ r ≤ q ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H (p - r) (q - r) ty' := by
  classical
  let c : E →+* E := (IsCMField.complexConj E).toAlgHom.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => by simp [c]
  let t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ) := Sum.elim (fun k => k.2.comp c) ty'
  have hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E) := by
    intro a
    rw [h a, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [t, c, H.bar_eq]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum
  have key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ} := by
    intro τ
    have hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c := fun σ =>
      ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by
        simp only [he]), Fintype.card_subtype,
      Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    congr 1
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  have hconj : conj H.rt0 = -H.rt0 := by
    have hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
    · exfalso
      have hre := Complex.conj_eq_iff_re.1 h'
      have h2 := H.sqrt_neg_disc_sq
      rw [← hre] at h2
      have h3 := congrArg Complex.re h2
      simp [pow_two] at h3
      nlinarith [mul_self_nonneg H.rt0.re]
    · exact h'
  have hne : -H.rt0 ≠ H.rt0 := by
    intro h0
    have h1 : H.rt0 = 0 := by linear_combination -h0 / 2
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    have h3 := congrArg Complex.re h2
    simp at h3
    have := H.d_prime.two_le
    omega
  have hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨τ0, h0⟩
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩
  obtain ⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩
    · exact ⟨τ0, by rw [h0]; exact hne⟩
  have hp := (hty τ1).1 h1
  have hq := (hty τ2).2 h2
  have k1 := key τ1
  have k2 := key τ2
  refine ⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have := (hty τ).1 hτ
    have := key τ
    omega
  · have := (hty τ).2 hτ
    have := key τ
    omega

end GlobalTheory.ComplementTypes
end

noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Complex

section Model

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem period_map_integer_vector (n : A.X →+ ℤ) : A.P0 (AnArc.La.mk 0 n 0) = ((Int.castAddHom ℂ).comp n, 0) := by
  ext <;> simp

theorem snd_eq_zero_iff (v : A.V) :
    v.2 = 0 ↔ v ∈ Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0)) := by
  constructor
  · intro hv
    have : v.1 ∈ (Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0))).comap (LinearMap.inl ℂ _ _) := by
      refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := v.1)))
      rintro _ ⟨n, rfl⟩
      exact Submodule.subset_span ⟨n, period_map_integer_vector A n⟩
    have h : v = LinearMap.inl ℂ _ _ v.1 := Prod.ext rfl hv
    rwa [h]
  · intro hv
    refine LinearMap.eqOn_span (f := LinearMap.snd ℂ _ _) (g := 0) ?_ hv
    rintro _ ⟨n, rfl⟩
    simp

theorem torusProj_eq_zero_iff {w : ℂ} (hw : (A.BwMat w).PosDef) (v : A.V) :
    A.torusProj v = 0 ↔ ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = 0 := by
  have h1 : ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = A.dualForm w (A.torusProj v) ((Int.castAddHom ℂ).comp n) :=
    fun n => by rw [period_map_integer_vector, A.Hw_apply]; simp [AnArc.torusProj_def]
  simp only [h1]
  refine ⟨fun h n => by simp [h], fun h => ?_⟩
  have h2 : A.dualForm w (A.torusProj v) = 0 := LinearMap.ext_on_range span_intHom h
  by_contra hne
  have := A.dualForm_pos hw hne
  simp [h2] at this

theorem trace_actV {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (A : AnArc (𝓞 E))
    {ty : Fin A.gB → (E →+* ℂ)} (hF : ∀ a z i, A.F a z i = ty i (a : E) * z i) (a : 𝓞 E) :
    LinearMap.trace ℂ A.V (A.actV a) =
      (Module.finrank (𝓞 E) A.X : ℂ) * ∑ τ : E →+* ℂ, τ ((star a : 𝓞 E) : E) + ∑ i, ty i (a : E) := by
  let f : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ A.actV a ∘ₗ LinearMap.inl ℂ _ _
  have h1 : A.actV a = f.prodMap (A.F a) := LinearMap.ext fun v => rfl
  have h2 : A.F a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [hF, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E A.X (star a) f fun _ _ => rfl, h2]
  simp

abbrev moduleLam : Module O A.abelian₂ where
  smul := A.FLam
  one_smul l := Subtype.ext (by show A.F 1 l = l; simp)
  mul_smul a b l := Subtype.ext (by show A.F (a * b) l = A.F a (A.F b l); simp)
  smul_zero a := Subtype.ext (map_zero (A.F a))
  smul_add a l m := Subtype.ext (map_add (A.F a) _ _)
  add_smul a b l := Subtype.ext (by show A.F (a + b) l = A.F a l + A.F b l; simp)
  zero_smul l := Subtype.ext (by show A.F 0 l = 0; simp)

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_datum_Lam : letI := H.starRing;
    ∀ (A : AnArc (𝓞 E)) (p q : ℕ) (ty : Fin A.gB → (E →+* ℂ)), IsTypeFn H p q ty →
      (∀ a z i, A.F a z i = ty i (a : E) * z i) →
      ∃ (DB : Datum H) (e : DB.La ≃+ A.abelian₂), DB.p = p ∧ DB.q = q ∧ (∀ (a : 𝓞 E) x, e (a • x) = A.FLam a (e x)) ∧
        (∀ x x', DB.EF x x' = A.Ef (e x) (e x')) ∧
        IsPeriod DB ty (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddMonoidHom) := by
  let _ := H.starRing
  intro A p q ty hty hF
  let _ := moduleLam A
  have hr : Set.range A.abelian₂.subtype.toAddMonoidHom = A.abelian₂ := Subtype.range_coe
  have hd : ∀ G : AddSubgroup (Fin A.gB → ℂ), (G : Set (Fin A.gB → ℂ)) = A.abelian₂ → DiscreteTopology G := fun G hG => by
    have : G = A.abelian₂.toAddSubgroup := SetLike.coe_injective hG
    rw [this]; exact A.discrete
  obtain ⟨DB, e, hp, hq, he⟩ := PeriodDatum.exists_datum E H A.abelian₂ A.Ef p q A.gB ty A.abelian₂.subtype.toAddMonoidHom A.Hm hty
    A.Ef_bij A.Ef_FLam (fun a x i => hF a x i) Subtype.val_injective (hd _ hr) (hr ▸ A.full) A.Hm_herm A.Hm_pos
    fun x y => (A.Ef_eq x y).symm
  have hr' : Set.range (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom) = A.abelian₂ :=
    (e.surjective.range_comp A.abelian₂.subtype.toAddMonoidHom).trans hr
  refine ⟨DB, e.toAddEquiv, hp, hq, e.map_smul, he, fun a x i => ?_, Subtype.val_injective.comp e.injective, hd _ hr',
    hr' ▸ A.full, A.Hm, A.Hm_herm, A.Hm_pos, fun x y => ?_⟩
  · exact (congrArg (fun l : A.abelian₂ => l.1 i) (e.map_smul a x)).trans (hF a _ i)
  · rw [he]; exact (A.Ef_eq _ _).symm

theorem exists_anArc_of_period (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (Hh : Submodule (𝓞 E) D.La) (hsat : ∀ (k : ℤ) (t : D.La), k ≠ 0 → k • t ∈ Hh → t ∈ Hh)
    (hiso : ∀ t ∈ Hh, ∀ t' ∈ Hh, D.EF t t' = 0)
    {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] (y : D.La →ₗ[𝓞 E] Y) (hy : Function.Surjective y)
    (hker : ∀ v, y v = 0 ↔ ∀ t ∈ Hh, D.EF t v = 0)
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x x', be x x' = be x' x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : 𝓞 E) x x', be (a • x) x' = be x (H.bar a • x')) (be_even : ∀ x, (2 : ℤ) ∣ be x x) :
    letI := H.starRing;
    ∃ (A : AnArc (𝓞 E)) (e : A.X ≃ₗ[𝓞 E] Y) (gam : D.La ≃ₗ[𝓞 E] A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] A.V),
      (∀ x x', A.be x x' = be (e x) (e x')) ∧
      (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))) ∧
      (∀ v v', A.EF (gam v) (gam v') = D.EF v v') ∧
      (∀ v, e (gam v).y = y v) ∧
      (∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0) ∧
      (∀ (a : 𝓞 E) z, h (fun i => ty i (a : E) * z i) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (gam v)) ∧
      (A.BwMat 0).PosDef ∧
      (∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z') ∧
      (∀ z, (h z).2 = 0 ↔ z ∈ Submodule.span ℂ (P '' Hh)) ∧
      (∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0) ∧
      (∀ u u', (∀ t ∈ Hh, hermForm Hm u (P t) = 0) → A.H (h u).2 (h u').2 = hermForm Hm u u') ∧
      (∀ l, l ∈ A.abelian₂ ↔ ∃ v, y v = 0 ∧ (h (P v)).2 = l) ∧
      (∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) ∧
      (∀ k : ℤ, (∀ v, y v = 0 → ∀ a ∈ Submodule.span ℝ (P '' Hh), (∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) →
        k • a ∈ P '' Hh) → ∀ x, k • A.ct x ∈ A.abelian₂) ∧
      Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh ∧
      ∃ tyB : Fin A.gB → (E →+* ℂ), (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧
        (IsTypeFn H D.p D.q ty → Module.finrank (𝓞 E) Hh ≤ D.p ∧ Module.finrank (𝓞 E) Hh ≤ D.q ∧
          IsTypeFn H (D.p - Module.finrank (𝓞 E) Hh) (D.q - Module.finrank (𝓞 E) Hh) tyB ∧
          ∃ (DB : Datum H) (eB : DB.La ≃+ A.abelian₂), DB.p = D.p - Module.finrank (𝓞 E) Hh ∧
            DB.q = D.q - Module.finrank (𝓞 E) Hh ∧ (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧
            (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
            IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)) := by
  let _ := H.starRing
  obtain ⟨hlin, hinj, hdisc, hspan, Hm', hherm, hpos', hHm'⟩ := hP
  have hS : ∀ z z', sesq Hm z z' = sesq Hm' z z' := sesq_ext hspan fun i k => (hHm i k).trans (hHm' i k).symm
  have hconj : ∀ z z', starRingEnd ℂ (sesq Hm z z') = sesq Hm z' z := fun z z' => by
    rw [hS, hS, sesq_conj hherm]
  have hpos : ∀ z, z ≠ 0 → 0 < (sesq Hm z z).re := fun z hz => by rw [hS]; exact hpos' z hz
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  have hadj : ∀ (a : 𝓞 E) x x', D.EF (a • x) x' = D.EF x (star a • x') := D.adj
  have halt : D.EF.IsAlt := D.alt
  obtain ⟨hfin, hrk, -⟩ := PeriodDatum.lattice_equiv P hinj hdisc hspan
  have : Module.IsTorsionFree ℤ D.La := hinj.moduleIsTorsionFree _ (map_zsmul P)
  have : Module.Finite ℤ Y := Module.Finite.of_surjective y.toAddMonoidHom.toIntLinearMap hy
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
    obtain ⟨v, rfl⟩ := hy x
    refine or_iff_not_imp_left.2 fun hk => (hker v).2 fun t ht => ?_
    simpa [hk] using (hker (k • v)).1 (by rw [map_zsmul, hx]) t ht
  have : Module.Free ℤ Y := Module.free_of_finite_type_torsion_free'
  have := Forms.projective_of_int (𝓞 E) Y
  have hHh : ∀ t, t ∈ Hh ↔ ∀ v, y v = 0 → D.EF t v = 0 := fun t => by
    have : Module.Finite ℤ (D.La ⧸ Hh) :=
      Module.Finite.of_surjective Hh.mkQ.toAddMonoidHom.toIntLinearMap Hh.mkQ_surjective
    have : Module.IsTorsionFree ℤ (D.La ⧸ Hh) := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
      obtain ⟨v, rfl⟩ := Hh.mkQ_surjective x
      refine or_iff_not_imp_left.2 fun hk => (Submodule.Quotient.mk_eq_zero _).2 (hsat k v hk ?_)
      exact (Submodule.Quotient.mk_eq_zero _).1 ((map_zsmul Hh.mkQ k v).trans hx)
    have : Module.Free ℤ (D.La ⧸ Hh) := Module.free_of_finite_type_torsion_free'
    refine ⟨fun ht v hv => (hker v).1 hv t ht, fun ht => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
    refine (KerPerp.ker_iff (hadj := hadj) (y := Hh.mkQ) D.unimod.2 t).2 fun v hv => ?_
    exact halt.eq_iff.1 (ht v ((hker v).2 fun t' ht' =>
      halt.eq_iff.1 (hv t' ((Submodule.Quotient.mk_eq_zero _).2 ht'))))
  obtain ⟨M, _, _, EM, e₀, hEM, he₁, he₂, he₃, hE⟩ := exists_split_of_coisotropic_ker (𝓞 E) D.La Y H.w0 D.EF y hw D.alt
    D.unimod hadj hy fun t ht => (hker t).2 fun t' ht' => hiso t' ht' t ((hHh t).2 ht)
  have : Module.Finite ℤ M := Module.Finite.of_surjective
    ((AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp e₀.toAddMonoidHom)).toIntLinearMap
    fun m => ⟨e₀.symm (0, 0, m), by simp⟩
  have : Module.IsTorsionFree ℤ M := Function.Injective.moduleIsTorsionFree (fun m : M => e₀.symm (0, 0, m))
    (fun m m' hm => by simpa using hm) fun k m => by rw [← map_zsmul]; simp
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  have hrk' : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ (Fin g → ℂ) := by
    have : Module.Finite ℤ (Y →+ ℤ) := Module.Finite.equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    have : Module.Free ℤ (Y →+ ℤ) := Module.Free.of_equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    rw [e₀.toIntLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, finrank_hom_int] at hrk
    rw [Module.finrank_fin_fun]
    omega
  let ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
    { toFun := fun a => LinearMap.pi fun i => ty i (a : E) • LinearMap.proj i
      map_one' := by ext; simp
      map_mul' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [add_mul] }
  have hρ : ∀ a z, ρ a z = fun i => ty i (a : E) * z i := fun _ _ => rfl
  have hPρ : ∀ a v, P (a • v) = ρ a (P v) := fun a v => funext (hlin a v)
  have hρS : ∀ a z z', sesq Hm (ρ a z) z' = sesq Hm z (ρ (star a) z') := fun a =>
    sesq_ext (S := sesq Hm ∘ₗ ρ a) (S' := (sesq Hm).compl₂ (ρ (star a))) hspan fun v v' => by
      show (hermForm Hm (ρ a (P v)) (P v')).im = (hermForm Hm (P v) (ρ (star a) (P v'))).im
      rw [← hPρ, ← hPρ, hHm, hHm, hadj]
  have he : ∀ (a : 𝓞 E) v, e₀ (a • v) =
      (a • (e₀ v).1, (e₀ v).2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • (e₀ v).2.2) := fun a v =>
    Prod.ext (by rw [he₁, he₁, map_smul]) (Prod.ext (AddMonoidHom.ext (he₂ a v)) (he₃ a v))
  obtain ⟨A, e, f, h, hbe, hchi, hpsi, hQ, hfF, hEf, hact, hh, hB⟩ := exists_arc hw EM hEM
    (P.comp e₀.symm.toAddMonoidHom)
    ((congrArg _ (e₀.symm.surjective.range_comp P)).trans hspan) hrk' hconj hpos
    (fun v v' => by
      show (hermForm Hm (P (e₀.symm v)) (P (e₀.symm v'))).im = _
      rw [hHm, hE, e₀.apply_symm_apply, e₀.apply_symm_apply]) ρ hρS
    (fun a v => by
      obtain ⟨v, rfl⟩ := e₀.surjective v
      rw [← he]
      simp [hPρ]) be be_symm be_pos be_adj be_even
    (fun n F => ∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) exists_diag
  obtain ⟨tyB, hF⟩ := hQ
  let gam : D.La ≃ₗ[𝓞 E] A.La :=
    { toFun := fun v => AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2)
      invFun := fun v => e₀.symm (e v.y, v.n.comp e.symm.toAddEquiv.toAddMonoidHom, f.symm v.l)
      map_add' := fun v v' => by ext <;> simp
      map_smul' := fun a v => by ext <;> simp [he, hfF]
      left_inv := fun v => e₀.injective (by ext <;> simp)
      right_inv := fun v => by ext <;> simp }
  have hgam : ∀ v, gam v =
      AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2) := fun _ => rfl
  have hiso' : ∀ v v', A.EF (gam v) (gam v') = D.EF v v' := fun v v' => by
    simp [hgam, AnArc.EF_apply, hEf, hE]
  have hgy : ∀ v, e (gam v).y = y v := fun v => by simp [hgam, he₁]
  have hgy0 : ∀ v, (gam v).y = 0 ↔ y v = 0 := fun v => by rw [← hgy, e.map_eq_zero_iff]
  have hgH : ∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0 := fun v => by
    rw [hHh, ← A.orth_ker_iff_exists, gam.surjective.forall]
    simp only [hgy0, hiso']
  have hhP : ∀ v, h (P v) = A.P0 (gam v) := fun v => by simpa [hgam] using hh (e₀ v)
  have hP0 : ∀ v, A.Pw 0 v = A.P0 v := fun v => by simp [AnArc.Pw_apply]
  have hHw : ∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z' :=
    sesq_ext (S := (A.Hw 0 ∘ₗ h.toLinearMap).compl₂ h.toLinearMap) (S' := sesq Hm) hspan fun v v' => by
      show (A.Hw 0 (h (P v)) (h (P v'))).im = (hermForm Hm (P v) (P v')).im
      rw [hhP, hhP, ← hP0, ← hP0, A.im_Hw_Pw hB, hiso', hHm]
  have himg : h '' (P '' Hh) = Set.range fun n => A.P0 (AnArc.La.mk 0 n 0) := by
    ext v
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      obtain ⟨n, hn⟩ := (hgH t).1 ht
      exact ⟨n, by rw [hhP, hn]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨gam.symm (AnArc.La.mk 0 n 0), (hgH _).2 ⟨n, by simp⟩, rfl⟩, by simp [hhP]⟩
  have hU : ∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0 := fun z => by
    rw [torusProj_eq_zero_iff A hB, ← Set.forall_mem_range (p := fun v => A.Hw 0 (h z) v = 0), ← himg]
    simp only [Set.forall_mem_image, hHw, SetLike.mem_coe]
  have hRind : ∀ z, (∀ t ∈ Hh, (sesq Hm z (P t)).im = 0) → ∀ r ∈ Submodule.span ℝ (P '' Hh), (sesq Hm z r).im = 0 :=
    fun z hz r hr => LinearMap.eqOn_span (f := imForm (sesq Hm) z) (g := 0) (by rintro _ ⟨t, ht, rfl⟩; exact hz t ht) hr
  have him : ∀ z z', (sesq Hm z z').im = -(sesq Hm z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hperp : ∀ v, y v = 0 → ∀ t ∈ Hh, (sesq Hm (P v) (P t)).im = 0 := fun v hv t ht => by
    rw [him, sesq_apply, hHm, (hker v).1 hv t ht]; simp
  have hex : ∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0 := by
    obtain ⟨b, hb, hb'⟩ := exists_imPart hpos (R := Submodule.span ℝ (P '' Hh)) fun r hr => hRind r fun t ht => by
      rw [him, hRind _ (hperp t ((hker t).2 fun t' ht' => hiso t' ht' t ht)) r hr, neg_zero]
    refine fun v hv => ⟨b (I • P v), ⟨hb _, fun t ht => ?_⟩, fun a ha => Eq.symm ?_⟩
    · rw [← sesq_apply, map_sub, LinearMap.sub_apply, hb' _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)]
      apply Complex.ext <;> simp [hperp v hv t ht]
    · refine imPart_eq hpos hb hb' ha.1 fun r hr => ?_
      have := LinearMap.eqOn_span (f := reForm (sesq Hm) (P v - a)) (g := 0)
        (by rintro _ ⟨t, ht, rfl⟩; exact congrArg Complex.re (ha.2 t ht)) hr
      simp at this ⊢
      linarith
  have hrank : Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh := by
    have h1 : KerPerp.kerPerp hadj y = Hh := Submodule.ext fun t => (hHh t).symm
    have h2 := KerPerp.finrank_kerPerp hadj D.unimod hy
    have := D.fin
    have : Module.Finite (𝓞 E) Y := Module.Finite.of_surjective y hy
    rw [h1, finrank_int_eq_mul_of_finite (O := 𝓞 E), finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := Y)] at h2
    rw [e.finrank_eq, Nat.eq_of_mul_eq_mul_left Module.finrank_pos h2]
  refine ⟨A, e, gam, h, hbe, hchi, hpsi, hiso', hgy, hgH, hact, hhP, hB, hHw, fun z => ?_, hU, fun u u' hu => ?_,
    fun l => ⟨fun hl => ?_, ?_⟩, hex, fun k hk x => ?_, hrank, tyB, hF, fun hty => ?_⟩
  · rw [snd_eq_zero_iff, ← himg]
    exact Submodule.apply_mem_span_image_iff_mem_span (f := h.toLinearMap) h.injective
  · rw [← hHw, A.Hw_apply, (hU u).2 hu]; simp
  · exact ⟨gam.symm (AnArc.La.mk 0 0 ⟨l, hl⟩), (hgy0 _).1 (by simp), by simp [hhP]⟩
  · rintro ⟨v, hv, rfl⟩
    simp [hhP, (hgy0 v).2 hv]
  · refine zsmul_mem_Lam A k _ fun l => ?_
    obtain ⟨v, hv⟩ := gam.surjective (AnArc.La.mk 0 0 l)
    have hv0 : y v = 0 := (hgy0 v).1 (by simp [hv])
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hex v hv0
    obtain ⟨t, ht, hta⟩ := hk v hv0 a ha ha'
    obtain ⟨n, hn⟩ := (hgH t).1 ht
    have h1 := congrArg (fun z => A.torusProj (h z) x) hta
    have h2 := congrArg (fun r => r x) ((hU _).2 ha')
    simp only [map_sub, map_zsmul, hhP, hv, hn, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
      AnArc.torusProj_periodZero_eq_real, AddMonoidHom.zero_apply] at h1 h2
    rw [← sub_eq_zero.1 h2] at h1
    refine ⟨n x, ?_⟩
    simpa using (congrArg Complex.re h1).symm
  · obtain ⟨h1, h2, h3⟩ := ComplementTypes.types E H D.p D.q (Module.finrank (𝓞 E) Hh) g A.gB ty tyB hty fun a => by
      have h4 : A.actV a = h.conj (ρ a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hact]
      have h5 : ρ a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
        LinearMap.ext fun z => funext fun i => by simp [hρ, Matrix.mulVec_diagonal]
      have h6 := trace_actV A hF a
      rw [h4, LinearMap.trace_conj', h5, hrank] at h6
      refine Eq.trans ?_ h6
      simp
    exact ⟨h1, h2, h3, exists_datum_Lam A _ _ tyB h3 hF⟩

end GlobalTheory.OfPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolating
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb relab
open scoped LaurentSeries

namespace GlobalTheory.AnAtFrame

open GlobalTheory.ArcFlow ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Transfer

variable {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]

omit [IsCMField E] in
lemma pairE_comp (e : X →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x)) (x : X) :
    pairE (E := E) ξ₁ x = pairE ξ (e x) := by
  simp only [pairE, h, map_smul]

lemma betaAt_comp (e : X ≃ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x))
    (be : LinearMap.BilinForm ℤ Y) (be₁ : LinearMap.BilinForm ℤ X) (hbe : ∀ x x', be₁ x x' = be (e x) (e x'))
    {N : ℕ} {ν₀ : E} {jj : ℤ} (hb : BetaAt ξ N be ν₀ jj) : BetaAt ξ₁ N be₁ ν₀ jj := by
  have hp : ∀ x, pairE (E := E) ξ₁ x = pairE ξ (e x) := pairE_comp e.toLinearMap ξ ξ₁ h
  refine ⟨hb.1, fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hb.2 s ⟨hs.1, fun y y' => by
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective y'
    rw [← hp, ← hp, hs.2, hbe]⟩
  refine ⟨h1, fun ν hν hν' hl => h2 ν hν hν' fun s' hs' => hl s' ⟨hs'.1, fun x x' => ?_⟩⟩
  rw [hp, hp]
  exact hs'.2 _ _

lemma adj_of_isBePar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (ξ : Module.Dual ℤ Y) (be : LinearMap.BilinForm ℤ Y) {s : E}
    (hs : IsBePar ξ be s) (a : 𝓞 E) (x x' : Y) : be (a • x) x' = be x (H.bar a • x') := by
  obtain ⟨p1, -⟩ := pairE_properties E Y ξ
  have h : (be (a • x) x' : ℚ) = be x (H.bar a • x') := by
    rw [← hs.2, ← hs.2, p1, p1, HermitianTraceFormVanishing.cc_mul, H.bar_eq]
    have : cc (IsCMField.complexConj E (a : E)) = a := by simp [FD.cc]
    rw [this]
    congr 1; ring
  exact_mod_cast h

end Transfer

variable {r : ℕ} (X : Data E r)

lemma transv_of_levelPar {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (y : La →ₗ[𝓞 E] Y) (hκ : X.κ0 = 2 * X.ξ0) (hrep : ∀ θ : Module.Dual ℤ Y, ∃ t, ∀ v, -EF t v = θ (y v))
    (ξ : Module.Dual ℤ Y) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) {N : ℕ} (hN : 0 < N) (s : E)
    (hs : LevelPar ξ N s) : ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm (φ t : Fin r → E) (s * X.κ0)).mulVec v - v = (N : E) • u := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have htr : ∀ (s : E) v v', Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ (y v'))) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm ((s * X.κ0 * herm X.Gm (φ v : Fin r → E) ξ') • ξ') (φ v')) := by
    intro s v v'
    rw [hp, hp, HermitianTraceFormVanishing.cc_mul, cc_neg, hc0, hcj, herm_smul_left, hκ]
    congr 1; ring
  intro w hw
  obtain ⟨v, rfl⟩ := hΛ w hw
  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual ℤ Y, ∀ x,
      Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ x)) = (N : ℚ) * θ x := by
    choose m hm using hs.2 (y v)
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨(AddMonoidHom.mk' m fun a b => ?_).toIntLinearMap, hm⟩
    have e := hm (a + b)
    rw [p2, cc_add, mul_add, map_add (f := _), hm, hm, ← mul_add] at e
    exact_mod_cast (mul_left_cancel₀ hN' e).symm
  obtain ⟨t', ht'⟩ := hrep θ
  refine ⟨-(φ t' : Fin r → E), X.Λ.neg_mem (φ t').2, ?_⟩
  rw [transvMat_mulVec, ← sub_eq_zero]
  refine eq_zero_of_trace_lattice X _ fun w hw => ?_
  obtain ⟨v', rfl⟩ := hΛ w hw
  have e := hθ (y v')
  rw [htr, ← ht', Int.cast_neg, iso, ← map_neg, ← nsmul_eq_mul, ← map_nsmul, ← sub_eq_zero, ← map_sub] at e
  rw [← neg_eq_zero, ← map_neg, ← e, herm_sub_left, smul_neg, ← neg_smul, herm_smul_left X.Gm (-(N : E))]
  congr 1; rw [nsmul_eq_mul]; ring

lemma re_eq_of_maj {x : Frame X.Ψ r} (hx : x ∈ X.dom) {La : Type} [AddCommGroup La] (φ : La →+ (Fin r → E)) {g : ℕ}
    (P : La →+ (Fin g → ℂ)) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (h : ∀ v, (hermForm Hm (P v) (P v)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ v))) (v w : La) :
    (hermForm Hm (P v) (P w)).re = ∑ τ, X.c τ * (X.Hf x τ (Data.emb τ.1 (φ v)) (Data.emb τ.1 (φ w))).re := by
  have hm : ∀ τ u, X.maj x τ u = (X.Hf x τ u u).re := fun τ u => by rw [X.Hf_self hx]; simp
  have he : ∀ τ : X.Ψ, Data.emb τ.1 (φ (v + w)) = Data.emb τ.1 (φ v) + Data.emb τ.1 (φ w) := fun τ => by
    funext k; simp [Data.emb]
  have hs : ∀ τ u u', (X.Hf x τ u' u).re = (X.Hf x τ u u').re := fun τ u u' => by
    rw [← UnipotentCoefficientShift.Hf_conj hx, Complex.conj_re]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  have h4 : (hermForm Hm (P w) (P v)).re = (hermForm Hm (P v) (P w)).re := by
    rw [← OfPeriod.sesq_apply, ← OfPeriod.sesq_conj hH, Complex.conj_re, OfPeriod.sesq_apply]
  simp only [hm] at h1 h2 h3
  simp only [he, UnipotentCoefficientShift.Hf_add_left, UnipotentCoefficientShift.Hf_add_right, Complex.add_re, hs _ (Data.emb _ (φ v)), mul_add,
    Finset.sum_add_distrib] at h1
  rw [← OfPeriod.sesq_apply, map_add P] at h1
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, OfPeriod.sesq_apply] at h1
  linarith

lemma Hf_eq_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (m : Fin r → E) (n : ℕ) (e e' : E)
    (h : (n : ℂ) • X.aproj x ξ (X.embV m) = X.embV (e • ξ)) (τ : X.Ψ) :
    X.Hf x τ (Data.emb τ.1 ((n : ℤ) • m - e • ξ)) (Data.emb τ.1 (e' • ξ)) = 0 := by
  have h0 : Data.emb τ.1 ξ ≠ 0 := fun h0 => hξ (funext fun k => by simpa [Data.emb] using congrFun h0 k)
  have hs : ∀ a : E, Data.emb τ.1 (a • ξ) = τ.1 a • Data.emb τ.1 ξ := fun a => by funext k; simp [Data.emb]
  have h1 : Data.emb τ.1 ((n : ℤ) • m - e • ξ) = (n : ℂ) • Data.emb τ.1 m - τ.1 e • Data.emb τ.1 ξ := by
    funext k; simp [Data.emb]
  have h2 : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ h0).ne'
  have h3 := congrFun h τ
  simp only [Pi.smul_apply, Data.aproj, Data.lineV, Data.embV, hs, smul_smul] at h3
  have h4 := smul_left_injective ℂ h0 h3
  rw [h1, hs, UnipotentCoefficientShift.Hf_smul_right, UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, UnipotentCoefficientShift.Hf_smul_left, ← h4]
  field_simp
  simp

lemma exists_quot {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (t : La) (ht : (φ t : Fin r → E) ≠ 0) :
    ∃ (Y : Submodule (𝓞 E) E) (y : La →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y), Function.Surjective y ∧
      Module.Finite ℤ Y ∧ Module.Free ℤ Y ∧ Module.finrank (𝓞 E) Y = 1 ∧ ξ ≠ 0 ∧ (∀ v, -EF t v = ξ (y v)) ∧
      (∀ v, y v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0) ∧
      ∀ v, y v = 0 ↔ ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := by
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  have hcj := herm_conj X.Gm X.Gm_herm
  let f : La →ₗ[𝓞 E] E :=
    { toFun := fun v => herm X.Gm (φ v : Fin r → E) (φ t)
      map_add' := fun v v' => by rw [map_add (f := _), Submodule.coe_add, herm_add_left]
      map_smul' := fun a v => by rw [hsm, herm_smul_left]; rfl }
  have hf0 : ∀ v, f.rangeRestrict v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0 := fun v => Subtype.ext_iff
  have hk : ∀ v, f.rangeRestrict v = 0 ↔
      ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := fun v => by
    rw [hf0]
    refine ⟨fun h t' ⟨e, he⟩ => ?_, fun h => ?_⟩
    · have := iso t' v
      rw [he, herm_smul_left, ← hcj, h] at this
      simpa using this
    · have : -X.ξ0 * herm X.Gm (φ t : Fin r → E) (φ v) = 0 := eq_zero_of_trace_mul _ fun β => by
        have h1 := iso (β • t) v
        rw [h _ ⟨β, hsm β t⟩, hsm, herm_smul_left] at h1
        rw [mul_left_comm, ← h1, Int.cast_zero]
      rw [← hcj, (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 X.ξ0_ne)]
      simp
  have hy := f.surjective_rangeRestrict
  haveI : Module.Finite ℤ (LinearMap.range f) := Module.Finite.trans (𝓞 E) _
  have hle : f.rangeRestrict.toAddMonoidHom.ker ≤ (-EF t).toAddMonoidHom.ker := fun v hv => by
    simpa using (hk v).1 hv t ⟨1, (one_smul _ _).symm⟩
  let ξ : LinearMap.range f →+ ℤ := f.rangeRestrict.toAddMonoidHom.liftOfSurjective hy ⟨_, hle⟩
  have hξ : ∀ v, -EF t v = ξ.toIntLinearMap (f.rangeRestrict v) := fun v =>
    (AddMonoidHom.liftOfRightInverse_comp_apply f.rangeRestrict.toAddMonoidHom _ (Function.rightInverse_surjInv hy)
      ⟨_, hle⟩ v).symm
  have hξ0 : ξ.toIntLinearMap ≠ 0 := fun h => ht (eq_zero_of_trace_lattice X _ fun w hw => by
    have h1 := hξ (φ.symm ⟨w, hw⟩)
    have h2 := iso t (φ.symm ⟨w, hw⟩)
    rw [h, LinearMap.zero_apply, neg_eq_zero] at h1
    rw [h1, neg_mul, map_neg] at h2
    simpa using h2.symm)
  refine ⟨LinearMap.range f, f.rangeRestrict, ξ.toIntLinearMap, hy, inferInstance, inferInstance, ?_, hξ0, hξ, hf0, hk⟩
  haveI : Nontrivial (LinearMap.range f) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hξ0 (LinearMap.ext fun a => by rw [Subsingleton.elim a 0]; simp)
  have h2 : Module.rank (𝓞 E) (LinearMap.range f) ≤ 1 := by
    refine (Submodule.rank_le _).trans ?_
    rw [← IsFractionRing.rank_right_eq (𝓞 E) E E, Module.rank_self]
  exact le_antisymm (Module.finrank_le_of_rank_le (by simpa using h2)) Module.finrank_pos

theorem exists_anArc_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x n' ν₀ hσ hU hξ' hx hn hν hν' hint
  letI := H.starRing
  obtain ⟨t, rfl⟩ : ∃ t, (Uw.φ k t : Fin r → E) = ξ' := ⟨(Uw.φ k).symm ⟨ξ', hξ'.1⟩, by simp⟩
  have hfin := (Uw.F.Di (Uw.ik k)).fin
  have hP := Uw.period k ⟨x, hx⟩
  obtain ⟨Hm, hHm⟩ := hP.2.2.2.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by
    subst h
    exact hξ'.2.2 (Subsingleton.elim _ _)
  obtain ⟨hmaj, hκ, -⟩ := GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k ⟨x, hx⟩ Hm hσ hU hHm
  replace hκ := hκ hr
  obtain ⟨Y, y, ξ, hy, _, _, hY, hξ, ht, hy0, hker⟩ := exists_quot (U.X k) (Uw.φ k) _ (Uw.iso k) t hξ'.2.2
  have hrep : ∀ (Z : Type) [AddCommGroup Z] [Module (𝓞 E) Z] (z : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Z)
      (θ : Module.Dual ℤ Z), ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = θ (z v) := fun Z _ _ z θ => by
    obtain ⟨t, ht⟩ := (Uw.F.Di (Uw.ik k)).unimod.2 (-(θ ∘ₗ z.toAddMonoidHom.toIntLinearMap))
    exact ⟨t, fun v => by rw [ht]; simp⟩
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨be, s, jj, hs, hsym, hpos, hdvd, hbeta⟩ := GlobalTheory.ArcQ.Isolate.exists_form_isolating E Y ξ l.M' ν₀ hξ hY hM hν hν'
    fun s hs => hint s hs.1 (transv_of_levelPar (U.X k) (Uw.φ k) _ (Uw.iso k) y hκ (hrep Y y) ξ t ht hM s hs)
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  let Hh : Submodule (𝓞 E) (Uw.F.Di (Uw.ik k)).La :=
    ((Submodule.span E {(Uw.φ k t : Fin r → E)}).restrictScalars (𝓞 E)).comap φ
  have hHh : ∀ v, v ∈ Hh ↔ ∃ e : E, (Uw.φ k v : Fin r → E) = e • (Uw.φ k t : Fin r → E) := fun v =>
    Submodule.mem_span_singleton.trans (exists_congr fun _ => eq_comm)
  have hker' : ∀ v, y v = 0 ↔ ∀ t' ∈ Hh, (Uw.F.Di (Uw.ik k)).EF t' v = 0 := fun v => by
    simp only [hHh, hker]
  have hyH : ∀ v ∈ Hh, y v = 0 := fun v hv => by
    obtain ⟨e, he⟩ := (hHh v).1 hv
    rw [hy0, he, herm_smul_left, hξ'.2.1, mul_zero]
  obtain ⟨A, e, gam, h, hbe, hchi, hpsi, hEF, hgy, -, hact, hh, -, -, -, -, -, -, huniq, hct, hrk, tyB, hF, hD⟩ :=
    GlobalTheory.OfPeriod.exists_anArc_of_period (Uw.F.Di (Uw.ik k)) hP hHm.2.2 Hh
      (fun m v hm hv => by
        obtain ⟨e, he⟩ := (hHh _).1 hv
        refine (hHh v).2 ⟨(m : E)⁻¹ * e, ?_⟩
        have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
        rw [mul_smul, ← he, map_zsmul, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul E, inv_smul_smul₀ hm'])
      (fun v hv v' hv' => (hker' v').1 (hyH v' hv') v hv) y hy hker' be hsym hpos
      (adj_of_isBePar H ξ be hs) (fun a => (dvd_mul_right _ _).trans (hdvd a a))
  have hX : Module.finrank (𝓞 E) A.X = 1 := e.finrank_eq.trans hY
  rw [hX] at hrk
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  rw [← hrk, hp, hq] at hD
  obtain ⟨-, -, htyB, DB, eB, hp', hq', hB1, hB2, hB3⟩ := hD ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ Uw.e)
  let ξ₁ : Module.Dual ℤ A.X := ξ ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap
  have hξ₁ : ∀ a, ξ₁ a = ξ (e a) := fun _ => rfl
  have hξ₁0 : ξ₁ ≠ 0 := fun h0 => hξ (LinearMap.ext fun a => by
    rw [← e.apply_symm_apply a, ← hξ₁, h0]; rfl)
  have ht₁ : ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = ξ₁ (gam v).y := fun v => by rw [hξ₁, hgy, ht]
  refine ⟨A, gam, ξ₁, jj, DB, tyB, eB, ⟨hEF, ⟨t, rfl, ht₁⟩, ?_⟩, hξ₁0, hX, fun a a' => by rw [hbe]; exact hdvd _ _,
    betaAt_comp e ξ ξ₁ hξ₁ be A.be hbe hbeta, ⟨hchi, hpsi⟩, fun a => ?_,
    ⟨hF, by rw [hp', hq']; exact htyB, hB1, hB2, hB3⟩, hp', hq'⟩
  · let nn := gam.symm.toLinearMap ∘ₗ A.nn ∘ₗ gam.toLinearMap
    have hnn : ∀ v, gam (nn v) = A.nn (gam v) := fun v => gam.apply_symm_apply _
    obtain ⟨sE, -, hsE, -, -, hform⟩ := rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) (A.yLin ∘ₗ gam.toLinearMap) hX hκ
      (A.yLin_surjective.comp gam.surjective) A.be A.be_symm A.be_pos nn
      (fun v v' => by rw [← hEF, hnn, A.nn_apply, A.EF_n_left, neg_neg]; rfl) (hrep _ _) ξ₁ hξ₁0 t ht₁
      (e.injective (by rw [map_zero]; exact (hgy t).trans (hyH t ((hHh t).2 ⟨1, (one_smul _ _).symm⟩))))
    obtain ⟨T₀, hT₀⟩ := A.exists_BwMat_posDef
    refine ⟨T₀, fun w hw => ?_⟩
    let P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      h.symm.toLinearMap.toAddMonoidHom.comp ((A.Pw w).comp gam.toLinearMap.toAddMonoidHom)
    have hPe : ∀ v, P v = h.symm (A.Pw w (gam v)) := fun _ => rfl
    have hPw := A.isPeriod (hT₀ w hw) (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) h.symm
      (fun a v i => by
        have := hact a (h.symm v)
        rw [h.apply_symm_apply] at this
        rw [← this, h.symm_apply_apply]) gam.toAddEquiv gam.map_smul hEF P hPe
    obtain ⟨hs, hPm⟩ := flow_period Uw hσ hU k hκ nn _ hξ'.2.1 sE hsE.1 hform ⟨x, hx⟩ w P hPw fun v => by
      rw [hPe, h.symm_apply_eq, map_add (f := _), map_smul, hh, hh, hnn, A.degeneratingTori_basePeriodMap_nilpotentMap, A.Pw_apply]
    exact ⟨_, hs, h, fun v => by rw [hPm, hPe, h.apply_symm_apply]⟩
  · rw [← natCast_zsmul]
    refine hct n' (fun v hv a ha ha' => ?_) a
    obtain ⟨e₀, he₀, hproj⟩ := hn (Uw.φ k v) ⟨(Uw.φ k v).2, (hy0 v).1 hv⟩
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (Uw.φ k t₀ : Fin r → E) = e₀ • (Uw.φ k t : Fin r → E) :=
      ⟨(Uw.φ k).symm ⟨_, he₀⟩, by simp⟩
    have ht₀' := (hHh t₀).2 ⟨e₀, ht₀⟩
    refine ⟨t₀, ht₀', (huniq ((n' : ℤ) • v) (by rw [map_zsmul, hv, smul_zero])).unique
      ⟨Submodule.subset_span ⟨t₀, ht₀', rfl⟩, fun t' ht' => ?_⟩ ⟨zsmul_mem ha _, fun t' ht' => ?_⟩⟩
    · rw [← map_sub]
      refine Complex.ext ?_ ?_
      · obtain ⟨e', he'⟩ := (hHh t').1 ht'
        rw [re_eq_of_maj (U.X k) hx φ.toAddMonoidHom _ hHm.1 hmaj]
        refine Finset.sum_eq_zero fun τ _ => ?_
        have h1 : φ.toAddMonoidHom ((n' : ℤ) • v - t₀) =
            (n' : ℤ) • (Uw.φ k v : Fin r → E) - e₀ • (Uw.φ k t : Fin r → E) := by
          rw [map_sub, map_zsmul, ← ht₀]; rfl
        rw [h1, show φ.toAddMonoidHom t' = _ from he', Hf_eq_zero (U.X k) hx hξ'.2.2 _ n' e₀ e' hproj]
        simp
      · have halt : (Uw.F.Di (Uw.ik k)).EF.IsAlt := (Uw.F.Di (Uw.ik k)).alt
        rw [hHm.2.2, halt.eq_iff.1 ((hker' _).1 (by rw [map_sub, map_zsmul, hv, hyH t₀ ht₀']; simp) t' ht')]
        simp
    · rw [map_zsmul, ← smul_sub, ← OfPeriod.sesq_apply, map_zsmul, LinearMap.smul_apply, OfPeriod.sesq_apply,
        ha' t' ht', smul_zero]

end GlobalTheory.AnAtFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolatingStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb relab
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  first | exact @GlobalTheory.AnAtFrame.exists_anArc_onOrbit | exact GlobalTheory.AnAtFrame.exists_anArc_onOrbit | (intros; apply GlobalTheory.AnAtFrame.exists_anArc_onOrbit <;> assumption)
end
