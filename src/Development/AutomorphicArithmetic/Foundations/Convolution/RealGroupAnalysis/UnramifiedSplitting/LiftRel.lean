module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open UpperTheory.V.Af.Smo (Eig)

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  let W (b : A F) (y : GL (Fin 2) (v.adicCompletion F)) :=
    f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))
  have hW (b : A F) : Eig v B (W b) := by
    simpa only [W, mul_assoc] using h (gl (nU b) * g)
  have hi (y : GL (Fin 2) (v.adicCompletion F)) :
      IntegrableOn (fun b => W b y * ψ b) (fundamentalSet F) (adeleMeasure F) :=
    intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  change Eig v B (fun y => ∫ b in fundamentalSet F, W b y * ψ b ∂(adeleMeasure F))
  refine ⟨(h 1).card, fun y k hk => by simp only [fun b => (hW b).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hsupp := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm F v 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hsum (G : GL (Fin 2) (v.adicCompletion F) ⧸ GlobalTheory.LFun.KGL v (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c =
        ∑ c ∈ hsupp.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hsum]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hb := (hW b).eig ϖ hϖ j hj y
  rw [hsum] at hb
  simp only [← mul_assoc, ← hb, Finset.sum_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CorePt
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.StdOm
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GenV
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem ml {R : Type} [CommRing R] (x y : Matrix.SpecialLinearGroup (Fin 2) R) (i k : Fin 2) :
    (x * y).1 i k = x.1 i 0 * y.1 0 k + x.1 i 1 * y.1 1 k := by
  show (x.1 * y.1) i k = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.ConvolutionTheory.R2.H.genV :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (g : G1 K), IntAt v g → g ∈ Subgroup.closure ({x : G1 K | ∃ b, IsInt (cp v b) ∧ x = nU b} ∪ {wW K}) := by
  intro K _ _ v g hg
  obtain ⟨⟨j, hj⟩, hJ⟩ := jEx K v
  obtain ⟨-, -, -, je⟩ := hJ j hj
  clear hJ
  obtain ⟨sa, sm, sc, -⟩ := sgLaws K v
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  set C := Subgroup.closure ({x : G1 K | ∃ b, IsInt (cp v b) ∧ x = nU b} ∪ {wW K}) with hC
  have hw : wW K ∈ C := Subgroup.subset_closure (Or.inr rfl)
  have hn : ∀ b, IsInt (cp v b) → nU b ∈ C := fun b hb => Subgroup.subset_closure (Or.inl ⟨b, hb, rfl⟩)
  let nv : Kv v → Matrix.SpecialLinearGroup (Fin 2) (Kv v) := fun b => ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩
  let lv : Kv v → Matrix.SpecialLinearGroup (Fin 2) (Kv v) := fun b => ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩
  let wv : Matrix.SpecialLinearGroup (Fin 2) (Kv v) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have jn : ∀ b, j (nv b) = nU (sg v b) := fun b => by
    ext i k : 1
    rw [je]
    fin_cases i <;> fin_cases k <;> simp [nv, nU, s0]
  have jl : ∀ b, j (lv b) * wW K = wW K * nU (-sg v b) := fun b => by
    have : j (lv b) = ⟨!![1, 0; sg v b, 1], by simp [Matrix.det_fin_two]⟩ := by
      ext i k : 1
      rw [je]
      fin_cases i <;> fin_cases k <;> simp [lv, s0]
    rw [this]
    ext i k : 1
    refine (ml _ _ i k).trans (Eq.trans ?_ (ml _ _ i k).symm)
    fin_cases i <;> fin_cases k <;> simp [wW, nU]
  have one : IsInt (1 : Kv v) := (map_one (Valued.v (R := Kv v))).le
  have h1 : ∀ x : Matrix.SpecialLinearGroup (Fin 2) (Kv v), (∀ i k, IsInt (x i k)) → Valued.v (x 1 0) = 1 → j x ∈ C := fun x hx hc => by
    have c0 : x 1 0 ≠ 0 := fun e => by simp [e] at hc
    have hd := x.det_coe
    rw [Matrix.det_fin_two] at hd
    have e : x = nv ((x 0 0 - 1) / x 1 0) * lv (x 1 0) * nv ((x 1 1 - 1) / x 1 0) := by
      ext i k : 1
      simp only [ml]
      fin_cases i <;> fin_cases k <;> simp [nv, lv] <;> field_simp
      all_goals first | ring1 | linear_combination hd | linear_combination (-1 : Kv v) * hd
    have hi : ∀ y, IsInt y → IsInt (cp v (sg v ((y - 1) / x 1 0))) := fun y hy => by
      rw [sc]
      show Valued.v _ ≤ 1
      rw [map_div₀, hc, div_one]
      exact Valuation.map_sub_le _ hy one
    rw [e, map_mul, map_mul, jn, jn, eq_mul_inv_of_mul_eq (jl _)]
    refine C.mul_mem (C.mul_mem (hn _ (hi _ (hx 0 0))) (C.mul_mem (C.mul_mem hw (hn _ ?_)) (C.inv_mem hw))) (hn _ (hi _ (hx 1 1)))
    rw [map_neg, sc]
    show Valued.v _ ≤ 1
    rw [Valuation.map_neg, hc]
  have zero : IsInt (0 : Kv v) := by simp [IsInt]
  have hwv : j wv ∈ C := h1 wv (fun i k => by fin_cases i <;> fin_cases k <;> simp [wv, IsInt]) (by simp [wv])
  have h2 : ∀ x : Matrix.SpecialLinearGroup (Fin 2) (Kv v), (∀ i k, IsInt (x i k)) → j x ∈ C := fun x hx => by
    by_cases hc : Valued.v (x 1 0) = 1
    · exact h1 x hx hc
    have hd := x.det_coe
    rw [Matrix.det_fin_two] at hd
    have ha : Valued.v (x 0 0) = 1 := by
      by_contra ha
      have a1 : Valued.v (x 0 0 * x 1 1) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_lt_of_le (lt_of_le_of_ne (hx 0 0) ha) (hx 1 1)
      have a2 : Valued.v (x 0 1 * x 1 0) < 1 := by
        rw [map_mul, mul_comm]
        exact mul_lt_one_of_lt_of_le (lt_of_le_of_ne (hx 1 0) hc) (hx 0 1)
      have := Valuation.map_sub_lt _ a1 a2
      rw [hd, map_one] at this
      exact lt_irrefl _ this
    have e : ∀ k, (wv * x) 0 k = x 1 k ∧ (wv * x) 1 k = -x 0 k := fun k => by
      constructor <;> rw [ml] <;> simp [wv]
    have := h1 (wv * x) (fun i k => by
      fin_cases i
      · exact (e k).1 ▸ hx 1 k
      · show Valued.v ((wv * x) 1 k) ≤ 1
        rw [(e k).2, Valuation.map_neg]
        exact hx 0 k) (by rw [(e 0).2, Valuation.map_neg, ha])
    rw [map_mul] at this
    exact (C.mul_mem_cancel_left hwv).1 this
  let p : G1 K →* Matrix.SpecialLinearGroup (Fin 2) (Kv v) := Matrix.SpecialLinearGroup.map (cp v)
  have pa : ∀ k i l, p k i l = cp v (k i l) := fun _ _ _ => rfl
  have pj : ∀ x, p (j x) = x := fun x => by
    ext i k : 1
    rw [pa, je, map_add (f := _), sc]
    fin_cases i <;> fin_cases k <;> simp
  have cm : ∀ x k, p k = 1 → j x * k = k * j x := fun x k hk => by
    have hk' : ∀ i l y, k i l * sg v y = sg v ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) i l * y) := fun i l y => by
      rw [sm, ← pa, hk]
      rfl
    ext i l : 1
    simp only [ml, je, add_mul, mul_add, mul_comm (sg v _), hk']
    fin_cases i <;> fin_cases l <;> simp [s0, Matrix.one_apply, add_comm]
  have h3 : ∀ k : G1 K, k * (j (p k))⁻¹ ∈ C := fun k => by
    have hk : k ∈ Subgroup.closure (Set.range (nU (F := K)) ∪ {wW K}) := (gen K).1 ▸ Subgroup.mem_top k
    have one' : ∀ k : G1 K, p (k * (j (p k))⁻¹) = 1 := fun k => by rw [map_mul, map_inv, pj, mul_inv_cancel]
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | rfl
      · have e1 : p (nU b) = nv (cp v b) := by
          ext i k : 1
          rw [pa]
          fin_cases i <;> fin_cases k <;> simp [nv, nU]
        have e2 : nU b = nU (b - sg v (cp v b)) * nU (sg v (cp v b)) := by
          ext i k : 1
          rw [ml]
          fin_cases i <;> fin_cases k <;> simp [nU]
        rw [e1, jn, mul_inv_eq_of_eq_mul e2]
        exact hn _ (by rw [map_sub, sc, sub_self]; exact zero)
      · have e1 : p (wW K) = wv := by
          ext i k : 1
          rw [pa]
          fin_cases i <;> fin_cases k <;> simp [wv, wW]
        rw [e1]
        exact C.mul_mem hw (C.inv_mem hwv)
    | one => simp
    | mul x y _ _ hx hy =>
      have e := cm (p x)⁻¹ _ (one' y)
      have e' : x * y * (j (p (x * y)))⁻¹ = x * (j (p x))⁻¹ * (y * (j (p y))⁻¹) := by
        rw [mul_assoc x (j (p x))⁻¹, ← map_inv j (p x), e, map_mul, map_mul, map_inv]
        group
      rw [e']
      exact C.mul_mem hx hy
    | inv x _ hx =>
      have e := cm (p x) _ (one' x)
      have e' : x⁻¹ * (j (p x⁻¹))⁻¹ = (x * (j (p x))⁻¹)⁻¹ := by
        rw [map_inv, map_inv, inv_inv]
        have : j (p x) * x = x * j (p x) := by
          have h := congrArg (· * j (p x)) e
          simpa [mul_assoc] using h
        rw [_root_.mul_inv_rev, inv_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← this, mul_inv_cancel_right]
      rw [e']
      exact C.inv_mem hx
  have := C.mul_mem (h3 g) (h2 (p g) fun i k => hg i k)
  rwa [inv_mul_cancel_right] at this
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.stdOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F), Gd D.δ v → ∀ (k : G1 F), IntAt v k → ∀ φ : S4 F, Std v φ.1 → Std v (W.Om k φ).1 := by
  intro F E _ _ _ _ _ _ _ D W v hG k hk
  obtain ⟨sa, sm, sc, -⟩ := sgLaws F v
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  have pa : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := fun x y => by simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have im : ∀ {x y : Kv v}, IsInt x → IsInt y → IsInt (x * y) := fun hx hy => by
    show Valued.v _ ≤ 1
    rw [map_mul]
    exact mul_le_one' hx hy
  have ia : ∀ {x y : Kv v}, IsInt x → IsInt y → IsInt (x + y) := fun hx hy => Valuation.map_add_le _ hx hy
  have ineg : ∀ {x : Kv v}, IsInt x → IsInt (-x) := fun hx => (Valuation.map_neg _ _).le.trans hx
  have i2 : IsInt (2 : Kv v) := hG.two.le
  have iδ : IsInt (cp v (rt D.δ)) := hG.del.le
  have k1 : ∀ (a : A F) y, IsInt (cp v a) → IsInt y → ψ (a * sg v y) = 1 := fun a y ha hy => by
    rw [sm]
    exact gi _ (im ha hy)
  have k2 : ∀ a : A F, (∀ c, IsInt c → ψ (a * sg v c) = 1) → IsInt (cp v a) := fun a h => gm _ fun c hc => by
    have := h c hc
    rwa [sm, mul_comm] at this
  have hn : ∀ b, IsInt (cp v b) → ∀ φ : S4 F, Std v φ.1 → Std v (W.Om (nU b) φ).1 := fun b hb φ hφ => by
    refine ⟨fun x hx => hφ.1 x fun e => hx (by rw [W.Om_n, e, mul_zero]), fun x y hy => ?_⟩
    rw [W.Om_n, W.Om_n, hφ.2 x y hy]
    by_cases h0 : φ.1 x = 0
    · rw [h0, mul_zero, mul_zero]
    have hx := hφ.1 x h0
    have e : b * q4 D.δ (fun i => x i + sg v (y i)) = b * q4 D.δ x + b * (2 * x 2 + sg v (y 2)) * sg v (y 2) +
        -(b * (rt D.δ * (2 * x 3 + sg v (y 3)))) * sg v (y 3) + -(b * x 1) * sg v (y 0) + -(b * (x 0 + sg v (y 0))) * sg v (y 1) := by
      simp only [q4]
      ring
    rw [e, pa, pa, pa, pa, k1 _ _ _ (hy 2), k1 _ _ _ (hy 3), k1 _ _ _ (hy 0), k1 _ _ _ (hy 1), mul_one, mul_one, mul_one, mul_one]
    all_goals simp only [map_neg, map_mul, map_add (f := _), map_ofNat, sc]
    · exact ineg (im hb (ia (hx 0) (hy 0)))
    · exact ineg (im hb (hx 1))
    · exact ineg (im hb (im iδ (ia (im i2 (hx 3)) (hy 3))))
    · exact im hb (ia (im i2 (hx 2)) (hy 2))
  have hw : ∀ φ : S4 F, Std v φ.1 → Std v (W.Om (wW F) φ).1 := fun φ hφ => by
    refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
    · rw [W.Om_w] at hx
      have h1 : ∀ y : Fin 4 → Kv v, (∀ i, IsInt (y i)) → ψ (B4 D.δ (fun i => sg v (y i)) x) = 1 := fun y hy => by
        have h2 := integral_add_right_eq_self (μ := adeleMeasurePi F) (fun z : V4 F => φ.1 z * ψ (B4 D.δ z x)) (fun i => sg v (y i))
        have h3 : ∀ z : V4 F, φ.1 (z + fun i => sg v (y i)) * ψ (B4 D.δ (z + fun i => sg v (y i)) x) =
            ψ (B4 D.δ (fun i => sg v (y i)) x) * (φ.1 z * ψ (B4 D.δ z x)) := fun z => by
          have e : B4 D.δ (z + fun i => sg v (y i)) x = B4 D.δ z x + B4 D.δ (fun i => sg v (y i)) x := by
            simp only [B4, Pi.add_apply]
            ring
          rw [e, pa, show φ.1 (z + fun i => sg v (y i)) = φ.1 z from hφ.2 z y hy]
          ring
        simp only [h3, integral_const_mul] at h2
        exact mul_right_cancel₀ hx (h2.trans (one_mul _).symm)
      have h4 : ∀ (i : Fin 4) c, IsInt c → ψ (B4 D.δ (fun j => sg v ((Pi.single i c : Fin 4 → Kv v) j)) x) = 1 := fun i c hc =>
        h1 _ fun j => by
          by_cases e : j = i
          · subst e; simpa using hc
          · simp [Pi.single_eq_of_ne e, IsInt]
      have a0 := k2 (-x 0) fun c hc => by rw [← h4 1 c hc]; congr 1; simp [B4, s0, mul_comm]
      have a1 := k2 (-x 1) fun c hc => by rw [← h4 0 c hc]; congr 1; simp [B4, s0, mul_comm]
      have a2 := k2 (2 * x 2) fun c hc => by rw [← h4 2 c hc]; congr 1; simp [B4, s0]; ring
      have a3 := k2 (-(2 * (rt D.δ * x 3))) fun c hc => by rw [← h4 3 c hc]; congr 1; simp [B4, s0]; ring
      have d1 : Valued.v (cp v (rt D.δ)) = 1 := hG.del
      simp only [IsInt, map_neg, Valuation.map_neg, map_mul, map_ofNat, hG.two, d1, one_mul] at a0 a1 a2 a3
      intro i
      fin_cases i
      exacts [a0, a1, a2, a3]
    · rw [W.Om_w, W.Om_w]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      beta_reduce
      by_cases h0 : φ.1 z = 0
      · rw [h0, zero_mul, zero_mul]
      have hz := hφ.1 z h0
      have e : B4 D.δ z (fun i => x i + sg v (y i)) = B4 D.δ z x + 2 * z 2 * sg v (y 2) + -(2 * (rt D.δ * z 3)) * sg v (y 3) +
          -z 1 * sg v (y 0) + -z 0 * sg v (y 1) := by
        simp only [B4]
        ring
      rw [e, pa, pa, pa, pa, k1 _ _ _ (hy 2), k1 _ _ _ (hy 3), k1 _ _ _ (hy 0), k1 _ _ _ (hy 1), mul_one, mul_one, mul_one, mul_one]
      all_goals simp only [map_neg, map_mul, map_ofNat]
      · exact ineg (hz 0)
      · exact ineg (hz 1)
      · exact ineg (im i2 (im iδ (hz 3)))
      · exact im i2 (hz 2)
  have ml : ∀ (x y : G1 F) (i k : Fin 2), (x * y).1 i k = x.1 i 0 * y.1 0 k + x.1 i 1 * y.1 1 k := fun x y i k => by
    show (x.1 * y.1) i k = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hk' := genV F v k hk
  clear hk
  induction hk' using Subgroup.closure_induction'' with
  | one => intro φ hφ; simpa using hφ
  | mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl
    exacts [hn b hb, hw]
  | inv_mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl
    · have e : (nU b)⁻¹ = nU (-b) := inv_eq_of_mul_eq_one_right (by
        ext i k : 1
        rw [ml]
        fin_cases i <;> fin_cases k <;> simp [nU])
      rw [e]
      exact hn _ (by rw [map_neg]; exact ineg hb)
    · have e : (wW F)⁻¹ = wW F * (wW F * wW F) := inv_eq_of_mul_eq_one_right (by
        ext i k : 1
        simp only [ml]
        fin_cases i <;> fin_cases k <;> simp [wW])
      rw [e, map_mul, map_mul]
      exact fun φ hφ => hw _ (hw _ (hw _ hφ))
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact fun φ hφ => hx _ (hy _ hφ)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.StdHat
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem psi_add' {K : Type} [Field K] [NumberField K] (a b : A K) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem psi_neg_one {K : Type} [Field K] [NumberField K] {a : A K} (h : ψ (-a) = 1) : ψ a = 1 := by
  have h0 : ψ (0 : A K) = 1 := by simp [ψ]
  have h1 := psi_add' a (-a)
  rw [add_neg_cancel, h, mul_one, h0] at h1
  exact h1.symm

private theorem isInt_zero {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (0 : Kv v) := by
  simp [IsInt]

private theorem isInt_mul {K : Type} [Field K] [NumberField K] {v : P K} {a b : Kv v}
    (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  unfold IsInt at *
  rw [map_mul]
  exact mul_le_one' ha hb

private theorem isInt_neg {K : Type} [Field K] [NumberField K] {v : P K} {a : Kv v}
    (ha : IsInt a) : IsInt (-a) := by
  unfold IsInt at *
  rwa [Valuation.map_neg]

theorem UpperTheory.ConvolutionTheory.R2.H.stdHat :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K) (v : P K), Gd δ v → ∀ φ : V4 K → ℂ, Std v φ → Std v (hat φ) := by
  intro K _ _ δ v hG φ hφ
  obtain ⟨hadd, hmul, hcp, -, -, -, -, -, -, -⟩ := sgLaws K v
  have hsg0 : sg v 0 = 0 := by simpa using hadd 0 0

  have hshift : ∀ (x : V4 K) (s : A K) (c : Kv v), IsInt c →
      φ (Function.update x 1 (s + sg v c)) = φ (Function.update x 1 s) := by
    intro x s c hc
    have h1 : Function.update x 1 (s + sg v c) =
        fun i => Function.update x 1 s i + sg v (Function.update (0 : Fin 4 → Kv v) 1 c i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp
      · simp [Function.update_of_ne hi, hsg0]
    rw [h1]
    refine hφ.2 _ _ fun i => ?_
    by_cases hi : i = 1
    · subst hi; simpa using hc
    · simpa [Function.update_of_ne hi] using isInt_zero v
  refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
  · by_cases hi : i = 1
    · subst hi
      refine hG.psi.2.2 (cp v (x 1)) fun c hc => ?_
      have key : hat φ x = ψ (-(sg v c * x 1)) * hat φ x := by
        calc hat φ x = ∫ s, φ (Function.update x 1 (s + sg v c)) * ψ (-((s + sg v c) * x 1)) ∂(adeleMeasure K) :=
              (integral_add_right_eq_self
                (fun s => φ (Function.update x 1 s) * ψ (-(s * x 1))) (sg v c)).symm
          _ = ∫ s, ψ (-(sg v c * x 1)) * (φ (Function.update x 1 s) * ψ (-(s * x 1))) ∂(adeleMeasure K) := by
              congr 1
              funext s
              rw [hshift x s c hc, show -((s + sg v c) * x 1) = -(s * x 1) + -(sg v c * x 1) by ring, psi_add']
              ring
          _ = ψ (-(sg v c * x 1)) * hat φ x := integral_const_mul _ _
      have h1 : ψ (-(sg v c * x 1)) = 1 := by
        have h2 : (ψ (-(sg v c * x 1)) - 1) * hat φ x = 0 := by
          rw [sub_mul, one_mul, ← key, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hx)
      have h3 := psi_neg_one h1
      rw [mul_comm (sg v c), hmul, mul_comm] at h3
      exact h3
    · have ex : ∃ s, φ (Function.update x 1 s) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (by simp [hat, h])
      obtain ⟨s, hs⟩ := ex
      have := hφ.1 _ hs i
      rwa [Function.update_of_ne hi] at this
  · unfold hat
    congr 1
    funext s
    have h1 : Function.update (fun i => x i + sg v (y i)) 1 s =
        fun i => Function.update x 1 s i + sg v (Function.update y 1 0 i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp [hsg0]
      · simp [Function.update_of_ne hi]
    have h2 : φ (Function.update (fun i => x i + sg v (y i)) 1 s) = φ (Function.update x 1 s) := by
      rw [h1]
      refine hφ.2 _ _ fun i => ?_
      by_cases hi : i = 1
      · subst hi; simpa using isInt_zero v
      · simpa [Function.update_of_ne hi] using hy i
    rw [h2]
    by_cases h0 : φ (Function.update x 1 s) = 0
    · simp [h0]
    · have hs : IsInt (cp v s) := by simpa using hφ.1 _ h0 1
      have h3 : ψ (-(s * sg v (y 1))) = 1 := by
        rw [← neg_mul, hmul]
        exact hG.psi.2.1 _ (isInt_mul (by rw [map_neg]; exact isInt_neg hs) (hy 1))
      show φ (Function.update x 1 s) * ψ (-(s * (x 1 + sg v (y 1)))) = φ (Function.update x 1 s) * ψ (-(s * x 1))
      rw [show -(s * (x 1 + sg v (y 1))) = -(s * x 1) + -(s * sg v (y 1)) by ring, psi_add', h3, mul_one]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem gl_mul {K : Type} [Field K] [NumberField K] (x y : G1 K) : gl (x * y) = gl x * gl y := map_mul _ x y

private theorem md_mul {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : mD (x * y) = mD x * mD y := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem dm_md {K : Type} [Field K] [NumberField K] (a p : (A K)ˣ) :
    dM (p ^ 2) * gl (mD (a * p)) = Matrix.GeneralLinearGroup.scalar (Fin 2) p * gl (mD a) := by
  refine Units.ext ?_
  have e : ((p ^ 2 : (A K)ˣ) : A K) * (((a * p)⁻¹ : (A K)ˣ) : A K) = p * ((a⁻¹ : (A K)ˣ) : A K) := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; rw [mul_inv, pow_two, mul_comm a⁻¹]; group
  change !![1, 0; 0, ((p ^ 2 : (A K)ˣ) : A K)] * !![((a * p : (A K)ˣ) : A K), 0; 0, (((a * p)⁻¹ : (A K)ˣ) : A K)] =
    Matrix.scalar (Fin 2) (p : A K) * !![(a : A K), 0; 0, ((a⁻¹ : (A K)ˣ) : A K)]
  rw [Matrix.mul_fin_two, e, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

private theorem fin_alg (A η q c s Y Y' H1 H0 H2 : ℂ) (hA : A ≠ 0) (hq : q ≠ 0)
    (key : c * q * Y * H1 = c * q * Y * H0 + s * Y' * H2) :
    q⁻¹ * q⁻¹ * ((A * q⁻¹)⁻¹ ^ 2 * (c * Y * (η * -1 * (A * q⁻¹) * H1))) =
      -(q⁻¹ * c) * (A⁻¹ ^ 2 * (Y * (η * A * H0))) + q⁻¹ * s * ((A * q)⁻¹ ^ 2 * (Y' * (-η * (A * q) * H2))) := by
  field_simp
  linear_combination (-η) * key

private theorem good_neg {K : Type} [Field K] [NumberField K] {v : P K} {χ : Kv v → ℂ} (h : Good χ) : Good fun x => χ (-x) :=
  ⟨fun x y => by simp only [neg_add, h.1], fun x hx => h.2.1 _ (by simpa [IsInt] using hx),
    fun x hx => h.2.2 x fun c hc => by simpa using hx (-c) (by simpa [IsInt] using hc)⟩

private theorem kat_of_int {K : Type} [Field K] [NumberField K] {v : P K} {g : G1 K} (h : IntAt v g) :
    Matrix.GeneralLinearGroup.map (cp v) (gl g) ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => h i j, fun i j => ?_⟩
  rw [← map_inv, ← map_inv, Matrix.SpecialLinearGroup.SL2_inv_expl]
  have hn : ∀ i j, cp v (-g i j) ∈ Formalism.UG.Ov K v := fun i j => by
    rw [map_neg]
    exact neg_mem (h i j)
  fin_cases i <;> fin_cases j
  exacts [h 1 1, hn 0 1, hn 1 0, h 0 0]

theorem UpperTheory.ConvolutionTheory.R2.H.corePt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → W.η.UnrAt v → W.η.val v = -1 →
      ∀ (Wt : GL (Fin 2) (A F) → ℂ) (α β : ℂˣ), EigAt v {α, β} Wt → (∀ b g, Wt (gl (nU b) * g) = ψ (-b) * Wt g) → ∀ φ : S4 F, Std v φ.1 →
      ∀ (a : (A F)ˣ), ∀ k ∈ KK F,
        ((ab (idl v ϖ ^ 2) : ℝ) : ℂ) * iw (fun g => Wt (dM (idl v ϖ ^ 2) * gl g) *
            hat (W.Om g φ).1 ![0, ((idl v ϖ ^ 2 : (A F)ˣ) : A F), (((idl v ϖ)⁻¹ : (A F)ˣ) : A F), 0]) (a * idl v ϖ, k) =
          -((q v)⁻¹ * ((α : ℂ) * β)) * iw (fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) (a, k) +
            (q v)⁻¹ * ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * iw (fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) (a * (idl v ϖ)⁻¹, k) := by
  intro F E _ _ _ _ _ _ _ D W v ϖ hϖ hg hu hv Wt α β hB hN φ hφ a k hk
  obtain ⟨-, s2, s3, s4, -, s6, -, -⟩ := sgLaws F v
  obtain ⟨l1, l2, -, -, l5, -, -⟩ := lcLaws F v
  have hH : Std v (UpperTheory.ConvolutionTheory.R2.hat (W.Om k φ).1) := stdHat F D.δ v hg _ (stdOm F E D W v hg k (hk.2 v) φ hφ)
  set H := UpperTheory.ConvolutionTheory.R2.hat (W.Om k φ).1 with hHd
  set p := idl v ϖ with hp
  have hm : ∀ (b : (A F)ˣ) (x y : A F), UpperTheory.ConvolutionTheory.R2.hat (W.Om (mD b * k) φ).1 ![0, x, y, 0] =
      ((W.η.1 b : ℂˣ) : ℂ) * ((ab b : ℝ) : ℂ) * H ![0, ((b⁻¹ : (A F)ˣ) : A F) * x, b * y, 0] := fun b x y => by
    rw [map_mul, Module.End.mul_apply, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).m]
    simp [hHd]
  have hϖv : Valued.v (ϖ : Kv v) = WithZero.exp (-1 : ℤ) := hϖ
  have hηp : ((W.η.1 p : ℂˣ) : ℂ) = -1 := by
    have h1 : W.η.loc v (ϖ * (atFin v (unif v))⁻¹) = 1 := hu _ (by
      have := unif_spec v
      unfold IsUnitAt
      unfold IsUnifAt at this
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, this, hϖv, mul_inv_cancel₀ WithZero.exp_ne_zero])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : W.η.1 p = W.η.val v := h1
    rw [h2, hv]
    simp
  have hq0 : q v ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have habm : ∀ x y : (A F)ˣ, ((ab (x * y) : ℝ) : ℂ) = ab x * ab y := fun x y => by
    simp only [ab, map_mul, Positive.val_mul, Complex.ofReal_mul]
  have hab0 : ∀ x : (A F)ˣ, ((ab x : ℝ) : ℂ) ≠ 0 := fun x => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F x).2.ne'
  have habp : ((ab p : ℝ) : ℂ) = (q v)⁻¹ := by rw [s6 ϖ hϖ]; simp [q]
  have habp' : ((ab (a * p⁻¹) : ℝ) : ℂ) = ab a * q v := by
    have := habm (a * p⁻¹) p
    rw [inv_mul_cancel_right, habp] at this
    rw [this]; field_simp
  have hηp' : ((W.η.1 (a * p⁻¹) : ℂˣ) : ℂ) = -W.η.1 a := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hηp]; simp
  have hcp : cp v (p : A F) = ϖ := by rw [s4, map_add (f := _), map_one, s3]; ring
  have hsc : dM (p ^ 2) * gl (mD (a * p) * k) = gl (mD a * k) * Matrix.GeneralLinearGroup.scalar (Fin 2) p := by
    have h2 : gl (mD a * k) * Matrix.GeneralLinearGroup.scalar (Fin 2) p = Matrix.GeneralLinearGroup.scalar (Fin 2) p * gl (mD a * k) :=
      Units.ext ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) (gl (mD a * k)).val).eq.symm)
    rw [h2, gl_mul, gl_mul, ← mul_assoc, ← mul_assoc, dm_md]
  obtain ⟨R, -, -, hR⟩ := heckeExpl F v ϖ hϖ
  have hcen : ∀ g, Wt (g * Matrix.GeneralLinearGroup.scalar (Fin 2) p) = (α : ℂ) * β * Wt g := fun g => by
    have h1 : Wt (g * lc v (1 * dL ϖ ϖ)) = (α : ℂ) * β * Wt (g * lc v 1) := (hR α β _ (hB g) 1).2
    rwa [one_mul, map_one, mul_one, l5] at h1
  have key : (α : ℂ) * β * q v * Wt (gl (mD a * k)) * H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] =
      (α : ℂ) * β * q v * Wt (gl (mD a * k)) * H ![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] +
      ((α : ℂ) ^ 2 + α * β + (β : ℂ) ^ 2) * Wt (gl (mD (a * p⁻¹) * k)) *
        H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] := by
    have hx : cp v (a : A F) * cp v ((a⁻¹ : (A F)ˣ) : A F) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hx0 : Valued.v (cp v (a : A F)) ≠ 0 := by
      rw [Ne, map_eq_zero]
      exact left_ne_zero_of_mul_eq_one hx
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (cp v (a : A F)) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
    have v1 : Valued.v (cp v ((a⁻¹ : (A F)ˣ) : A F)) = WithZero.exp (-n) := by
      rw [eq_inv_of_mul_eq_one_right hx, map_inv₀, hn, WithZero.exp_neg]
    have v2 : Valued.v (cp v (((a⁻¹ : (A F)ˣ) : A F) * p)) = WithZero.exp (-n - 1) := by
      rw [map_mul, map_mul, v1, hcp, hϖv, ← WithZero.exp_add]; rfl
    have hap : ((a * p⁻¹ : (A F)ˣ) : A F) * p = a := by rw [← Units.val_mul, inv_mul_cancel_right]
    have v3 : Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) = WithZero.exp (n + 1) := by
      have := congrArg (fun x => Valued.v (cp v x)) hap
      simp only [map_mul, hcp, hϖv, hn] at this
      rw [(eq_mul_inv_iff_mul_eq₀ WithZero.exp_ne_zero).2 this, ← WithZero.exp_neg, ← WithZero.exp_add]; simp
    have v4 : IsInt ((ϖ : Kv v) - 1) := (Valuation.map_sub _ _ _).trans (max_le (by
      rw [hϖv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega) (by rw [map_one]))
    have z : ∀ (x y : A F) (i j : ℤ), Valued.v (cp v x) = WithZero.exp i → Valued.v (cp v y) = WithZero.exp j → (0 < i ∨ 0 < j) →
        H ![0, x, y, 0] = 0 := fun x y i j hi hj h => by
      by_contra h0
      have h1 : Valued.v (cp v x) ≤ 1 := hH.1 _ h0 1
      have h2 : Valued.v (cp v y) ≤ 1 := hH.1 _ h0 2
      rw [hi, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      rw [hj, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
      omega
    have tr : ∀ (x : V4 F) (i : Fin 4), IsInt (cp v (x i)) → H (Function.update x i (x i * p)) = H x := fun x i hi => by
      rw [← hH.2 x (Pi.single i (cp v (x i) * ((ϖ : Kv v) - 1))) fun j => by
        by_cases e : j = i
        · subst e
          rw [Pi.single_eq_same]
          unfold IsInt
          rw [map_mul]
          exact mul_le_one' hi v4
        · rw [Pi.single_eq_of_ne e]
          unfold IsInt
          simp]
      congr 1
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self, Pi.single_eq_same, s4, mul_add, mul_one, s2]
      · have := s2 0 0
        rw [zero_mul, mul_zero] at this
        rw [Function.update_of_ne e, Pi.single_eq_of_ne e, ← this, add_zero]
    by_cases n0 : n = 0
    · have h1 := tr ![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] 1 (show Valued.v (cp v ((a⁻¹ : (A F)ˣ) : A F)) ≤ 1 from by rw [v1, n0]; simp)
      have e : Function.update (![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] : V4 F) 1 ((![0, ((a⁻¹ : (A F)ˣ) : A F), a, 0] : V4 F) 1 * p) =
          ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] := by
        funext j; fin_cases j <;> simp
      rw [← e, h1, z _ _ _ _ v2 v3 (by omega), mul_zero, add_zero]
    by_cases n1 : n = -1
    · have h1 := tr ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] 2 (show Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) ≤ 1 from by
        rw [v3, n1]; simp)
      have e : Function.update (![0, ((a⁻¹ : (A F)ˣ) : A F) * p, ((a * p⁻¹ : (A F)ˣ) : A F), 0] : V4 F) 2
          (((a * p⁻¹ : (A F)ˣ) : A F) * p) = ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] := by
        rw [hap]
        funext j; fin_cases j <;> simp
      have h1' : H ![0, ((a⁻¹ : (A F)ˣ) : A F) * p, a, 0] = _ := e ▸ h1
      have hI : IntAt v (mD (a * p⁻¹)) := fun i j => by
        have w1 : Valued.v (cp v ((a * p⁻¹ : (A F)ˣ) : A F)) = 1 := by rw [v3, n1]; simp
        have w2 : Valued.v (cp v (((a * p⁻¹)⁻¹ : (A F)ˣ) : A F)) = 1 := by
          rw [_root_.mul_inv_rev, inv_inv, mul_comm, Units.val_mul, v2, n1]; simp
        fin_cases i <;> fin_cases j
        exacts [w1.le, zero_mem _, zero_mem _, w2.le]
      have hK : KAt v (gl (mD (a * p⁻¹) * k)) := by
        unfold KAt
        rw [gl_mul, map_mul]
        exact mul_mem (kat_of_int hI) (kat_of_int (hk.2 v))
      have t := (whTorus F v ϖ hϖ _ (good_neg hg.psi) α β _ ((fixTr F v Wt _ hK).2 _ hB 1) fun b y => by
        show Wt (1 * lc v _ * _) = ψ (sg v (-b)) * Wt (1 * lc v _ * _)
        have : sg v (-b) = -sg v b := by
          have := s2 (-1) b
          rw [map_neg, map_one, neg_one_mul, neg_one_mul] at this
          exact this.symm
        rw [one_mul, one_mul, map_mul, l1, mul_assoc, hN, this]).2
      change _ * Wt (1 * lc v _ * _) = _ * Wt (1 * lc v _ * _) at t
      have e2 : mD p * (mD (a * p⁻¹) * k) = mD a * k := by
        rw [← mul_assoc]
        congr 1
        rw [← md_mul, mul_comm a, mul_inv_cancel_left]
      rw [one_mul, one_mul, map_one, one_mul, l2, ← gl_mul, e2] at t
      rw [h1', z _ _ _ _ v1 hn (by omega), mul_zero, zero_add, t]
    · rw [z _ _ _ _ v2 hn (by omega), z _ _ _ _ v1 hn (by omega), z _ _ _ _ v2 v3 (by omega)]
      simp
  have e1 : (((a * p)⁻¹ : (A F)ˣ) : A F) * ((p ^ 2 : (A F)ˣ) : A F) = ((a⁻¹ : (A F)ˣ) : A F) * p := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; rw [mul_inv, pow_two]; group
  have e2 : ((a * p : (A F)ˣ) : A F) * ((p⁻¹ : (A F)ˣ) : A F) = a := by rw [← Units.val_mul, mul_inv_cancel_right]
  have e3 : (((a * p⁻¹)⁻¹ : (A F)ˣ) : A F) = ((a⁻¹ : (A F)ˣ) : A F) * p := by rw [mul_inv, inv_inv, Units.val_mul]
  simp only [iw, hm, hsc, hcen, e1, e2, e3, mul_one]
  simp only [Complex.ofReal_pow, Complex.ofReal_inv]
  rw [pow_two p, habm, habm, habp, habp', hηp', map_mul, Units.val_mul, hηp]
  linear_combination fin_alg (ab a) (W.η.1 a) _ _ _ _ _ _ _ _ (hab0 a) hq0 key
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.core :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → W.η.UnrAt v → W.η.val v = -1 →
      ∀ (Wt : GL (Fin 2) (A F) → ℂ) (α β : ℂˣ), EigAt v {α, β} Wt → (∀ b g, Wt (gl (nU b) * g) = ψ (-b) * Wt g) → ∀ φ : S4 F, Std v φ.1 →
      Integrable (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) M.ν →
      ((ab (idl v ϖ ^ 2) : ℝ) : ℂ) * (M.I0 fun g => Wt (dM (idl v ϖ ^ 2) * gl g) *
          hat (W.Om g φ).1 ![0, ((idl v ϖ ^ 2 : (A F)ˣ) : A F), (((idl v ϖ)⁻¹ : (A F)ˣ) : A F), 0]) =
        (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * M.I0 fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
  intro F E _ _ _ _ _ _ _ D W M v ϖ hϖ hg hu hv Wt α β hB hN φ hφ hi
  have := M.prob
  have mp : ∀ p : IdeleGroup F, MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight p) (MeasurableEquiv.refl (G1 F))) M.ν M.ν :=
    fun p => (measurePreserving_mul_right (ideleMeasure F) p).prod (MeasurePreserving.id M.κ)
  have hk : ∀ᵐ x ∂M.ν, x.2 ∈ KK F :=
    Measure.quasiMeasurePreserving_snd.ae (show ∀ᵐ k ∂M.κ, k ∈ KK F from M.supp)
  unfold Meas.I0
  have e1 := (mp (idl v ϖ)⁻¹).integral_comp' (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0])
  have i1 := ((mp (idl v ϖ)⁻¹).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [← (mp (idl v ϖ)).integral_comp', ← integral_const_mul]
  refine (integral_congr_ae (hk.mono fun x hx => corePt F E D W v ϖ hϖ hg hu hv Wt α β hB hN φ hφ x.1 x.2 hx)).trans ?_
  refine (integral_add (hi.const_mul _) (i1.const_mul _)).trans ?_
  rw [integral_const_mul, integral_const_mul]
  erw [e1]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WfEig
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.wfEig :
    ∀ (K : Type) [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ), Continuous f → (∀ γ g, f (ratGL K 2 γ * g) = f g) →
      (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧ ∀ v B, EigAt v B f → EigAt v B (Wf f) := by
  intro K _ _ f hc hl
  exact ⟨(UpperTheory.ConvolutionTheory.R2.Pp.wfBasic K f ⟨hc, hl⟩).2.1, UpperTheory.ConvolutionTheory.R2.Pp.wfEig K f ⟨hc, hl⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ConjStep
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.conjStep :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (α : (A E)ˣ),
      Measurable (w1 W f φ (aE α)) → (∀ b g, w1 W f φ (aE α) (nU b * g) = w1 W f φ (aE α) g) → Integrable (iw (w1 W f φ (aE α))) M.ν →
      W1 W M f φ (aE α) = ((ab (ideleNorm F E α) : ℝ) : ℂ) * M.I0 fun g => Wf f (dM (ideleNorm F E α) * gl g) *
        hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
  intro F E _ _ _ _ _ _ _ D W M f φ α h1 h2 h3
  have hn : nu F (aE α) = ideleNorm F E α := by
    unfold nu
    congr 1
    exact Units.ext (by simp [aE, Matrix.det_fin_two])
  have h4 := ((UpperTheory.ConvolutionTheory.R2.inv F M _ h1 h2 h3).2 (ideleNorm F E α)).2
  have hab : ((ab (ideleNorm F E α) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F (ideleNorm F E α)).2.ne'
  have h5 : (fun g => w1 W f φ (aE α) (cD (ideleNorm F E α) g)) = fun g => Wf f (dM (ideleNorm F E α) * gl g) *
      hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
    funext g
    have e1 : gl (cD (ideleNorm F E α) g) * dM (ideleNorm F E α) = dM (ideleNorm F E α) * gl g := by
      generalize ideleNorm F E α = t
      refine Units.ext ?_
      show (cD t g).1 * (dM t).val = (dM t).val * g.1
      ext i j : 2
      fin_cases i <;> fin_cases j <;> simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    have e2 : W.Om (cD (ideleNorm F E α) g) (W.L (aE α) φ) = W.L (aE α) (W.Om g φ) := by
      have := LinearMap.congr_fun (W.comm (aE α) g) φ
      rw [hn] at this
      exact this.symm
    have e3 : D.mkE 1 0 = 1 := by simp [Dat.mkE]
    rw [w1, hn, e1, e2, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).aE, e3, mul_one, mul_one]
  rw [← h5, h4, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hab, one_mul]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CosetShift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical
open scoped nonZeroDivisors

private theorem coset_shift {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b x s : FiniteAdeleRing (𝓞 K) K)
    (hs : s ∈ idealFiniteAdeles J) : cosetIndicator J b (x + s) = cosetIndicator J b x := by
  rw [cosetIndicator_apply, cosetIndicator_apply]
  have e : x + s - b = (x - b) + s := by ring
  have h : x + s - b ∈ idealFiniteAdeles J ↔ x - b ∈ idealFiniteAdeles J := by
    rw [e]
    exact AddSubgroup.add_mem_cancel_right _ hs
  simp only [h]

private theorem std_gen {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : P K)
    (hJ : FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0) (y : Kv v) (hy : IsInt y) :
    (sg v y).2 ∈ idealFiniteAdeles J := by
  rw [mem_idealFiniteAdeles]
  intro v'
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := sgLaws K v
  by_cases hv : v' = v
  · subst hv
    have h3 := ((sgLaws K v').2.2.1 y)
    have : (sg v' y).2 v' = y := h3
    rw [this, hJ, neg_zero, WithZero.exp_zero]
    exact hy
  · rw [(h8 y).2 v' hv]
    change Valued.v (0 : v'.adicCompletion K) ≤ _
    rw [map_zero]
    exact zero_le

theorem UpperTheory.ConvolutionTheory.R2.H.stdAe :
    ∀ (K : Type) [Field K] [NumberField K] (φ : S4 K), ∀ᶠ v in cofinite, Std v φ.1 := by
  intro K _ _ φ
  obtain ⟨f, hf⟩ := φ
  change ∀ᶠ v in cofinite, Std v f
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hf
  induction hf using Submodule.span_induction with
  | mem F h =>
    obtain ⟨g, J, b, rfl⟩ := h
    have h1 : ∀ᶠ v : P K in cofinite, FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.finite_factors (J : FractionalIdeal (𝓞 K)⁰ K)
    have h2 : ∀ᶠ v : P K in cofinite, ∀ i, Valued.v ((b i) v) ≤ 1 :=
      eventually_all.2 fun i => (b i).2
    filter_upwards [h1, h2] with v hJ hb
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · have hi : cosetIndicator J (b i) ((x i).2) ≠ 0 := by
        intro h0
        apply hx
        simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]
      rw [cosetIndicator_apply] at hi
      have hm : (x i).2 - b i ∈ idealFiniteAdeles J := by
        by_contra hc
        exact hi (if_neg hc)
      have hv := (mem_idealFiniteAdeles J).1 hm v
      rw [hJ, neg_zero, WithZero.exp_zero] at hv
      have e : (x i).2 v = ((x i).2 - b i) v + (b i) v := by
        change _ = (x i).2 v - (b i) v + (b i) v
        ring
      change Valued.v ((x i).2 v) ≤ 1
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hv (hb i))
    · have e : ∀ i, (x i + sg v (y i)).1 = (x i).1 := fun i => by
        change (x i).1 + (sg v (y i)).1 = _
        rw [((sgLaws K v).2.2.2.2.2.2.2.1 (y i)).1, add_zero]
      have e2 : ∀ i, cosetIndicator J (b i) (x i + sg v (y i)).2 = cosetIndicator J (b i) (x i).2 :=
        fun i => coset_shift J (b i) _ _ (std_gen J v hJ (y i) (hy i))
      have e3 : infPartPi (fun i => x i + sg v (y i)) = infPartPi x := by
        unfold infPartPi
        simp only [e]
      simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi, e2, e3]
  | zero =>
    refine Eventually.of_forall fun v => ⟨fun x hx => absurd rfl hx, fun x y _ => rfl⟩
  | add f g _ _ ihf ihg =>
    filter_upwards [ihf, ihg] with v a c
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · by_cases h : f x = 0
      · refine c.1 x (fun h' => hx ?_) i
        simp [h, h']
      · exact a.1 x h i
    · simp only [Pi.add_apply, a.2 x y hy, c.2 x y hy]
  | smul t f _ ih =>
    filter_upwards [ih] with v a
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · refine a.1 x (fun h' => hx ?_) i
      simp [h']
    · simp only [Pi.smul_apply, a.2 x y hy]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem nu_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x y : GL (Fin 2) (A E)) :
    nu F (x * y) = nu F x * nu F y := by simp only [nu, map_mul]

private theorem nu_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by simp only [nu, map_one]

private theorem dM_mul' {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : dM (s * t) = dM s * dM t :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two])

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM])

private theorem coordinate_embedNorm_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) = Pi.single 0 u := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have e : D.mkE u 0 = u • AdeleBaseChange.adeleBasis D.b 0 := by
    rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one, Algebra.smul_def, mul_one, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  funext i
  simp only [Dat.co, e, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_pi_single]

private theorem co_mkE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 0 = u := by rw [coordinate_embedNorm_zero]; simp

private theorem co_mkE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 1 = 0 := by rw [coordinate_embedNorm_zero]; simp

theorem UpperTheory.ConvolutionTheory.R2.H.liftRel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h₀ : GL (Fin 2) (A E),
      ∀ᶠ v : P F in cofinite, W.η.UnrAt v → W.η.val v = -1 → ∀ α β : ℂˣ, π.HasSat v {α, β} → ∀ (ϖ : (Kv v)ˣ) (z : (A E)ˣ), IsU ϖ →
        (z : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 → ideleNorm F E z = idl v ϖ ^ 2 →
        WE D (lift W M f.1 φ) (aE z * h₀) = (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D (lift W M f.1 φ) h₀ ∧
          ∀ h, lift W M f.1 φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((α : ℂ) * β) ^ 2 * lift W M f.1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h₀
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hl : IsOpen {k : GL (Fin 2) (Af F) | ∀ g, f.1 (g * finGL F 2 k) = f.1 g} := by
    convert (π.cusp f hf).1.level using 1
    exact Set.ext fun k => ⟨fun a => Subtype.ext (funext a), fun a g => congrFun (congrArg Subtype.val a) g⟩
  let f₁ : GL (Fin 2) (A F) → ℂ := fun g => f.1 (g * dM (nu F h₀))
  have hc : Continuous f₁ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).1.comp (continuous_mul_const _)
  have hleft : ∀ γ g, f₁ (ratGL F 2 γ * g) = f₁ g := fun γ g => by
    simp only [f₁, mul_assoc]
    exact (π.cusp f hf).1.left γ _
  have hw : ∀ x, w1 W f.1 φ (x * h₀) = w1 W f₁ (W.L h₀ φ) x := fun x => funext fun g => by
    simp only [w1, Wf, f₁, nu_mul', dM_mul', map_mul, Module.End.mul_apply, mul_assoc]
  have hb : w1 W f.1 φ h₀ = fun g => Wf f₁ (gl g) * UpperTheory.ConvolutionTheory.R2.hat (W.Om g (W.L h₀ φ)).1 ![0, 1, 1, 0] := by
    rw [← one_mul h₀, hw, one_mul]
    funext g
    simp only [w1, nu_one', dM_one', map_one, mul_one, Module.End.one_apply]
  obtain ⟨hN, hE⟩ := wfEig F f₁ hc hleft
  filter_upwards [gdAe F D.δ hδ, (aeK F).2.1 (nu F h₀), (aeK F).2.2 f.1 hl, stdAe F (W.L h₀ φ)] with v hg hk hfix hstd
    hu hval α β hB ϖ z hϖ hz hn
  have hEig := UpperTheory.V.Af.Smo.eigOfSat F 2 π v _ hB f hf hfix
  refine ⟨?_, fun h => ?_⟩
  · rw [UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ, UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ]
    obtain ⟨-, -, c1, c2, c3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ (aE z * h₀)
    obtain ⟨-, -, -, -, c4⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h₀
    rw [hw] at c1 c2 c3
    rw [hb] at c4
    have e1 : W1 W M f.1 φ (aE z * h₀) = W1 W M f₁ (W.L h₀ φ) (aE z) := by simp only [W1, hw]
    have hz' : ((z⁻¹ : (A E)ˣ) : A E) = D.mkE (((idl v ϖ)⁻¹ : (A F)ˣ) : A F) 0 := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hz]
      simp only [Dat.mkE, map_zero, zero_mul, add_zero, ← map_mul, Units.mul_inv, map_one]
    rw [e1, conjStep F E D W M f₁ _ z c1 c2 c3, hn, hz', co_mkE, co_mkE',
      core F E D W M v ϖ hϖ hg hu hval (Wf f₁) α β (hE v _ ((fixTr F v f.1 _ hk).2 _ hEig)) hN _ hstd c4]
    simp only [W1, hb]
  · rw [(UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf), hn]
    by_cases h0 : f.1 = 0
    · simp [UpperTheory.ConvolutionTheory.R2.lift, h0]
    · obtain ⟨g, hg0⟩ := Function.ne_iff.1 h0
      obtain ⟨R, -, -, hR⟩ := heckeExpl F v ϖ hϖ
      have h1 : f.1 (g * lc v (1 * dL ϖ ϖ)) = (α : ℂ) * β * f.1 (g * lc v 1) := (hR α β _ (hEig g) 1).2
      have h2 : g * Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) * g :=
        Units.ext ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq.symm)
      rw [one_mul, map_one, mul_one, (lcLaws F v).2.2.2.2.1, h2, hω f hf] at h1
      rw [map_pow, Units.val_pow_eq_pow_val, mul_right_cancel₀ hg0 h1]
