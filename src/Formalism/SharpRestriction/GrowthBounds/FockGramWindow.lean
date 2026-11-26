module

public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.InitialPointNumericBound

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.DiagRank
namespace PI


open Classical in
def DiagRank : Prop := by
  classical
  exact ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

end PI
end

section -- merged from Formalism.PeriodIntegrals.LatMin
namespace PI

open MvPolynomial

def LatMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

end PI
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.WinLvl
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LettersAtUPos
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.NormFockLe
section -- merged from Formalism.SharpRestriction.GrowthBounds.FockGramWindow.GramWindow2Proved
noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset

section Point

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem zsmul_eq (c : ℤ_[p]) (x : MvPolynomial σ ℚ_[p]) : c • x = (c : ℚ_[p]) • x := by
  rw [← algebraMap_smul ℚ_[p] c x, PadicInt.algebraMap_apply]

theorem norm_ge_of_gt (d : ℚ_[p]) (k : ℤ) (h : (p : ℝ) ^ (-((k : ℝ) + 1)) < ‖d‖) : (p : ℝ) ^ (-k) ≤ ‖d‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hd : d ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact absurd h (not_lt.2 (Real.rpow_nonneg (by linarith) _))
  rw [Padic.norm_eq_zpow_neg_valuation hd] at h ⊢
  have e1 : (p : ℝ) ^ (-((k : ℝ) + 1)) = (p : ℝ) ^ (-(k + 1) : ℤ) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [e1] at h
  have h2 := (zpow_lt_zpow_iff_right₀ hp1).1 h
  exact (zpow_le_zpow_iff_right₀ hp1).2 (by omega)

theorem bad_le_smith (n : ℕ) (k : ℤ) (Ψ : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (e : Fin n → MvPolynomial σ ℚ_[p]) (hli : LinearIndependent ℤ_[p] e)
    (h1 : ∀ (a : ℚ_[p]) u v, Ψ (a • u) v = a * Ψ u v) (h2 : ∀ u u' v, Ψ (u + u') v = Ψ u v + Ψ u' v)
    (h3 : ∀ (a : ℚ_[p]) u v, Ψ u (a • v) = a * Ψ u v) (h4 : ∀ u v v', Ψ u (v + v') = Ψ u v + Ψ u v')
    (s : ℚ_[p]) (hs0 : s ≠ 0) (hs1 : ‖s‖ ≤ 1) (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p])
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hG : ∀ a b, s * Ψ (e a) (e b) = (((U * Matrix.diagonal d * V) a b : ℤ_[p]) : ℚ_[p])) :
    Formalism.GM.M.bad p Ψ (Submodule.span ℤ_[p] (Set.range e)) k ≤
      (Finset.univ.filter (fun i => ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  set be : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p] :=
    LinearMap.mk₂ ℚ_[p] Ψ h2 (fun c u v => by rw [h1, smul_eq_mul]) h4 (fun c u v => by rw [h3, smul_eq_mul]) with hbe
  have hbeΨ : ∀ u v, be u v = Ψ u v := fun u v => rfl
  set L := Submodule.span ℤ_[p] (Set.range e) with hL
  have heL : ∀ a, e a ∈ L := fun a => Submodule.subset_span ⟨a, rfl⟩

  set P := U⁻¹ with hP
  set Q := V⁻¹ with hQ
  have hPU : P * U = 1 := Matrix.nonsing_inv_mul U hU
  have hVQ : V * Q = 1 := Matrix.mul_nonsing_inv V hV
  set x : Fin n → MvPolynomial σ ℚ_[p] := fun i => ∑ a, P i a • e a with hx
  set y : Fin n → MvPolynomial σ ℚ_[p] := fun l => ∑ b, Q b l • e b with hy
  have hxL : ∀ i, x i ∈ L := fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)
  have hyL : ∀ i, y i ∈ L := fun i => L.sum_mem fun a _ => L.smul_mem _ (heL a)
  have hxy : ∀ i l, s * Ψ (x i) (y l) = if i = l then (d i : ℚ_[p]) else 0 := by
    intro i l
    have e1 : s * Ψ (x i) (y l) = ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p]) := by
      rw [← hbeΨ, hx, hy]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [zsmul_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hbeΨ,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have e2 : (((P * (U * Matrix.diagonal d * V) * Q) i l : ℤ_[p]) : ℚ_[p]) =
        ∑ a, ∑ b, (P i a : ℚ_[p]) * (s * Ψ (e a) (e b)) * (Q b l : ℚ_[p]) := by
      simp only [hG]
      generalize U * Matrix.diagonal d * V = M
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [PadicInt.coe_sum, PadicInt.coe_mul]
    have e3 : P * (U * Matrix.diagonal d * V) * Q = Matrix.diagonal d := by
      calc P * (U * Matrix.diagonal d * V) * Q = (P * U) * Matrix.diagonal d * (V * Q) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal d := by rw [hPU, hVQ, Matrix.one_mul, Matrix.mul_one]
    rw [e1, ← e2, e3, Matrix.diagonal_apply]
    split_ifs <;> simp

  set S := Finset.univ.filter (fun i => ¬ ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1))) with hS
  set m := S.card with hm
  set ι : Fin m → Fin n := fun t => (S.equivFin.symm t : Fin n) with hι
  have hιinj : Function.Injective ι := fun t t' h => S.equivFin.symm.injective (Subtype.ext h)
  have hιS : ∀ t, (p : ℝ) ^ (-k) ≤ ‖(d (ι t) : ℚ_[p])‖ := by
    intro t
    have : ι t ∈ S := (S.equivFin.symm t).2
    rw [hS, Finset.mem_filter] at this
    exact norm_ge_of_gt _ k (not_le.1 this.2)
  have hd0 : ∀ t, (d (ι t) : ℚ_[p]) ≠ 0 := by
    intro t h0
    have := hιS t
    rw [h0, norm_zero] at this
    exact absurd this (not_le.2 (zpow_pos (by linarith) _))
  have hsc : ∀ t, ‖(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p])‖ ≤ 1 := by
    intro t
    rw [norm_div, norm_mul, norm_zpow, Padic.norm_p, inv_zpow', div_le_one (norm_pos_iff.2 (hd0 t))]
    calc (p : ℝ) ^ (-k) * ‖s‖ ≤ (p : ℝ) ^ (-k) * 1 :=
          mul_le_mul_of_nonneg_left hs1 (zpow_nonneg (by linarith) _)
      _ ≤ ‖(d (ι t) : ℚ_[p])‖ := by rw [mul_one]; exact hιS t
  have hgood : m ≤ Formalism.GM.M.goodCount p Ψ L k := by
    have hW : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Set.range e)) :=
      FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range e)
    have hb := Formalism.MainNotions.G.SymmetricFormBlocks.gc_bdd_gen p Ψ h1
      (fun n' s' f v => by
        show be (∑ i ∈ s', f i) v = ∑ i ∈ s', be (f i) v
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, LinearMap.sum_apply])
      L (Submodule.span ℚ_[p] (Set.range e)) (fun z hz => Submodule.span_subset_span ℤ_[p] ℚ_[p] _ hz) k
    set cc : Fin m → ℤ_[p] := fun t => ⟨(p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]), hsc t⟩ with hcc
    refine le_csSup hb ⟨fun t => x (ι t), fun t => cc t • y (ι t), fun t => hxL _,
      fun t => L.smul_mem _ (hyL _), ?_⟩
    intro t t'
    show Ψ (x (ι t)) (cc t' • y (ι t')) = _
    rw [zsmul_eq, h3]
    have hh := hxy (ι t) (ι t')
    have hΨ : Ψ (x (ι t)) (y (ι t')) = (if ι t = ι t' then (d (ι t) : ℚ_[p]) else 0) / s := by
      rw [← hh]; field_simp
    rw [hΨ]
    by_cases htt : t = t'
    · subst htt
      rw [if_pos rfl, if_pos rfl]
      show (p : ℚ_[p]) ^ k * s / (d (ι t) : ℚ_[p]) * ((d (ι t) : ℚ_[p]) / s) = _
      have := hd0 t
      field_simp
    · rw [if_neg htt, if_neg (fun h => htt (hιinj h)), zero_div, mul_zero]
  have hrank : Module.finrank ℤ_[p] L = n := by
    rw [hL, finrank_span_eq_card hli, Fintype.card_fin]
  have hcard : (Finset.univ.filter (fun i => ‖(d i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card + m = n := by
    rw [hm, hS, Finset.card_filter_add_card_filter_not]
    simp
  unfold Formalism.GM.M.bad
  omega

end Point

open Formalism.GM Formalism.GM.MeanGammaLemmas in
theorem gramWindow2_proved : GramWindow2 := by
  intro p hp σ n del h Y0 k La0 t0 Ψ e s c hli h1 h2 h3 h4 hY0 hYh hdel hk hc hdet hlead hgram
  classical
  set Aq := binMatK ℚ_[p] del c with hAq

  set cz : Fin n → Fin n → ℕ → ℤ_[p] := fun a b i => ⟨c a b i, hc a b i⟩ with hcz
  have hczc : ∀ a b i, ((cz a b i : ℤ_[p]) : ℚ_[p]) = c a b i := fun _ _ _ => rfl
  set M : ℕ → Matrix (Fin n) (Fin n) ℤ_[p] := fun j a b =>
    ∑ i ∈ Finset.range (del + 1), cz a b i * (((t0 + j).choose i : ℕ) : ℤ_[p]) with hMdef
  have hM : ∀ j a b, ((M j a b : ℤ_[p]) : ℚ_[p]) = (Aq a b).eval (((t0 + j : ℕ) : ℚ_[p])) := by
    intro j a b
    rw [hAq, binMatK_eval_nat]
    simp only [hMdef, PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_natCast, hczc]
  choose U V d hU hV hfac using fun j => Formalism.GM.Top.smithZp p n (M j)

  have hpt : ∀ j ∈ Finset.range Y0,
      (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ) ≤
        ((Finset.univ.filter (fun i => ‖(d j i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) := by
    intro j hj
    obtain ⟨hs0, hs1, hg⟩ := hgram j hj
    have := bad_le_smith n k (Ψ j) e hli (h1 j) (h2 j) (h3 j) (h4 j) (s j) hs0 hs1 (U j) (V j) (d j) (hU j) (hV j)
      (fun a b => by rw [hg a b, ← hfac j, hM, Matrix.map_apply])
    exact_mod_cast this

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set φ : ℤ_[p] →+* PadicAlgCl p := alg.comp PadicInt.Coe.ringHom with hφ
  have hφn : ∀ z : ℤ_[p], ‖φ z‖ = ‖z‖ := by
    intro z
    show ‖alg (z : ℚ_[p])‖ = _
    rw [halg, norm_algebraMap', PadicInt.norm_def]
  set c' : Fin n → Fin n → ℕ → PadicAlgCl p := fun i j k => alg (c i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) del c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg del _
  have hDk : (binMatK (PadicAlgCl p) del c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) del c').det
  have hlc : (binMatK (PadicAlgCl p) del c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, Polynomial.leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) del c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, Polynomial.natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hleadne : (binMatK (PadicAlgCl p) del c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm, norm_pos_iff]
    exact Polynomial.leadingCoeff_ne_zero.2 hdet
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) del c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) del c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0 := by
    rw [hlcnorm, hcard, hnd]; exact hlead
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap']
    exact hc i j k
  set idx : ℤ → ℕ := fun t => (t - (t0 : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (t0 : ℤ) 1 j) = j := by
    intro j
    simp only [hidxdef, progr]
    omega
  set U' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (U (idx t)) with hU'
  set V' : ℤ → Matrix (Fin n) (Fin n) (PadicAlgCl p) := fun t => φ.mapMatrix (V (idx t)) with hV'
  set dg' : ℤ → Fin n → PadicAlgCl p := fun t b => φ (d (idx t) b) with hdg'
  have hsm : ∀ j ∈ Finset.range Y0, (∀ x y, ‖U' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (t0 : ℤ) 1 j) x y‖ ≤ 1) ∧
      ‖(U' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧ ‖(V' (progr (t0 : ℤ) 1 j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) del c').map (Polynomial.eval ((progr (t0 : ℤ) 1 j : ℤ) : PadicAlgCl p)) =
        U' (progr (t0 : ℤ) 1 j) * Matrix.diagonal (dg' (progr (t0 : ℤ) 1 j)) * V' (progr (t0 : ℤ) 1 j) := by
    intro j _
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, hφn]; exact PadicInt.norm_le_one _
    · rw [RingHom.mapMatrix_apply, Matrix.map_apply, hφn]; exact PadicInt.norm_le_one _
    · rw [← RingHom.map_det, hφn]; exact PadicInt.isUnit_iff.1 (hU j)
    · rw [← RingHom.map_det, hφn]; exact PadicInt.isUnit_iff.1 (hV j)
    · have e1 : (Matrix.diagonal fun b => φ (d j b)) = φ.mapMatrix (Matrix.diagonal (d j)) := by
        rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero φ)]
      rw [e1, ← map_mul, ← map_mul, ← hfac j, hAK]
      ext x y
      have hpt' : ((progr (t0 : ℤ) 1 j : ℤ) : PadicAlgCl p) = ((t0 + j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      rw [Matrix.map_apply, Matrix.map_apply, hpt', Polynomial.eval_natCast_map, ← hM, RingHom.mapMatrix_apply,
        Matrix.map_apply]
      rfl
  have hE0 : (0 : ℝ) < (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have key := Formalism.GM.Top.windowFullAP p (PadicAlgCl p) n del h ((k : ℝ) + 1) c'
    (binMatK (PadicAlgCl p) del c').det.leadingCoeff (binMatK (PadicAlgCl p) del c').det.roots (t0 : ℤ) 1 Y0 La0
    U' V' dg' isCoprime_one_left hY0 hYh (by omega) hE0 hleadne hc'norm hsplit hsm hLB'
  have hYpos : (0 : ℝ) < Y0 := by exact_mod_cast hY0
  rw [div_le_iff₀ hYpos] at key
  calc (∑ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ))
      ≤ ∑ j ∈ Finset.range Y0,
          ((Finset.univ.filter (fun i => ‖(d j i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) :=
        Finset.sum_le_sum hpt
    _ = ∑ j ∈ Finset.range Y0,
          ((Finset.univ.filter (fun i => ‖dg' (progr (t0 : ℤ) 1 j) i‖ ≤ (p : ℝ) ^ (-((k : ℝ) + 1)))).card : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hdg', hidx, hφn, PadicInt.norm_def]
    _ ≤ (n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1)) * Y0 := key
    _ = (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1))) := by ring

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality

section Ops

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type} {r : ℕ}

theorem one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

theorem bnd_Xl (w e : Fin r → σ) (J l : ℕ) (hl : l ≤ J) (B : ℝ) (hB : 0 ≤ B) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd B u) :
    Bnd (B * (p : ℝ) ^ ((r + 1) * Nat.log p J))
      ((((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u))) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  set Mc : ℝ := (p : ℝ) ^ (Nat.log p J) with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ J, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right hj))
  let D : Fin r → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (D a) (D b) := by
    intro a b
    simp only [D, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum D hcomm (fun a k => contr_D _ _ k) hM1 J hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : Formalism.GM.tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, D c := rfl
  have h1 := hF l hl B hB u hu
  rw [← hFeq] at h1
  have h2 := contr_pow zero_le_one (contr_E (p := p) w e) l _ (by positivity) _ h1
  have eq : (((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u)) =
      (((J.choose l : ℕ) : ℚ_[p])⁻¹) • ((tieE w e ^ l) (((((l.factorial : ℚ_[p]) ^ 2))⁻¹ • (tieF w e ^ l)) u)) := by
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv, mul_comm]
  rw [eq]
  refine bnd_mono (bnd_smul _ h2) ?_
  have hA := hM J le_rfl l hl
  calc ‖(((J.choose l : ℕ) : ℚ_[p]))⁻¹‖ * (B * Mc ^ r * 1 ^ l) ≤ Mc * (B * Mc ^ r * 1 ^ l) := by gcongr
    _ = B * (p : ℝ) ^ ((r + 1) * Nat.log p J) := by
        rw [hMc, one_pow, mul_one, ← pow_mul, mul_comm ((p : ℝ) ^ Nat.log p J), mul_assoc, ← pow_add]
        congr 2; ring

theorem bnd_pow_iff (k : ℕ) (u : MvPolynomial σ ℚ_[p]) :
    Bnd ((p : ℝ) ^ k) u ↔ M.IsIntegral' p (((p : ℚ_[p]) ^ k) • u) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one one_le_p
  have hk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  refine forall_congr' fun m => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hk, mul_one]

theorem bnd_phi (w e : Fin r → σ) (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (hr : 1 ≤ r) (o n z Λ : ℕ) (hΛ : Nat.log p (o + n + r + z) + 1 ≤ Λ) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) : Bnd ((p : ℝ) ^ (k + (r + 1) * Λ)) (tiePhi w e o n z u) := by
  have h1 := (bnd_pow_iff k u).1 hu
  have h2 := Formalism.GM.projectorIntegral p σ r w e hw he hwe hr o n z _ h1
  rw [map_smul, smul_smul, ← pow_add] at h2
  refine bnd_mono ((bnd_pow_iff _ _).2 h2) (pow_le_pow_right₀ one_le_p ?_)
  have := Nat.mul_le_mul_left (r + 1) hΛ
  omega

theorem bnd_foldr {ι : Type} (φ : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (c : ℕ) (l : List ι)
    (h : ∀ i ∈ l, ∀ k u, Bnd ((p : ℝ) ^ k) u → Bnd ((p : ℝ) ^ (k + c)) (φ i u)) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) :
    Bnd ((p : ℝ) ^ (k + l.length * c)) ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) u) := by
  induction l with
  | nil => simpa using hu
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
    have h1 := ih (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))
    have h2 := h i List.mem_cons_self _ _ h1
    rw [show k + (l.length + 1) * c = k + l.length * c + c by ring]
    exact h2

theorem norm_fock_le (U v : MvPolynomial σ ℚ_[p]) (dF : ℕ) (hdF : dF ≠ 0) (k E : ℕ) (hU : Bnd ((p : ℝ) ^ k) U)
    (hv : Bnd 1 v)
    (hval : ∀ m ∈ v.support, padicValNat p dF ≤ padicValNat p (m.prod fun _ i => i.factorial) + E) :
    ‖M.fockK U v / (dF : ℚ_[p])‖ ≤ (p : ℝ) ^ (k + E) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  unfold M.fockK
  rw [Finset.sum_div]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
  by_cases hm : m ∈ v.support
  · have hne : (m.prod fun _ i => i.factorial) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _
    have hcast : (m.prod fun _ j => (j.factorial : ℚ_[p])) = (((m.prod fun _ i => i.factorial) : ℕ) : ℚ_[p]) := by
      simp [Finsupp.prod]
    rw [hcast, norm_div, norm_mul, norm_mul, Formalism.GM.MeanGammaLemmas.norm_nat p _ hne, Formalism.GM.MeanGammaLemmas.norm_nat p _ hdF,
      mul_div_assoc, ← zpow_sub₀ hp0.ne']
    have h3 : (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ)) ≤
        (p : ℝ) ^ E := by
      rw [← zpow_natCast]
      apply zpow_le_zpow_right₀ hp1
      have := hval m hm
      omega
    calc ‖AddMonoidAlgebra.coeff U m‖ * ‖AddMonoidAlgebra.coeff v m‖ *
          (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ))
        ≤ (p : ℝ) ^ k * 1 * (p : ℝ) ^ E := by
          gcongr
          · exact hU m
          · exact hv m
      _ = (p : ℝ) ^ (k + E) := by rw [mul_one, pow_add]
  · rw [notMem_support_iff.1 hm, mul_zero, zero_mul, zero_div, norm_zero]
    positivity

end Ops

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality Formalism.MainNotions.G.SymmetricFormBlocks
open scoped Nat

section Lat

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Ljj_le (S : Submodule ℤ_[p] (MvPolynomial (M.BVar N r G.T.t) ℚ_[p])) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (h : ∀ y ∈ M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∀ g ∈ M.XiPolZ p N r G.T.t (G.B - jp),
      rename (M.chainEmb N r G.T.t) y * g ∈ S) : Ljj p (r := r) G j jp ≤ S := by
  unfold Ljj
  rw [Submodule.span_le]
  rintro x ⟨y, hy, g, hg, rfl⟩
  exact h y hy g hg

theorem Ljj_int (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : Bnd 1 v := by
  have h := Ljj_le p G (M.IntPol p (M.BVar N r G.T.t)) j jp
    (fun y hy g hg => M.intPol_mul' (M.intPol_rename' _ hy.2.2) hg.2) hv
  exact (Formalism.InvariantFactorPaths.KP.LL.intPol_iff_bnd v).1 h

def dJ (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  chDeg (G.lettersAt j jp) a + (if Fin.last N = a then G.B - jp else 0)

theorem Ljj_hom (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : IsWeightedHomogeneous (wL (r := r) G a) v (dJ G j jp a) := by
  have key : Ljj p (r := r) G j jp ≤
      (weightedHomogeneousSubmodule ℚ_[p] (wL (r := r) G a) (dJ G j jp a)).restrictScalars ℤ_[p] := by
    refine Ljj_le p G _ j jp ?_
    intro y hy g hg
    exact (hom_chain p G a _ y hy.2.1).mul (hom_xi p G a _ g hg)
  exact key hv

theorem prod_dJ (j : Fin G.T.t → ℕ) (jp : ℕ) : ∏ a, (dJ G j jp a)! = degFact G j jp := by
  unfold dJ degFact chDeg
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro a0 _
    simp [Fin.castSucc_inj, (Fin.castSucc_lt_last a0).ne']
  · simp [Fin.castSucc_ne_last]

theorem lettersAt_le (j : Fin G.T.t → ℕ) (jp : ℕ) (a0 : Fin N) : (G.lettersAt j jp).deg a0 ≤ G.LL.deg a0 := by
  unfold M.BlockData.lettersAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem dJ_le (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (a : Fin (N + 1)) : dJ G j jp a ≤ 2 * A := by
  unfold dJ chDeg
  by_cases ha : Fin.last N = a
  · subst ha
    simp [Fin.castSucc_ne_last]
    omega
  · rw [if_neg ha]
    obtain ⟨a0, rfl⟩ : ∃ a0, Fin.castSucc a0 = a := Fin.exists_castSucc_eq.2 (Ne.symm ha)
    have h1 := lettersAt_le G j jp a0
    have h2 := hdeg a0
    simp [Fin.castSucc_inj]
    omega

theorem log_le_lgN (A x : ℕ) (hx : x ≤ 8 * A + r) : Nat.log p x + 1 ≤ lgN p A r := by
  unfold lgN
  have h1 := Nat.log_mono_right (b := p) hx
  omega

theorem Ljj_val (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hv : v ∈ Ljj p (r := r) G j jp) :
    ∀ m ∈ v.support, padicValNat p (degFact G j jp) ≤
      padicValNat p (m.prod fun _ i => i !) + ((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r := by
  intro m hm
  rw [← prod_dJ G j jp]
  have hw : ∀ a, Finsupp.weight (wL (r := r) G a) m = dJ G j jp a :=
    fun a => Ljj_hom p G a j jp v hv (mem_support_iff.mp hm)
  refine val_letters_le p G m (dJ G j jp) hw (lgN p A r) (fun a => ?_)
  have h1 := dJ_le G A hdeg hBa j jp a
  have h2 := log_le_lgN p (r := r) A (dJ G j jp a) (by omega)
  omega

theorem lettersAt_uPos (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (G.lettersAt j jp).deg G.uPos = G.LL.deg G.uPos - jp := by
  obtain ⟨-, hpos, -, -⟩ := hB
  have hz : (∑ i : Fin G.T.t, if (G.uPos : ℕ) = G.T.pos i ∨ (G.uPos : ℕ) = G.T.pos i + 1 then j i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg (by have := hpos i; omega)
  change (List.map (fun i : Fin G.T.t => if (G.uPos : ℕ) = G.T.pos i ∨ (G.uPos : ℕ) = G.T.pos i + 1 then j i else 0) (List.finRange G.T.t)).sum = 0 at hz
  unfold M.BlockData.lettersAt
  simp only [hz, ite_true, Nat.sub_zero]

theorem Ljj_biHom (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) :
    BiHom (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
      (G.LL.deg G.uPos - jp) (G.B - jp) v := by
  have h1 := Formalism.InvariantFactorPaths.KP.LL.biHom_plus (p := p) (r := r) (D := G) j jp v hv
  rw [lettersAt_uPos G hB j jp] at h1
  exact h1

end Lat

end Formalism.MainNotions.G.GramWindowAlt

end
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality Formalism.MainNotions.G.SymmetricFormBlocks
open scoped Nat

section Lvl

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem bnd_phisB (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hz : ∀ i, G.T.z i ≤ 2 * A)
    (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : Bnd 1 u) :
    Bnd ((p : ℝ) ^ (G.T.t * ((r + 1) * lgN p A r))) (phisB p (r := r) G j jp u) := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  have h := bnd_foldr (p := p) (fun i : Fin G.T.t =>
    Formalism.GM.tiePhi (k := ℚ_[p]) (fun c => (Sum.inl (M.finPos N (G.T.pos i), c) : M.BVar N r G.T.t))
      (fun c => Sum.inl (M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i)) ((r + 1) * lgN p A r) (List.finRange G.T.t)
    (fun i _ k u hu => by
      refine bnd_phi _ _ ?_ ?_ ?_ hr _ _ _ (lgN p A r) ?_ k u hu
      · intro c d h
        simpa using h
      · intro c d h
        simpa using h
      · intro c d h
        simp only [Sum.inl.injEq, Prod.mk.injEq] at h
        have h1 := congrArg Fin.val h.1
        have h2 : min (G.T.pos i) N = min (G.T.pos i + 1) N := h1
        have h3 := hB.2.1 i
        have h4 := G.uPos.2
        omega
      · refine log_le_lgN p A _ ?_
        have h1 := (lettersAt_le G j jp (G.letterAt (G.T.pos i))).trans (hdeg _)
        have h2 := (lettersAt_le G j jp (G.letterAt (G.T.pos i + 1))).trans (hdeg _)
        have h3 := hz i
        omega) 0 u (by simpa using hu)
  rw [List.length_finRange, zero_add] at h
  exact h

theorem int_lvl (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ) (l : ℕ) (hl : l ≤ JN G jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    ‖(p : ℚ_[p]) ^ (x0N p A r N G.T.t) *
      (mX (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c) (JN G jp) l
        (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p]))‖ ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have h1 := bnd_phisB p G hB A hdeg hz j jp u (Ljj_int p G j jp u hu)
  have h2 := bnd_Xl (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
    (JN G jp) l hl _ (by positivity) _ h1
  have hJ : JN G jp ≤ 2 * A := (min_le_right _ _).trans ((Nat.sub_le _ _).trans hBa)
  have hlog : Nat.log p (JN G jp) ≤ lgN p A r := by
    have := log_le_lgN p (r := r) A (JN G jp) (by omega)
    omega
  have h3 : Bnd ((p : ℝ) ^ (G.T.t * ((r + 1) * lgN p A r) + (r + 1) * lgN p A r)) _ :=
    bnd_mono h2 (by
      rw [← pow_add]
      exact pow_le_pow_right₀ hp1 (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlog) _))
  have h4 := norm_fock_le _ v (degFact G j jp) (degFact_ne_zero G j jp) _
    (((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r) h3 (Ljj_int p G j jp v hv) (Ljj_val p G A hdeg hBa j jp v hv)
  rw [ProjS.fockK_smul_left] at h4
  have hx : G.T.t * ((r + 1) * lgN p A r) + (r + 1) * lgN p A r + ((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r =
      x0N p A r N G.T.t := by
    unfold x0N; ring
  rw [hx] at h4
  unfold mX
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, div_eq_inv_mul (M.fockK _ _)]
  rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
  exact h4

end Lvl

theorem winLvl : WinLvl := by
  intro p _ N r _ G hB j jp _ A _ hdeg hBa hz n₁ f hf hli horth D hsmall z0 W h k hk hW hWh hJh
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  have hJ : JN G jp ≤ 2 * A := (min_le_right _ _).trans ((Nat.sub_le _ _).trans hBa)
  have hV : ((min (G.LL.deg G.uPos - jp) (G.B - jp) : ℕ) : ℝ) / ((p : ℝ) - 1) -
      padicValNat p (min (G.LL.deg G.uPos - jp) (G.B - jp)).factorial ≤ (lgN p A r : ℝ) := by
    refine (Formalism.GM.MeanGammaLemmas.legendre' p _).trans ?_
    have := log_le_lgN p (r := r) A (JN G jp) (by omega)
    exact_mod_cast this
  exact win_abs (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
    gramWindow2_proved
    (by intro c d h; simpa using h)
    (by intro c d h; simpa [M.xiVar] using h)
    (by
      intro c d h
      simp only [M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact (Fin.castSucc_lt_last G.uPos).ne h.1)
    hr (G.LL.deg G.uPos - jp) (G.B - jp) (phisB p (r := r) G j jp) (degFact G j jp : ℚ_[p]) n₁ f hli
    (fun b => Ljj_biHom p G hB j jp (f b) (hf b)) (x0N p A r N G.T.t)
    (fun l hl a b => int_lvl p G hB A hdeg hBa hz j jp l hl (f a) (f b) (hf a) (hf b))
    horth D hsmall (lgN p A r : ℝ) hV z0 W h k hk hW hWh hJh

end Formalism.MainNotions.G.GramWindowAlt

end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiagRank
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe
noncomputable section

namespace PI.UnitaryGroupMassFormula.DiagRank

open Finset

theorem det_one_sub_p_ne {p : ℕ} [Fact p.Prime] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (1 - (p : ℤ_[p]) • M).det ≠ 0 := by

  intro h0
  have h1 := congrArg (PadicInt.toZMod (p := p)) h0
  rw [RingHom.map_det, map_zero] at h1
  have hI : (PadicInt.toZMod (p := p)).mapMatrix (1 - (p : ℤ_[p]) • M) = 1 := by
    ext i j
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [hI, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem exists_int_mul {p : ℕ} [Fact p.Prime] (D : ℤ) (x : ℚ_[p]) (hx : x ≠ 0 → D < x.valuation) :
    ∃ u : ℤ_[p], x = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hv := hx h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (D + 1) ≠ 0 := zpow_ne_zero _ hp0
  have hnp : ‖(p : ℚ_[p]) ^ (D + 1)‖ = (p : ℝ) ^ (-(D + 1)) := by
    rw [norm_zpow, Padic.norm_p, inv_zpow', zpow_neg]
  refine ⟨⟨x / (p : ℚ_[p]) ^ (D + 1), ?_⟩, ?_⟩
  · rw [PadicInt.mem_subring_iff, norm_div, hnp, Padic.norm_eq_zpow_neg_valuation h0]
    rw [div_le_one (zpow_pos (by linarith) _)]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  · show x = (p : ℚ_[p]) ^ (D + 1) * (x / (p : ℚ_[p]) ^ (D + 1))
    field_simp

open Classical in
theorem diagRank : PI.DiagRank := by
  unfold PI.DiagRank
  intro p _ n m X Y c D h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpD : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ hp0
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m),
      S = Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D) := ⟨_, rfl⟩
  rw [← hS]
  have hsplit : ∀ a, a ∉ S → ∃ u : ℤ_[p], c a = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
    intro a ha
    apply exists_int_mul D (c a)
    intro hc
    by_contra hle
    exact ha (by rw [hS]; simp [hc, not_lt.mp hle])
  choose! u hu using hsplit

  obtain ⟨s, hs⟩ : ∃ s : Fin m → ℚ_[p], s = fun a => if a ∈ S then c a / (p : ℚ_[p]) ^ D else 0 :=
    ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : Fin m → ℤ_[p], u' = fun a => if a ∈ S then 0 else u a := ⟨_, rfl⟩
  have key : ∀ a, c a = (p : ℚ_[p]) ^ D * s a + (p : ℚ_[p]) ^ (D + 1) * (u' a : ℚ_[p]) := by
    intro a
    by_cases ha : a ∈ S
    · simp [hs, hu', ha]; field_simp
    · simp [hs, hu', ha, hu a ha]
  have hent : ∀ i j, ∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) =
      (if i = j then 1 else 0) - (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by
    intro i j
    have h1 := h i j
    have h2 : ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = (p : ℚ_[p]) ^ D *
        (∑ a, (X i a : ℚ_[p]) * s a * (Y j a : ℚ_[p]) +
          (p : ℚ_[p]) * ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p])) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [key a, zpow_add₀ hp0, zpow_one]
      ring
    have h3 : (if i = j then (p : ℚ_[p]) ^ D else 0) = (p : ℚ_[p]) ^ D * (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h2, h3] at h1
    exact eq_sub_of_add_eq (mul_left_cancel₀ hpD h1)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℤ_[p], N = fun i j => ∑ a, X i a * u' a * Y j a :=
    ⟨_, rfl⟩
  obtain ⟨Xq, hXq⟩ : ∃ Xq : Matrix (Fin n) (Fin m) ℚ_[p], Xq = fun i a => (X i a : ℚ_[p]) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin n) ℚ_[p], B = fun a j => (Y j a : ℚ_[p]) := ⟨_, rfl⟩
  have heq : Xq * Matrix.diagonal s * B = PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N) := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    subst hXq hB
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hent i j, hN]
    show _ = ((_ : ℤ_[p]) : ℚ_[p])
    have hc : ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = ∑ a, (X i a : ℚ_[p]) * (u' a : ℚ_[p]) * (Y j a : ℚ_[p]) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show ((∑ a, X i a * u' a * Y j a : ℤ_[p]) : ℚ_[p]) = PadicInt.Coe.ringHom (∑ a, X i a * u' a * Y j a) from rfl, map_sum]
      rfl
    split_ifs <;> push_cast <;> rw [hc]
  have hdet : (PadicInt.Coe.ringHom.mapMatrix (1 - (p : ℤ_[p]) • N)).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact det_one_sub_p_ne N (Subtype.ext h0)
  have hrank : (Xq * Matrix.diagonal s * B).rank = n := by
    rw [heq, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc n = (Xq * Matrix.diagonal s * B).rank := hrank.symm
    _ ≤ (Xq * Matrix.diagonal s).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal s).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {a // s a ≠ 0} := Matrix.rank_diagonal s
    _ = (Finset.univ.filter (fun a => s a ≠ 0)).card := Fintype.card_subtype _
    _ ≤ S.card := by
      apply Finset.card_le_card
      intro a ha
      by_contra haS
      simp [hs, haS] at ha

end PI.UnitaryGroupMassFormula.DiagRank

end
end

theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatMin
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne
namespace PI.LatMinWork

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have h1 : ‖((2 : ℤ) : ℚ_[p])‖ ≤ 1 := by
    first
      | exact Padic.norm_int_le_one 2
      | exact padicNormE.norm_int_le_one 2
  have h3 : ¬ ‖((2 : ℤ) : ℚ_[p])‖ < 1 := fun h => h2 (by
    first
      | exact Padic.norm_intCast_lt_one_iff.mp h
      | exact (Padic.norm_int_lt_one_iff_dvd 2).1 h
      | exact (padicNormE.norm_int_lt_one_iff_dvd 2).1 h)
  have := le_antisymm h1 (not_lt.1 h3)
  exact_mod_cast this

variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]

lemma bound_span (B : V → V → ℚ_[p])
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (S : Set V) (w : V) (M : ℝ) (hM : 0 ≤ M) (hS : ∀ b ∈ S, ‖B b w‖ ≤ M) :
    ∀ v ∈ Submodule.span ℤ_[p] S, ‖B v w‖ ≤ M := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : B 0 w = 0 := by simpa using hsm 0 0 w
    rw [h0, norm_zero]; exact hM
  | add x y _ _ hx hy =>
    rw [hadd]
    exact (show ‖B x w + B y w‖ ≤ max ‖B x w‖ ‖B y w‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [hsm, norm_mul]
    have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
      first
        | exact c.2
        | simpa using PadicInt.norm_le_one c
    calc ‖(c : ℚ_[p])‖ * ‖B x w‖ ≤ 1 * ‖B x w‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hx

theorem main (hp2 : p ≠ 2) (B : V → V → ℚ_[p]) (L : Submodule ℤ_[p] V) (hL : L.FG)
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (hsym : ∀ u ∈ L, ∀ v ∈ L, B u v = B v u) (hne : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) :
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨u0, hu0, v0, hv0, hne0⟩ := hne
  have hSL : ∀ a ∈ S, a ∈ L := fun a ha => hS ▸ Submodule.subset_span ha
  have hB0 : ∀ v, B 0 v = 0 := fun v => by simpa using hsm 0 0 v
  have hSn : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · subst h
      rw [Finset.coe_empty, Submodule.span_empty] at hS
      rw [← hS, Submodule.mem_bot] at hu0
      subst hu0
      exact absurd (hB0 v0) hne0
    · exact h
  obtain ⟨q, hq, hqmax⟩ := (S ×ˢ S).exists_max_image (fun q : V × V => ‖B q.1 q.2‖) (hSn.product hSn)
  obtain ⟨a, b⟩ := q
  have ha : a ∈ S := (Finset.mem_product.1 hq).1
  have hb : b ∈ S := (Finset.mem_product.1 hq).2
  have hmaxS : ∀ a' ∈ S, ∀ b' ∈ S, ‖B a' b'‖ ≤ ‖B a b‖ := fun a' ha' b' hb' =>
    hqmax (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)
  have hM0 : 0 ≤ ‖B a b‖ := norm_nonneg _
  have h1 : ∀ b' ∈ S, ∀ u ∈ L, ‖B u b'‖ ≤ ‖B a b‖ := fun b' hb' u hu => by
    rw [← hS] at hu
    exact bound_span B hsm hadd (↑S) b' _ hM0 (fun a' ha' => hmaxS a' ha' b' hb') u hu
  have hbound : ∀ u ∈ L, ∀ v ∈ L, ‖B u v‖ ≤ ‖B a b‖ := by
    intro u hu v hv
    rw [hsym u hu v hv]
    have h2 : ∀ b' ∈ (S : Set V), ‖B b' u‖ ≤ ‖B a b‖ := fun b' hb' => by
      rw [hsym b' (hSL b' hb') u hu]; exact h1 b' hb' u hu
    rw [← hS] at hv
    exact bound_span B hsm hadd (↑S) u _ hM0 h2 v hv
  have hMpos : 0 < ‖B a b‖ := lt_of_lt_of_le (norm_pos_iff.2 hne0) (hbound u0 hu0 v0 hv0)
  have haL := hSL a ha
  have hbL := hSL b hb
  have hx : ∃ x ∈ L, ‖B x x‖ = ‖B a b‖ := by
    by_cases haa : ‖B a a‖ = ‖B a b‖
    · exact ⟨a, haL, haa⟩
    by_cases hbb : ‖B b b‖ = ‖B a b‖
    · exact ⟨b, hbL, hbb⟩
    have habL := L.add_mem haL hbL
    refine ⟨a + b, habL, ?_⟩
    have e : B (a + b) (a + b) = 2 * B a b + (B a a + B b b) := by
      rw [hadd, hsym a haL _ habL, hsym b hbL _ habL, hadd, hadd, hsym b hbL a haL]; ring
    have hlt : ‖B a a + B b b‖ < ‖B a b‖ := lt_of_le_of_lt (show ‖B a a + B b b‖ ≤ max ‖B a a‖ ‖B b b‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (lt_of_le_of_ne (hbound a haL a haL) haa) (lt_of_le_of_ne (hbound b hbL b hbL) hbb))
    have h2ab : ‖2 * B a b‖ = ‖B a b‖ := by rw [norm_mul, norm_two_eq_one hp2, one_mul]
    rw [e, (show ‖2 * B a b + (B a a + B b b)‖ = max ‖2 * B a b‖ ‖B a a + B b b‖ by
      first
        | exact Padic.add_eq_max_of_ne (by rw [h2ab]; exact hlt.ne')
        | exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2ab]; exact hlt.ne')), h2ab]
    exact max_eq_left hlt.le
  obtain ⟨x, hxL, hxn⟩ := hx
  have hxx : B x x ≠ 0 := fun h => by rw [h, norm_zero] at hxn; linarith
  refine ⟨x, hxL, hxx, fun u hu => ?_⟩
  have hc : ‖B u x / B x x‖ ≤ 1 := by
    rw [norm_div, hxn, div_le_one hMpos]; exact hbound u hu x hxL
  exact ⟨(⟨B u x / B x x, hc⟩ : {y : ℚ_[p] // ‖y‖ ≤ 1}), (div_mul_cancel₀ _ hxx).symm⟩

end PI.LatMinWork

namespace PI

end PI
end

namespace PI

theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
end

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem restWinE_proved (D : Formalism.BasicNotions.D7) : RestWinE D := by
  intro Cc _
  refine ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 h1 h2 => ⟨2, two_pos, fun CYb Cde Ck CD Cb a1 _ _ a4 a5 => ?_⟩⟩⟩
  intro Ckap Cs CM hCM X _ hH
  have hS : SegFacts C0 CE1 CE2 X := segFacts a1 (by linarith) (by linarith) (by linarith) (by linarith) hH
  have hpk : X.L.k ^ 2 * X.L.Y ^ 2 ≤ (X.L.p : ℝ) := by
    obtain ⟨h0, -⟩ := hH
    obtain ⟨-, hpk, -⟩ := h0
    exact hpk
  exact restWin_of_lvl (by linarith) (by linarith) (by linarith) hH CM winLvl (restWinNum_proved hS hpk CM hCM)
    (a_mem_win hS)

theorem theorem_A_closed_form_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound (restWinE_proved D)

end Formalism.MainNotions.G.GramWindowAlt

end
