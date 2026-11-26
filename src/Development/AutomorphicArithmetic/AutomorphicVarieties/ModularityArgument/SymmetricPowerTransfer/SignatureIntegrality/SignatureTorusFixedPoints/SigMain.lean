module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TwistedOrbitalIntegralGL3Formula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkDOrb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NormalG
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

private theorem exists_conj_diag {k : Type} [Field k] (N : GL (Fin 3) k) (μ : Fin 3 → kˣ)
    (hμ : Function.Injective μ) (hroot : ∀ i, ((N : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot (μ i : k)) :
    ∃ g : GL (Fin 3) k, N = g * diagT k (Fin 3) μ * g⁻¹ :=
  UpperTheory.V.Lib.Small.conj_of_roots (fun i => (μ i : k)) (fun _ _ e => hμ (Units.ext e)) N _ (GlobalTheory.SmGL.val_diagT k μ) hroot

private theorem diag_of_comm {k : Type} [Field k] (μ : Fin 3 → kˣ) (hμ : Function.Injective μ)
    (e : GL (Fin 3) k) (h : e * diagT k (Fin 3) μ = diagT k (Fin 3) μ * e) :
    ∃ u : Fin 3 → kˣ, e = diagT k (Fin 3) u := by
  have hoff : ∀ i j, i ≠ j → (e : Matrix (Fin 3) (Fin 3) k) i j = 0 := by
    intro i j hij
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M i j) (congrArg Units.val h)
    simp only [Units.val_mul, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (μ j : k) ≠ μ i := fun h' => hij (hμ (Units.ext h')).symm
    have h3 : (e : Matrix (Fin 3) (Fin 3) k) i j * ((μ j : k) - μ i) = 0 := by
      rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)
  have hdiag : (e : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal fun i => (e : Matrix (Fin 3) (Fin 3) k) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (e : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 e.isUnit).ne_zero
  have hne : ∀ i, (e : Matrix (Fin 3) (Fin 3) k) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [val_diagT]
  simpa using hdiag

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.normalG :
    UpperTheory.V.Z.Sym.Sig.NormalG := by
  intro k _ _ _ _
  obtain ⟨-, -, hd, hθ, hΦ, hi, hc⟩ := thFacts k (Lev.iw k)
  obtain hP := (thFacts k (Lev.iw k)).1
  have ht : ∀ u : GL (Fin 3) k, th' k u = Phi k * th k 3 u * (Phi k)⁻¹ := fun u => rfl
  have hprod : ∀ x y z : kˣ, dg ![x, y, z] * th' k (dg ![x, y, z]) = dg ![x / z, 1, z / x] := by
    intro x y z
    rw [hd, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
  refine ⟨fun g₀ x y z => ?_, fun δ a ha hch => ?_⟩
  · rw [← hprod x y z, ht]
    simp only [map_mul, map_inv, hθ, hΦ]
    group
  · have ha0 : (a : k) ≠ 0 := a.ne_zero
    have hgt : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 ha0))).2 ha
    have h1 : (a : k) ≠ 1 := fun h => by rw [h, map_one] at ha; exact lt_irrefl _ ha
    have h2 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun h => by rw [h, map_one] at hgt; exact lt_irrefl _ hgt
    have h3 : (a : k) ≠ ((a⁻¹ : kˣ) : k) := fun h => by
      rw [← h] at hgt; exact lt_asymm ha hgt
    have hμ : Function.Injective (![a, 1, a⁻¹] : Fin 3 → kˣ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso
           have hij' := congrArg Units.val hij
           simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Units.val_one] at hij'
           first
             | exact h1 hij' | exact h1 hij'.symm | exact h2 hij' | exact h2 hij'.symm
             | exact h3 hij' | exact h3 hij'.symm)
    have hroot : ∀ i, (((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot
        (((![a, 1, a⁻¹] : Fin 3 → kˣ) i : kˣ) : k) := by
      intro i
      rw [hch]
      fin_cases i <;> simp [Polynomial.IsRoot]
    obtain ⟨g₀, hN⟩ := exists_conj_diag (δ * th k 3 δ) _ hμ hroot
    set n : GL (Fin 3) k := dg ![a, 1, a⁻¹] with hn
    set e : GL (Fin 3) k := g₀⁻¹ * δ * th k 3 g₀ * (Phi k)⁻¹ with he
    have hen : e * th' k e = n := by
      have : e * th' k e = g₀⁻¹ * (δ * th k 3 δ) * g₀ := by
        rw [ht, he]
        simp only [map_mul, map_inv, hθ, hΦ, inv_inv]
        group
      rw [this, hN]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      try rfl
    have hfix : th' k n = n := by
      rw [hn, hd]
      simp
    have hne : th' k e * e = n := by
      have := congrArg (th' k) hen
      rwa [map_mul, hP.invol, hfix] at this
    have hcomm : e * n = n * e := by
      nth_rewrite 1 [← hne]
      nth_rewrite 1 [← hen]
      group
    obtain ⟨u, hu⟩ := diag_of_comm _ hμ e hcomm
    have hu' : u = ![u 0, u 1, u 2] := by
      funext i; fin_cases i <;> rfl
    refine ⟨g₀, u 0, u 1, u 2, ?_, ?_⟩
    · have : dg ![u 0, u 1, u 2] = e := by rw [hu]; exact congrArg _ hu'.symm
      rw [this, he]
      group
    · have h4 : dg ![u 0 / u 2, 1, u 2 / u 0] = n := by
        rw [← hprod, ← hu' , ← hen, hu]
      have h5 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) (congrArg Units.val h4)
      simp only [hn, dg, val_diagT] at h5
      simpa [Units.ext_iff] using h5

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicatorAlt
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.supp0 : UpperTheory.V.Z.Sym.Sig.Supp0 := by
  intro k _ _ _ _ V d hd g hg
  have hmem : g * (Phi k)⁻¹ ∈ V.DC d := by
    by_contra h
    exact hg (by simp [Lev.unitaryDoubleCosetIndicator, h])
  obtain ⟨hP, -, -, -, -, -, hcomm⟩ := thFacts k V
  obtain ⟨j, -, s, hs, hjs⟩ := contract k V 3 (th' k) hP d hd _ hmem
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨j, t 0 * d 0, t 1 * d 1, t 2 * d 2, ?_, ?_⟩
  · have h1 : dg ![t 0 * d 0, t 1 * d 1, t 2 * d 2] = diagT k (Fin 3) t * dg d := by
      rw [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [h1, ← hjs]
    have h2 : th' k j * Phi k = Phi k * th k 3 j := hcomm j
    symm
    calc j * (j⁻¹ * (g * (Phi k)⁻¹) * th' k j) * Phi k * (th k 3 j)⁻¹
        = g * (Phi k)⁻¹ * (th' k j * Phi k) * (th k 3 j)⁻¹ := by group
      _ = g := by rw [h2]; group
  · have h3 : t 0 * d 0 / (t 2 * d 2) / (d 0 / d 2) = t 0 / t 2 := by
      rw [mul_div_mul_comm, mul_div_cancel_right]
    rw [h3]
    exact div_mem (ht 0 trivial) (ht 2 trivial)

end
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_of_roots {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (a : kˣ) (τ : k)
    (h : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) = ((X - 1) * (X ^ 2 - C τ * X + 1) : k[X])) :
    τ = (a : k) + ((a⁻¹ : kˣ) : k) := by
  have hu : C (a : k) * C ((a⁻¹ : kˣ) : k) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have e1 : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) =
      (X - 1) * (X ^ 2 - C ((a : k) + ((a⁻¹ : kˣ) : k)) * X + 1) := by
    rw [C_add, C_1]
    linear_combination (X - 1) * hu
  rw [e1] at h
  have hne : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
  have h' := mul_left_cancel₀ hne h
  have hc := congrArg (fun q : k[X] => q.coeff 1) h'
  simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_one] at hc
  norm_num at hc
  rw [Units.val_inv_eq_inv_val]
  linear_combination hc

private theorem charpoly_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c : kˣ) :
    (((dg ![a, b, c] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).charpoly = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)) := by
  rw [dg.eq_1, val_diagT, charpoly_diagonal]
  simp [Fin.prod_univ_three]

theorem UpperTheory.V.Z.Sym.Sig.okG :
    UpperTheory.V.Z.Sym.Sig.OkG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  simp only [Lev.data.eq_1, Set.mem_setOf_eq] at ht ⊢
  obtain ⟨hbij, htheta, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  have hinv : ∀ (d : Fin 3 → kˣ) (u : GL (Fin 3) k), u ∈ V.J 3 →
      ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g :=
    fun d u hu u' hu' g => ((eqG k V 1 ∅ ∅ 1 1 d).1 u hu u' hu' g).1
  have hfin : ∀ d : Fin 3 → kˣ,
      {y : GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) | V.unitaryDoubleCosetIndicator d (Quotient.out y) ≠ 0}.Finite :=
    fun d => (eqG k V 1 ∅ ∅ 1 1 d).2.1
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    rw [Subgroup.mem_comap] at hu
    constructor
    · simp only [map_mul, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa [map_one] using hinv _ (eU hs u) hu 1 (Subgroup.one_mem _) (eU hs y)
    · simp only [map_mul, htheta, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa using hinv _ 1 (Subgroup.one_mem _) (eU hs u) hu (eU hs y)
  · let ψ : U3 Δ ⧸ Subgroup.comap (eU hs) (V.J 3) → GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) :=
      fun x => QuotientGroup.mk (th k 3 (eU hs (Quotient.out x)))
    have hψ : Function.Injective ψ := by
      intro x x' hxx
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      rw [QuotientGroup.eq] at hxx ⊢
      rw [Subgroup.mem_comap]
      obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hxx
      have hth : Function.Injective (th k 3) := fun a b hab => by
        have := congrArg (th k 3) hab
        rwa [(thFacts k V).2.2.2.1, (thFacts k V).2.2.2.1] at this
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at hjeq
      rw [← hth hjeq]
      exact hj
    let T : Set (GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3)) :=
      ⋃ y ∈ Ry, {z | V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] (Quotient.out z) ≠ 0}
    have hT : T.Finite := Set.Finite.biUnion Ry.finite_toSet fun y _ => hfin _
    refine (hT.preimage hψ.injOn).subset fun x hx => ?_
    have hx' : V.unitaryHeckeTestSum Ry t (eU hs (theta Δ (Quotient.out x))) ≠ 0 := hx
    rw [htheta, Lev.unitaryHeckeTestSum.eq_1] at hx'
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    simp only [Set.mem_preimage, T, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨y, hy, ?_⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.map (th k 3) (V.J 3))
      (th k 3 (eU hs (Quotient.out x)))
    obtain ⟨j, hj, hjm⟩ := Subgroup.mem_map.1 m.2
    change V.unitaryDoubleCosetIndicator _ (Quotient.out (QuotientGroup.mk (th k 3 (eU hs (Quotient.out x))) :
      GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3))) ≠ 0
    rw [hm, ← hjm]
    have e := hinv ![t * (unif k)⁻¹, y, (unif k)⁻¹] 1 (Subgroup.one_mem _) j hj
      (th k 3 (eU hs (Quotient.out x)))
    rw [one_mul] at e
    rw [e]
    exact hne
  · intro δ τ hτ hne
    rw [Lev.unitaryHeckeTestSum.eq_1] at hne
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hv : (valuation k) ((unif k : kˣ) : k) < 1 := by
      rw [GlAx.unif_spec]
      exact uniformizer_lt_one
    have hv0 : 0 < (valuation k) ((unif k : kˣ) : k) := by
      rw [zero_lt_iff]
      exact (_root_.map_ne_zero _).2 (unif k).ne_zero
    obtain ⟨hy1, hy2⟩ := hRy.1 y hy
    have h01 : (valuation k) ((t * (unif k)⁻¹ : kˣ) : k) < (valuation k) (y : k) := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← div_eq_mul_inv,
        div_lt_iff₀ hv0]
      calc (valuation k) (t : k) < (valuation k) ((unif k : kˣ) : k) ^ 2 := ht
        _ = (valuation k) ((unif k : kˣ) : k) * (valuation k) ((unif k : kˣ) : k) := sq _
        _ ≤ (valuation k) (y : k) * (valuation k) ((unif k : kˣ) : k) := by gcongr
    have h12 : (valuation k) (y : k) < (valuation k) (((unif k)⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact hy2.trans_lt ((one_lt_inv₀ hv0).2 hv)
    have hSD : SDom ![t * (unif k)⁻¹, y, (unif k)⁻¹] := by
      rw [SDom.eq_1]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | exact h01
        | exact h12
        | exact h01.trans h12
    obtain ⟨g₀, x, y', z, hδ, hH⟩ := supp0 k V _ hSD _ hne
    have hd : (![t * (unif k)⁻¹, y, (unif k)⁻¹] 0 / ![t * (unif k)⁻¹, y, (unif k)⁻¹] 2 : kˣ) = t := by
      simp
    rw [hd] at hH
    have hcp := (htau δ τ).1 hτ
    rw [hδ, (normalG k).1 g₀ x y' z] at hcp
    have hc2 : ((g₀ * dg ![x / z, 1, z / x] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly
        = (X - C ((x / z : kˣ) : k)) * (X - C 1) * (X - C (((x / z)⁻¹ : kˣ) : k)) := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, charpoly_units_conj, charpoly_dg,
        inv_div, Units.val_one]
    rw [hc2] at hcp
    have hτ' := tau_of_roots h2 (x / z) τ hcp
    rw [Ind.eq_1]
    refine ⟨x / z / t, hH, ?_⟩
    have hm : t * (x / z / t) = x / z := by
      rw [mul_comm]
      exact div_mul_cancel (x / z) t
    rw [hm]
    exact hτ'

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkGOrb
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ModelG
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical Loc Glob

section Alg

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_ofE' (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [sigL, ofE]

private def Am (y : Sp Δ τ) : Sp Δ τ := (y.1, ofE Δ (QuadraticAlgebra.omega : Etau K τ) * y.2)

private theorem semi_semi {d : EL Δ τ} (h : d * sigL d = ofE Δ (QuadraticAlgebra.omega : Etau K τ)) (y : Sp Δ τ) :
    semi d (semi d y) = Am y := by
  simp only [semi, Am, star_star, sigL_mul', sigL_sigL', ← mul_assoc, h]

private theorem semi_tor (d : EL Δ τ) (z : (Etau K τ)ˣ) (y : Sp Δ τ) :
    semi d (tor Δ z y) = tor Δ z (semi d y) := by
  simp only [semi, tor, sigL_mul', sigL_ofE']
  exact Prod.ext rfl (mul_left_comm _ _ _)

private theorem star_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (v : Fin 3 → Lsq K Δ) :
    star (M *ᵥ v) = M.map star *ᵥ star v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, star_mul']

private theorem mat_ext {V : Type} [AddCommGroup V] [Module (Lsq K Δ) V] (Q : V ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    {M M' : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : ∀ y, M *ᵥ Q y = M' *ᵥ Q y) : M = M' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h (Q.symm v))

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem N_act (hd : IsDat c d m) (h : Models c d m δ ι Q) (y : Sp Δ τ) :
    ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ Q y = Q (Am y) := by
  rw [← semi_semi hd.d_norm, h.semi, h.semi, star_mulVec', star_star, Matrix.mulVec_mulVec]
  rfl

private theorem comm_U (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) : δ * theta Δ (ι t) = ι t * δ := by
  apply Subtype.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  obtain ⟨y, rfl⟩ : ∃ y, star (Q y) = v := ⟨Q.symm (star v), by simp⟩
  simp only [Matrix.toLin'_apply]
  have e1 : ((δ * theta Δ (ι t) : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (Q y) = Q (semi d (tor Δ t y)) := by
    rw [h.semi, h.tor, star_mulVec', Matrix.mulVec_mulVec]
    rfl
  have e2 : ((ι t * δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) *ᵥ star (Q y) = Q (tor Δ t (semi d y)) := by
    rw [h.tor, h.semi, Matrix.mulVec_mulVec]
    rfl
  rw [e1, e2, semi_tor]

private def crd : (Fin 3 → Lsq K Δ) ≃ₗ[Lsq K Δ] Sp Δ τ where
  toFun v := (v 0, ⟨v 1, v 2⟩)
  invFun y := ![y.1, y.2.re, y.2.im]
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv y := by ext <;> simp

private def A0 (Δ τ : K) : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
  !![1, 0, 0; 0, 0, -1; 0, 1, algebraMap K _ τ]

private theorem Am_crd (v : Fin 3 → Lsq K Δ) : Am (crd (τ := τ) v) = crd (A0 Δ τ *ᵥ v) := by
  ext <;> simp [Am, crd, A0, ofE, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem companion_charpoly_factor : (A0 Δ τ).charpoly = (X - 1) * (X ^ 2 - C (algebraMap K _ τ) * X + 1) := by
  simp [Matrix.charpoly, A0, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.diagonal]
  ring

private theorem hasTau_of (hd : IsDat c d m) (h : Models c d m δ ι Q) : HasTau δ τ := by
  set R : (Fin 3 → Lsq K Δ) ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ) := (crd (τ := τ)).trans Q with hR
  let B := LinearMap.toMatrix' (R : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
  let B' := LinearMap.toMatrix' (R.symm : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
  have hB : ∀ v, B *ᵥ v = R v := fun v => by simp [B, LinearMap.toMatrix'_mulVec]
  have hB' : ∀ v, B' *ᵥ v = R.symm v := fun v => by simp [B', LinearMap.toMatrix'_mulVec]
  have h1 : B * B' = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    simp [← Matrix.mulVec_mulVec, hB, hB'])
  have h2 : B' * B = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    simp [← Matrix.mulVec_mulVec, hB, hB'])
  have h3 : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * B = B * A0 Δ τ :=
    Matrix.toLin'.injective (LinearMap.ext fun v => by
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB]
      simp only [hR, LinearEquiv.trans_apply]
      rw [N_act hd h, Am_crd])
  let u : (Matrix (Fin 3) (Fin 3) (Lsq K Δ))ˣ := ⟨B, B', h1, h2⟩
  have h4 : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = u.val * A0 Δ τ * u⁻¹.val := by
    change _ = B * A0 Δ τ * B'
    rw [← h3, mul_assoc, h1, mul_one]
  unfold HasTau
  rw [h4, Matrix.coe_units_inv, Matrix.charpoly_units_conj, companion_charpoly_factor]

end Alg

section Mid

variable {K : Type} [Field K] {Δ τ : K}

private theorem tor_of_fst (z : (Etau K τ)ˣ) (w : Sp Δ τ) (hw : w.1 = 0) :
    tor Δ z w = algebraMap K (Lsq K Δ) (quo z).re • w + algebraMap K (Lsq K Δ) (quo z).im • Am w := by
  obtain ⟨w₀, w₁⟩ := w
  obtain rfl : w₀ = 0 := hw
  ext <;> simp [tor, Am, ofE] <;> ring

private theorem tor_of_snd (z : (Etau K τ)ˣ) (w : Sp Δ τ) (hw : w.2 = 0) : tor Δ z w = w := by
  obtain ⟨w₀, w₁⟩ := w
  obtain rfl : w₁ = 0 := hw
  simp [tor]

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem id1 (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (ι t : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) =
      (algebraMap K (Lsq K Δ) (quo t).re • (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) +
        algebraMap K (Lsq K Δ) (quo t).im • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ))) *
      (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) := by
  apply mat_ext Q
  intro y
  have e : (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) - 1) *ᵥ Q y = Q (Am y - y) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, N_act hd h, map_sub]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, ← h.tor, tor_of_fst t _ (by simp [Am]),
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, N_act hd h, map_add, map_smul, map_smul]

private theorem id2 (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (ι t : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1) =
      ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1 := by
  apply mat_ext Q
  intro y
  have e : (((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) * ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) -
        algebraMap K (Lsq K Δ) τ • ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) + 1) *ᵥ Q y =
      Q (Am (Am y) - algebraMap K (Lsq K Δ) τ • Am y + y) := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      N_act hd h, N_act hd h, map_add, map_sub, map_smul]
  rw [← Matrix.mulVec_mulVec, e, ← h.tor, tor_of_snd]
  ext <;> simp [Am, ofE] <;> ring

end Mid

section Lin

variable {K : Type} [Field K]

private theorem col_of {T : Matrix (Fin 3) (Fin 3) K} {u v : Fin 3 → K}
    (h : T * diagonal u = diagonal v * diagonal u) (j : Fin 3) (hj : u j ≠ 0) (i : Fin 3) :
    T i j = diagonal v i j := by
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal] at this
  exact mul_right_cancel₀ hj this

private theorem diag_of {T : Matrix (Fin 3) (Fin 3) K} {a b re im τ : K} (ha : a ≠ 1) (hb : b ≠ 1) (ht : 2 - τ ≠ 0)
    (hA : a * a - τ * a + 1 = 0) (hB : b * b - τ * b + 1 = 0)
    (h1 : T * (diagonal ![a, 1, b] - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • diagonal ![a, 1, b]) * (diagonal ![a, 1, b] - 1))
    (h2 : T * (diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1) =
      diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1) :
    T = diagonal ![re + im * a, 1, re + im * b] := by
  have e1 : (diagonal ![a, 1, b] - 1 : Matrix (Fin 3) (Fin 3) K) = diagonal ![a - 1, 0, b - 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have e2 : (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • diagonal ![a, 1, b]) = diagonal ![re + im * a, re + im, re + im * b] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have e3 : (diagonal ![a, 1, b] * diagonal ![a, 1, b] - τ • diagonal ![a, 1, b] + 1 : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![0, 2 - τ, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, hA, hB]
    ring
  rw [e1, e2] at h1
  rw [e3] at h2
  have h2' : T * diagonal ![0, 2 - τ, 0] = diagonal 1 * diagonal ![0, 2 - τ, 0] := by
    rw [h2, show (diagonal 1 : Matrix (Fin 3) (Fin 3) K) = 1 from Matrix.diagonal_one, one_mul]
  have c0 := col_of h1 0 (by simpa using sub_ne_zero.2 ha)
  have c2 := col_of h1 2 (by simpa using sub_ne_zero.2 hb)
  have c1 := col_of h2' 1 (by simpa using ht)
  ext i j
  fin_cases j
  · rw [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl] ; rw [c0]; fin_cases i <;> simp
  · rw [show (⟨1, by omega⟩ : Fin 3) = 1 from rfl] ; rw [c1]; fin_cases i <;> simp
  · rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl] ; rw [c2]; fin_cases i <;> simp

private theorem conj_ids {G Gi T D₀ Dm : Matrix (Fin 3) (Fin 3) K} {re im τ : K} (hG : Gi * G = 1) (hD : Dm * G = G * D₀)
    (h1 : T * (Dm - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * (Dm - 1))
    (h2 : T * (Dm * Dm - τ • Dm + 1) = Dm * Dm - τ • Dm + 1) :
    (Gi * T * G) * (D₀ - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • D₀) * (D₀ - 1) ∧
    (Gi * T * G) * (D₀ * D₀ - τ • D₀ + 1) = D₀ * D₀ - τ • D₀ + 1 := by
  have hA : (Dm - 1) * G = G * (D₀ - 1) := by rw [sub_mul, mul_sub, one_mul, mul_one, hD]
  have hB : (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * G = G * (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • D₀) := by
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hD, one_mul, mul_one]
  have hDD : Dm * Dm * G = G * (D₀ * D₀) := by rw [mul_assoc, hD, ← mul_assoc, hD, mul_assoc]
  have hC : (Dm * Dm - τ • Dm + 1) * G = G * (D₀ * D₀ - τ • D₀ + 1) := by
    rw [add_mul, sub_mul, mul_add, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hD, hDD, one_mul, mul_one]
  have cancel : ∀ X : Matrix (Fin 3) (Fin 3) K, Gi * (G * X) = X := fun X => by rw [← mul_assoc, hG, one_mul]
  constructor
  · calc Gi * T * G * (D₀ - 1) = Gi * (T * (Dm - 1)) * G := by
          simp only [mul_assoc]; rw [← hA]
      _ = Gi * (((re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm) * G) * (D₀ - 1)) + 0 := by
          rw [h1, mul_assoc (re • (1 : Matrix (Fin 3) (Fin 3) K) + im • Dm), add_zero, mul_assoc Gi, mul_assoc _ (Dm - 1), hA]
      _ = _ := by rw [hB, add_zero, mul_assoc G, cancel]
  · calc Gi * T * G * (D₀ * D₀ - τ • D₀ + 1) = Gi * (T * (Dm * Dm - τ • Dm + 1)) * G := by
          simp only [mul_assoc]; rw [← hC]
      _ = _ := by rw [h2, mul_assoc Gi, hC, cancel]

end Lin

section Proj

variable {K : Type} [Field K] {Δ s τ : K}

private theorem pm_smul (hs : s * s = Δ) (x : K) (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) :
    (proj hs).mapMatrix (algebraMap K (Lsq K Δ) x • M) = x • (proj hs).mapMatrix M := by
  ext i j
  simp [proj]
  ring

private theorem pm_coe (hs : s * s = Δ) (g : U3 Δ) :
    (proj hs).mapMatrix (g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = (eU hs g : Matrix (Fin 3) (Fin 3) K) := rfl

variable {c : K} {d m : EL Δ τ} {δ : U3 Δ} {ι : (Etau K τ)ˣ →* U3 Δ} {Q : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)}

private theorem id1K (hs : s * s = Δ) (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (eU hs (ι t) : Matrix (Fin 3) (Fin 3) K) * ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) - 1) =
      ((quo t).re • (1 : Matrix (Fin 3) (Fin 3) K) + (quo t).im • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K)) *
      ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) - 1) := by
  have h1 := congrArg (proj hs).mapMatrix (id1 hd h t)
  rw [map_mul, map_mul, map_sub, map_add (f := _), pm_smul, pm_smul, map_one, pm_coe, pm_coe] at h1
  exact h1

private theorem id2K (hs : s * s = Δ) (hd : IsDat c d m) (h : Models c d m δ ι Q) (t : (Etau K τ)ˣ) :
    (eU hs (ι t) : Matrix (Fin 3) (Fin 3) K) * ((eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) * (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) -
        τ • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) + 1) =
      (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) * (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) -
        τ • (eU hs (δ * theta Δ δ) : Matrix (Fin 3) (Fin 3) K) + 1 := by
  have h1 := congrArg (proj hs).mapMatrix (id2 hd h t)
  rw [map_mul, map_add (f := _), map_sub, map_mul, pm_smul, map_one, pm_coe, pm_coe] at h1
  exact h1

end Proj

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dg_val (x y z : kˣ) :
    ((dg ![x, y, z] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = diagonal ![(x : k), (y : k), (z : k)] := by
  rw [val_diagT]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem conj_form {g₀ : GL (Fin 3) k} {T Dm : Matrix (Fin 3) (Fin 3) k} {a b r r' : kˣ} {re im τ : k}
    (hD : Dm * (g₀ : Matrix (Fin 3) (Fin 3) k) = (g₀ : Matrix (Fin 3) (Fin 3) k) * diagonal ![(a : k), 1, (b : k)])
    (ha : (a : k) ≠ 1) (hb : (b : k) ≠ 1) (ht : 2 - τ ≠ 0)
    (hA : (a : k) * a - τ * a + 1 = 0) (hB : (b : k) * b - τ * b + 1 = 0)
    (h1 : T * (Dm - 1) = (re • (1 : Matrix (Fin 3) (Fin 3) k) + im • Dm) * (Dm - 1))
    (h2 : T * (Dm * Dm - τ • Dm + 1) = Dm * Dm - τ • Dm + 1)
    (hr : re + im * a = r) (hr' : re + im * b = r') :
    T = ((g₀ * dg ![r, 1, r'] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have hGi : ((g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g₀ : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul]; simp
  have hGG : (g₀ : Matrix (Fin 3) (Fin 3) k) * ((g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul]; simp
  obtain ⟨c1, c2⟩ := conj_ids hGi hD h1 h2
  have hT := diag_of ha hb ht hA hB c1 c2
  rw [hr, hr'] at hT
  rw [Units.val_mul, Units.val_mul, dg_val, Units.val_one, ← hT]
  simp only [mul_assoc]
  rw [hGG, mul_one, ← mul_assoc, hGG, one_mul]

end Loc

theorem modelG : ModelG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0
  obtain ⟨-, hth, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  refine ⟨fun τ c d m δ ι Q hd hm => ⟨hasTau_of hd hm, fun t => ?_⟩, ?_⟩
  · rw [mul_assoc, comm_U hm t, ← mul_assoc, inv_mul_cancel, one_mul]
  intro a ha c d m δ ι Q hd hm
  have hab : (a : k) * ((a⁻¹ : kˣ) : k) = 1 := by simp
  have hcp := (htau δ _).1 (hasTau_of hd hm)
  have hcp' : ((eU hs δ * th k 3 (eU hs δ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly =
      (X - C 1) * (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) := by
    have e : (C (a : k) : k[X]) * C ((a⁻¹ : kˣ) : k) = 1 := by rw [← C_mul, hab, C_1]
    rw [hcp]
    simp only [C_add, C_1]
    linear_combination (-(X - 1 : k[X])) * e
  obtain ⟨g₀, x, y, z, hδ, hxz⟩ := (normalG k).2 _ a ha hcp'
  have hN := (normalG k).1 g₀ x y z
  rw [← hδ, hxz, show z / x = a⁻¹ by rw [← hxz, inv_div]] at hN
  refine ⟨g₀, x, y, z, hδ, hxz, fun t => ?_⟩
  have hDm : eU hs (δ * theta Δ δ) = g₀ * dg ![a, 1, a⁻¹] * g₀⁻¹ := by rw [map_mul, hth, hN]
  have hDG : ((eU hs (δ * theta Δ δ) : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (g₀ : Matrix (Fin 3) (Fin 3) k) =
      (g₀ : Matrix (Fin 3) (Fin 3) k) * diagonal ![(a : k), 1, ((a⁻¹ : kˣ) : k)] := by
    have e : eU hs (δ * theta Δ δ) * g₀ = g₀ * dg ![a, 1, a⁻¹] := by rw [hDm, inv_mul_cancel_right]
    have e' := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) e
    simp only [Units.val_mul] at e'
    rw [e', dg_val, Units.val_one]
  have ha1 : (a : k) ≠ 1 := fun e => by simp [e] at ha
  have hb1 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun e => ha1 (by rw [e, mul_one] at hab; exact hab)
  have ht : 2 - ((a : k) + (a⁻¹ : kˣ)) ≠ 0 := fun e => hd.reg (by
    have e' : (a : k) + (a⁻¹ : kˣ) = 2 := by linear_combination -e
    rw [e']; norm_num)
  obtain ⟨-, -, hr⟩ := roots k O hO a ha
  obtain ⟨r1, r2⟩ := hr t
  have r1' : (quo t).re + (quo t).im * (a : k) = (((evU (root_left a) / evU (root_right a)) t : kˣ) : k) := by
    rw [MonoidHom.div_apply, ← r1, mul_comm (quo t).im]; rfl
  have r2' : (quo t).re + (quo t).im * ((a⁻¹ : kˣ) : k) = ((((evU (root_left a) / evU (root_right a)) t)⁻¹ : kˣ) : k) := by
    rw [MonoidHom.div_apply, inv_div, ← r2, mul_comm (quo t).im]; rfl
  apply Units.ext
  exact conj_form hDG ha1 hb1 ht (by linear_combination -hab) (by linear_combination -hab)
    (id1K hs hd hm t) (id2K hs hd hm t) r1' r2'

end UpperTheory.V.Z.Sym.Sig
end
end

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open _root_.UpperTheory.V.Z.Sym.Loc Glob

private theorem theta_theta {K : Type} [Field K] {Δ : K} (g : U3 Δ) : theta Δ (theta Δ g) = g := by
  apply Subtype.ext
  change ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).map star).map star = _
  exact Matrix.ext fun i j => by simp

private theorem hasTau_conj {K : Type} [Field K] {Δ τ : K} {δ : U3 Δ} (h : HasTau δ τ) (y : U3 Δ) :
    HasTau (y⁻¹ * δ * theta Δ y) τ := by
  unfold HasTau at h ⊢
  have e : y⁻¹ * δ * theta Δ y * theta Δ (y⁻¹ * δ * theta Δ y) = y⁻¹ * (δ * theta Δ δ) * y := by
    simp only [map_mul, map_inv, theta_theta]
    group
  rw [e, ← h, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc,
    ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, mul_one]

private theorem val_unif_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) < 1 := by
  rw [GlAx.unif_spec]
  exact uniformizer_lt_one

private theorem uc_relIndex (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) :
    (Uc k m).relIndex (Uo k) ≠ 0 := by
  have h1 := (finFacts k (Lev.deep k m)).1
  have hle : Uc k (m + 1) ≤ Uc k m := by
    intro u hu
    rw [mem_Uc] at hu ⊢
    exact ⟨hu.1, hu.2.trans (GlAx.zpow_le (by push_cast; omega))⟩
  intro h
  apply h1
  have := Subgroup.relIndex_dvd_of_le_left (Uo k) hle
  rw [h, zero_dvd_iff] at this
  exact this

end UpperTheory.V.Z.Sym.Sig

private theorem relIndex_comap_stabilizer_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : UpperTheory.V.Z.Sym.Sig.Lev k) {T : Type} [CommGroup T]
    (r : T →* kˣ) (hr : Function.Surjective r) (ι' : T →* GL (Fin 3) k) (g₀ w : GL (Fin 3) k)
    (hι : ∀ s, ι' s = g₀ * UpperTheory.V.Z.Sym.Sig.dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) :
    (Subgroup.comap ι' (MulAction.stabilizer (GL (Fin 3) k)
      ((w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3))).relIndex (Subgroup.comap r (Uo k)) ≠ 0 := by
  obtain ⟨M, hM⟩ := UpperTheory.V.Z.Sym.Sig.stabFin k V 3 (g₀⁻¹ * w)
  have hle : Subgroup.comap r (Uc k M)
      ≤ Subgroup.comap ι' (MulAction.stabilizer (GL (Fin 3) k) ((w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)) := by
    intro s hs
    rw [Subgroup.mem_comap] at hs ⊢
    rw [MulAction.mem_stabilizer_iff]
    change ((ι' s * w : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = w
    rw [QuotientGroup.eq]
    have hu : ∀ i, (![r s, 1, (r s)⁻¹] : Fin 3 → kˣ) i ∈ Uc k M := by
      intro i
      fin_cases i
      · exact hs
      · exact one_mem _
      · exact inv_mem hs
    have := inv_mem (hM _ hu)
    rw [hι]
    convert this using 1
    group
  have hidx : (Subgroup.comap r (Uc k M)).relIndex (Subgroup.comap r (Uo k)) ≠ 0 := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hr]
    exact UpperTheory.V.Z.Sym.Sig.uc_relIndex k M
  intro h0
  apply hidx
  have := Subgroup.relIndex_dvd_of_le_left (Subgroup.comap r (Uo k)) hle
  rw [h0, zero_dvd_iff] at this
  exact this

open ValuativeRel UpperTheory.V.Hi UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Sig.okGOrb :
    UpperTheory.V.Z.Sym.Sig.OkGOrb := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht S τ c d m δ ι Q hD hM
  obtain ⟨hτ, hfix⟩ := (Sig.modelG k O hO h2 Δ s hs hs0).1 τ c d m δ ι Q hD hM
  obtain ⟨-, -, hind⟩ := Sig.okG k O hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  by_cases hI : Ind (V.data hs Ry χ).H τ t
  swap
  · have hz : ∀ y : U3 Δ, (V.data hs Ry χ).fG t (y⁻¹ * δ * theta Δ y) = 0 := fun y => by
      by_contra hne
      exact hI (hind _ τ (Sig.hasTau_conj hτ y) hne)
    refine ⟨⟨∅, fun y hy => absurd (hz y) hy⟩, ?_, fun h => absurd h hI⟩
    simp [S, orb, wcount, hz, Glob.one, hI]
  have hI' := hI
  obtain ⟨h, hH, rfl⟩ := hI
  have hva : valuation k ((t * h : kˣ) : k) < 1 := by
    have ht' : valuation k (t : k) < valuation k (unif k : k) ^ 2 := ht
    have hh : valuation k (h : k) = 1 := V.H_le hH
    rw [Units.val_mul, Valuation.map_mul, hh, mul_one]
    exact ht'.trans (pow_lt_one₀ zero_le (Sig.val_unif_lt k) (by norm_num))
  obtain ⟨g₀, x, y, z, hδ, hxz, hι⟩ := (Sig.modelG k O hO h2 Δ s hs hs0).2 (t * h) hva c d m δ ι Q hD hM
  obtain ⟨hsurj, hC, -⟩ := Sig.roots k O hO (t * h) hva
  obtain ⟨hbij, hcomm, -, -⟩ := Sig.eU_facts k O hO h2 Δ s hs hs0
  have hfinv : ∀ u ∈ V.J 3, ∀ g : GL (Fin 3) k,
      V.unitaryHeckeTestSum Ry t (u⁻¹ * g * Sig.th k 3 u) = V.unitaryHeckeTestSum Ry t g := by
    intro u hu g
    unfold Sig.Lev.unitaryHeckeTestSum
    refine Finset.sum_congr rfl fun e _ => ?_
    exact ((Sig.eqG k V χ Ry Ry t t _).1 u⁻¹ (inv_mem hu) u hu g).1
  have hnorm : (Cint O (((t * h : kˣ) : k) + ((t * h : kˣ)⁻¹ : kˣ))).Normal := Subgroup.normal_of_isMulCommutative _
  have hOM := Sig.orbMap _ _ _ (Sig.eU hs) hbij ι (Cint O _) (theta Δ) (Sig.th k 3) hcomm (V.J 3)
    (V.unitaryHeckeTestSum Ry t) δ hfinv hfix hnorm
  have hxz1 : valuation k ((x / z : kˣ) : k) < 1 := by
    rw [hxz]
    exact hva
  have hG := Sig.orbital_integral_over_extended_group k V Ry hRy t ht _ _ hsurj g₀ ((Sig.eU hs).comp ι) (fun s => hι s) x y z hxz1
  rw [← hδ, ← hC] at hG
  refine ⟨hOM.2.1.mpr hG.1, hOM.1.trans (hG.2.trans ?_), fun _ yq => ?_⟩
  · have hm : x / z / t ∈ V.H := by
      rw [hxz, mul_div_cancel_left]
      exact hH
    rw [show Glob.one (x / z / t ∈ V.H) = 1 from if_pos hm,
      show Glob.one (Ind S.H (((t * h : kˣ) : k) + ((t * h : kˣ)⁻¹ : kˣ)) t) = 1 from if_pos hI']
    show _ = (((V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ) : ℝ) : ℂ) * 1
    push_cast
    rfl
  · obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective yq
    have key := relIndex_comap_stabilizer_ne_zero V _ hsurj ((Sig.eU hs).comp ι) g₀ (Sig.eU hs w) (fun s => hι s)
    rw [← hOM.2.2 w, ← hC] at key
    exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NotIntegral
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem index_comap {G G' : Type} [Group G] [Group G'] (e : G →* G') (he : Function.Surjective e)
    {A B : Subgroup G'} (h : A.relIndex B ≠ 0) : (A.comap e).relIndex (B.comap e) ≠ 0 := Subgroup.relIndex_comap_ne_zero e h

private theorem J_index {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (V : Lev k) (n : ℕ) : (V.J n).relIndex (KO k (Fin n)) ≠ 0 :=
  fun h0 => GlAx.Kc_index (k := k) (n := n) (V.c + 1) le_rfl (Subgroup.relIndex_eq_zero_of_le_left (kc_le V) h0)

private theorem not_integral {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) {a : kˣ} (ha : valuation k (a : k) < 1) :
    ¬ IsIntegral O ((a : k) + (a⁻¹ : kˣ)) := by
  intro hint
  have hv : Valuation.Integers (valuation k) O :=
    { hom_inj := hO.inj
      map_le_one := fun x => (hO.range _).1 ⟨x, rfl⟩
      exists_of_le_one := fun r hr => (hO.range r).2 hr }
  have h1 : valuation k ((a : k) + ((a⁻¹ : kˣ) : k)) ≤ 1 := hv.isIntegral_iff_v_le_one.mp hint
  have hprod : valuation k ((a⁻¹ : kˣ) : k) * valuation k (a : k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hsub : ((a⁻¹ : kˣ) : k) = ((a : k) + ((a⁻¹ : kˣ) : k)) - a := by ring
  have h2 : valuation k ((a⁻¹ : kˣ) : k) ≤ 1 := by
    rw [hsub]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 ha.le)
  exact (mul_lt_of_le_one_of_lt h2 ha).ne hprod

theorem UpperTheory.V.Z.Sym.Sig.okLev :
    UpperTheory.V.Z.Sym.Sig.OkLev := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry _ χ _
  obtain ⟨hU, -, hKU, -⟩ := eU_facts k O hO h2 Δ s hs hs0
  obtain ⟨hD, hKD, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨f1, f2, f3, -, -, f6⟩ := finFacts k V
  have hpos : V.H.relIndex V.H2 ≠ 0 := fun h0 => f1 (by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ f3 f2, h0, zero_mul])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hKU]; exact Subgroup.comap_mono (f6 3).2.2.2
  · rw [← hKU]; exact index_comap _ hU.2 (J_index V 3)
  · rw [← hKD]; exact Subgroup.comap_mono (f6 2).2.2.2
  · rw [← hKD]; exact index_comap _ hD.2 (J_index V 2)
  · change 0 < (V.H.relIndex (Uo k) : ℝ) * (V.H.relIndex V.H2 : ℝ)
    have a1 : 0 < V.H.relIndex (Uo k) := Nat.pos_of_ne_zero f1
    have a2 : 0 < V.H.relIndex V.H2 := Nat.pos_of_ne_zero hpos
    positivity
  · change 0 < (V.H.relIndex (Uo k) : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero f1
  · rintro t ht τ ⟨h, hh, rfl⟩
    have ht' : valuation k (t : k) < valuation k (unif k : k) ^ 2 := ht
    have hu : valuation k (unif k : k) < 1 := by rw [GlAx.unif_spec]; exact uniformizer_lt_one
    have ha : valuation k ((t * h : kˣ) : k) < 1 := by
      have e : valuation k (h : k) = 1 := V.H_le hh
      rw [Units.val_mul, map_mul, e, mul_one]
      exact ht'.trans (pow_lt_one₀ zero_le' hu two_ne_zero)
    refine ⟨⟨((t * h : kˣ) : k) - ((t * h)⁻¹ : kˣ), ?_⟩, not_integral hO ha⟩
    have e : ((t * h : kˣ) : k) * ((t * h)⁻¹ : kˣ) = 1 := Units.mul_inv _
    linear_combination (4 : k) * e

end
end

open UpperTheory.V.Z.Sym.Sig in
theorem UpperTheory.V.Z.Sym.Sig.sigMain : UpperTheory.V.Z.Sym.Sig.SigMain := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ
  obtain ⟨hJ, hJf, hJ2, hJ2f, hcG, hcS, hreg⟩ := okLev k O hO h2 Δ s hs hs0 V Ry hR χ hχ
  exact ⟨hcG, hcS, hcS, hJ, hJf, hJ2, hJ2f, hreg,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okG k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okGOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okS k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.1,
    fun t ht => (okK k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht).2.2,
    fun t ht => okDOrb k O hO h2 Δ s hs hs0 V Ry hR χ hχ t ht⟩
