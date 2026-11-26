module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryHyperbolicOrbitCount
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FixG
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem sDom_of_valuation_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ) (h1 : valuation k (a : k) < 1) : SDom ![a, 1, a⁻¹] := by
  have hne : valuation k (a : k) ≠ 0 := ((valuation k).ne_zero_iff).mpr a.ne_zero
  have h2 : 1 < (valuation k (a : k))⁻¹ :=
    (one_lt_inv₀ (((valuation k).pos_iff).mpr a.ne_zero)).mpr h1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact h1
  · exact h1.trans h2
  · exact h2

theorem UpperTheory.V.Z.Sym.Sig.fixG : UpperTheory.V.Z.Sym.Sig.FixG := by
  intro k _ _ _ _ V d hd x₁ y₁ z₁ hxz y
  have hF := thFacts k V
  have hth : ∀ g, th k 3 g = (Phi k)⁻¹ * th' k g * Phi k := fun g => by
    rw [mul_assoc, hF.2.2.2.2.2.2 g]
    group
  have hdom : Dom d := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact (hd i j h).le
    · rw [h]
  have hmul : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → g ∈ V.DC d → a * g * b ∈ V.DC d := by
    intro a b g ha hb hg
    obtain ⟨p, hp, q, hq, rfl⟩ := hg
    exact ⟨a * p, (V.J 3).mul_mem ha hp, q * b, (V.J 3).mul_mem hq hb, by group⟩
  have hDC : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → (a * g * b ∈ V.DC d ↔ g ∈ V.DC d) := by
    intro a b g ha hb
    refine ⟨fun h => ?_, hmul ha hb⟩
    have h2 := hmul ((V.J 3).inv_mem ha) ((V.J 3).inv_mem hb) h
    simpa [mul_assoc] using h2
  have hL : y⁻¹ * (dg ![x₁, y₁, z₁] * Phi k) * th k 3 y * (Phi k)⁻¹ = y⁻¹ * dg ![x₁, y₁, z₁] * th' k y := by
    rw [hth]
    group
  rw [hL]
  have key : ∀ (u : Fin 3 → kˣ) (j : GL (Fin 3) k), j ∈ V.J 3 → y = dg u * j →
      (y⁻¹ * dg ![x₁, y₁, z₁] * th' k y ∈ V.DC d ↔
        (x₁ / (u 0 * u 2) / d 0 ∈ V.H ∧ y₁ / u 1 ^ 2 / d 1 ∈ V.H ∧ z₁ / (u 0 * u 2) / d 2 ∈ V.H)) := by
    intro u j hj hy
    have hu3 : dg u = dg ![u 0, u 1, u 2] := by
      congr 1
      funext i
      fin_cases i <;> rfl
    have hc : (dg ![u 0, u 1, u 2])⁻¹ * dg ![x₁, y₁, z₁] * dg ![(u 2)⁻¹, (u 1)⁻¹, (u 0)⁻¹] =
        dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] := by
      simp only [dg, ← map_inv, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, sq, mul_comm, mul_left_comm, mul_assoc]
    have e1 : y⁻¹ * dg ![x₁, y₁, z₁] * th' k y =
        j⁻¹ * dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] * th' k j := by
      rw [hy, map_mul, hu3, hF.2.2.1, ← hc]
      group
    rw [e1, hDC ((V.J 3).inv_mem hj) (hF.2.1 j hj), diagDC k V 3 d _ hdom]
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
  constructor
  · intro hg
    obtain ⟨j, hj, s, hs, hjs⟩ := contract k V 3 (th' k) hF.1 d hd _ hg
    obtain ⟨h, hh, rfl⟩ := hs
    have hhH : ∀ i, h i ∈ V.H := fun i => hh i (Set.mem_univ i)
    set g := y⁻¹ * dg ![x₁, y₁, z₁] * th' k y with hg_def
    have hD : dg ![x₁, y₁, z₁] * dg ![z₁⁻¹, y₁⁻¹, x₁⁻¹] = dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] := by
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
    have A : g * th' k g = y⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * y := by
      have : g * th' k g = y⁻¹ * (dg ![x₁, y₁, z₁] * th' k (dg ![x₁, y₁, z₁])) * y := by
        rw [hg_def, map_mul, map_mul, map_inv, Pres.invol hF.1]
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [this, hF.2.2.1, hD]
    set p := h 0 * d 0 / (h 2 * d 2) with hp
    have C : diagT k (Fin 3) h * dg d * th' k (diagT k (Fin 3) h * dg d) = dg ![p, 1, p⁻¹] := by
      have e : diagT k (Fin 3) h * dg d = dg ![h 0 * d 0, h 1 * d 1, h 2 * d 2] := by
        simp only [dg, ← map_mul]
        congr 1
        funext i
        fin_cases i <;> rfl
      rw [e, hF.2.2.1]
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [hp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have B : (j⁻¹ * g * th' k j) * th' k (j⁻¹ * g * th' k j) = j⁻¹ * (g * th' k g) * j := by
      simp only [map_mul, map_inv, Pres.invol hF.1]
      group
    rw [hjs, C, A] at B
    have hconj : (y * j)⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * (y * j) = dg ![p, 1, p⁻¹] := by
      rw [B]
      group
    have hp1 : valuation k (p : k) < 1 := by
      have e2 : p = h 0 / h 2 * (d 0 / d 2) := by
        rw [hp, div_mul_div_comm]
      have hv1 : valuation k ((h 0 / h 2 : kˣ) : k) = 1 := V.H_le (V.H.div_mem (hhH 0) (hhH 2))
      rw [e2, Units.val_mul, map_mul, hv1, one_mul, Units.val_div_eq_div_val, map_div₀]
      exact (div_lt_one₀ (((valuation k).pos_iff).mpr (d 2).ne_zero)).mpr (hd 0 2 (by decide))
    obtain ⟨-, u, hu⟩ := conjDiag k 3 _ _ (sDom_of_valuation_lt_one _ hxz) (sDom_of_valuation_lt_one _ hp1) (y * j) hconj
    have hy : y = dg u * j⁻¹ := by
      rw [← hu]
      group
    exact ⟨u, j⁻¹, (V.J 3).inv_mem hj, hy, (key u j⁻¹ ((V.J 3).inv_mem hj) hy).mp hg⟩
  · rintro ⟨u, j, hj, hy, hc⟩
    exact (key u j hj hy).mpr hc

end
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

open MulAction

private theorem wcount_of {T Y A : Type} [Group T] [MulAction T Y] [Finite A] (C : Subgroup T) (f : Y → ℂ) (n : ℕ)
    (Ψ : A → orbitRel.Quotient T Y) (inj : Function.Injective Ψ)
    (hr : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 ↔ o ∈ Set.range Ψ)
    (h1 : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → f o.out = 1 ∧ (stabilizer T o.out).relIndex C = n) :
    {o : orbitRel.Quotient T Y | f o.out ≠ 0}.Finite ∧ wcount C f = (n : ℂ) * (Nat.card A : ℂ) := by
  classical
  have hs : {o : orbitRel.Quotient T Y | f o.out ≠ 0} = Set.range Ψ := Set.ext fun o => hr o
  have : Fintype A := Fintype.ofFinite A
  refine ⟨hs ▸ Set.finite_range Ψ, ?_⟩
  unfold wcount
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image Ψ)]
  · rw [Finset.sum_image (fun a _ b _ h => inj h)]
    have key : ∀ a, ((stabilizer T (Ψ a).out).relIndex C : ℂ) * f (Ψ a).out = n := by
      intro a
      have ha : f (Ψ a).out ≠ 0 := (hr _).2 ⟨a, rfl⟩
      obtain ⟨h1a, h2a⟩ := h1 _ ha
      rw [h1a, h2a, mul_one]
    simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    ring
  · intro o ho
    have hne : f o.out ≠ 0 := fun h => ho (by simp [h])
    obtain ⟨a, rfl⟩ := (hr o).1 hne
    simp

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dg_mem (V : Lev k) (w : Fin 3 → kˣ) : dg w ∈ V.J 3 ↔ ∀ i, w i ∈ V.H := by
  refine ⟨fun h i => ?_, V.dg_mem⟩
  obtain ⟨u, hu, he⟩ := ((memJ k V 3 (dg w)).1 h).2.2 i
  have hu' : u = w i := Units.ext (by rw [he]; simp [dg, val_diagT])
  exact hu' ▸ hu

private theorem mk_eq (V : Lev k) (g₀ : GL (Fin 3) k) (u u' : Fin 3 → kˣ) :
    ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = ((g₀ * dg u' : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ↔
      ∀ i, (u i)⁻¹ * u' i ∈ V.H := by
  rw [QuotientGroup.eq, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← map_inv, ← map_mul]
  exact (dg_mem V _).trans (by simp [Pi.mul_apply, Pi.inv_apply])

private def Cd (V : Lev k) (d : Fin 3 → kˣ) (x y z : kˣ) (u : Fin 3 → kˣ) : Prop :=
  x / (u 0 * u 2) / d 0 ∈ V.H ∧ y / u 1 ^ 2 / d 1 ∈ V.H ∧ z / (u 0 * u 2) / d 2 ∈ V.H

private theorem supp_iff (V : Lev k) (d : Fin 3 → kˣ) (hd : SDom d) (x y z : kˣ) (hv : valuation k ((x / z : kˣ) : k) < 1)
    (g₀ w : GL (Fin 3) k) :
    V.unitaryDoubleCosetIndicator d (w⁻¹ * (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 w) ≠ 0 ↔
      ∃ u, (w : GL (Fin 3) k ⧸ V.J 3) = ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ∧ Cd V d x y z u := by
  have hf : ∀ g : GL (Fin 3) k, V.unitaryDoubleCosetIndicator d g ≠ 0 ↔ g * (Phi k)⁻¹ ∈ V.DC d := by
    intro g
    unfold Lev.unitaryDoubleCosetIndicator
    split_ifs <;> simp_all
  have hM : w⁻¹ * (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 w =
      (g₀⁻¹ * w)⁻¹ * (dg ![x, y, z] * Phi k) * th k 3 (g₀⁻¹ * w) := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [hf, hM, fixG k V d hd x y z hv]
  constructor
  · rintro ⟨u, j, hj, he, h1, h2, h3⟩
    refine ⟨u, ?_, h1, h2, h3⟩
    have hj' : (g₀ * dg u)⁻¹ * w = j := by
      rw [_root_.mul_inv_rev, mul_assoc, he, inv_mul_cancel_left]
    rw [QuotientGroup.eq]
    rw [← hj'] at hj
    have := inv_mem hj
    rw [_root_.mul_inv_rev, inv_inv] at this
    exact this
  · rintro ⟨u, hq, h1, h2, h3⟩
    rw [QuotientGroup.eq] at hq
    refine ⟨u, (g₀ * dg u)⁻¹ * w, ?_, ?_, h1, h2, h3⟩
    · have := inv_mem hq
      rw [_root_.mul_inv_rev, inv_inv] at this
      exact this
    · rw [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]

end

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem gl3_spherical_value_one (V : Lev k) (d : Fin 3 → kˣ) (g : GL (Fin 3) k) (h : V.unitaryDoubleCosetIndicator d g ≠ 0) : V.unitaryDoubleCosetIndicator d g = 1 := by
  classical
  unfold Lev.unitaryDoubleCosetIndicator at h ⊢
  split_ifs at h ⊢ with h'
  · rfl
  · exact absurd rfl h

private theorem cd_act (V : Lev k) (d : Fin 3 → kˣ) (x y z a : kˣ) (u : Fin 3 → kˣ) (h : Cd V d x y z u) :
    Cd V d x y z (![a, 1, a⁻¹] * u) := by
  have e0 : (![a, 1, a⁻¹] * u) 0 * (![a, 1, a⁻¹] * u) 2 = u 0 * u 2 := by
    simp [Pi.mul_apply, mul_mul_mul_comm]
  have e1 : (![a, 1, a⁻¹] * u) 1 = u 1 := by simp [Pi.mul_apply]
  unfold Cd
  rw [e0, e1]
  exact h

end

theorem orbital_integral_over_base_group : UnitaryHyperbolicOrbitCount := by
  unfold UnitaryHyperbolicOrbitCount
  intro k _ _ _ _ V T _ r hr g₀ ι hι d hd x₁ y₁ z₁ hv
  letI : MulAction T (GL (Fin 3) k ⧸ V.J 3) := MulAction.compHom _ ι
  set δ := g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹ with hδ
  have hF : ∀ q : GL (Fin 3) k ⧸ V.J 3, V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out) ≠ 0 ↔
      ∃ u, q = ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) ∧ Cd V d x₁ y₁ z₁ u := by
    intro q
    have h := supp_iff V d hd x₁ y₁ z₁ hv g₀ q.out
    rw [QuotientGroup.out_eq'] at h
    exact h
  have hact : ∀ (s : T) (u : Fin 3 → kˣ), s • ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) =
      ((g₀ * dg (![r s, 1, (r s)⁻¹] * u) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) := by
    intro s u
    show ((ι s * (g₀ * dg u) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = _
    rw [hι, show dg (![r s, 1, (r s)⁻¹] * u) = dg ![r s, 1, (r s)⁻¹] * dg u from map_mul _ _ _]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hstab : ∀ u : Fin 3 → kˣ, stabilizer T ((g₀ * dg u : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) =
      Subgroup.comap r V.H := by
    intro u
    ext s
    rw [mem_stabilizer_iff, hact, mk_eq, Subgroup.mem_comap]
    have e : ∀ i, ((![r s, 1, (r s)⁻¹] * u) i)⁻¹ * u i = (![r s, 1, (r s)⁻¹] i)⁻¹ := by
      intro i
      simp only [Pi.mul_apply, mul_inv, inv_mul_cancel_right]
    constructor
    · intro h
      have h2 := h 2
      rw [e] at h2
      simpa using h2
    · intro h i
      rw [e]
      rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl <;> simp [h]
  have FF := finFacts k V
  have hne : V.H.relIndex V.H2 ≠ 0 := by
    intro h0
    apply FF.1
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ FF.2.2.1 FF.2.1, h0, zero_mul]
  unfold orb
  by_cases hc : x₁ / z₁ / (d 0 / d 2) ∈ V.H ∧ ∃ s, y₁ / (d 1 * s ^ 2) ∈ V.H
  · rw [if_pos hc]
    obtain ⟨hxz, s0, hs0⟩ := hc
    haveI : (V.H.subgroupOf V.H2).FiniteIndex := ⟨hne⟩
    let U : ↥V.H2 → Fin 3 → kˣ := fun v => ![x₁ / d 0, s0 * (v : kˣ), 1]
    let q : ↥V.H2 → GL (Fin 3) k ⧸ V.J 3 := fun v => ((g₀ * dg (U v) : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)
    let Ψ : ↥V.H2 ⧸ V.H.subgroupOf V.H2 → orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3) :=
      Quotient.lift (s := QuotientGroup.leftRel (V.H.subgroupOf V.H2))
        (fun v => (Quotient.mk'' (q v) : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3))) (by
        intro a b hab
        have hab' : a⁻¹ * b ∈ V.H.subgroupOf V.H2 := QuotientGroup.leftRel_apply.mp hab
        rw [Subgroup.mem_subgroupOf] at hab'
        apply congrArg
        simp only [q]
        rw [mk_eq]
        intro i
        rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
        · convert one_mem V.H using 1
          ext
          simp [U] <;> field_simp
        · convert hab' using 1
          ext
          simp [U] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U])
    have hΨ : ∀ v : ↥V.H2, Ψ (v : ↥V.H2 ⧸ V.H.subgroupOf V.H2) =
        (Quotient.mk'' (q v) : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3)) := fun v => rfl
    have hinj : Function.Injective Ψ := by
      intro a b hab
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
      rw [hΨ, hΨ] at hab
      have hab' := Quotient.exact' hab
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab'
      obtain ⟨s, hs⟩ := hab'
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [q] at hs
      rw [hact, mk_eq] at hs
      have h1 := inv_mem (hs 1)
      convert h1 using 1
      ext
      simp [U, Pi.mul_apply] <;> field_simp
    have hrng : ∀ o : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3),
        V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) ≠ 0 ↔ o ∈ Set.range Ψ := by
      intro o
      rw [hF]
      constructor
      · rintro ⟨u, hu, h1, h2, h3⟩
        have hv2 : u 1 * s0⁻¹ ∈ V.H2 := by
          show (u 1 * s0⁻¹) ^ 2 ∈ V.H
          have e : (u 1 * s0⁻¹) ^ 2 = y₁ / (d 1 * s0 ^ 2) / (y₁ / u 1 ^ 2 / d 1) := by
            ext
            simp <;> field_simp
          rw [e]
          exact div_mem hs0 h2
        obtain ⟨s, hs⟩ := hr (u 2)
        refine ⟨((⟨u 1 * s0⁻¹, hv2⟩ : ↥V.H2) : ↥V.H2 ⧸ V.H.subgroupOf V.H2), ?_⟩
        rw [hΨ]
        refine (Quotient.sound' ?_).trans (Quotient.out_eq' o)
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        refine ⟨s, ?_⟩
        rw [hu, hact, hs]
        simp only [q]
        rw [mk_eq]
        intro i
        rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
        · convert h1 using 1
          ext
          simp [U, Pi.mul_apply] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U, Pi.mul_apply] <;> field_simp
        · convert one_mem V.H using 1
          ext
          simp [U, Pi.mul_apply]
      · rintro ⟨a, rfl⟩
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
        rw [hΨ]
        have hm := Quotient.mk_out' (s₁ := orbitRel T (GL (Fin 3) k ⧸ V.J 3)) (q v)
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hm
        obtain ⟨s, hs⟩ := hm
        refine ⟨![r s, 1, (r s)⁻¹] * U v, hs.symm.trans (hact s (U v)), cd_act V d x₁ y₁ z₁ (r s) (U v) ?_⟩
        have hv2 : (v : kˣ) ^ 2 ∈ V.H := v.2
        refine ⟨?_, ?_, ?_⟩
        · convert one_mem V.H using 1
          ext
          simp [U] <;> field_simp
        · convert mul_mem hs0 (inv_mem hv2) using 1
          ext
          simp [U] <;> field_simp
        · convert inv_mem hxz using 1
          ext
          simp [U] <;> field_simp
    have hone : ∀ o : orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3),
        V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) ≠ 0 →
          V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * δ * th k 3 o.out.out) = 1 ∧
            (stabilizer T o.out).relIndex (Subgroup.comap r (Uo k)) = V.H.relIndex (Uo k) := by
      intro o h
      refine ⟨gl3_spherical_value_one V d _ h, ?_⟩
      obtain ⟨u, hu, -⟩ := (hF _).1 h
      rw [hu, hstab, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hr]
    obtain ⟨hfin, hsum⟩ := wcount_of (C := Subgroup.comap r (Uo k))
      (f := fun q : GL (Fin 3) k ⧸ V.J 3 => V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out))
      (n := V.H.relIndex (Uo k)) Ψ hinj hrng hone
    exact ⟨hfin, hsum.trans rfl⟩
  · rw [if_neg hc]
    have hzero : ∀ q : GL (Fin 3) k ⧸ V.J 3, V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out) = 0 := by
      intro q
      by_contra h
      obtain ⟨u, -, h1, h2, h3⟩ := (hF q).1 h
      refine hc ⟨?_, u 1, ?_⟩
      · convert div_mem h1 h3 using 1
        ext
        simp <;> field_simp
      · convert h2 using 1
        ext
        simp <;> field_simp
    haveI : IsEmpty Empty := ⟨Empty.elim⟩
    obtain ⟨hfin, hsum⟩ := wcount_of (A := Empty) (C := Subgroup.comap r (Uo k))
      (f := fun q : GL (Fin 3) k ⧸ V.J 3 => V.unitaryDoubleCosetIndicator d (q.out⁻¹ * δ * th k 3 q.out))
      (n := 0) (fun e => e.elim) (fun e => e.elim) (fun o => by simp [hzero])
      (fun o h => absurd (hzero _) h)
    exact ⟨hfin, hsum.trans (by simp)⟩

end UpperTheory.V.Z.Sym.Sig

end
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
open MulAction

variable {T G : Type} [Group T] [Group G]

private def OrbSupp (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : Prop :=
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite

private theorem orb_sum {I : Type} (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    orb ι C θ U (fun g => ∑ i ∈ S, f i g) δ = ∑ i ∈ S, orb ι C θ U (f i) δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  unfold orb wcount
  simp only [Finset.mul_sum]
  rw [finsum_sum_comm]
  intro i hi
  refine (h i hi).subset ?_
  intro o ho
  simp only [Function.mem_support] at ho
  exact right_ne_zero_of_mul ho

private theorem finOrb_of (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G)
    (hf : ∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ)
    (h : OrbSupp ι θ U f δ) : FinOrb ι θ U f δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  classical
  have h' : {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite := h
  refine ⟨h'.toFinset.image (fun o => o.out.out), ?_⟩
  intro y hy
  let o : orbitRel.Quotient T (G ⧸ U) := Quotient.mk _ (QuotientGroup.mk y : G ⧸ U)
  obtain ⟨t, ht⟩ : ∃ t : T, t • (QuotientGroup.mk y : G ⧸ U) = o.out :=
    Quotient.exact (Quotient.out_eq o)
  have hs : (QuotientGroup.mk (o.out.out) : G ⧸ U) = QuotientGroup.mk (ι t * y) := by
    rw [QuotientGroup.out_eq', ← ht]
    rfl
  have hu := QuotientGroup.eq.mp hs.symm
  set s := o.out.out with hsdef
  set u := (ι t * y)⁻¹ * s with hudef
  have hs' : s = ι t * y * u := by rw [hudef]; group
  refine ⟨t⁻¹, s, ?_, u⁻¹, U.inv_mem hu, ?_⟩
  · refine Finset.mem_image.mpr ⟨o, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    show f (s⁻¹ * δ * θ s) ≠ 0
    have e : s⁻¹ * δ * θ s = u⁻¹ * (y⁻¹ * δ * θ y) * θ u := by
      rw [hs', map_mul, map_mul]
      calc (ι t * y * u)⁻¹ * δ * (θ (ι t) * θ y * θ u)
          = u⁻¹ * (y⁻¹ * ((ι t)⁻¹ * δ * θ (ι t)) * θ y) * θ u := by group
        _ = _ := by rw [hδ]
    rw [e, hf u hu]
    exact hy
  · rw [hs', map_inv]
    group

private theorem finOrb_sum {I : Type} (ι : T →* G) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (hf : ∀ i ∈ S, ∀ u ∈ U, ∀ x, f i (u⁻¹ * x * θ u) = f i x)
    (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    FinOrb ι θ U (fun g => ∑ i ∈ S, f i g) δ := by
  refine finOrb_of ι θ U _ δ ?_ hδ ?_
  · intro u hu x
    exact Finset.sum_congr rfl fun i hi => hf i hi u hu x
  · letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
    change {o : orbitRel.Quotient T (G ⧸ U) | (∑ i ∈ S, f i (o.out.out⁻¹ * δ * θ o.out.out)) ≠ 0}.Finite
    have hU : (⋃ i ∈ (S : Set I),
        {o : orbitRel.Quotient T (G ⧸ U) | f i (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}).Finite :=
      Set.Finite.biUnion S.finite_toSet fun i hi => h i hi
    refine hU.subset ?_
    intro o ho
    simp only [Set.mem_setOf_eq] at ho
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
    exact Set.mem_biUnion (Finset.mem_coe.mpr hi) hne

end

theorem UpperTheory.V.Z.Sym.Sig.orbital_integral_over_extended_group :
    UpperTheory.V.Z.Sym.Sig.TwistedOrbitalIntegralGL3Formula := by
  intro k _ _ _ _ V Ry hR t ht T _ r hr g₀ ι hι x y z hxz
  set θ := th k 3 with hθ
  set δ := g₀ * dg ![x, y, z] * Phi k * (θ g₀)⁻¹ with hδdef
  obtain ⟨_, _, hth'dg, _, _, _, hth'Φ⟩ := thFacts k V
  have hδ : ∀ s, (ι s)⁻¹ * δ * θ (ι s) = δ := by
    intro s
    have hΦ : Phi k * θ (dg ![r s, 1, (r s)⁻¹]) = dg ![r s, 1, (r s)⁻¹] * Phi k := by
      rw [← hth'Φ, hth'dg, inv_inv, inv_one]
    have hc : dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹] = dg ![r s, 1, (r s)⁻¹] * dg ![x, y, z] := by
      simp only [dg]
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hι s, map_mul, map_mul, map_inv]
    calc (g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹)⁻¹ * δ * (θ g₀ * θ (dg ![r s, 1, (r s)⁻¹]) * (θ g₀)⁻¹)
        = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * dg ![x, y, z] * (Phi k * θ (dg ![r s, 1, (r s)⁻¹])) *
            (θ g₀)⁻¹ := by
          rw [hδdef]; group
      _ = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * (dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹]) * Phi k *
            (θ g₀)⁻¹ := by
          rw [hΦ]; group
      _ = δ := by rw [hc, hδdef]; group
  set ϖ := unif k with hϖ
  let d : kˣ → Fin 3 → kˣ := fun a => ![t * ϖ⁻¹, a, ϖ⁻¹]
  have hw1 : valuation k (ϖ : k) < 1 := by
    rw [hϖ, GlAx.unif_spec]
    exact uniformizer_lt_one
  have hw0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
  have hSD : ∀ a ∈ Ry, SDom (d a) := by
    intro a ha i j hij
    obtain ⟨hal, hau⟩ := hR.1 a ha
    have htw : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < valuation k (ϖ : k) := by
      rw [mul_inv_lt_iff₀ hw0]
      simpa [pow_two, hϖ] using ht
    have ht1 : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < 1 := htw.trans hw1
    have hinv : 1 < (valuation k (ϖ : k))⁻¹ := (one_lt_inv₀ hw0).mpr hw1
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [d, map_mul, map_inv₀, Units.val_inv_eq_inv_val]
    · exact htw.trans_le hal
    · exact ht1.trans hinv
    · exact hau.trans_lt hinv
  have hinvar : ∀ a ∈ Ry, ∀ u ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator (d a) (u⁻¹ * g * θ u) = V.unitaryDoubleCosetIndicator (d a) g := by
    intro a _ u hu g
    exact ((eqG k V 1 Ry Ry x z (d a)).1 u⁻¹ ((V.J 3).inv_mem hu) u hu g).1
  have h0 := fun a (ha : a ∈ Ry) => orbital_integral_over_base_group k V T r hr g₀ ι hι (d a) (hSD a ha) x y z hxz
  have hfun : V.unitaryHeckeTestSum Ry t = fun g => ∑ a ∈ Ry, V.unitaryDoubleCosetIndicator (d a) g := rfl
  rw [hfun]
  refine ⟨finOrb_sum ι θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) hinvar hδ (fun a ha => (h0 a ha).1), ?_⟩
  rw [orb_sum ι _ θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) (fun a ha => (h0 a ha).1)]
  rw [Finset.sum_congr rfl fun a ha => (h0 a ha).2]
  obtain ⟨a₀, ⟨ha₀, hq₀⟩, huniq⟩ := hR.2 y
  rw [Finset.sum_eq_single a₀]
  · have e : (d a₀) 0 / (d a₀) 2 = t := by simp [d]
    rw [e]
    unfold Glob.one
    by_cases hP : x / z / t ∈ V.H
    · rw [if_pos ⟨hP, hq₀⟩, if_pos hP, mul_one]
    · rw [if_neg (fun hh => hP hh.1), if_neg hP, mul_zero]
  · intro b hb hne
    rw [if_neg]
    rintro ⟨_, hq⟩
    exact hne (huniq b ⟨hb, hq⟩)
  · intro hn
    exact absurd ha₀ hn

end
