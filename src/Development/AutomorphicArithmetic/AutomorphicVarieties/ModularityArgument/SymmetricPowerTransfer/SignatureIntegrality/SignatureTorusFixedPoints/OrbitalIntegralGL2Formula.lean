module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScalarComm
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.Sig

section Abs

open MulAction

private theorem one_orbit {T Y : Type} [Group T] [MulAction T Y] (C S : Subgroup T) (f : Y → ℂ) (y₀ : Y) (c : ℂ)
    (P : Prop) [Decidable P] (hs : ∀ y, f y ≠ 0 → P ∧ y ∈ orbit T y₀) (hv : P → ∀ y ∈ orbit T y₀, f y = c)
    (ht : ∀ y ∈ orbit T y₀, stabilizer T y = S) :
    {o : orbitRel.Quotient T Y | f o.out ≠ 0}.Finite ∧
      wcount C f = if P then (S.relIndex C : ℂ) * c else 0 := by
  have key : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → o = Quotient.mk'' y₀ := fun o ho =>
    (Quotient.out_eq' o).symm.trans (Quotient.eq''.2 (hs _ ho).2)
  refine ⟨Set.Subsingleton.finite fun o ho o' ho' => (key o ho).trans (key o' ho').symm, ?_⟩
  unfold wcount
  by_cases hP : P
  · rw [if_pos hP, finsum_eq_single _ (Quotient.mk'' y₀)]
    · have hm : (Quotient.mk'' y₀ : orbitRel.Quotient T Y).out ∈ orbit T y₀ :=
        orbitRel_apply.1 (Quotient.eq''.1 (Quotient.out_eq' _))
      rw [ht _ hm, hv hP _ hm]
    · intro o ho
      have h0 : f o.out = 0 := by_contra fun h => ho (key o h)
      simp [h0]
  · rw [if_neg hP]
    have h0 : ∀ o : orbitRel.Quotient T Y, f o.out = 0 := fun o => by_contra fun h => hP (hs _ h).1
    simp [h0]

end Abs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scalar_eq {n : ℕ} (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = dg (fun _ => z) := by
  apply Units.ext
  ext i j
  simp [val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]

private theorem scalar_comm {n : ℕ} (z : kˣ) (x : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) z * x = x * GeneralLinearGroup.scalar (Fin n) z := by
  apply Units.ext
  ext i j
  simp [GeneralLinearGroup.scalar, mul_comm]

private theorem conj_sc {G : Type} [Group G] (S j W : G) (h : S * j⁻¹ = j⁻¹ * S) :
    S * (j⁻¹ * W * j) = j⁻¹ * S * W * j := by
  rw [← mul_assoc, ← mul_assoc, h]

private theorem dg_mul {n : ℕ} (a b : Fin n → kˣ) : dg (a * b) = dg a * dg b := map_mul _ _ _

private theorem dg_inv {n : ℕ} (a : Fin n → kˣ) : dg a⁻¹ = (dg a)⁻¹ := map_inv _ _

private theorem dg_comm {n : ℕ} (a b : Fin n → kˣ) : dg a * dg b = dg b * dg a := by
  rw [← dg_mul, ← dg_mul, mul_comm]

private theorem sdom2 {x : Fin 2 → kˣ} (h : valuation k (x 0 : k) < valuation k (x 1 : k)) : SDom x := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact h | exact absurd hij (by decide)

private theorem dg_mem_ZJ (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) {w : Fin 2 → kˣ} :
    dg w ∈ V.ZJ 2 ↔ w 0 / w 1 ∈ V.H := by
  have hz : ∀ u : GL (Fin 2) k, u ∈ V.ZJ 2 ↔ ∃ z : kˣ, ∃ j ∈ V.J 2, u = GeneralLinearGroup.scalar (Fin 2) z * j := by
    haveI : (GeneralLinearGroup.scalar (Fin 2) : kˣ →* GL (Fin 2) k).range.Normal := ⟨by
      rintro _ ⟨z, rfl⟩ g
      exact ⟨z, by rw [← scalar_comm z g]; simp⟩⟩
    intro u
    rw [← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
      exact ⟨z, j, hj, rfl⟩
    · rintro ⟨z, j, hj, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
  constructor
  · intro h
    obtain ⟨z, j, hj, e⟩ := (hz _).1 h
    have e1 : dg w = dg (fun _ => z) * j := by rw [e, scalar_eq]
    have e2 : j = dg ((fun _ => z)⁻¹ * w) := by
      rw [dg_mul, dg_inv, e1, inv_mul_cancel_left]
    have hm : ∀ i, ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i ∈ V.H := by
      intro i
      obtain ⟨u, hu, hu'⟩ := ((memJ k V 2 j).1 hj).2.2 i
      have : u = ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i := by
        apply Units.ext
        rw [hu', e2, dg, val_diagT, diagonal_apply_eq]
      exact this ▸ hu
    have := div_mem (hm 0) (hm 1)
    simpa [mul_div_mul_left_eq_div] using this
  · intro h
    refine (hz _).2 ⟨w 1, dg ![w 0 / w 1, 1], V.dg_mem ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h
      · exact one_mem _
    · rw [scalar_eq, ← dg_mul]
      congr 1
      funext i
      fin_cases i <;> simp

private theorem supp_orb (V : Lev k) (ω : kˣ →* ℂˣ) (d : Fin 2 → kˣ) (hd : SDom d) (g₀ : GL (Fin 2) k) (a b : kˣ)
    (hab : valuation k (a : k) < valuation k (b : k)) (g : GL (Fin 2) k)
    (h : V.fZ ω d (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ≠ 0) :
    a / b / (d 0 / d 1) ∈ V.H ∧ ∃ u : Fin 2 → kˣ, ∃ j ∈ V.J 2, g = g₀ * dg u * j := by
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ∈ V.DC d := by
    by_contra hn
    exact h (by rw [Lev.fZ, dite_eq_right hn])
  obtain ⟨z, hz⟩ := hex
  obtain ⟨j, hj, s, ⟨s', hs', rfl⟩, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ hz
  have hs : ∀ i, s' i ∈ V.H := fun i => hs' i trivial
  have e' : j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g)) * j = dg s' * dg d := e
  have hc := scalar_comm z j⁻¹
  have e3 : (g₀⁻¹ * g * j)⁻¹ * dg ![a, b] * (g₀⁻¹ * g * j) = dg ((fun _ => z) * s' * d) := by
    rw [dg_mul, dg_mul, mul_assoc (dg fun _ => z), ← e', ← scalar_eq, conj_sc _ _ _ hc]
    group
  have hv : ∀ i, valuation k (s' i : k) = 1 := fun i => V.H_le (hs i)
  have hzpos : 0 < valuation k (z : k) := zero_lt_iff.2 (by simp)
  have hsd : SDom ((fun _ => z) * s' * d) := sdom2 (by
    simp only [Pi.mul_apply, Units.val_mul, map_mul, hv, mul_one]
    exact mul_lt_mul_of_pos_left (hd 0 1 (by decide)) hzpos)
  obtain ⟨E, u, hu⟩ := conjDiag k 2 ![a, b] _ (sdom2 hab) hsd _ e3
  have ha : a = z * s' 0 * d 0 := congrFun E 0
  have hb : b = z * s' 1 * d 1 := congrFun E 1
  refine ⟨?_, u, j⁻¹, inv_mem hj, ?_⟩
  · have : a / b / (d 0 / d 1) = s' 0 / s' 1 := by
      rw [ha, hb, mul_assoc z, mul_assoc z, mul_div_mul_left_eq_div, mul_div_mul_comm, mul_div_cancel_right]
    rw [this]
    exact div_mem (hs 0) (hs 1)
  · rw [← hu]
    group

private theorem value_orb (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (d : Fin 2 → kˣ) (hd : SDom d)
    (g₀ : GL (Fin 2) k) (a b : kˣ) (hc : a / b / (d 0 / d 1) ∈ V.H) (u : Fin 2 → kˣ) (v : GL (Fin 2) k)
    (hv : v ∈ V.ZJ 2) :
    V.fZ ω d ((g₀ * dg u * v)⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * (g₀ * dg u * v)) = (ω (d 1 / b) : ℂ) := by
  have hz : ∀ u : GL (Fin 2) k, u ∈ V.ZJ 2 ↔ ∃ z : kˣ, ∃ j ∈ V.J 2, u = GeneralLinearGroup.scalar (Fin 2) z * j := by
    haveI : (GeneralLinearGroup.scalar (Fin 2) : kˣ →* GL (Fin 2) k).range.Normal := ⟨by
      rintro _ ⟨z, rfl⟩ g
      exact ⟨z, by rw [← scalar_comm z g]; simp⟩⟩
    intro u
    rw [← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
      exact ⟨z, j, hj, rfl⟩
    · rintro ⟨z, j, hj, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
  obtain ⟨z', j, hj, rfl⟩ := (hz v).1 hv
  have hD : dg ![a, b] = GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (dg ![a / b / (d 0 / d 1), 1] * dg d) := by
    rw [scalar_eq, ← dg_mul, ← dg_mul]
    congr 1
    funext i
    fin_cases i
    · apply Units.ext
      simp
      field_simp
    · simp
  have hX : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
      (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
      GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j) := by
    have h1 : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
        (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
        j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * ((dg u)⁻¹ * dg ![a, b] * dg u) *
          GeneralLinearGroup.scalar (Fin 2) z') * j := by group
    have h2 : (dg u)⁻¹ * dg ![a, b] * dg u = dg ![a, b] := by
      rw [mul_assoc, dg_comm ![a, b] u, inv_mul_cancel_left]
    have h3 : (GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * dg ![a, b] * GeneralLinearGroup.scalar (Fin 2) z' = dg ![a, b] := by
      rw [mul_assoc, ← scalar_comm, inv_mul_cancel_left]
    rw [h1, h2, h3, hD, mul_assoc j⁻¹ (dg ![a / b / (d 0 / d 1), 1]) (dg d), conj_sc _ _ _ (scalar_comm _ j⁻¹)]
    group
  have hdc : j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j ∈ V.DC d := by
    refine ⟨j⁻¹ * dg ![a / b / (d 0 / d 1), 1], mul_mem (inv_mem hj) (V.dg_mem ?_), j, hj, rfl⟩
    intro i
    fin_cases i
    · exact hc
    · exact one_mem _
  have hH : ∀ {g : GL (Fin 2) k} {z : kˣ}, g ∈ V.DC d →
      GeneralLinearGroup.scalar (Fin 2) z * g ∈ V.DC d → z ∈ V.H := by
    intro g z hg h
    obtain ⟨j, hj, _, ⟨t, ht, rfl⟩, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd g hg
    obtain ⟨a, ha, b, hb, e2⟩ := h
    have e3 : dg ((fun _ => z) * t * d) = (j⁻¹ * a) * dg d * (b * j) := by
      have e4 : dg ((fun _ => z) * t * d) = GeneralLinearGroup.scalar (Fin 2) z * (dg t * dg d) := by
        rw [scalar_eq, dg_mul, dg_mul, mul_assoc]
      rw [e4, ← e, MonoidHom.id_apply]
      calc GeneralLinearGroup.scalar (Fin 2) z * (j⁻¹ * g * j) = j⁻¹ * (GeneralLinearGroup.scalar (Fin 2) z * g) * j := by
            rw [← mul_assoc, ← mul_assoc, scalar_comm z j⁻¹]; simp only [mul_assoc]
        _ = _ := by rw [e2]; group
    have h1 : dg ((fun _ => z) * t * d) ∈ V.DC d := ⟨_, mul_mem (inv_mem hj) ha, _, mul_mem hb hj, e3⟩
    have h2 := (diagDC k V 2 d _ (fun i j h => h.eq_or_lt.elim (fun e => by rw [e]) (fun l => (hd i j l).le))).1 h1 0
    have h3 : z * t 0 * d 0 / d 0 ∈ V.H := h2
    have h4 := div_mem h3 (ht 0 trivial)
    simpa using h4
  rw [hX, Lev.fZ]
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ *
      (GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j)) ∈ V.DC d :=
    ⟨b / d 1, by rw [inv_mul_cancel_left]; exact hdc⟩
  rw [dite_eq_left hex]
  have hchoose := hex.choose_spec
  generalize hex.choose = c at hchoose ⊢
  have h1 : (b / d 1) / c ∈ V.H := hH (z := (b / d 1) / c) hdc (by
    convert hchoose using 1
    rw [map_div, div_eq_mul_inv, ← map_inv, scalar_comm (b / d 1) (GeneralLinearGroup.scalar (Fin 2) (c⁻¹))]
    group)
  have h2 := hω _ h1
  rw [map_div, div_eq_one] at h2
  rw [← h2, ← map_inv, inv_div]

theorem orbZ : OrbZ := by
  classical
  intro k _ _ _ _ V ω hω d hd T _ p q hpq g₀ ι hι a b hab
  letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι
  have hJ : V.J 2 ≤ V.ZJ 2 := le_sup_right
  have hrel : (V.H.comap (p / q)).relIndex ((Uo k).comap (p / q)) = V.H.relIndex (Uo k) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hpq]
  have horb : ∀ y ∈ MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2),
      ∃ u : Fin 2 → kˣ, y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨![p s, q s], ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [hι]
    congr 1
    group
  have horb' : ∀ u : Fin 2 → kˣ, ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) ∈
      MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    intro u
    obtain ⟨s, hs⟩ := hpq (u 0 / u 1)
    refine ⟨s, ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [QuotientGroup.eq, hι]
    have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * g₀)⁻¹ * (g₀ * dg u) = dg (![p s, q s]⁻¹ * u) := by
      rw [dg_mul, dg_inv]
      group
    rw [e, dg_mem_ZJ V ω hω]
    have hs' : p s / q s = u 0 / u 1 := hs
    have : (![p s, q s]⁻¹ * u) 0 / (![p s, q s]⁻¹ * u) 1 = 1 := by
      simp only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_div_mul_comm, ← hs']
      simp
    rw [this]
    exact one_mem _
  have main := one_orbit ((Uo k).comap (p / q)) (V.H.comap (p / q))
    (fun y : GL (Fin 2) k ⧸ V.ZJ 2 => V.fZ ω d (y.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * y.out))
    ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) (ω (d 1 / b) : ℂ) (a / b / (d 0 / d 1) ∈ V.H)
    (by
      intro y hy
      obtain ⟨hP, u, j, hj, e⟩ := supp_orb V ω d hd g₀ a b hab _ hy
      refine ⟨hP, ?_⟩
      have : y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
        rw [← QuotientGroup.out_eq' y, e]
        exact QuotientGroup.mk_mul_of_mem _ (hJ hj)
      exact this ▸ horb' u)
    (by
      intro hP y hy
      obtain ⟨u, rfl⟩ := horb y hy
      have hm : (g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out ∈ V.ZJ 2 :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      have e : (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out =
          g₀ * dg u * ((g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out) := by
        group
      show V.fZ ω d _ = _
      rw [e]
      exact value_orb V ω hω d hd g₀ a b hP u _ hm)
    (by
      intro y hy
      obtain ⟨u, rfl⟩ := horb y hy
      ext s
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MonoidHom.div_apply]
      change ((ι s * (g₀ * dg u) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _ ↔ _
      rw [QuotientGroup.eq, hι]
      have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u))⁻¹ * (g₀ * dg u) = dg ![p s, q s]⁻¹ := by
        rw [dg_inv]
        have : g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u) = g₀ * dg u * dg ![p s, q s] := by
          rw [mul_assoc g₀ (dg u), dg_comm u]
          group
        rw [this]
        group
      rw [e, dg_mem_ZJ V ω hω]
      have : (![p s, q s]⁻¹ : Fin 2 → kˣ) 0 / (![p s, q s]⁻¹ : Fin 2 → kˣ) 1 = (p s / q s)⁻¹ := by
        simp
        rw [div_eq_mul_inv, mul_comm]
      rw [this, inv_mem_iff])
  rw [hrel] at main
  refine ⟨main.1, ?_⟩
  unfold orb
  exact main.2

end UpperTheory.V.Z.Sym.Sig

end
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem scal_eq (z : kˣ) : GeneralLinearGroup.scalar (Fin 2) z = dg (fun _ : Fin 2 => z) := by
  ext i j
  simp [dg, val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]

private theorem scal_comm (z : kˣ) (g : GL (Fin 2) k) :
    GeneralLinearGroup.scalar (Fin 2) z * g = g * GeneralLinearGroup.scalar (Fin 2) z := by
  ext : 1
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : k) (fun _ => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) k))

private theorem sdom2_aux {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) : SDom ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem key (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b z : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) {w : GL (Fin 2) k}
    (h : (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (w⁻¹ * dg ![a, b] * w) ∈ V.DC d) :
    ∃ (u : Fin 2 → kˣ), ∃ j ∈ V.J 2, w = dg u * j ∧ a / (z * d 0) ∈ V.H ∧ b / (z * d 1) ∈ V.H := by
  obtain ⟨j, hj, s, hs, E⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ h
  obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
  simp only [Subgroup.mem_pi, Set.mem_univ, true_implies] at hs'
  have hv : ∀ i, valuation k ((s' i : kˣ) : k) = 1 := fun i => V.H_le (hs' i)
  have hE : (w * j)⁻¹ * dg ![a, b] * (w * j) = dg (fun i => z * s' i * d i) := by
    have c := scal_comm z j⁻¹
    calc (w * j)⁻¹ * dg ![a, b] * (w * j)
        = GeneralLinearGroup.scalar (Fin 2) z * (j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ *
            (w⁻¹ * dg ![a, b] * w)) * MonoidHom.id _ j) := by
          simp only [MonoidHom.id_apply, ← mul_assoc]
          rw [c]
          group
      _ = dg (fun i => z * s' i * d i) := by
          rw [E, scal_eq]
          simp only [dg, ← map_mul]
          congr 1
          funext i
          simp [mul_assoc]
  have hsd : SDom (fun i => z * s' i * d i) := by
    intro i i' hii
    simp only [Units.val_mul, map_mul, hv, mul_one]
    have hz0 : valuation k (z : k) ≠ 0 := by simp
    exact mul_lt_mul_of_pos_left (hd i i' hii) (zero_lt_iff.mpr hz0)
  obtain ⟨hab', u, hu⟩ := conjDiag k 2 ![a, b] _ (sdom2_aux hab) hsd (w * j) hE
  refine ⟨u, j⁻¹, inv_mem hj, ?_, ?_, ?_⟩
  · rw [← hu]
    group
  · have h0 : a = z * s' 0 * d 0 := congrFun hab' 0
    rw [h0, mul_right_comm, mul_div_cancel_left]
    exact hs' 0
  · have h1 : b = z * s' 1 * d 1 := congrFun hab' 1
    rw [h1, mul_right_comm, mul_div_cancel_left]
    exact hs' 1

private theorem orbit_of {T : Type} [Group T] (V : Lev k) {p q : T →* kˣ}
    (hpq : ∀ x : kˣ, ∃ t, p t / q t = x) {g₀ : GL (Fin 2) k} {ι : T →* GL (Fin 2) k}
    (hι : ∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) {u : Fin 2 → kˣ} {j : GL (Fin 2) k} (hj : j ∈ V.J 2) :
    ∃ t, ∃ v ∈ V.ZJ 2, g₀ * (dg u * j) = ι t * g₀ * v := by
  obtain ⟨t, ht⟩ := hpq (u 0 / u 1)
  have hz : GeneralLinearGroup.scalar (Fin 2) (u 1 / q t) ∈ V.ZJ 2 := by
    show _ ∈ (GeneralLinearGroup.scalar (Fin 2)).range ⊔ V.J 2
    exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  have hzj : GeneralLinearGroup.scalar (Fin 2) (u 1 / q t) * j ∈ V.ZJ 2 := by
    refine mul_mem hz ?_
    show _ ∈ (GeneralLinearGroup.scalar (Fin 2)).range ⊔ V.J 2
    exact Subgroup.mem_sup_right hj
  refine ⟨t, _, hzj, ?_⟩
  have h0 : u 0 = p t / q t * u 1 := by rw [ht, div_mul_cancel]
  have hu : u = ![p t, q t] * fun _ => u 1 / q t := by
    funext i
    fin_cases i
    · show u 0 = p t * (u 1 / q t)
      rw [h0, mul_div_assoc', div_mul_eq_mul_div]
    · show u 1 = q t * (u 1 / q t)
      rw [mul_div_cancel]
  rw [hι, scal_eq]
  conv_lhs => rw [hu]
  simp only [dg, map_mul]
  group

private theorem orb_congr' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    {f f' : G → ℂ} (δ : G) (h : ∀ y, f (y⁻¹ * δ * θ y) = f' (y⁻¹ * δ * θ y)) :
    orb ι C θ U f δ = orb ι C θ U f' δ := by
  simp only [orb, h]

private theorem orb_smul' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    (c : ℂ) (f : G → ℂ) (δ : G) :
    orb ι C θ U (fun g => c * f g) δ = c * orb ι C θ U f δ := by
  unfold orb wcount
  simp only [mul_left_comm _ c]
  exact (smul_finsum c _).symm

private theorem orb_zero' {T G : Type} [Group T] [Group G] (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G)
    (δ : G) : orb ι C θ U (fun _ => 0) δ = 0 := by
  simp [orb, wcount]

private theorem inv_gt {x : kˣ} (h : valuation k (x : k) < 1) : valuation k (x : k) < valuation k ((x⁻¹ : kˣ) : k) := by
  have hp : 0 < valuation k (x : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact h.trans ((one_lt_inv₀ hp).2 h)

private theorem key' (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b z : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) (g₀ y : GL (Fin 2) k)
    (h : (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (y⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC d) :
    ∃ (u : Fin 2 → kˣ), ∃ j ∈ V.J 2, y = g₀ * (dg u * j) ∧ a / (z * d 0) ∈ V.H ∧ b / (z * d 1) ∈ V.H := by
  have e : (g₀⁻¹ * y)⁻¹ * dg ![a, b] * (g₀⁻¹ * y) = y⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * MonoidHom.id _ y := by
    simp only [MonoidHom.id_apply]; group
  obtain ⟨u, j, hj, hw, h1, h2⟩ := key V hd hab (w := g₀⁻¹ * y) (z := z) (by rw [e]; exact h)
  exact ⟨u, j, hj, by rw [← hw]; group, h1, h2⟩

private theorem fin_of {T : Type} [Group T] (V : Lev k) {d : Fin 2 → kˣ} (hd : SDom d) {a b : kˣ}
    (hab : valuation k (a : k) < valuation k (b : k)) {p q : T →* kˣ}
    (hpq : ∀ x : kˣ, ∃ t, p t / q t = x) {g₀ : GL (Fin 2) k} {ι : T →* GL (Fin 2) k}
    (hι : ∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) (f : GL (Fin 2) k → ℂ)
    (hf : ∀ g, f g ≠ 0 → ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * g ∈ V.DC d) :
    FinOrb ι (MonoidHom.id _) (V.ZJ 2) f (g₀ * dg ![a, b] * g₀⁻¹) := by
  refine ⟨{g₀}, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := hf _ hy
  obtain ⟨u, j, hj, rfl, -, -⟩ := key' V hd hab g₀ y hz
  obtain ⟨t, v, hv, e⟩ := orbit_of V hpq hι (u := u) hj
  exact ⟨t, g₀, by simp, v, hv, e⟩

end

theorem UpperTheory.V.Z.Sym.Sig.orbital_integral_degree_one : UpperTheory.V.Z.Sym.Sig.OrbitalIntegralGL2Formula := by
  intro k _ _ _ _ V χ hχ t ht T _ p q hpq g₀ ι hι a ha
  have hpq' : ∀ x : kˣ, ∃ s, p s / q s = x := fun x => by
    obtain ⟨s, hs⟩ := hpq x
    exact ⟨s, by simpa using hs⟩
  have htd : SDom ![t, t⁻¹] := sdom2_aux (inv_gt ht)
  have haa : valuation k (a : k) < valuation k ((a⁻¹ : kˣ) : k) := inv_gt ha
  have ht1 : SDom ![t, 1] := sdom2_aux (by simpa using ht)
  refine ⟨⟨?_, ?_⟩, fun b hb => ?_⟩
  · refine fin_of V htd haa hpq' hι (V.quaternionDoubleCosetIndicator t) (fun g hg => ⟨1, ?_⟩)
    have hm : g ∈ V.DC ![t, t⁻¹] := by
      by_contra hn
      exact hg (by simp [Lev.quaternionDoubleCosetIndicator, Glob.one, hn])
    simpa using hm
  · have h1H : ∀ u ∈ V.H, (1 : kˣ →* ℂˣ) u = 1 := fun _ _ => rfl
    have E := (orbZ k V 1 h1H ![t, t⁻¹] htd T p q hpq g₀ ι hι a a⁻¹ haa).2
    by_cases hat : a / t ∈ V.H
    · have hX : ∀ y : GL (Fin 2) k,
          V.quaternionDoubleCosetIndicator t (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) =
          V.fZ 1 ![t, t⁻¹] (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) := by
        intro y
        have hiff : y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y ∈ V.DC ![t, t⁻¹] ↔
            ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ *
              (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC ![t, t⁻¹] := by
          constructor
          · intro hm
            exact ⟨1, by simpa using hm⟩
          · rintro ⟨z, hz⟩
            obtain ⟨u, j, hj, rfl, -, -⟩ := key' V htd haa g₀ y hz
            have hr : dg ![a / t, (a / t)⁻¹] ∈ V.J 2 := by
              have hm : dg ![a / t, (a / t)⁻¹] ∈ V.TH 2 := by
                refine Subgroup.mem_map_of_mem _ ?_
                simp only [Subgroup.mem_pi, Set.mem_univ, true_implies]
                intro i
                fin_cases i
                · exact hat
                · exact inv_mem hat
              show _ ∈ (glIwa k 2).N ⊔ V.TH 2 ⊔ (glIwa k 2).Nm V.c
              exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hm)
            refine ⟨j⁻¹, inv_mem hj, dg ![a / t, (a / t)⁻¹] * j, mul_mem hr hj, ?_⟩
            have hD : dg ![a, a⁻¹] = dg u * (dg ![t, t⁻¹] * dg ![a / t, (a / t)⁻¹]) * (dg u)⁻¹ := by
              simp only [dg, ← map_mul, ← map_inv]
              congr 1
              funext i
              fin_cases i
              · show a = u 0 * (t * (a / t)) * (u 0)⁻¹
                rw [mul_div_cancel, mul_inv_cancel_comm]
              · show a⁻¹ = u 1 * (t⁻¹ * (a / t)⁻¹) * (u 1)⁻¹
                rw [← mul_inv, mul_div_cancel, mul_inv_cancel_comm]
            rw [hD]
            simp only [MonoidHom.id_apply]
            group
        by_cases hm : y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y ∈ V.DC ![t, t⁻¹]
        · simp only [Lev.quaternionDoubleCosetIndicator, Lev.fZ, Glob.one]
          rw [if_pos hm, dite_eq_left (hiff.mp hm)]
          simp
        · simp only [Lev.quaternionDoubleCosetIndicator, Lev.fZ, Glob.one]
          rw [if_neg hm, dite_eq_right (mt hiff.mpr hm)]
      rw [orb_congr' ι _ _ _ _ hX, E]
      have hsq : a / a⁻¹ / (![t, t⁻¹] 0 / ![t, t⁻¹] 1) = (a / t) * (a / t) := by
        ext
        simp [Units.val_div_eq_div_val]
        field_simp
      rw [hsq, if_pos (mul_mem hat hat)]
      simp [Glob.one, hat]
    · have hX : ∀ y : GL (Fin 2) k,
          V.quaternionDoubleCosetIndicator t (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) =
          (fun _ => (0 : ℂ)) (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) := by
        intro y
        simp only [Lev.quaternionDoubleCosetIndicator, Glob.one]
        rw [if_neg]
        intro hm
        have hz : (GeneralLinearGroup.scalar (Fin 2) (1 : kˣ))⁻¹ *
            (y⁻¹ * (g₀ * dg ![a, a⁻¹] * g₀⁻¹) * MonoidHom.id _ y) ∈ V.DC ![t, t⁻¹] := by
          simpa using hm
        obtain ⟨u, j, hj, -, h0, -⟩ := key' V htd haa g₀ y hz
        apply hat
        simpa using h0
      rw [orb_congr' (f' := fun _ => (0 : ℂ)) ι _ _ _ _ hX, orb_zero']
      simp [Glob.one, hat]
  have h1a : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.mpr (by simp))).mpr ha
  have hvb : valuation k (b : k) = valuation k ((a⁻¹ : kˣ) : k) := by
    rw [hb]
    exact Valuation.map_add_eq_of_lt_right _ (by simpa using h1a)
  have habb : valuation k ((a * b : kˣ) : k) < valuation k (b : k) := by
    rw [Units.val_mul, map_mul]
    exact mul_lt_of_lt_one_left (zero_lt_iff.mpr (by simp)) ha
  refine ⟨?_, ?_⟩
  · refine fin_of V ht1 habb hpq' hι (V.twistedCentralTestFunction χ t) (fun g hg => ?_)
    by_contra hn
    apply hg
    simp only [Lev.twistedCentralTestFunction, Lev.fZ]
    rw [dite_eq_right hn, mul_zero]
  · have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
    have E := (orbZ k V χ hχH ![t, 1] ht1 T p q hpq g₀ ι hι (a * b) b habb).2
    have hfk : V.twistedCentralTestFunction χ t = fun g => (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] g := rfl
    rw [hfk, orb_smul', E]
    have hq : a * b / b / (![t, 1] 0 / ![t, 1] 1) = a / t := by simp
    rw [hq]
    by_cases hat : a / t ∈ V.H
    · rw [if_pos hat]
      have hvat : valuation k (a : k) = valuation k (t : k) := by
        have h1 : valuation k ((a / t : kˣ) : k) = 1 := V.H_le hat
        rw [Units.val_div_eq_div_val, map_div₀, div_eq_one_iff_eq (by simp)] at h1
        exact h1
      have htb : t * b ∈ Uo k := by
        show valuation k ((t * b : kˣ) : k) = 1
        rw [Units.val_mul, map_mul, hvb, ← hvat, Units.val_inv_eq_inv_val, map_inv₀,
          mul_inv_cancel₀ (by simp)]
      have hc : (χ t)⁻¹ * χ (![t, 1] 1 / b) = 1 := by
        have := hχ _ htb
        simp only [map_mul] at this
        show (χ t)⁻¹ * χ (1 / b) = 1
        rw [one_div, map_inv, ← mul_inv, this, inv_one]
      simp only [Glob.one, if_pos hat]
      rw [mul_left_comm, ← Units.val_mul, hc, Units.val_one]
    · simp [Glob.one, hat]

end
