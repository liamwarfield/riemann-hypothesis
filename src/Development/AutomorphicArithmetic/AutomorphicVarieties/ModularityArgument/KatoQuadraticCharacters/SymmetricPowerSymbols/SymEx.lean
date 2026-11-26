module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAdmissibleSmoothingFactorDividedIndices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CastEqZeroOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PowValOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.Imports
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.coc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s s' x y, Ok x y → Cgr m (w (s * s') x y) (w s x y * tw X m M s (w s') x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw s s' x y hxy
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  set x1 := gr M s⁻¹ x
  set y1 := gr M s⁻¹ y
  have hxy1 : Ok x1 y1 := (hok x y hxy).2.2.1 s⁻¹
  have hxy2 : Ok (gr M s'⁻¹ x1) (gr M s'⁻¹ y1) := (hok x1 y1 hxy1).2.2.1 s'⁻¹
  have ex : gr M (s * s')⁻¹ x = gr M s'⁻¹ x1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have ey : gr M (s * s')⁻¹ y = gr M s'⁻¹ y1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have w1 := (hw s' x1 y1 hxy1).2
  have w2 := (hw s x y hxy).2
  have w3 := (hw (s * s') x y hxy).2
  rw [ex, ey] at w3
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have gs : ∀ (r : Gal(Ω/ℚ)) (a b : Row M), Ok a b → (X.gal r) (sg X c M a) = sg X c M (gr M r a) ∧ (X.gal r) (sg X d M b) = sg X d M (gr M r b) := by
    intro r a b hab
    exact ⟨(sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).2.2.1 r, (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).2.2.1 r⟩
  have inv1 : ∀ (r : Gal(Ω/ℚ)) (a : Row M), gr M r (gr M r⁻¹ a) = a := by
    intro r a
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 a).2]
  have q1 : IsPt X m ((X.gal s') (sg X c M (gr M s'⁻¹ x1))) ((X.gal s') (sg X d M (gr M s'⁻¹ y1))) (t (sg X c M x1) (sg X d M y1)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1]
    exact pt _ _ hxy1
  have q2 : IsPt X m ((X.gal s) ((X.gal s') (sg X c M (gr M s'⁻¹ x1)))) ((X.gal s) ((X.gal s') (sg X d M (gr M s'⁻¹ y1)))) (t (sg X c M x) (sg X d M y)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1, (gs s _ _ hxy1).1, (gs s _ _ hxy1).2, inv1, inv1]
    exact pt _ _ hxy
  have comp := mvComp Ω ε X m hm (X.gal s') (X.gal s) s' s (hadm s') (hadm s) _ _ _ _ _ (pt _ _ hxy2) q1 q2 _ _ w1 w2
  have eg : (X.gal s').trans (X.gal s) = X.gal (s * s') := by
    ext f
    rw [gal_mul_apply]
    rfl
  rw [eg] at comp
  have u := ((mvEx Ω ε X m hm (X.gal (s * s')) (s * s') (hadm _) _ _ _ (pt _ _ hxy2)).2.2.2 _ ?_ _ _ comp).1 w3
  · unfold tw
    rw [mul_comm (w s x y)]
    exact u
  · rw [gal_mul_apply, gal_mul_apply]
    exact q2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.KaU
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.PE

theorem kaU : KaU := by
  intro Ω _ _ _ ε X m hm θ hθ g h hgz hhz hgm hhm
  haveI : NeZero m := NeZero.of_pos hm
  obtain ⟨hprim, hrep, hlg, -⟩ := lgB Ω ε X m hm
  have hpow : zt X m ^ m = 1 := hprim.pow_eq_one
  have hgθ : g θ = zt X m ^ (ka X m θ g).val * θ := hrep (g θ) θ hθ (by rw [← map_pow, hgm])
  have hhθ : h θ = zt X m ^ (ka X m θ h).val * θ := hrep (h θ) θ hθ (by rw [← map_pow, hhm])
  have hadd : ∀ i j : ZMod m, zt X m ^ i.val * zt X m ^ j.val = zt X m ^ (i + j).val := by
    intro i j
    rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hpow]
  have hhg : h (g θ) = zt X m ^ (ka X m θ h).val * g θ := by
    rw [hgθ, map_mul, map_pow, hhz, hhθ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine hlg _ _ _ hθ ?_
    show g (h θ) = _
    rw [hhθ, map_mul, map_pow, hgz, hgθ, ← mul_assoc, hadd, add_comm]
  · exact hlg _ _ _ ((map_ne_zero g).2 hθ) hhg
  · refine hlg _ _ _ hθ ?_
    show g.symm (h (g θ)) = _
    have e2 : g.symm (zt X m) = zt X m := by
      rw [RingEquiv.symm_apply_eq, hgz]
    rw [hhg, map_mul, map_pow, e2, RingEquiv.symm_apply_apply]

end UpperTheory.V.Z.Kato.Sym.PE
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PCoc
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.pCoc :
    UpperTheory.V.Z.Kato.Sym.PCoc := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  exact ⟨PC.eqv Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw,
    PC.coc Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw,
    PC.loc Ω ε X m c d M hm hc hd hc6 hd6 hL t w ht hw⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.RtRt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SgDist
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem siegel_admissible_to_rat (c M : ℕ) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hM : 0 < M) (hcM : Nat.Coprime c M)
    (x : Row M) (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨hc, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  apply hx
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i : Fin 2, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0 := by
    intro i n hn
    have hlt := ZMod.val_lt (x i)
    have e : (n : ℚ) * M = (c * (x i).val : ℕ) := by
      rw [hn, toQ]
      push_cast
      field_simp
    have e' : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ) := by exact_mod_cast e
    have hd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ) := ⟨n, by rw [← e', mul_comm]⟩
    have hd' : M ∣ c * (x i).val := by exact_mod_cast hd
    have hv : M ∣ (x i).val := (Nat.Coprime.symm hcM).dvd_of_dvd_mul_left hd'
    have hv0 : (x i).val = 0 := by
      rcases Nat.eq_zero_or_pos (x i).val with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hv) (not_le.mpr hlt)
    exact (ZMod.val_eq_zero _).mp hv0
  funext i
  fin_cases i
  · exact key 0 n0 hn0
  · exact key 1 n1 hn1

private theorem add_mul_lt_mul {k M a v : ℕ} (ha : a < k) (hv : v < M) : v + a * M < k * M := by
  have h1 : v + a * M < (a + 1) * M := by nlinarith
  have h2 : (a + 1) * M ≤ k * M := Nat.mul_le_mul_right _ ha
  omega

private theorem dn_val (k M : ℕ) [NeZero (k * M)] (x' : Row (k * M)) (i : Fin 2) :
    (dn k M x' i).val = (x' i).val % M := by
  show (ZMod.castHom _ (ZMod M) (x' i)).val = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

private theorem val_lt_mul_of_zmod_mul {k M : ℕ} (y : ZMod (k * M)) (hkM : k * M ≠ 0) : y.val < M * k := by
  haveI : NeZero (k * M) := ⟨hkM⟩
  have h := ZMod.val_lt y
  linarith [Nat.mul_comm k M]

theorem UpperTheory.V.Z.Kato.Sym.sgDist :
    UpperTheory.V.Z.Kato.Sym.SgDist := by
  classical
  intro Ω _ _ _ ε X c k M _ hc h6 hcop x hx
  have hkM : k * M ≠ 0 := NeZero.ne _
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  have hM : 0 < M := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  haveI : NeZero M := ⟨hM.ne'⟩
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hcop
  have hck : c.Coprime k := Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hcop
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have split : ∀ x' : Row (k * M), dn k M x' = x → ∀ i : Fin 2,
      (x' i).val = (x i).val + (x' i).val / M * M := by
    intro x' hx' i
    have h := dn_val k M x' i
    rw [hx'] at h
    rw [h, Nat.mod_add_div']
  have qlt : ∀ x' : Row (k * M), ∀ i : Fin 2, (x' i).val / M < k := fun x' i =>
    Nat.div_lt_of_lt_mul (val_lt_mul_of_zmod_mul (x' i) hkM)
  let sel : ℕ × ℕ → Fin 2 → ℕ := fun p => ![p.1, p.2]
  let j : ℕ × ℕ → Row (k * M) := fun p i => (((x i).val + sel p i * M : ℕ) : ZMod (k * M))
  have jval : ∀ p ∈ Finset.range k ×ˢ Finset.range k, ∀ i : Fin 2,
      (j p i).val = (x i).val + sel p i * M := by
    intro p hp i
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hs : sel p i < k := by
      fin_cases i
      · exact hp.1
      · exact hp.2
    show ((((x i).val + sel p i * M : ℕ)) : ZMod (k * M)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (add_mul_lt_mul hs (ZMod.val_lt (x i)))
  rw [sg, ← GlobalTheory.KZDist.siegel_distribution Ω ε X c k (toQ M x) (siegel_admissible_to_rat c M hc h6 hM hcM x hx) hk hck,
    ← Finset.prod_product']
  refine Finset.prod_nbij' (fun x' => ((x' 0).val / M, (x' 1).val / M)) j ?_ ?_ ?_ ?_ ?_
  · intro x' _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨qlt x' 0, qlt x' 1⟩
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    apply ZMod.val_injective
    rw [dn_val, jval p hp i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt (x i))]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    funext i
    have e := split x' hx'.2 i
    show ((((x i).val + sel _ i * M : ℕ)) : ZMod (k * M)) = x' i
    have hsel : sel ((x' 0).val / M, (x' 1).val / M) i = (x' i).val / M := by
      fin_cases i <;> rfl
    rw [hsel, ← e, ZMod.natCast_zmod_val]
  · intro p hp
    have h0 := jval p hp 0
    have h1 := jval p hp 1
    have v0 := ZMod.val_lt (x 0)
    have v1 := ZMod.val_lt (x 1)
    rw [h0, h1]
    ext
    · show ((x 0).val + p.1 * M) / M = p.1
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v0, zero_add]
    · show ((x 1).val + p.2 * M) / M = p.2
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v1, zero_add]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    have e0 := split x' hx'.2 0
    have e1 := split x' hx'.2 1
    show siegel X c (toQ (k * M) x') = _
    congr 1
    funext i
    fin_cases i
    · show ((x' 0).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 0 + (((x' 0).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 0).val / M = q at e0 ⊢
      rw [e0]
      push_cast
      field_simp
    · show ((x' 1).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 1 + (((x' 1).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 1).val / M = q at e1 ⊢
      rw [e1]
      push_cast
      field_simp
end

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem rt_rt {M : ℕ} (x : Row M) (γ δ : SL(2, ℤ)) (h : γ * δ = 1) : rt (rt x γ) δ = x := by
  unfold rt
  rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  simp

theorem pDist : PDist := by
  unfold PDist
  intro Ω _ _ _ ε X m c d k M _ _ hm hc hd hc6 hd6 hLv t w' w hsec hsym' hsym
  obtain ⟨hL, hcL, hdL⟩ := hLv
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  haveI : NeZero (k * M) := ⟨hL.ne'⟩
  have hcM : c.Coprime M := (Nat.coprime_mul_iff_right.mp hcL).2
  have hdM : d.Coprime M := (Nat.coprime_mul_iff_right.mp hdL).2
  obtain ⟨hAslR, hAgal, -⟩ := admB Ω ε X
  obtain ⟨hgrM, hokM, -, hup⟩ := rowB Ω M hM
  obtain ⟨-, -, -, hokdn, hgrdn, hrtdn, hsurj⟩ := hup k hk
  obtain ⟨hgrL, hokL, -⟩ := rowB Ω (k * M) hL
  have hinvM : ∀ (s : Gal(Ω/ℚ)) (x : Row M), gr M s (gr M s⁻¹ x) = x := by
    intro s x
    rw [← (hgrM s s⁻¹ x).1, mul_inv_cancel, (hgrM 1 1 x).2]
  have hinvL : ∀ (s : Gal(Ω/ℚ)) (x : Row (k * M)), gr (k * M) s (gr (k * M) s⁻¹ x) = x := by
    intro s x
    rw [← (hgrL s s⁻¹ x).1, mul_inv_cancel, (hgrL 1 1 x).2]
  have hnz : ∀ (x' : Row (k * M)) (x : Row M), dn k M x' = x → x ≠ 0 → x' ≠ 0 := by
    rintro x' x rfl hx rfl
    apply hx
    funext i
    simp [dn]
  have sgc := sgB Ω ε X c (k * M) hc hc6 hL hcL
  have sgd := sgB Ω ε X d (k * M) hd hd6 hL hdL
  have sgcM := sgB Ω ε X c M hc hc6 hM hcM
  have sgdM := sgB Ω ε X d M hd hd6 hM hdM
  have key : ∀ x y : Row M, Ok x y →
      (Finset.univ.filter (fun x' => dn k M x' = x)).Nonempty ∧
      (Finset.univ.filter (fun y' => dn k M y' = y)).Nonempty ∧
      ∀ x' ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        ∀ y' ∈ Finset.univ.filter (fun y' => dn k M y' = y),
          IsPt X m (sg X c (k * M) x') (sg X d (k * M) y')
            (t (sg X c (k * M) x') (sg X d (k * M) y')) := by
    intro x y h
    obtain ⟨x₀, hx₀⟩ := hsurj x
    obtain ⟨y₀, hy₀⟩ := hsurj y
    refine ⟨⟨x₀, by simp [hx₀]⟩, ⟨y₀, by simp [hy₀]⟩, ?_⟩
    intro x' hx' y' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' hy'
    obtain ⟨hx0, hy0, -⟩ := hokL x' y' (hokdn x' y' (by rw [hx', hy']; exact h))
    exact (hsec _ _ (sgc x' hx0).1 (sgd y' hy0).1).1
  have hex : ∀ x y : Row M, ∃ R : Pt X m, Ok x y →
      IsSum X m (Finset.univ.filter (fun x' => dn k M x' = x))
        (Finset.univ.filter (fun y' => dn k M y' = y))
        (fun x' y' => t (sg X c (k * M) x') (sg X d (k * M) y')) R := by
    intro x y
    by_cases h : Ok x y
    · obtain ⟨R, hR⟩ := (sumB Ω ε X m hm _ _ _ _ (sg X c (k * M)) (sg X d (k * M)) _
        (key x y h).1 (key x y h).2.1 (key x y h).2.2).1
      exact ⟨R, fun _ => hR⟩
    · exact ⟨t (sg X c M x) (sg X d M y), fun h' => absurd h' h⟩
  choose Qs hQs using hex
  have hQpt : ∀ x y : Row M, Ok x y → IsPt X m (sg X c M x) (sg X d M y) (Qs x y) := by
    intro x y h
    obtain ⟨hx0, hy0, -⟩ := hokM x y h
    have hp := (sumB Ω ε X m hm _ _ _ _ (sg X c (k * M)) (sg X d (k * M)) _
      (key x y h).1 (key x y h).2.1 (key x y h).2.2).2 _ (hQs x y h)
    rwa [sgDist Ω ε X c k M hc hc6 hcL x hx0, sgDist Ω ε X d k M hd hd6 hdL y hy0] at hp
  have hfibgr : ∀ (s : Gal(Ω/ℚ)) (z : Row M),
      Set.BijOn (gr (k * M) s⁻¹) ↑(Finset.univ.filter (fun x' => dn k M x' = z))
        ↑(Finset.univ.filter (fun x' => dn k M x' = gr M s⁻¹ z)) := by
    intro s z
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [hgrdn, hi]
    · intro i _ j _ hij
      rw [← hinvL s i, hij, hinvL]
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      refine ⟨gr (k * M) s j, ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        rw [hgrdn, hj, hinvM]
      · have h1 := hinvL s⁻¹ j
        rwa [inv_inv] at h1
  have hQmv : ∀ (s : Gal(Ω/ℚ)) (x y : Row M), Ok x y →
      Mv X m (X.gal s) s (Qs (gr M s⁻¹ x) (gr M s⁻¹ y)) (Qs x y) (pushD X k M (w' s) x y) := by
    intro s x y h
    have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
    obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
    have hu : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        sg X c (k * M) i = X.gal s (sg X c (k * M) (gr (k * M) s⁻¹ i)) := by
      intro i hi
      have hm' := (hfibgr s x).1 hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      rw [(sgc _ (hnz _ _ hm' hx1)).2.2.1 s, hinvL]
    have hv : ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = y),
        sg X d (k * M) j = X.gal s (sg X d (k * M) (gr (k * M) s⁻¹ j)) := by
      intro j hj
      have hm' := (hfibgr s y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      rw [(sgd _ (hnz _ _ hm' hy1)).2.2.1 s, hinvL]
    have hf : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = y),
          Mv X m (X.gal s) s (t (sg X c (k * M) (gr (k * M) s⁻¹ i)) (sg X d (k * M) (gr (k * M) s⁻¹ j)))
            (t (sg X c (k * M) i) (sg X d (k * M) j)) (w' s i j) := by
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact (hsym' s i j (hokdn i j (by rw [hi, hj]; exact h))).2
    exact sumMv Ω ε X m hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ (gr (k * M) s⁻¹) (gr (k * M) s⁻¹)
      (X.gal s) s (hAgal s) (key _ _ h1).1 (key _ _ h1).2.1 (hfibgr s x) (hfibgr s y)
      (key _ _ h1).2.2 (key x y h).2.2 hu hv (hQs _ _ h1) (hQs x y h) (fun i j => w' s i j) hf
  have hfibrt : ∀ (γ : SL(2, ℤ)) (z : Row M),
      Set.BijOn (fun i : Row (k * M) => rt i γ⁻¹) ↑(Finset.univ.filter (fun x' => dn k M x' = rt z γ))
        ↑(Finset.univ.filter (fun x' => dn k M x' = z)) := by
    intro γ z
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [hrtdn, hi, rt_rt _ _ _ (mul_inv_cancel γ)]
    · intro i _ j _ hij
      have hij' : rt (rt i γ⁻¹) γ = rt (rt j γ⁻¹) γ := by
        simp only at hij
        rw [hij]
      rwa [rt_rt _ _ _ (inv_mul_cancel γ), rt_rt _ _ _ (inv_mul_cancel γ)] at hij'
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      refine ⟨rt j γ, ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        rw [hrtdn, hj]
      · exact rt_rt _ _ _ (mul_inv_cancel γ)
  have hQsl : ∀ (γ : SL(2, ℤ)) (x y : Row M), Ok x y →
      Mv X m (slR X (ofSL γ)) 1 (Qs x y) (Qs (rt x γ) (rt y γ)) 1 := by
    intro γ x y h
    have h1 : Ok (rt x γ) (rt y γ) := (hokM x y h).2.2.2 γ
    obtain ⟨hx0, hy0, -⟩ := hokM _ _ h
    have hu : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = rt x γ),
        sg X c (k * M) i = slR X (ofSL γ) (sg X c (k * M) (rt i γ⁻¹)) := by
      intro i hi
      have hm' := (hfibrt γ x).1 hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      have e1 := (sgc _ (hnz _ _ hm' hx0)).2.1 γ
      rw [rt_rt _ _ _ (inv_mul_cancel γ)] at e1
      exact e1.symm
    have hv : ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = rt y γ),
        sg X d (k * M) j = slR X (ofSL γ) (sg X d (k * M) (rt j γ⁻¹)) := by
      intro j hj
      have hm' := (hfibrt γ y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      have e1 := (sgd _ (hnz _ _ hm' hy0)).2.1 γ
      rw [rt_rt _ _ _ (inv_mul_cancel γ)] at e1
      exact e1.symm
    have hf : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = rt x γ),
        ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = rt y γ),
          Mv X m (slR X (ofSL γ)) 1 (t (sg X c (k * M) (rt i γ⁻¹)) (sg X d (k * M) (rt j γ⁻¹)))
            (t (sg X c (k * M) i) (sg X d (k * M) j)) ((fun _ _ => (1 : X.Kˣ)) i j) := by
      intro i hi j hj
      have hi' := (hfibrt γ x).1 hi
      have hj' := (hfibrt γ y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi' hj'
      have hi0 := hnz _ _ hi' hx0
      have hj0 := hnz _ _ hj' hy0
      have e := ((hsec _ _ (sgc _ hi0).1 (sgd _ hj0).1).2 γ)
      rw [(sgc _ hi0).2.1 γ, (sgd _ hj0).2.1 γ, rt_rt _ _ _ (inv_mul_cancel γ),
        rt_rt _ _ _ (inv_mul_cancel γ)] at e
      exact e
    have e := sumMv Ω ε X m hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun i : Row (k * M) => rt i γ⁻¹) (fun i : Row (k * M) => rt i γ⁻¹)
      (slR X (ofSL γ)) 1 (hAslR _) (key x y h).1 (key x y h).2.1 (hfibrt γ x) (hfibrt γ y)
      (key x y h).2.2 (key _ _ h1).2.2 hu hv (hQs x y h) (hQs _ _ h1) (fun _ _ => (1 : X.Kˣ)) hf
    simpa only [Finset.prod_const_one] using e
  obtain ⟨a, hcob, ha⟩ := cmp Ω ε X m M hm hM (sg X c M) (sg X d M) Qs
    (fun x y => t (sg X c M x) (sg X d M y)) (fun s => pushD X k M (w' s)) w
    (fun x y h => by
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      exact ⟨hQpt x y h, (hsec _ _ (sgcM x hx0).1 (sgdM y hy0).1).1⟩)
    (fun s x y h => by
      have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
      obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
      refine ⟨?_, ?_, hQmv s x y h, (hsym s x y h).2⟩
      · rw [(sgcM _ hx1).2.2.1 s, hinvM]
      · rw [(sgdM _ hy1).2.2.1 s, hinvM])
  refine ⟨a, fun x y h => ⟨(ha x y h).1, fun γ => ?_⟩, hcob⟩
  obtain ⟨hx0, hy0, -⟩ := hokM x y h
  have hT : Mv X m (slR X (ofSL γ)) 1 (t (sg X c M x) (sg X d M y))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) 1 := by
    have e := (hsec _ _ (sgcM x hx0).1 (sgdM y hy0).1).2 γ
    rwa [(sgcM x hx0).2.1 γ, (sgdM y hy0).2.1 γ] at e
  exact (ha x y h).2 (slR X (ofSL γ)) (rt x γ) (rt y γ) (hAslR _) ((hokM x y h).2.2.2 γ)
    ((sgcM x hx0).2.1 γ) ((sgdM y hy0).2.1 γ) (hQsl γ x y h) hT

end UpperTheory.V.Z.Kato.Sym

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PRed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CastVal
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_red (ε : Ω →+* ℂ) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    eOm ε (1 / ((k * m : ℕ) : ℚ)) ^ k = eOm ε (1 / (m : ℚ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  apply ε.injective
  rw [map_pow, eps_eOm, eps_eOm, ← Complex.exp_nat_mul]
  congr 1
  have h1 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have h2 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

private theorem zt_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) : zt X (k * m) ^ k = zt X m := by
  unfold zt
  rw [← map_pow, ← map_pow, eOm_red ε hk hm]

private theorem cast_val {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (i : ZMod (k * m)) :
    (ZMod.castHom (dvd_mul_left m k) (ZMod m) i).val = i.val % m := by
  haveI : NeZero (k * m) := ⟨(Nat.mul_pos hk hm).ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

private theorem lg_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {a b : Kb X} (hb : b ≠ 0)
    (h : a ^ (k * m) = b ^ (k * m)) :
    lg X m (a ^ k) (b ^ k) = ZMod.castHom (dvd_mul_left m k) (ZMod m) (lg X (k * m) a b) := by
  obtain ⟨-, hrep1, -, -, -, -, -⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  obtain ⟨hp2, -, huniq2, -, -, -, -⟩ := lgB Ω ε X m hm
  apply huniq2 _ _ _ (pow_ne_zero _ hb)
  rw [cast_val hk hm]
  have e : zt X m ^ (lg X (k * m) a b).val = zt X m ^ ((lg X (k * m) a b).val % m) := by
    conv_lhs => rw [← Nat.div_add_mod (lg X (k * m) a b).val m, pow_add, pow_mul, hp2.pow_eq_one,
      one_pow, one_mul]
  rw [← e, ← zt_red X hk hm, ← pow_mul, mul_comm k (lg X (k * m) a b).val, pow_mul, ← mul_pow,
    ← hrep1 a b hb h]

private theorem ka_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {θ : Kb X} {u : X.K} (hu : u ≠ 0)
    (hθ : θ ^ (k * m) = io X u) {h : RingAut (Kb X)} (hh : InD X h) :
    ka X m (θ ^ k) h = ZMod.castHom (dvd_mul_left m k) (ZMod m) (ka X (k * m) θ h) := by
  have h0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_pos hk hm).ne'] at hθ
    exact hu ((map_eq_zero _).1 hθ.symm)
  unfold ka
  rw [map_pow]
  exact lg_red X hk hm h0 (by rw [← map_pow, hθ, hh])

private theorem cyc_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (s : Ω ≃ₐ[ℚ] Ω) :
    cyc m s = ZMod.castHom (dvd_mul_left m k) (ZMod m) (cyc (k * m) s) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hp, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  obtain ⟨-, -, -, -, -, -, hcyc2⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  have hζ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m :=
    IsPrimitiveRoot.of_map_of_injective (f := (io X).comp (algebraMap Ω X.K)) hp
      (RingHom.injective _)
  have h1 : (eOm ε (1 / (m : ℚ))) ^ m = 1 := hζ.pow_eq_one
  have hA := (hcyc s s).2.2 _ h1
  have hB := (hcyc2 s s).2.2 _ (by rw [mul_comm, pow_mul, h1, one_pow])
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← hA, cast_val hk hm, hB]
  conv_lhs => rw [← Nat.div_add_mod (cyc (k * m) s).val m, pow_add, pow_mul, h1, one_pow, one_mul]

end

theorem UpperTheory.V.Z.Kato.Sym.redB :
    UpperTheory.V.Z.Kato.Sym.RedB := by
  intro Ω _ _ _ ε X k m hk hm
  have hkm := Nat.mul_pos hk hm
  refine ⟨fun u v P hP => ⟨hP.hu, hP.hv, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hP.ha, pow_mul]; rfl
  · rw [← hP.hb, pow_mul]; rfl
  · intro g h hg hh
    simp only [Pt.red]
    rw [ka_red X hk hm hP.hu.1 hP.ha hg, ka_red X hk hm hP.hv.1 hP.hb hh, ← map_mul, hP.cob g h hg hh, map_add (f := _), map_sub]
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B, fun h h' a b c => ?_⟩
    simp only [Pt.red]
    rw [hB h h' a b c]
  · intro B h a b c
    simp only [Pt.red]
    rw [hP.unr B h a b c, map_zero]
  · rintro τ s - u v P Q hP hQ f ⟨σ, hσ, θ, hθ, hd⟩
    refine ⟨σ, hσ, θ ^ k, by rw [← hθ, pow_mul], fun h hh => ?_⟩
    have nz : ∀ (a : Kb X) (w : X.K), w ≠ 0 → a ^ (k * m) = io X w → a ≠ 0 := by
      rintro a w hw ha rfl
      rw [zero_pow hkm.ne'] at ha
      exact hw ((map_eq_zero _).1 ha.symm)
    have ea : σ P.a ^ (k * m) = Q.a ^ (k * m) := by rw [← map_pow, hP.ha, hσ, hQ.ha]
    have eb : σ P.b ^ (k * m) = Q.b ^ (k * m) := by rw [← map_pow, hP.hb, hσ, hQ.hb]
    rw [ka_red X hk hm f.ne_zero hθ hh, hd h hh]
    simp only [dif, Pt.mv, Pt.red, map_add (f := _), map_sub, map_mul, map_pow]
    rw [ka_red X hk hm hQ.hu.1 hQ.ha hh, ka_red X hk hm hQ.hv.1 hQ.hb hh, lg_red X hk hm (nz _ _ hQ.hu.1 hQ.ha) ea,
      lg_red X hk hm (nz _ _ hQ.hv.1 hQ.hb) eb, cyc_red X hk hm s]
end

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

theorem pRed : PRed := by
  unfold PRed
  intro Ω _ _ _ ε X k m c d M hk hm hc hd hc6 hd6 hLv t' t w' w hsec' hsec hsym' hsym
  obtain ⟨hM, hcM, hdM⟩ := hLv
  have hkm : 0 < k * m := Nat.mul_pos hk hm
  obtain ⟨hAslR, hAgal, -⟩ := admB Ω ε X
  obtain ⟨hgrM, hokM, -⟩ := rowB Ω M hM
  obtain ⟨hred, hredmv⟩ := redB Ω ε X k m hk hm
  have hinvM : ∀ (s : Gal(Ω/ℚ)) (x : Row M), gr M s (gr M s⁻¹ x) = x := by
    intro s x
    rw [← (hgrM s s⁻¹ x).1, mul_inv_cancel, (hgrM 1 1 x).2]
  have sgc := sgB Ω ε X c M hc hc6 hM hcM
  have sgd := sgB Ω ε X d M hd hd6 hM hdM
  obtain ⟨a, hcob, ha⟩ := cmp Ω ε X m M hm hM (sg X c M) (sg X d M)
    (fun x y => Pt.red k m (t' (sg X c M x) (sg X d M y)))
    (fun x y => t (sg X c M x) (sg X d M y)) w' w
    (fun x y h => by
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      exact ⟨hred _ _ _ (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1,
        (hsec _ _ (sgc x hx0).1 (sgd y hy0).1).1⟩)
    (fun s x y h => by
      have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
      obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      have ex : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
        rw [(sgc _ hx1).2.2.1 s, hinvM]
      have ey : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
        rw [(sgd _ hy1).2.2.1 s, hinvM]
      refine ⟨ex, ey, ?_, (hsym s x y h).2⟩
      refine hredmv (X.gal s) s (hAgal s) _ _ _ _
        (hsec' _ _ (sgc _ hx1).1 (sgd _ hy1).1).1 ?_ _ (hsym' s x y h).2
      rw [ex, ey]
      exact (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1)
  refine ⟨a, fun x y h => ⟨(ha x y h).1, fun γ => ?_⟩, hcob⟩
  obtain ⟨hx0, hy0, -⟩ := hokM x y h
  have h1 : Ok (rt x γ) (rt y γ) := (hokM x y h).2.2.2 γ
  obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
  have hT : Mv X m (slR X (ofSL γ)) 1 (t (sg X c M x) (sg X d M y))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) 1 := by
    have e := (hsec _ _ (sgc x hx0).1 (sgd y hy0).1).2 γ
    rwa [(sgc x hx0).2.1 γ, (sgd y hy0).2.1 γ] at e
  have hR : Mv X m (slR X (ofSL γ)) 1 (Pt.red k m (t' (sg X c M x) (sg X d M y)))
      (Pt.red k m (t' (sg X c M (rt x γ)) (sg X d M (rt y γ)))) 1 := by
    have e := (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).2 γ
    rw [(sgc x hx0).2.1 γ, (sgd y hy0).2.1 γ] at e
    refine hredmv _ 1 (hAslR _) _ _ _ _ (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1 ?_ _ e
    have e1 : slR X (ofSL γ) (sg X c M x) = sg X c M (rt x γ) := (sgc x hx0).2.1 γ
    have e2 : slR X (ofSL γ) (sg X d M y) = sg X d M (rt y γ) := (sgd y hy0).2.1 γ
    rw [e1, e2]
    exact (hsec' _ _ (sgc _ hx1).1 (sgd _ hy1).1).1
  exact (ha x y h).2 (slR X (ofSL γ)) (rt x γ) (rt y γ) (hAslR _) h1
    ((sgc x hx0).2.1 γ) ((sgd y hy0).2.1 γ) hR hT

end UpperTheory.V.Z.Kato.Sym

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PSymb
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.pSymb :
    UpperTheory.V.Z.Kato.Sym.PSymb := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t ht
  unfold UpperTheory.V.Z.Kato.Sym.Lv at hL
  unfold UpperTheory.V.Z.Kato.Sym.IsSec at ht
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := UpperTheory.V.Z.Kato.Sym.rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := UpperTheory.V.Z.Kato.Sym.admB Ω ε X
  have key : ∀ (s : Gal(Ω/ℚ)) (x y : UpperTheory.V.Z.Kato.Sym.Row M), UpperTheory.V.Z.Kato.Sym.Ok x y →
      ∃ f ∈ X.Un m, UpperTheory.V.Z.Kato.Sym.Mv X m (X.gal s) s
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ x)) (UpperTheory.V.Z.Kato.Sym.sg X d M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ y)))
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y)) f := by
    intro s x y hxy
    obtain ⟨hx0, hy0, -⟩ := hok _ _ ((hok x y hxy).2.2.1 s⁻¹)
    have hsx := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM _ hx0
    have hsy := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM _ hy0
    have hP := (ht _ _ hsx.1 hsy.1).1
    have hx1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM x (hok x y hxy).1
    have hy1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM y (hok x y hxy).2.1
    have ex := UpperTheory.V.Z.Kato.Sym.mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ hP
    have ex1 := ex.1 (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y))
    rw [hsx.2.2.1, hsy.2.2.1, ← (hgr s s⁻¹ x).1, ← (hgr s s⁻¹ y).1, mul_inv_cancel, (hgr 1 1 x).2, (hgr 1 1 y).2] at ex1
    exact ex1 (ht _ _ hx1.1 hy1.1).1
  classical
  refine ⟨fun s x y => if h : UpperTheory.V.Z.Kato.Sym.Ok x y then Classical.choose (key s x y h) else 1, ?_⟩
  unfold UpperTheory.V.Z.Kato.Sym.IsSymb
  intro s x y hxy
  simp only [dif_pos hxy]
  exact Classical.choose_spec (key s x y hxy)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvCancel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtEx
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.ptEx :
    UpperTheory.V.Z.Kato.Sym.PtEx := by
  intro Ω _ _ _ ε X m hm u v hu hv
  have LG := lgB Ω ε X m hm
  have KU := PE.kaU Ω ε X m hm
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (io X u) hm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (io X v) hm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at ha
    exact hu0 ((map_eq_zero_iff _ (io X).injective).mp ha.symm)
  obtain ⟨η, hη, hlc, hunr⟩ := PE.etaEx Ω ε X m hm u v a b hu hv ha hb
  have hinU : ∀ g, InD X g → PE.InU X u v g := fun g hg => ⟨fun c => hg _, hg _, hg _, hg _⟩
  refine ⟨⟨a, b, η⟩, ⟨hu, hv, ha, hb, fun g h hg hh => hη g h (hinU g hg) (hinU h hh), hlc, hunr⟩, ?_⟩
  intro γ hu' hv'
  obtain ⟨σ, hσ⟩ := (admB Ω ε X).2.2.2.2.2.2.1 (slR X (ofSL γ))
  have hfix : ∀ f, X.sl (ofSL γ) f = f → σ (io X f) = io X f := fun f hf => by
    rw [hσ f]
    exact congrArg _ hf
  have hσU : PE.InU X u v σ :=
    ⟨fun c => hfix _ ((X.sl (ofSL γ)).commutes c), hfix _ (X.j_inv γ), hfix _ hu', hfix _ hv'⟩
  have hinv : ∀ x, σ x = x → σ⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    exact σ.symm_apply_apply x
  have hσiU : PE.InU X u v σ⁻¹ :=
    ⟨fun c => hinv _ (hσU.1 c), hinv _ hσU.2.1, hinv _ hσU.2.2.1, hinv _ hσU.2.2.2⟩
  have hz : ∀ g, PE.InU X u v g → g (zt X m) = zt X m := fun g hg => by
    unfold zt
    exact hg.1 _
  have hka1 : ka X m a 1 = 0 := by
    show lg X m a a = 0
    exact LG.2.2.1 a a 0 ha0 (by simp)
  have hk1 : ∀ g : RingAut (Kb X), ka X m 1 g = 0 := fun g => by
    show lg X m (g 1) 1 = 0
    rw [map_one]
    exact LG.2.2.1 1 1 0 one_ne_zero (by simp)
  have hcyc : cyc (Ω := Ω) m 1 = 1 := (LG.2.2.2.2.2.2 1 1).2.1
  have hη1 : η 1 = 0 := by
    have := hη 1 1 (hinU 1 (fun _ => rfl)) (hinU 1 (fun _ => rfl))
    rw [mul_one, hka1] at this
    linear_combination -this
  unfold Mv
  refine ⟨σ, hσ, ?_⟩
  simp only [IsKum, dif, Pt.mv]
  refine ⟨1, by simp, fun h hh => ?_⟩
  have hhU := hinU h hh
  have E1 := hη σ⁻¹ (h * σ) hσiU ⟨fun c => by show h (σ _) = _; rw [hσU.1 c, hhU.1 c], by show h (σ _) = _; rw [hσU.2.1, hhU.2.1], by show h (σ _) = _; rw [hσU.2.2.1, hhU.2.2.1], by show h (σ _) = _; rw [hσU.2.2.2, hhU.2.2.2]⟩
  have E2 := hη h σ hhU hσU
  have E3 := hη σ⁻¹ σ hσiU hσU
  rw [inv_mul_cancel, hη1] at E3
  have K1 := (KU b (by rintro rfl; rw [zero_pow hm.ne'] at hb; exact hv.1 ((map_eq_zero_iff _ (io X).injective).mp hb.symm)) h σ (hz h hhU) (hz σ hσU) (by rw [hb]; exact hhU.2.2.2) (by rw [hb]; exact hσU.2.2.2)).1
  have K2 := (KU a ha0 σ⁻¹ σ (hz _ hσiU) (hz σ hσU) (by rw [ha]; exact hσiU.2.2.1) (by rw [ha]; exact hσU.2.2.1)).1
  rw [inv_mul_cancel, hka1] at K2
  rw [hk1, hcyc, mul_assoc]
  show 0 = 1 ^ 2 * η (σ⁻¹ * (h * σ)) - η h + ka X m a h * ka X m b σ - ka X m a σ * ka X m b h
  linear_combination (-1 : ZMod m) * E1 - E2 + E3 + ka X m a σ⁻¹ * K1 - ka X m b h * K2
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m : ℕ}

omit [IsAlgClosure ℚ Ω] in
private theorem sl_sl (γ δ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
  rw [map_mul, X.sl_mul]

omit [IsAlgClosure ℚ Ω] in
private theorem sl_inv (γ : SL(2, ℤ)) (f : X.K) : X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) f) = f := by
  rw [← sl_sl, mul_inv_cancel, map_one, X.sl_one]

private theorem mv_comp (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R) {f : X.Kˣ}
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL δ)) 1 Q R f) :
    Mv X m (slR X (ofSL (γ * δ))) 1 P R f := by
  have key := mvComp Ω ε X m hm (slR X (ofSL γ)) (slR X (ofSL δ)) 1 1 ((admB Ω ε X).1 _)
    ((admB Ω ε X).1 _) u v P Q R hP hQ hR 1 f h1 h2
  have he : (slR X (ofSL γ)).trans (slR X (ofSL δ)) = slR X (ofSL (γ * δ)) := by
    ext x
    show X.sl (ofSL δ) (X.sl (ofSL γ) x) = X.sl (ofSL (γ * δ)) x
    exact (sl_sl X γ δ x).symm
  rw [he, mul_one, map_one, one_pow, one_mul] at key
  exact key

private theorem mv_cancel (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R)
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL (γ * δ))) 1 P R 1) :
    Mv X m (slR X (ofSL δ)) 1 Q R 1 := by
  have hA := admB Ω ε X
  obtain ⟨f, -, hf⟩ := (mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).1 R hR
  have h3 := mv_comp X hm γ δ hP hQ hR h1 hf
  have hR' : IsPt X m (X.sl (ofSL (γ * δ)) u) (X.sl (ofSL (γ * δ)) v) R := by
    rw [sl_sl X γ δ u, sl_sl X γ δ v]
    exact hR
  obtain ⟨k, hk⟩ := ((mvEx Ω ε X m hm (slR X (ofSL (γ * δ))) 1 (hA.1 _) u v P hP).2.2.2
    R hR' 1 f h2).mp h3
  refine ((mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).2.2.2 R hR f 1 hf).mpr ⟨k⁻¹, ?_⟩
  rw [hk, one_mul, inv_pow, mul_inv_cancel]

omit [IsAlgClosure ℚ Ω] in
private theorem rep_ex : ∃ (r : X.K × X.K → X.K × X.K) (g : X.K × X.K → SL(2, ℤ)),
    (∀ p, X.sl (ofSL (g p)) (r p).1 = p.1 ∧ X.sl (ofSL (g p)) (r p).2 = p.2) ∧
    ∀ (p : X.K × X.K) (γ : SL(2, ℤ)), r (X.sl (ofSL γ) p.1, X.sl (ofSL γ) p.2) = r p := by
  let S : Setoid (X.K × X.K) :=
    { r := fun p q => ∃ g : SL(2, ℤ), X.sl (ofSL g) p.1 = q.1 ∧ X.sl (ofSL g) p.2 = q.2
      iseqv := ⟨fun p => ⟨1, by rw [map_one, X.sl_one], by rw [map_one, X.sl_one]⟩,
        fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, sl_inv], by rw [← h2, sl_inv]⟩,
        fun ⟨g, h1, h2⟩ ⟨k, k1, k2⟩ => ⟨g * k, by rw [sl_sl, h1, k1], by rw [sl_sl, h2, k2]⟩⟩ }
  refine ⟨fun p => (Quotient.mk S p).out, fun p => Classical.choose (Quotient.mk_out (s := S) p),
    fun p => Classical.choose_spec (Quotient.mk_out (s := S) p), fun p γ => ?_⟩
  show (Quotient.mk S _).out = (Quotient.mk S p).out
  rw [Quotient.sound (s := S) ⟨γ⁻¹, sl_inv X γ p.1, sl_inv X γ p.2⟩]

end

theorem UpperTheory.V.Z.Kato.Sym.secEx :
    UpperTheory.V.Z.Kato.Sym.SecEx := by
  intro Ω _ _ _ ε X m hm
  obtain ⟨r, g, hg, hr⟩ := rep_ex X
  have hA := admB Ω ε X
  haveI : Nonempty (Pt X m) := ⟨⟨0, 0, fun _ => 0⟩⟩
  have hUsl : ∀ (γ : SL(2, ℤ)) (a : X.K), IsU X a → IsU X (X.sl (ofSL γ) a) :=
    fun γ a ha => (hA.2.2.2.2.2.1 _ _ (hA.1 (ofSL γ))).1 a ha
  let Good : X.K → X.K → Pt X m → Prop := fun a b P => IsPt X m a b P ∧
    ∀ γ : SL(2, ℤ), X.sl (ofSL γ) a = a → X.sl (ofSL γ) b = b → Mv X m (slR X (ofSL γ)) 1 P P 1
  let P0 : X.K → X.K → Pt X m := fun a b => Classical.epsilon (Good a b)
  have hP0 : ∀ a b, IsU X a → IsU X b → Good a b (P0 a b) :=
    fun a b ha hb => Classical.epsilon_spec (ptEx Ω ε X m hm a b ha hb)
  have hrep : ∀ a b, X.sl (ofSL (g (a, b))) (r (a, b)).1 = a ∧
      X.sl (ofSL (g (a, b))) (r (a, b)).2 = b := fun a b => hg (a, b)
  have hrU : ∀ a b, IsU X a → IsU X b → IsU X (r (a, b)).1 ∧ IsU X (r (a, b)).2 := by
    intro a b ha hb
    have e1 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).1
    have e2 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).2
    simp only [sl_inv] at e1 e2
    rw [e1, e2]
    exact ⟨hUsl _ a ha, hUsl _ b hb⟩
  let t : X.K → X.K → Pt X m := fun a b => Classical.epsilon (fun Q => IsPt X m a b Q ∧
    Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1)
  have ht : ∀ a b, IsU X a → IsU X b → IsPt X m a b (t a b) ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) (t a b) 1 := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := hrU a b ha hb
    obtain ⟨Q, hQ, hM⟩ := (mvEx Ω ε X m hm (slR X (ofSL (g (a, b)))) 1 (hA.1 _) _ _ _
      (hP0 _ _ h1 h2).1).2.1
    change IsPt X m (X.sl (ofSL (g (a, b))) (r (a, b)).1)
      (X.sl (ofSL (g (a, b))) (r (a, b)).2) Q at hQ
    rw [(hrep a b).1, (hrep a b).2] at hQ
    exact Classical.epsilon_spec (p := fun Q => IsPt X m a b Q ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1) ⟨Q, hQ, hM⟩
  refine ⟨t, fun u v hu hv => ⟨(ht u v hu hv).1, fun γ => ?_⟩⟩
  have hu' := hUsl γ u hu
  have hv' := hUsl γ v hv
  have hrr : r (X.sl (ofSL γ) u, X.sl (ofSL γ) v) = r (u, v) := hr (u, v) γ
  obtain ⟨hQt, hMa⟩ := ht u v hu hv
  obtain ⟨hRt, hMb⟩ := ht _ _ hu' hv'
  obtain ⟨q1, q2⟩ := hrU u v hu hv
  have hgood := hP0 _ _ q1 q2
  obtain ⟨e1, e2⟩ := hrep u v
  obtain ⟨f1, f2⟩ := hrep (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)
  rw [hrr] at hMb f1 f2
  have hs1 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).1
      = (r (u, v)).1 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e1]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).1
    rw [f1] at k
    exact k
  have hs2 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).2
      = (r (u, v)).2 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e2]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).2
    rw [f2] at k
    exact k
  have stab := hgood.2 _ hs1 hs2
  have comp := mv_comp X hm _ (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) hgood.1
    (by rw [hs1, hs2]; exact hgood.1) (by rw [hs1, hs2, f1, f2]; exact hRt) stab hMb
  rw [inv_mul_cancel_right] at comp
  exact mv_cancel X hm (g (u, v)) γ hgood.1 (by rw [e1, e2]; exact hQt)
    (by rw [e1, e2]; exact hRt) hMa comp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PLev
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

theorem pLev : PLev := by
  unfold PLev
  intro Ω _ _ _ ε X m c d k M hm hc hd hc6 hd6 hlv t w' w ht hw' hw
  obtain ⟨hkM, hck, hdk⟩ := hlv
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  obtain ⟨-, hgal, -, -, -, -, -, hUn⟩ := admB Ω ε X
  obtain ⟨hgr, hok, -, hup⟩ := rowB Ω M hM
  obtain ⟨-, hokK, -, -⟩ := rowB Ω (k * M) hkM
  obtain ⟨hupQ, hupOk, hupgr, -⟩ := hup k hk
  have hsgup : ∀ e : ℕ, 1 < e → e.Coprime 6 → e.Coprime (k * M) → ∀ z : Row M, z ≠ 0 →
      up k M z ≠ 0 → sg X e (k * M) (up k M z) = sg X e M z := by
    intro e he he6 hek z hz hz'
    have hem : e.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hek
    rw [← (sgB Ω ε X e (k * M) he he6 hkM hek (up k M z) hz').2.2.2 (toQ M z)
      (fun i => ⟨0, by simp [hupQ z]⟩)]
    exact (sgB Ω ε X e M he he6 hM hem z hz).2.2.2 (toQ M z) (fun i => ⟨0, by simp⟩)
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hck
  have hdM : d.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hdk
  unfold Coh Eqv CobBy
  refine ⟨fun _ _ => (1 : X.Kˣ), ?_, ?_⟩
  · intro x y _
    refine ⟨(hUn m).1, fun γ => ⟨1, by simp [slU]⟩⟩
  · intro s x y hxy
    have hxy1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hok x y hxy).2.2.1 s⁻¹
    have hupxy := hupOk x y hxy
    have hupxy1 := hupOk _ _ hxy1
    have hx := (hok x y hxy).1
    have hy := (hok x y hxy).2.1
    have hx1 := (hok _ _ hxy1).1
    have hy1 := (hok _ _ hxy1).2.1
    have hux := (hokK _ _ hupxy).1
    have huy := (hokK _ _ hupxy).2.1
    have hux1 := (hokK _ _ hupxy1).1
    have huy1 := (hokK _ _ hupxy1).2.1
    obtain ⟨-, hwMv⟩ := hw s x y hxy
    obtain ⟨-, hw'Mv⟩ := hw' s (up k M x) (up k M y) hupxy
    rw [hupgr s⁻¹ x, hupgr s⁻¹ y, hsgup c hc hc6 hck _ hx1 hux1, hsgup d hd hd6 hdk _ hy1 huy1,
      hsgup c hc hc6 hck _ hx hux, hsgup d hd hd6 hdk _ hy huy] at hw'Mv
    have hgx : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
      intro z
      rw [← (hgr s s⁻¹ z).1, mul_inv_cancel, (hgr 1 1 z).2]
    have hτu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
      rw [(sgB Ω ε X c M hc hc6 hM hcM _ hx1).2.2.1 s, hgx]
    have hτv : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
      rw [(sgB Ω ε X d M hd hd6 hM hdM _ hy1).2.2.1 s, hgx]
    have hP := (ht (sg X c M (gr M s⁻¹ x)) (sg X d M (gr M s⁻¹ y))
      (sgB Ω ε X c M hc hc6 hM hcM _ hx1).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy1).1).1
    have hQ := (ht (sg X c M x) (sg X d M y)
      (sgB Ω ε X c M hc hc6 hM hcM _ hx).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy).1).1
    have key := (mvEx Ω ε X m hm (X.gal s) s (hgal s) _ _ _ hP).2.2.2 _
      (by rw [hτu, hτv]; exact hQ) _ (w' s (up k M x) (up k M y)) hwMv
    have htw : tw X m M s (fun _ _ => (1 : X.Kˣ)) x y = 1 := by simp [tw]
    rw [htw, mul_one, div_one]
    exact key.1 hw'Mv

end UpperTheory.V.Z.Kato.Sym

end
end

namespace UpperTheory.V.Z.Kato.Sym

theorem symEx : SymEx := symEx_of secEx pSymb pCoc pRed pLev pDist pIsog pTop

end UpperTheory.V.Z.Kato.Sym
