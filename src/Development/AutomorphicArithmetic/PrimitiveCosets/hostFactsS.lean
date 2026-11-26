module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.hostFactsS
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private lemma inPhi_of_jac {φ : Frame} (H : HostAx φ) (u : (ZMod H.toHostRaw.condN)ˣ) (k : ℕ)
    (hk : (u : ZMod H.toHostRaw.condN).val ≡ k [MOD H.d]) (hj : jacobiSym (k : ℤ) H.d = 1) :
    Formalism.D5.InPhi (Multiplicative.toAdd (recH H.toHostRaw u)) := by
  have h1 : ((H.toHostRaw.art u).1.2 : ℤ) = 1 := by
    rw [H.der.art_ch u, jacobi_congr hk, hj]
  have h2 : (H.toHostRaw.art u).1.2 = 1 := Units.ext h1
  show Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.toHostRaw.art u).1.2) = 0
  rw [Formalism.LFunctionChainParameters.LHost.sgn2_toAdd_eq_zero_iff]
  exact h2

private lemma jac_of_dvd {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    jacobiSym (p : ℤ) H.d = 1 := by
  have hd4 := H.d_mod_four
  rcases (H.dvd_QSq_iff hp).mp h with hQ | rfl
  · by_cases h2 : p = 2
    · subst h2
      exact jac_two_d H.hyp
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
      rw [← jacobi_neg_recip hd4 hodd]
      exact H.QS_split p hp h2 hQ
  · have hodd : H.q % 2 = 1 := by
      have := H.hyp.2.2.1
      omega
    rw [← jacobi_neg_recip hd4 hodd]
    exact H.hyp.2.2.2.2

private lemma d_dvd_ordCompl {φ : Frame} (H : HostRaw φ) {p : ℕ} (hp : p.Prime) (h : p ∣ H.QS * H.q) :
    H.d ∣ ordCompl[p] H.condN := by
  apply Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
  intro hpd
  have hpe : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp hpd
  exact H.d_not_dvd_QSq (hpe ▸ h)

private lemma toE_iod' (φ : Frame) : Multiplicative.toAdd (toE φ φ.iod) = sgc0 := by
  rw [(toE_bij φ).2.1]
  rfl

private theorem hostFactsS_pf :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (H.QS * H.q).primeFactors := by
  intro φ H
  haveI : NeZero H.toHostRaw.condN := ⟨H.toHostRaw.condN_ne_zero⟩
  have hQq0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
  refine
    { d_prime := H.d_prime
      two_mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_of_dvd_left H.two_dvd_QS _, hQq0⟩
      q1_mem := Nat.mem_primeFactors.mpr ⟨H.q_prime, dvd_mul_left _ _, hQq0⟩
      d_not_mem := fun hm => H.d_not_dvd_QSq (Nat.dvd_of_mem_primeFactors hm)
      unram := ?_
      split_inertia := ?_
      split_frob := ?_
      inertia_d := ?_ }
  · intro p hp hpS hpd
    have hpN : ¬ p ∣ H.toHostRaw.condN := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
      · exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h1, hQq0⟩)
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).mp h1)
    have hloc := (unramified_spec _ p H.toHostRaw.condN_ne_zero hp hpN).1
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [hloc, Subgroup.mem_bot] at hu
    subst hu
    simp
  · intro p hpS x hx
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff H.q H.d (recH H.toHostRaw) p x).mp hx
    rw [mem_localUnits_iff] at hu
    exact inPhi_of_jac H u 1 (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hu) (by simp)
  · intro p hpS
    have hp := Nat.prime_of_mem_primeFactors hpS
    have hdvd := Nat.dvd_of_mem_primeFactors hpS
    have hf := (frobUnit_modEq (N := H.toHostRaw.condN) hp).1
    exact inPhi_of_jac H _ p (Nat.ModEq.of_dvd (d_dvd_ordCompl H.toHostRaw hp hdvd) hf)
      (jac_of_dvd H.toHostRaw hp hdvd)
  · intro x
    have hparts := parts_of_eq (N := H.toHostRaw.condN) (k := 1) (m := H.QS * H.q) H.d_prime
      (by show H.QS * H.q * H.d = _; ring) H.d_not_dvd_QSq hQq0
    refine (mem_inertia_iff H.q H.d (recH H.toHostRaw) H.d x).trans ?_
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [mem_localUnits_iff, hparts.2] at hu
      rcases H.art_d u hu with h | h
      · left
        simp [recH, h]
      · right
        show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
        rw [h]
        exact toE_iod' φ
    · rintro (rfl | rfl)
      · exact ⟨1, Subgroup.one_mem _, by simp⟩
      · obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (N := H.toHostRaw.condN) (a := H.QS * H.q) (b := H.d)
          rfl H.coprime_QSq_d (dvd_mul_right _ _) H.d_dvd_condN 1 (-1)
        have hloc : (u : ZMod H.toHostRaw.condN).val ≡ 1 [MOD H.QS * H.q] :=
          (unitsMap_eq_one_iff _ u).mp hu1
        refine ⟨u, ?_, ?_⟩
        · rw [mem_localUnits_iff, hparts.2]
          exact hloc
        · have hcast : (((u : ZMod H.toHostRaw.condN).val : ℤ) : ZMod H.d) = ((-1 : ℤ) : ZMod H.d) := by
            have h3 := congrArg (fun v : (ZMod H.d)ˣ => (v : ZMod H.d)) hu2
            simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
              Units.val_neg, Units.val_one] at h3
            push_cast
            rw [ZMod.natCast_val]
            exact h3
          rw [ZMod.intCast_eq_intCast_iff] at hcast
          have hjac : ((H.toHostRaw.art u).1.2 : ℤ) = -1 := by
            rw [H.der.art_ch u, jacobiSym.mod_left,
              show (((u : ZMod H.toHostRaw.condN).val : ℕ) : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) from hcast,
              ← jacobiSym.mod_left, jacobiSym.at_neg_one (H.d_prime.odd_of_ne_two H.d_ne_two),
              ZMod.χ₄_nat_three_mod_four H.d_mod_four]
          rcases H.art_d u hloc with h | h
          · exfalso
            rw [h] at hjac
            simp at hjac
          · show Multiplicative.toAdd (toE φ (H.toHostRaw.art u)) = sgc0
            rw [h]
            exact toE_iod' φ

theorem UpperTheory.Comparison₂.hostFactsS :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (insert H.q H.small) := by
  intro φ H
  have hset : insert H.q H.small = (H.QS * H.q).primeFactors := by
    rw [Nat.primeFactors_mul H.QS_ne_zero H.q_prime.ne_zero, H.q_prime.primeFactors]
    show insert H.q H.QS.primeFactors = _
    ext a
    simp [or_comm]
  rw [hset]
  exact hostFactsS_pf φ H
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.CardPsiA
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem exists_comp_eq {G Q M : Type} [AddCommGroup G] [AddCommGroup Q] [CommGroupWithZero M] (π : G →+ Q)
    (hπ : Function.Surjective π) (ψ : AddChar G M) (h : ∀ x, π x = 0 → ψ x = 1) :
    ∃ χ : AddChar Q M, χ.compAddMonoidHom π = ψ := by
  have wd : ∀ x y, π x = π y → ψ x = ψ y := by
    intro x y hxy
    have h0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    calc ψ x = ψ (y + (x - y)) := by rw [add_sub_cancel]
      _ = ψ y * ψ (x - y) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ y := by rw [h _ h0, mul_one]
  let s := Function.surjInv hπ
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
  refine ⟨{ toFun := fun q => ψ (s q), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
  · intro a b
    rw [← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add (f := _), hs, hs])]
  · ext x
    exact wd _ _ (hs _)

private theorem card_PsiA_index {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (A0 : AddSubgroup H) :
    (PsiA A0).card = 4 * A0.index := by
  classical
  let π : E0 × H →+ E0 × (H ⧸ A0) := (AddMonoidHom.id E0).prodMap (QuotientAddGroup.mk' A0)
  have hπ : Function.Surjective π := by
    rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective A0 q
    exact ⟨(a, b), rfl⟩
  have inj : Function.Injective (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    intro χ1 χ2 h
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    exact DFunLike.congr_fun h x
  have himg : PsiA A0 = Finset.univ.image (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    ext ψ
    simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine exists_comp_eq π hπ ψ fun x hx => ?_
      obtain ⟨a, b⟩ := x
      have ha : a = 0 := congrArg Prod.fst hx
      have hb : (QuotientAddGroup.mk' A0 b) = 0 := congrArg Prod.snd hx
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hb
      subst ha
      exact h b hb
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π (0, s)) = 1
      have : π (0, s) = 0 := by
        simp [π, QuotientAddGroup.eq_zero_iff, hs]
      rw [this, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ inj, Finset.card_univ, AddChar.card_eq, Fintype.card_prod,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  simp [E0]

theorem UpperTheory.Comparison₂.card_PsiA :
    ∀ φ : Frame, (PsiA φ.A0).card = 4 * φ.o := by
  intro φ
  rw [card_PsiA_index, φ.index_A0_eq_o]
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.prim_read_dir (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    H.dir (chr φ ψ) = dirChar (recH H) ψ := by
  refine MulChar.ext fun u => ?_
  rw [H.dir_unit, dirChar_unit]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_surj (φ : Frame) : Function.Surjective (toE φ) := by
  have key : ∀ a : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = a := by
    intro a
    fin_cases a
    · exact ⟨1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
    · exact ⟨-1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
  intro x
  obtain ⟨s1, hs1⟩ := key (Multiplicative.toAdd x).1.1
  obtain ⟨s2, hs2⟩ := key (Multiplicative.toAdd x).1.2
  refine ⟨((s2, s1), Multiplicative.ofAdd (Multiplicative.toAdd x).2), ?_⟩
  simp only [toE, MonoidHom.coe_mk, OneHom.coe_mk, hs1, hs2]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_max (y : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hfl : 0 < ⌊y⌋₊ := by omega
  have hy : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have h1y : 1 ≤ y / n := (one_le_div hpos).mpr hny
  exact max_eq_left (by linarith)

private theorem UpperTheory.Comparison₂.prim_read_Gz (y : ℝ) : Gz y = An.G y := by
  unfold Gz Sz An.G
  rw [Finset.sum_congr rfl fun n hn => congrArg (fun t => An.abelian₂ n * t) (UpperTheory.Comparison₂.prim_read_max y n hn)]
  ring

private theorem UpperTheory.Comparison₂.prim_read_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem UpperTheory.Comparison₂.prim_read :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by
  intro φ H ell hell ψ
  unfold HostAddCharCompatible at hell
  set R := H.toHostRaw with hR
  have hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ := prim_read_dir φ R ψ
  have hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n := by
    intro n hn
    show (R.dir (chr φ ψ)).primitiveCharacter n = _
    rw [hdir]
    exact (primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n
      (HostRaw.condN_pos R).ne' hn).symm
  have h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ := fun hψ =>
    @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval
  have hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0 := by
    show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0
    rw [prim_read_one, hdir]
    constructor
    · intro h
      rw [AddChar.eq_zero_iff]
      intro x
      obtain ⟨g, hg⟩ := prim_read_surj φ (Multiplicative.ofAdd x)
      obtain ⟨u, hu⟩ := HostDer.art_surj H.der g
      have hu1 : (dirChar (recH R) ψ) u = 1 := by
        rw [h]
        exact MulChar.one_apply_coe u
      rw [dirChar_unit] at hu1
      have e : recH R u = Multiplicative.ofAdd x := by
        show toE φ (R.art u) = _
        rw [hu, hg]
      rwa [e, toAdd_ofAdd] at hu1
    · rintro rfl
      refine MulChar.ext fun u => ?_
      rw [dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]
  refine ⟨h1, fun y => ?_⟩
  by_cases hψ : ψ = 0
  · have hχ : (R.prim (chr φ ψ)).χ = 1 := hone.mpr hψ
    unfold GPsi An.gChi
    rw [if_pos hψ, if_pos hχ, prim_read_Gz]
  · have hχ : (R.prim (chr φ ψ)).χ ≠ 1 := fun h => hψ (hone.mp h)
    unfold GPsi An.gChi
    rw [if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hval n hn0, prim_read_max y n hn]
end
