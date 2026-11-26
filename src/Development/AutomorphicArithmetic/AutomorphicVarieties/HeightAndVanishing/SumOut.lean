module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.RedPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.redPrime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ H.index →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, Vlen Ω c e ψ := by
  intro E _ _ _ N _ H hH l _ hl2 hlH c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨σ, hσ, hplus, -⟩ := Chr.partModel E N H hH l c.O Ω' D Ω e
  haveI hroots : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    have hdvd : Monoid.exponent ((ZMod N)ˣ ⧸ H) ∣ Nat.totient N := by
      refine Group.exponent_dvd_nat_card.trans ?_
      rw [← Subgroup.index_eq_card, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
      exact Subgroup.index_dvd_card H
    exact HasEnoughRootsOfUnity.of_dvd c.O hdvd
  rw [hplus]
  refine (Chr.signLe Ω N H l c.O hl2 e e σ hσ T (by rw [hT])).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hχ' : χ ∈ Chr.evenSet c.O H e := by
    have : χ ∈ (T : Set _) := hχ
    rwa [hT] at this
  have hker : H ≤ (MulChar.toUnitHom χ).ker := hχ'.1
  obtain ⟨hopen, -⟩ := Chr.clsFacts ℚ Ω N
  have hsurj := (Chr.clsOnto Ω N).1
  have hUopen : IsOpen ((Chr.levH ℚ Ω H : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ hopen
    intro g hg
    show Chr.cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.mp hg]
    exact H.one_mem
  have hUker : Chr.levH ℚ Ω H ≤ (Chr.dirG ℚ Ω χ).ker := by
    intro g hg
    exact hker hg
  have hidx : (Chr.levH ℚ Ω H).index = H.index :=
    Subgroup.index_comap_of_surjective H hsurj
  have hHidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Chr.eigV ℚ Ω l c.O e (Chr.dirG ℚ Ω χ) (Chr.levH ℚ Ω H) hUopen hUker (by rwa [hidx])]
  have hψopen : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono hUker hUopen
  have hpow : Chr.dirG ℚ Ω χ ^ H.index = 1 := by
    refine MonoidHom.ext fun g => ?_
    have hm : (Chr.cls ℚ Ω N g) ^ H.index ∈ H := Subgroup.pow_index_mem H _
    have := hker hm
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    exact this
  exact ((Chr.vLe Ω l c.O N e H.index (Chr.dirG ℚ Ω χ) (NeZero.ne N) he hHidx hψopen hpow).2 hlH)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem exists_closure : ∃ (Q : Type) (_ : Field Q) (_ : CharZero Q), IsAlgClosure ℚ Q := by
  refine ⟨AlgebraicClosure ℚ, inferInstance, inferInstance,
    (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).2 ⟨inferInstance, ?_⟩⟩
  have h := AlgebraicClosure.isAlgebraic ℚ
  convert h using 1

private theorem card_small (S : Finset Nat.Primes) (n : ℕ) (h : ∀ l ∈ S, (l : ℕ) ≤ n) : S.card ≤ n := by
  have key : S.card ≤ (Finset.Icc 1 n).card := by
    apply Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l : ℕ))
    · intro l hl
      have h1 := h l hl
      have h2 := l.2.one_lt
      simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_Icc, Finset.mem_coe]
      omega
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  simpa using key

private theorem final_le (M t : ℝ) (a b : ℕ) (hM : 2 ≤ M) (ht : t ≤ M) :
    t * (M ^ a + 2 * M * M ^ b) ≤ M ^ (a + b + 4) := by
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hpos : 0 ≤ M ^ a + 2 * M * M ^ b := by positivity
  have h1 : t * (M ^ a + 2 * M * M ^ b) ≤ M * (M ^ a + 2 * M * M ^ b) :=
    mul_le_mul_of_nonneg_right ht hpos
  have hA : M ^ (a + 1) ≤ M ^ (a + b + 3) := pow_le_pow_right₀ hM1 (by omega)
  have hB : M ^ (b + 2) ≤ M ^ (a + b + 2) := pow_le_pow_right₀ hM1 (by omega)
  have hY : 0 ≤ M ^ (a + b + 2) := by positivity
  have hX : 0 ≤ M ^ (a + b + 3) := by positivity
  have eX : M ^ (a + b + 3) = M * M ^ (a + b + 2) := by ring
  have e4 : M ^ (a + b + 4) = M * M ^ (a + b + 3) := by ring
  have eL : M * (M ^ a + 2 * M * M ^ b) = M ^ (a + 1) + 2 * M ^ (b + 2) := by ring
  have k1 : 0 ≤ (M - 2) * M ^ (a + b + 2) := mul_nonneg (by linarith) hY
  have k2 : 0 ≤ (M - 1) * M ^ (a + b + 3) := mul_nonneg (by linarith) hX
  rw [e4]
  nlinarith

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.HV.sumOut :
    CountI → CountZ → CountII → CountIII → SumOut := by
  classical
  intro hI hZ hII hIII χ
  obtain ⟨C1, r₁, r₂, hr₁, hr₂, hI⟩ := hI χ
  obtain ⟨CZ, hZ⟩ := hZ χ
  obtain ⟨C2, hII⟩ := hII χ
  obtain ⟨C3, hIII⟩ := hIII χ
  refine ⟨C1 + 3 * max CZ (max C2 C3) + 4, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ hq1 hd hq1' hd' t ht2 hbig E _ _ _ hE Ω _ _ _ ld S hS
  subst hχ
  obtain ⟨Ω0, iF, iC, iA⟩ := exists_closure
  set K := max CZ (max C2 C3) with hK
  have hN1 : (1:ℝ) ≤ (h.N : ℝ) := by exact_mod_cast h.N_pos
  have ht2' : (2:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht2
  set M : ℝ := (h.N : ℝ) * t with hM
  have hM2 : 2 ≤ M := by nlinarith
  have htM : (t:ℝ) ≤ M := by nlinarith
  have hNM : (h.N:ℝ) ≤ M := by nlinarith
  haveI : NeZero h.N.totient := ⟨(Nat.totient_pos.2 h.N_pos).ne'⟩
  choose c hc using fun l : Nat.Primes => exists_coef (l : ℕ) h.N.totient
  have hfacts := fun (l : Nat.Primes) (hl : l ∈ S) =>
    (bchiFacts h t hbig).2.2.2.2 (l:ℕ) l.2 (hS l hl).1 (hS l hl).2
  have hother : ∀ l ∈ S, ∀ e, 0 < e → e < t → ¬ h.CaseI (l:ℕ) e →
      ∀ ψ ∈ h.X (c l) e, VLe Ω0 (c l) e ψ (M ^ (3 * K)) := by
    intro l hl e he1 he2 hn ψ hψ
    have hl2 := (hS l hl).1
    have hlB := (hS l hl).2
    have hchar := ((Host.mem_X h).1 hψ).1
    have hc4 := ((UpperTheory.V.HV.cases h t hbig (↥(c l).O) ψ hchar (l:ℕ) e l.2 hl2 he1 he2).1 hlB).2.2.2.2.2
    have hdv : (l:ℕ) - 1 ∣ 2 * e := by
      simp only [Host.CaseI, not_and, not_not] at hn
      exact hn hlB
    have hle := (hfacts l hl).2.2.2.2.2.2.2 e he1 he2 hdv
    have hl' : ((l:ℕ):ℝ) ≤ 2 * t := by exact_mod_cast hle.2.1
    have he' : (e:ℝ) ≤ t := by exact_mod_cast he2.le
    have hl1 : (1:ℝ) ≤ (l:ℕ) := by exact_mod_cast l.2.one_lt.le
    have he1' : (1:ℝ) ≤ e := by exact_mod_cast he1
    have hbase1 : (1:ℝ) ≤ ((l:ℕ):ℝ) * h.N * e := by
      have a1 := mul_le_mul hl1 hN1 zero_le_one (by positivity)
      have a2 := mul_le_mul a1 he1' zero_le_one (by positivity)
      simpa using a2
    have hbase : ((l:ℕ):ℝ) * h.N * e ≤ M ^ 3 := by
      have a1 : ((l:ℕ):ℝ) * h.N ≤ (2 * t) * h.N := mul_le_mul_of_nonneg_right hl' (by positivity)
      have a2 : ((l:ℕ):ℝ) * h.N * e ≤ (2 * t) * h.N * t :=
        mul_le_mul a1 he' (by positivity) (by positivity)
      have hM0 : 0 ≤ M := by linarith
      have a4 : 2 * M * t ≤ M * M * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM2 hM0) (by positivity)
      have a5 : M * M * t ≤ M * M * M := mul_le_mul_of_nonneg_left htM (by positivity)
      have a3 : (2 * (t:ℝ)) * h.N * t = 2 * M * t := by rw [hM]; ring
      calc _ ≤ _ := a2
        _ = 2 * M * t := a3
        _ ≤ M * M * M := a4.trans a5
        _ = M ^ 3 := by ring
    have key : ∀ C', C' ≤ K → VLe Ω0 (c l) e ψ ((((l:ℕ):ℝ) * h.N * e) ^ C') →
        VLe Ω0 (c l) e ψ (M ^ (3 * K)) := by
      intro C' hC' v
      apply VLe.mono Ω0 (c l) v
      calc _ ≤ (((l:ℕ):ℝ) * h.N * e) ^ K := pow_le_pow_right₀ hbase1 hC'
        _ ≤ (M ^ 3) ^ K := pow_le_pow_left₀ (by linarith) hbase K
        _ = M ^ (3 * K) := by rw [← pow_mul]
    rcases hc4 with h1 | h1 | h1 | h1
    · exact absurd h1 hn
    · exact key CZ (le_max_left _ _) (hZ h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
    · exact key C2 (le_trans (le_max_left _ _) (le_max_right _ _))
        (hII h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
    · exact key C3 (le_trans (le_max_right _ _) (le_max_right _ _))
        (hIII h rfl t hbig Ω0 (l:ℕ) (c l) e hl2 he1 he2 ψ hψ h1)
  have hfin : ∀ l ∈ S, ∀ e, 0 < e → e < t → ∀ ψ ∈ h.X (c l) e, Vlen Ω0 (c l) e ψ ≠ ⊤ := by
    intro l hl e he1 he2 ψ hψ
    by_cases hn : h.CaseI (l:ℕ) e
    · have hLs : ∀ l' ∈ ({l} : Finset Nat.Primes), (l':ℕ) ≠ 2 ∧ h.CaseI (l':ℕ) e := by
        intro l' hl'
        rw [Finset.mem_singleton] at hl'
        rw [hl']
        exact ⟨(hS _ hl).1, hn⟩
      exact (hI h rfl hq1 hd hq1' hd' t hbig e he1 he2 Ω0 c {l} hLs).1 l
        (Finset.mem_singleton_self l) ψ hψ
    · exact (hother l hl e he1 he2 hn ψ hψ).1
  have hper : ∀ l ∈ S, (∀ e, 0 < e → e < t → plusLen (ld l) e ≠ ⊤) ∧
      ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤
        ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
    intro l hl
    haveI := (c l).dvr
    haveI := (c l).fin
    haveI := hc l
    have hidx := (hfacts l hl).2.2.2.2.2.2.1
    have hlev := hostLevel h E hE
    have hT : ∀ e, (↑(h.X (c l) e) : Set (DirichletCharacter (↥(c l).O) h.N)) =
        Chr.evenSet (↥(c l).O) h.H e := by
      intro e
      ext ψ
      simp [Host.mem_X, Chr.evenSet, Host.IsChar, PsiEven]
    have hred := fun e (he : e ≠ 0) =>
      redPrime E h.N h.H hlev (l:ℕ) (hS l hl).1 hidx (c l) Ω (ld l) Ω0 e he (h.X (c l) e) (hT e)
    have r := Chr.sumBack (l:ℕ) (↥(c l).O) (DirichletCharacter (↥(c l).O) h.N)
      (fun e => if e < t then h.X (c l) e else ∅)
      ((Finset.range t).biUnion (fun e => h.X (c l) e))
      (fun ψ e => Vlen Ω0 (c l) e ψ) (fun e => plusLen (ld l) e) (fun _ => 0) t
      (by
        intro e
        split_ifs with h'
        · intro ψ hψ
          exact Finset.mem_biUnion.2 ⟨e, Finset.mem_range.2 h', hψ⟩
        · exact Finset.empty_subset _)
      (by
        intro e he1 he2
        simp only [he2, if_true, Nat.cast_zero, zero_mul, add_zero]
        exact ⟨hfin l hl e he1 he2, hred e he1.ne'⟩)
    refine ⟨r.1, ?_⟩
    have r2 := r.2
    simp only [Nat.cast_zero, Finset.sum_const_zero, mul_zero, add_zero] at r2
    refine r2.trans (le_of_eq (Finset.sum_congr rfl fun e he => ?_))
    simp only [Finset.mem_Ico] at he
    simp only [if_pos he.2]
    rfl
  have hstep : ∀ e, 0 < e → e < t →
      ∑ l ∈ S, Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤
        M ^ C1 + 2 * M * M ^ (3 * K) := by
    intro e he1 he2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => h.CaseI (l:ℕ) e)]
    have hLs : ∀ l ∈ S.filter (fun l : Nat.Primes => h.CaseI (l:ℕ) e), (l:ℕ) ≠ 2 ∧ h.CaseI (l:ℕ) e := by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨(hS l hl.1).1, hl.2⟩
    have hA := (hI h rfl hq1 hd hq1' hd' t hbig e he1 he2 Ω0 c _ hLs).2
    have hB : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e),
        Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤ (h.N:ℝ) * M ^ (3 * K) := by
      intro l hl
      rw [Finset.mem_filter] at hl
      rw [Finset.mul_sum]
      calc ∑ ψ ∈ h.X (c l) e, Real.log ((l:ℕ):ℝ) * Vn Ω0 (c l) e ψ
          ≤ ∑ ψ ∈ h.X (c l) e, M ^ (3 * K) := by
            apply Finset.sum_le_sum
            intro ψ hψ
            rw [mul_comm]
            exact (hother l hl.1 e he1 he2 hl.2 ψ hψ).2
        _ = ((h.X (c l) e).card : ℝ) * M ^ (3 * K) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (h.N:ℝ) * M ^ (3 * K) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (xCard (↥(c l).O) h.N).1 _
    have hcard : ((S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)).card : ℝ) ≤ 2 * t := by
      have := card_small (S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)) (2 * t) (by
        intro l hl
        rw [Finset.mem_filter] at hl
        have hn := hl.2
        simp only [Host.CaseI, not_and, not_not] at hn
        exact ((hfacts l hl.1).2.2.2.2.2.2.2 e he1 he2 (hn (hS l hl.1).2)).2.1)
      exact_mod_cast this
    have hB' : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e),
        Real.log ((l:ℕ):ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ ≤ 2 * M * M ^ (3 * K) := by
      calc _ ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e), (h.N:ℝ) * M ^ (3 * K) :=
            Finset.sum_le_sum hB
        _ = ((S.filter (fun l : Nat.Primes => ¬ h.CaseI (l:ℕ) e)).card : ℝ) * ((h.N:ℝ) * M ^ (3 * K)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * t) * ((h.N:ℝ) * M ^ (3 * K)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * M * M ^ (3 * K) := by rw [hM]; ring
    exact add_le_add hA hB'
  refine ⟨fun l hl e he1 he2 => (hper l hl).1 e he1 he2, ?_⟩
  calc ∑ l ∈ S, Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
      ≤ ∑ l ∈ S, Real.log ((l:ℕ):ℝ) *
          ∑ e ∈ Finset.Ico 1 t, ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
        apply Finset.sum_le_sum
        intro l hl
        apply mul_le_mul_of_nonneg_left (hper l hl).2
        exact Real.log_nonneg (by exact_mod_cast l.2.one_lt.le)
    _ = ∑ e ∈ Finset.Ico 1 t, ∑ l ∈ S, Real.log ((l:ℕ):ℝ) *
          ∑ ψ ∈ h.X (c l) e, Vn Ω0 (c l) e ψ := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ e ∈ Finset.Ico 1 t, (M ^ C1 + 2 * M * M ^ (3 * K)) := by
        apply Finset.sum_le_sum
        intro e he
        simp only [Finset.mem_Ico] at he
        exact hstep e (by omega) he.2
    _ ≤ (t:ℝ) * (M ^ C1 + 2 * M * M ^ (3 * K)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le t 1
    _ ≤ M ^ (C1 + 3 * K + 4) := final_le M t C1 (3 * K) hM2 htM
