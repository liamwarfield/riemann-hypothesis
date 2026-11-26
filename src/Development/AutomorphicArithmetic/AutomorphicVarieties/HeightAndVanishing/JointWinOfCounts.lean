module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ShaLeV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Klen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SumOut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountIV
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.IvField
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) (m : ℕ) [NeZero m] (h : ψ.conductor ∣ m) :
    (Chr.cls ℚ Ω m).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  obtain ⟨hd, χ₀, hχ⟩ := ψ.factorsThrough_conductor
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have e1 := (Chr.clsFacts ℚ Ω N).2.1 ψ.conductor hd
  have e2 := (Chr.clsFacts ℚ Ω m).2.1 ψ.conductor h
  have hc : Chr.cls ℚ Ω ψ.conductor σ = 1 := by
    rw [← e2, MonoidHom.comp_apply, hσ, map_one]
  have hu : ∀ u : (ZMod N)ˣ, MulChar.toUnitHom ψ u = MulChar.toUnitHom χ₀ (ZMod.unitsMap hd u) := by
    intro u
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom]
    conv_lhs => rw [hχ]
    rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  unfold Chr.dirG
  rw [MonoidHom.comp_apply, hu, ← MonoidHom.comp_apply (ZMod.unitsMap hd), e1, hc, map_one]

theorem UpperTheory.V.HV.ivField :
    ∀ (χ : PChar) (l : ℕ) [Fact l.Prime] (j : ℕ), l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω],
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁) (_ : Algebra L₁ Ω)
        (_ : IsAlgClosure L₁ Ω) (_ : IsAbelianGalois ℚ L₁), IsAbField (Lchi χ l) L₀ ∧ IsLayer l j L₀ L₁ ∧ Module.finrank ℚ L₁ ≤ l * χ.N * l ^ j ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.conductor ∣ χ.N → galOf ℚ L₁ Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro χ l _ j hl2 Ω _ _ _
  haveI := χ.ne
  have hlp : l.Prime := Fact.out
  have hAm : (Lchi χ l).m = l * χ.N := by
    simp only [Lchi, AbF.cyc]
    exact max_eq_left (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hlp.ne_zero (NeZero.ne _)))
  have hldvd : l ∣ (Lchi χ l).m := by rw [hAm]; exact dvd_mul_right l _
  obtain ⟨L₀, i0, i1, hab, hdeg⟩ := exists_numberField_isAbField_finrank_eq_deg (Lchi χ l)
  have hmu : (Lchi χ l).HasMu l := by
    refine ⟨hldvd, ?_⟩
    rintro a ⟨u, hu, hua⟩
    have hu1 : u = 1 := (Subgroup.mem_bot).mp hu
    rw [hu1, Units.val_one] at hua
    have h2 : ((a : ℕ) : ZMod (Lchi χ l).m) = ((1 : ℕ) : ZMod (Lchi χ l).m) := by
      rw [Nat.cast_one]; exact hua.symm
    exact Nat.ModEq.of_dvd hldvd ((ZMod.natCast_eq_natCast_iff _ _ _).mp h2)
  obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot (Lchi χ l) l hlp hl2 L₀ hab).mp hmu
  obtain ⟨L₁, i2, i3, i4, hlay⟩ := exists_cyclotomic_layer_of_primitiveRoot l j hlp hl2 L₀ ⟨z, hz⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra L₁ Ω := (IsAlgClosed.lift (R := ℚ) (S := L₁) (M := Ω)).toRingHom.toAlgebra
  letI : Algebra L₀ Ω := ((algebraMap L₁ Ω).comp (algebraMap L₀ L₁)).toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower ℚ L₁ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L₀ L₁ := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI hcl : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L₁⟩
  obtain ⟨N', hN', H, hlev⟩ := Chr.layerLevel (Lchi χ l) l j hlp L₀ L₁ hab hlay
  obtain ⟨habel, -, -⟩ := Chr.levGal L₁ N' H hlev
  have hlev0 := Chr.abLevel.1 (Lchi χ l) L₀ hab
  have hgal0 := ((Chr.levGal L₀ _ _ hlev0).2.2 Ω).1
  refine ⟨L₀, i0, i1, L₁, i2, i3, i4, inferInstance, hcl, habel, hab, hlay, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ L₀ L₁, hdeg, hlay.2]
    apply Nat.mul_le_mul_right
    rw [AbF.deg]
    show (⊥ : Subgroup (ZMod (Lchi χ l).m)ˣ).index ≤ l * χ.N
    rw [Subgroup.index_bot, ← hAm]
    haveI : NeZero (Lchi χ l).m := ⟨(AbF.pos _).ne'⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_le _
  · intro O _ _ N _ ψ hψ
    calc galOf ℚ L₁ Ω ≤ galOf ℚ L₀ Ω := galOf_le ℚ L₀ Ω L₁
      _ = Chr.levH ℚ Ω (Lchi χ l).H := hgal0
      _ ≤ (Chr.dirG ℚ Ω ψ).ker := by
        rw [Chr.levH]
        show Subgroup.comap _ ⊥ ≤ _
        rw [MonoidHom.comap_bot]
        exact ker_le Ω ψ _ (hψ.trans (hAm ▸ dvd_mul_left _ _))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem sum_le (n N t : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) :
    ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ (N * t) ^ (n + 3) := by
  have h1 : ∀ m : ℕ, 2 * m ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h2 : 2 ≤ 2 ^ (m + 1) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ 2 (m + 1)]
      omega
  have hNt : 2 ≤ N * t := by nlinarith
  have h2 : 2 ^ (n + 1) ≤ (N * t) ^ (n + 1) := Nat.pow_le_pow_left hNt _
  have h3 : N * t ^ 2 ≤ (N * t) ^ 2 := by nlinarith
  calc ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ ∑ e ∈ Finset.Ico 1 t, n * (2 * N * t) :=
        Finset.sum_le_sum fun e he => by
          have := (Finset.mem_Ico.1 he).2
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this.le)
    _ = (t - 1) * (n * (2 * N * t)) := by simp [Finset.sum_const, Nat.card_Ico]
    _ ≤ t * (n * (2 * N * t)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = (2 * n) * (N * t ^ 2) := by ring
    _ ≤ (N * t) ^ (n + 1) * (N * t) ^ 2 := Nat.mul_le_mul (le_trans (h1 n) h2) h3
    _ = (N * t) ^ (n + 3) := by rw [← pow_add]

theorem UpperTheory.V.HV.countIV :
    CountIV := by
  intro χ l _ j hlB
  obtain ⟨hlp, hl2⟩ := prime_of_mem_Bchi hlB
  refine ⟨l * χ.N * l ^ j + 3, ?_⟩
  intro h hχ t ht hbig B hLay Ω _ _ _ c ψ hψ hodd
  haveI := c.dvr
  haveI := c.fin
  have hNpos : 0 < h.N := Host.N_pos h
  have hN16 := (hostIndex h).2.2.1
  have hN2 : 2 ≤ h.N := le_trans (by norm_num) (Nat.le_of_dvd hNpos hN16)
  have hbf := bchiFacts h t hbig
  have hlB' : l ∈ Bchi h.chi := by rw [hχ]; exact hlB
  have hlq1 : l ≠ h.q1 := (hbf.1 l hlB').1.ne
  have hld : l ≠ h.d := (hbf.1 l hlB').2.ne
  have hcond : ψ.conductor ∣ χ.N := by
    have := ((hostOdd h c.O ψ hψ).2 l hlp hl2 hlq1 hld hodd).1
    rw [← hχ]
    exact this
  obtain ⟨L₀, _, _, L₁, _, _, _, _, _, _, hAb, hLayer, hdeg, hker⟩ := ivField χ l j hl2 Ω
  have hgal := hker c.O h.N ψ hcond
  obtain ⟨D⟩ := ldata_nonempty (F := L₁) (Ω := Ω) l
  have hVV := hLay L₀ hAb L₁ hLayer Ω D
  have hT : Subgroup.closure ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)) : Set (L₁ ≃ₐ[ℚ] L₁)) = ⊤ := by simp
  have hcard : (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card ≤ l * χ.N * l ^ j := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hdeg
  have hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [Chr.dirG, hσ]
  have hb : ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e
      ≤ (h.N * t) ^ (l * χ.N * l ^ j + 3) := by
    calc _ ≤ ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * (2 * h.N * e) :=
          Finset.sum_le_sum fun e he => Nat.mul_le_mul_left _
            (lossLe l h.N 0 e hlp hl2 hN2 (Nat.zero_le _) (Finset.mem_Ico.1 he).1).2
      _ ≤ (h.N * t) ^ ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card + 3) := sum_le _ h.N t (by omega) ht
      _ ≤ _ := Nat.pow_le_pow_right (Nat.mul_pos hNpos (by omega)) (by omega)
  refine Chr.nuSum.2 l c.O (fun e => Vlen Ω c e ψ) (fun e => shaLen D (e : ℤ))
    (fun e => (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e) t B _ ?_ hVV.2 ?_
  · intro e he1 he2
    refine ⟨hVV.1 e he1 he2, ?_⟩
    have h1 := Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N e (Chr.dirG ℚ Ω ψ)
    have h2 := Chr.upV ℚ Ω L₁ l c.O D e (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT
    have h3 := (Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N e (Chr.dirG ℚ Ω ψ) he1.ne' hclsker).2
    calc Vlen Ω c e ψ ≤ Chr.V l e (Chr.dirG ℚ Ω ψ) := h1
      _ ≤ _ := h2
      _ ≤ shaLen D (e : ℤ) * eO l c.O + ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card : ℕ∞) *
            ((LDataCardLeFinrank.nuBound l h.N e : ℕ∞) * eO l c.O) := by gcongr
      _ = _ := by push_cast; ring
  · exact_mod_cast hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountVs
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PowTotientConductor
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem pow_totient_conductor {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    χ ^ Nat.totient χ.conductor = 1 := by
  obtain ⟨hd, χ₀, e⟩ := χ.factorsThrough_conductor
  have h0 : χ₀ ^ Nat.totient χ.conductor = 1 := by
    refine MulChar.ext (fun a => ?_)
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
      ZMod.pow_totient, Units.val_one, map_one]
  have h1 : DirichletCharacter.changeLevel hd χ₀ ^ Nat.totient χ.conductor = 1 := by
    rw [← map_pow, h0, map_one]
  rwa [← e] at h1

private theorem totient_two_pow_dvd (c : ℕ) : Nat.totient (2 ^ c) ∣ 2 ^ c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two hc]
    simpa using Nat.pow_dvd_pow 2 (Nat.sub_le c 1)

theorem UpperTheory.V.HV.vsOrd :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 → 2 ^ c2 ψ < h.R1 l ψ →
      orderOf ψ ≤ 2 * h.o * (16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o))) := by
  intro h O _ _ ψ hψ l hl hl2 hlt
  obtain ⟨-, -, -, hR1, -⟩ := cmDatum_char_two_adic_order_bounds h O ψ hψ l hl hl2
  obtain ⟨-, -, -, hopos, -⟩ := hostIndex h
  have hc2 : comp 2 ψ ^ (2 ^ c2 ψ) = 1 := by
    obtain ⟨-, -, -, hpow2, -⟩ := compCond O h.N ψ 2 Nat.prime_two
    have ht := pow_totient_conductor (comp 2 ψ)
    rw [show (comp 2 ψ).conductor = 2 ^ c2 ψ from hpow2.symm] at ht
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one ht).trans (totient_two_pow_dvd _))
  have hall : ψ ^ (2 * h.o * 2 ^ c2 ψ) = 1 := by
    apply (compAlg O h.N 2 Nat.prime_two).2.2.2.2.2.2.2 ψ
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases h2p : p = 2
    · subst h2p
      rw [mul_comm, pow_mul, hc2, one_pow]
    · have hd := ((hostComp h O ψ hψ).2.2 p hpp h2p).1
      rw [pow_mul, orderOf_dvd_iff_pow_eq_one.mp hd, one_pow]
  have hmpos : 0 < 2 * h.o * 2 ^ c2 ψ := by positivity
  calc orderOf ψ ≤ 2 * h.o * 2 ^ c2 ψ := Nat.le_of_dvd hmpos (orderOf_dvd_of_pow_eq_one hall)
    _ ≤ _ := Nat.mul_le_mul_left _ (hlt.le.trans hR1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.VsField
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem idx_le (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) :
    ψ.toUnitHom.ker.index ≤ orderOf ψ := by
  have hpos := MulChar.orderOf_pos ψ
  haveI : NeZero (orderOf ψ) := ⟨hpos.ne'⟩
  rw [Subgroup.index_ker]
  calc Nat.card ψ.toUnitHom.range ≤ Nat.card (rootsOfUnity (orderOf ψ) O) := by
        apply Subgroup.card_le_of_le
        rintro _ ⟨u, rfl⟩
        rw [mem_rootsOfUnity]
        ext
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' ψ hpos.ne',
          pow_orderOf_eq_one, MulChar.one_apply_coe, Units.val_one]
    _ ≤ orderOf ψ := card_rootsOfUnity O _

theorem UpperTheory.V.HV.vsField :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N),
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra L Ω) (_ : IsAlgClosure L Ω) (_ : IsAbelianGalois ℚ L), HasMuQ l L ∧
        Module.finrank ℚ L ≤ orderOf ψ * l ∧ Nonempty (L →ₐ[ℚ] CyclotomicField (l * N) ℚ) ∧ galOf ℚ L Ω ≤ (Chr.dirG ℚ Ω ψ).ker := by
  intro Ω _ _ _ l hl hl2 O _ _ N _ ψ
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  haveI hMz : NeZero (l * N) := ⟨mul_ne_zero hlp.ne_zero (NeZero.ne N)⟩
  let φN : (ZMod (l * N))ˣ →* (ZMod N)ˣ := ZMod.unitsMap (dvd_mul_left N l)
  let φl : (ZMod (l * N))ˣ →* (ZMod l)ˣ := ZMod.unitsMap (dvd_mul_right l N)
  let H : Subgroup (ZMod (l * N))ˣ := (ψ.toUnitHom.comp φN).ker ⊓ φl.ker
  let A : AbF := ⟨l * N, Nat.pos_of_ne_zero (NeZero.ne (l * N)), H⟩
  obtain ⟨L, fL, nfL, hab, -⟩ := exists_numberField_isAbField_finrank_eq_deg A
  have hlev : Chr.HasLevel L (l * N) H := Chr.abLevel.1 A L hab
  obtain ⟨hgal, hfin, hΩ⟩ := Chr.levGal L (l * N) H hlev
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let f : L →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra L Ω := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Ω := inferInstance
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI hcl : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  refine ⟨L, fL, nfL, inferInstance, hcl, hgal, ?_, ?_, ?_, ?_⟩
  · have hmu : A.HasMu l := by
      unfold AbF.HasMu
      refine ⟨dvd_mul_right l N, ?_⟩
      intro a ha
      unfold AbF.ker at ha
      obtain ⟨u, hu, hua⟩ := ha
      have h1 : φl u = 1 := MonoidHom.mem_ker.mp hu.2
      have h2 : ((φl u : (ZMod l)ˣ) : ZMod l) = (a : ZMod l) := by
        simp only [φl, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply]
        rw [hua, ZMod.cast_natCast (dvd_mul_right l N)]
      rw [h1, Units.val_one] at h2
      exact (ZMod.natCast_eq_natCast_iff a 1 l).mp (by rw [← h2, Nat.cast_one])
    obtain ⟨z, hz⟩ := (abelianField_hasMu_iff_exists_primitiveRoot A l hlp hl2 L hab).mp hmu
    unfold HasMuQ
    rw [if_neg hl2]
    exact ⟨z, hz⟩
  · rw [hfin]
    refine (Subgroup.index_inf_le).trans (Nat.mul_le_mul ?_ ?_)
    · rw [← MonoidHom.comap_ker, Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)]
      exact idx_le O N ψ
    · rw [Subgroup.index_ker]
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le l
  · have hab' := hab
    unfold IsAbField at hab'
    obtain ⟨N', hN', j, ζ, hmN, hζ, h3⟩ := hab'
    haveI : NeZero N' := hN'
    haveI : NeZero ((N' : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N')⟩
    haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension N' ℚ
    haveI : IsGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isGalois {N'} ℚ _
    haveI : FiniteDimensional ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.finiteDimensional {N'} ℚ _
    haveI : NeZero ((l * N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne (l * N))⟩
    haveI : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    have hmN' : l * N ∣ N' := hmN
    have hdpos : N' / (l * N) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N')) hmN')
        (Nat.pos_of_ne_zero (NeZero.ne (l * N)))).ne'
    have hη : IsPrimitiveRoot (ζ ^ (N' / (l * N))) (l * N) := by
      have := hζ.pow_of_dvd hdpos (Nat.div_dvd_of_dvd hmN')
      rwa [Nat.div_div_self hmN' (NeZero.ne N')] at this
    let F : IntermediateField ℚ (CyclotomicField N' ℚ) := IntermediateField.adjoin ℚ {ζ ^ (N' / (l * N))}
    haveI : IsCyclotomicExtension {l * N} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hmem : ∀ x, j x ∈ F := by
      intro x
      rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hτη : τ (ζ ^ (N' / (l * N))) = ζ ^ (N' / (l * N)) :=
        (IntermediateField.mem_fixingSubgroup_iff F τ).mp hτ _
          (IntermediateField.mem_adjoin_simple_self ℚ _)
      have hτζ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val := (hζ.autToPow_spec ℚ τ).symm
      have hpow : (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val = ζ ^ (N' / (l * N)) := by
        calc (ζ ^ (N' / (l * N))) ^ ((hζ.autToPow ℚ τ : ZMod N')).val
            = (ζ ^ ((hζ.autToPow ℚ τ : ZMod N')).val) ^ (N' / (l * N)) := by
              rw [← pow_mul, ← pow_mul, mul_comm]
          _ = (τ ζ) ^ (N' / (l * N)) := by rw [hτζ]
          _ = τ (ζ ^ (N' / (l * N))) := (map_pow τ ζ _).symm
          _ = ζ ^ (N' / (l * N)) := hτη
      have hne : ζ ^ (N' / (l * N)) ≠ 0 := hη.ne_zero (NeZero.ne (l * N))
      have hz : (ζ ^ (N' / (l * N))) ^ ((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_one, hpow, div_self hne]
      have hd := (hη.zpow_eq_one_iff_dvd _).mp hz
      have hc : ((((((hζ.autToPow ℚ τ : ZMod N')).val : ℤ) - 1 : ℤ)) : ZMod (l * N)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ (l * N)).mpr hd
      push_cast at hc
      have hker : A.ker ((hζ.autToPow ℚ τ : ZMod N')).val := by
        unfold AbF.ker
        exact ⟨1, Subgroup.one_mem _, by rw [Units.val_one]; exact (sub_eq_zero.mp hc).symm⟩
      exact ((h3 τ _ hτζ).mpr hker) x
    exact ⟨(IsCyclotomicExtension.algEquiv {l * N} ℚ F (CyclotomicField (l * N) ℚ)).toAlgHom.comp
      (j.codRestrict F.toSubalgebra hmem)⟩
  · intro σ hσ
    rw [(hΩ Ω).1] at hσ
    unfold Chr.levH at hσ
    rw [Subgroup.mem_comap] at hσ
    rw [MonoidHom.mem_ker]
    unfold Chr.dirG
    rw [← (Chr.clsFacts ℚ Ω (l * N)).2.1 N (dvd_mul_left N l)]
    exact MonoidHom.mem_ker.mp hσ.1
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem kBound_le (K n n0 D : ℕ) (x : ℝ) (hx : 2 ≤ x) (hn : n ≤ n0) (hD : 0 < D)
    (hl : Real.log (D : ℝ) ≤ (n : ℝ) * Real.log x) :
    kBound (K : ℝ) 1 n D ≤ x ^ ((2 * n0) ^ K * (n0 + 1)) := by
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hx1 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h3 : Real.log (2 * (D : ℝ)) ≤ ((n0 : ℝ) + 1) * Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hn' hx1]
  have h4 : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by linarith)
  unfold kBound
  rw [← Real.exp_log (pow_pos hx0 _), Real.exp_le_exp, Real.log_pow, Real.rpow_natCast]
  push_cast
  rw [mul_assoc ((2 * (n0 : ℝ)) ^ K)]
  refine mul_le_mul ?_ h3 h4 (by positivity)
  rw [mul_one]
  gcongr

private theorem nrm_le (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (hT : eO l O ≠ ⊤)
    (a : ℕ∞) (m : ℕ) (h : a ≤ (m : ℕ∞) * eO l O) : a ≠ ⊤ ∧ Chr.nrm l O a ≤ m := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hk] at h
  have hmk : (m : ℕ∞) * (k : ℕ∞) = ((m * k : ℕ) : ℕ∞) := by push_cast; rfl
  rw [hmk] at h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  refine ⟨ha, ?_⟩
  lift a to ℕ using ha
  have h' : a ≤ m * k := by exact_mod_cast h
  unfold Chr.nrm
  rw [← hk]
  simp only [ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · rw [div_le_iff₀ (by exact_mod_cast hk0)]
    exact_mod_cast h'

private theorem final_le (A n0 : ℕ) (x v y l N : ℝ) (hl : 1 ≤ l) (hN : 2 ≤ N) (hx : x = l * N)
    (hy0 : 0 ≤ y) (hy : y ≤ l) (hv : v ≤ 2 * x ^ A + n0 * (2 * N)) :
    v * y ≤ x ^ (A + n0 + 3) := by
  have h2n : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ]; omega
  have hx2 : 2 ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hlx : l ≤ x := by rw [hx]; nlinarith
  have hX : x ≤ x ^ (A + 1) := le_self_pow₀ (by linarith) (by omega)
  have hX0 : 0 ≤ x ^ (A + 1) := pow_nonneg hx0 _
  have hn00 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have hp2 : (1 : ℝ) ≤ 2 ^ n0 := one_le_pow₀ (by norm_num)
  have hn0 : (n0 : ℝ) + 1 ≤ 2 ^ n0 := by exact_mod_cast h2n n0
  have hpow : (2 : ℝ) ^ (n0 + 2) ≤ x ^ (n0 + 2) := pow_le_pow_left₀ (by norm_num) hx2 _
  have hA0 : 0 ≤ x ^ A := pow_nonneg hx0 A
  have hpos : 0 ≤ 2 * x ^ A + n0 * (2 * N) := by nlinarith
  have e1 : x ^ A * l ≤ x ^ (A + 1) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left hlx hA0
  calc v * y ≤ (2 * x ^ A + n0 * (2 * N)) * y := mul_le_mul_of_nonneg_right hv hy0
    _ ≤ (2 * x ^ A + n0 * (2 * N)) * l := mul_le_mul_of_nonneg_left hy hpos
    _ = 2 * (x ^ A * l) + 2 * n0 * x := by rw [hx]; ring
    _ ≤ 2 * x ^ (A + 1) + 2 * n0 * x ^ (A + 1) := by nlinarith
    _ ≤ x ^ (A + 1) * 2 ^ (n0 + 2) := by
      rw [pow_add (2 : ℝ) n0 2]
      nlinarith [mul_le_mul_of_nonneg_left hn0 hX0, mul_le_mul_of_nonneg_left hp2 hX0]
    _ ≤ x ^ (A + 1) * x ^ (n0 + 2) := mul_le_mul_of_nonneg_left hpow hX0
    _ = x ^ (A + n0 + 3) := by rw [← pow_add]; congr 1; omega

theorem UpperTheory.V.HV.countVs :
    GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ CK : ℝ, LemmaK CK → CountVs := by
  intro hPT hLF hLT CK hK χ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (Bchi χ).sup id := ⟨_, rfl⟩
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = 2 * ordC χ * (16 * ordC χ * (M * χ.N) ^ 2 * M ^ (2 * (4 * ordC χ).totient)) * M :=
    ⟨_, rfl⟩
  have hK' : LemmaK (⌈CK⌉₊ : ℝ) := Win.kmono CK _ (Nat.le_ceil CK) hK
  refine ⟨(2 * n0) ^ ⌈CK⌉₊ * (n0 + 1) + n0 + 3, ?_⟩
  intro h hχ t hbig Ω _ _ _ l _ c e hl2 he0 het ψ hψX hP
  obtain ⟨⟨hlB, he1⟩, hR⟩ := hP
  subst he1
  subst hχ
  haveI := c.dvr
  haveI := c.fin
  have hlp : l.Prime := Fact.out
  have hl2' : 2 ≤ l := hlp.two_le
  obtain ⟨hIs, -⟩ := (Host.mem_X h).1 hψX
  have hNpos : 0 < h.N := Host.N_pos h
  have hN2 : 2 ≤ h.N := le_trans (by norm_num) (Nat.le_of_dvd hNpos (hostIndex h).2.2.1)
  have hlM : l ≤ M := by rw [hM]; exact Finset.le_sup (f := id) hlB
  have hord := vsOrd h c.O ψ hIs l hlp hl2 hR
  have hordM : orderOf ψ * l ≤ n0 := by
    rw [hn0]
    refine Nat.mul_le_mul (le_trans hord ?_) hlM
    show 2 * ordC h.chi * (16 * ordC h.chi * (l * h.chi.N) ^ 2 * l ^ (2 * (4 * ordC h.chi).totient)) ≤ _
    gcongr
  obtain ⟨L, _, _, _, _, _, hMu, hdeg, hcyc, hgal⟩ := vsField Ω l hl2 c.O h.N ψ
  obtain ⟨D⟩ := ldata_nonempty (F := L) (Ω := Ω) l
  have hdegn : Module.finrank ℚ L ≤ n0 := le_trans hdeg hordM
  have hT : Subgroup.closure ((Finset.univ : Finset (L ≃ₐ[ℚ] L)) : Set (L ≃ₐ[ℚ] L)) = ⊤ := by simp
  have hcard : (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card ≤ n0 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hdegn
  have hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [Chr.dirG, hσ]
  have hsha : shaLen D ((1 : ℕ) : ℤ) ≤ VLen D ((1 : ℕ) : ℤ) := PropA.shaLeV hPT hLF hLT L Ω l (Or.inl hl2) D _
  have hkl := Win.klen _ hK' l L Ω D hMu 1 le_rfl
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℕ, VLen D ((1 : ℕ) : ℤ) = m1 := ⟨_, (ENat.coe_toNat hkl.1).symm⟩
  have hup := Chr.upV ℚ Ω L l c.O D 1 (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT
  have hh0 := (Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N 1 (Chr.dirG ℚ Ω ψ) one_ne_zero hclsker).2
  have heO : eO l c.O ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) (dvrFacts l c.O).2.2.2.2.2.2.1
  have hV : Vlen Ω c 1 ψ ≤ ((m1 + (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card *
      LDataCardLeFinrank.nuBound l h.N 1 : ℕ) : ℕ∞) * eO l c.O := by
    calc Vlen Ω c 1 ψ ≤ Chr.V l 1 (Chr.dirG ℚ Ω ψ) := Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N 1 (Chr.dirG ℚ Ω ψ)
      _ ≤ _ := hup
      _ ≤ VLen D ((1 : ℕ) : ℤ) * eO l c.O + ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℕ∞) *
            ((LDataCardLeFinrank.nuBound l h.N 1 : ℕ∞) * eO l c.O) := by gcongr
      _ = _ := by rw [hm1]; push_cast; ring
  obtain ⟨hne, hnrm⟩ := nrm_le l c.O heO _ _ hV
  refine ⟨hne, ?_⟩
  have hD : 0 < (discr L).natAbs := Int.natAbs_pos.2 (discr_ne_zero L)
  have hx2 : (2 : ℝ) ≤ (l : ℝ) * h.N := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl2'
    have : (2 : ℝ) ≤ h.N := by exact_mod_cast hN2
    nlinarith
  have hlogD : Real.log ((discr L).natAbs : ℝ) ≤ (Module.finrank ℚ L : ℝ) * Real.log ((l : ℝ) * h.N) := by
    have := Win.disc L (l * h.N) (Nat.mul_pos (by omega) hNpos) hcyc
    push_cast at this
    exact this
  have hkb := kBound_le ⌈CK⌉₊ (Module.finrank ℚ L) n0 (discr L).natAbs ((l : ℝ) * h.N) hx2 hdegn hD hlogD
  have hnu : LDataCardLeFinrank.nuBound l h.N 1 ≤ 2 * h.N * 1 := (lossLe l h.N 0 1 hlp hl2 hN2 (Nat.zero_le _) le_rfl).2
  have hv : Vn Ω c 1 ψ ≤ 2 * ((l : ℝ) * h.N) ^ ((2 * n0) ^ ⌈CK⌉₊ * (n0 + 1)) + n0 * (2 * (h.N : ℝ)) := by
    have hc1 : ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℝ) ≤ n0 := by exact_mod_cast hcard
    have hc2 : (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) ≤ 2 * h.N := by
      have : (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) ≤ ((2 * h.N * 1 : ℕ) : ℝ) := by exact_mod_cast hnu
      push_cast at this
      linarith
    have hc3 : (m1 : ℝ) ≤ 2 * kBound (⌈CK⌉₊ : ℝ) 1 (Module.finrank ℚ L) (discr L).natAbs := by
      have := hkl.2
      rw [hm1, ENat.toNat_coe] at this
      exact this
    calc Vn Ω c 1 ψ ≤ ((m1 + (Finset.univ : Finset (L ≃ₐ[ℚ] L)).card *
          LDataCardLeFinrank.nuBound l h.N 1 : ℕ) : ℝ) := hnrm
      _ = (m1 : ℝ) + ((Finset.univ : Finset (L ≃ₐ[ℚ] L)).card : ℝ) *
          (LDataCardLeFinrank.nuBound l h.N 1 : ℝ) := by push_cast; ring
      _ ≤ 2 * kBound (⌈CK⌉₊ : ℝ) 1 (Module.finrank ℚ L) (discr L).natAbs + n0 * (2 * (h.N : ℝ)) := by
          gcongr
      _ ≤ _ := by linarith
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hlp.one_lt.le
  have hy0 : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg hl1
  have hyl : Real.log (l : ℝ) ≤ l := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hfin := final_le ((2 * n0) ^ ⌈CK⌉₊ * (n0 + 1)) n0 ((l : ℝ) * h.N) (Vn Ω c 1 ψ) (Real.log l) l h.N
    hl1 (by exact_mod_cast hN2) rfl hy0 hyl hv
  simpa using hfin
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem point_arith (x B : ℝ) (hx : 2 ≤ x) (hB : 0 ≤ B) (k K D C0 : ℕ) (hk : k ≤ K) :
    (k : ℝ) * (x ^ D + D * B) + x ^ C0 ≤ x ^ (C0 + D + K + K * D) + ((C0 + D + K + K * D : ℕ) : ℝ) * B := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  have h1 := one_add_mul_le_pow (show (-2:ℝ) ≤ x - 1 by linarith) K
  rw [show (1:ℝ) + (x - 1) = x by ring] at h1
  have hKr : (k:ℝ) ≤ K := by exact_mod_cast hk
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hC0 : (0:ℝ) ≤ C0 := by positivity
  have hc : (K:ℝ) + 1 ≤ x ^ K := by nlinarith
  have ha : 1 ≤ x ^ C0 := one_le_pow₀ hx1
  have hb : 1 ≤ x ^ D := one_le_pow₀ hx1
  have he : 1 ≤ x ^ (K * D) := one_le_pow₀ hx1
  have hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D) := by
    rw [pow_add, pow_add, pow_add]
  have hM : (k:ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hMB : (k:ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right hM hB
  have hab : x ^ C0 ≤ x ^ C0 * x ^ D := le_mul_of_one_le_right (by positivity) hb
  have habc : x ^ C0 * x ^ D * ((K:ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D) :=
    le_mul_of_one_le_right (by positivity) he
  have hkb : (k:ℝ) * x ^ D ≤ K * x ^ D := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hKb : (K:ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0
  rw [hpow]
  nlinarith

theorem UpperTheory.V.HV.point :
    SumIn → SumOut → PointHV := by
  intro hin hout χ j
  classical
  obtain ⟨C0, r₁, r₂, hr₁, hr₂, hO⟩ := hout χ
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi χ),
      Cl l = Classical.choose (hin χ l (j l) hl) :=
    ⟨fun n => if hn : n.Prime ∧ n ∈ Bchi χ then Classical.choose (hin χ ⟨n, hn.1⟩ (j n) hn.2) else 0,
      fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi χ from ⟨l.2, hl⟩)⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi χ, Cl l ≤ D :=
    ⟨∑ l ∈ Bchi χ, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩
  refine ⟨C0 + D + (Bchi χ).card + (Bchi χ).card * D, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1 h2 h3 h4 t ht hbig B hB hlay E _ _ _ hE Ω _ _ _ ld
  have hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi χ →
      PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B) := by
    intro l hl
    rw [hCl l hl]
    exact Classical.choose_spec (hin χ l (j l) hl) h hχ t ht hbig B hB (hlay l hl) E hE Ω ld
  have hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi χ) →
      PlusLe ld S t (((h.N:ℝ) * t) ^ C0) :=
    fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS
  have hx2 : (2:ℝ) ≤ (h.N:ℝ) * t := by
    have hN : (1:ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have ht' : (2:ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  refine ⟨?_, ?_⟩
  · intro p hpf e hp2 he1 he2
    by_cases hb : p ∈ Bchi χ
    · exact (hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
    · refine (hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
      intro l hl
      obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨hp2, hb⟩
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)]
    have hout2 := (hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi χ)) (by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨hS2 l hl.1, hl.2⟩)).2
    have hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ),
        Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
        ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have h0 := (hIn l hl.2).2
      rw [Finset.sum_singleton] at h0
      have hle := hD l hl.2
      have hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D := pow_le_pow_right₀ (by linarith) hle
      have hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hin2
    have hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)).card ≤ (Bchi χ).card :=
      Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ))
        (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
    have key := point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi χ).card D C0 hcard
    linarith
end

open Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.HV

theorem pointHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) : PointHV :=
  point (sumIn h2 h5 (countVs hP hF hT CK hK) countIV) (sumOut h1 hZ h2 h3)

theorem thmHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) (K : BConst) {Ct : ℝ}
    (hC : 0 < Ct) : ThmHV K Ct :=
  thmHV (pointHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ) K Ct hC

theorem jointWin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV)
    (hZ : CountZ) : JointWin 401 :=
  jointWin_of (by norm_num) hB (thmHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ K (by norm_num))

theorem vwin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (hc : ThmBcFree) (h1 : CountI) (h2 : CountII) (h3 : CountIII)
    (h5 : CountV) (hZ : CountZ) : VWin :=
  vwin_of_joint (jointWin_of_counts hP hF hT hK hB h1 h2 h3 h5 hZ) ((thmBc_iff (by norm_num)).2 hc)

end UpperTheory.V.HV
