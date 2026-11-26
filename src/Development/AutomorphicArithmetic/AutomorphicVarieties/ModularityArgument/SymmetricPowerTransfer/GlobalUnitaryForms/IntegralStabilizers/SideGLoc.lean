module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinprodSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.UnitAdd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SelCard
open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

open Loc

private theorem ev_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {x y : K} (h : EvenVal O x) (h' : EvenVal O y) :
    EvenVal O (x * y) := by
  obtain ⟨u, s, hs, rfl⟩ := h
  obtain ⟨u', s', hs', rfl⟩ := h'
  exact ⟨u * u', s * s', mul_ne_zero hs hs', by simp only [Units.val_mul, map_mul]; ring⟩

private theorem ev_sq {O K : Type} [CommRing O] [Field K] [Algebra O K] {s : K} (hs : s ≠ 0) : EvenVal O (s ^ 2) :=
  ⟨1, s, hs, by simp⟩

variable {F : Type} [Field F] [NumberField F]

private theorem dvd_of_ev (v : Pl F) (a : Fˣ) (h : EvenVal (Ov v) (cv v (a : F))) : ((2 : ℕ) : ℤ) ∣ Kum.ordv v a := by
  obtain ⟨u, s, hs, hx⟩ := h
  have hu : ∀ w : (Ov v)ˣ, Valued.v (algebraMap (Ov v) (Kv v) ↑w) = 1 := by
    intro w
    have ha : Valued.v (algebraMap (Ov v) (Kv v) ↑w) ≤ 1 := (w : Ov v).2
    have hb : Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) ≤ 1 := ((w⁻¹ : (Ov v)ˣ) : Ov v).2
    have hm : Valued.v (algebraMap (Ov v) (Kv v) ↑w) * Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm ha ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
      _ ≤ Valued.v (algebraMap (Ov v) (Kv v) ↑w) * 1 := by gcongr
      _ = _ := mul_one _
  have hv := congrArg Valued.v hx
  rw [map_mul, hu, one_mul, map_pow] at hv
  have hs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs
  obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.mp hs0
  have hva : Valued.v (cv v (a : F)) = v.valuation F (a : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : F)
  have h2 : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((w ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ← hva, hv, WithZero.coe_pow, hw]
  have h3 := WithZero.coe_inj.mp h2
  refine ⟨-Multiplicative.toAdd w, ?_⟩
  simp only [Kum.ordv, h3, toAdd_pow, smul_eq_mul]
  push_cast
  ring

private theorem fin_sel (S : Finset (Pl F)) :
    {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2}.Finite := by
  classical
  have hS : (S : Set (Pl F)).Finite := S.finite_toSet
  have hc := Kum.cardSel F (S : Set (Pl F)) 2 two_ne_zero
  have hu := Kum.cardSUnit F (S : Set (Pl F)) 2 hS
  have hne : Nat.card (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸
      (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) ≠ 0 := by
    rw [hc, hu]
    have h1 : Nat.card ↥(rootsOfUnity 2 F) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } ≠ 0 := by
      haveI : Nonempty { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } := ⟨⟨1, one_pow 2⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) h1) h2
  haveI := Nat.finite_of_card_ne_zero hne
  let f : {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2} →
      (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸ (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) :=
    fun c => QuotientGroup.mk ⟨c.1.out, c.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h' := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    apply Subtype.ext
    show c = c'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    apply QuotientGroup.eq.mpr
    simpa [Kum.powK] using h'
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

variable {Δ : F} (D : Dat Δ)

private theorem quotient_out_eq_mul_sq (a : Fˣ) :
    ∃ b : Fˣ, ((Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) : Fˣ) : F) = (a : F) * (b : F) ^ 2 := by
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))
  obtain ⟨b, hb⟩ := h
  have hb' : b ^ 2 = (Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))⁻¹ * a := hb
  refine ⟨b⁻¹, ?_⟩
  have e : Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = a * (b⁻¹) ^ 2 := by
    rw [inv_pow, hb']
    group
  rw [e]
  push_cast
  ring

private theorem mem_sel (y : F) (a : Fˣ) (h : TPos (a : F)) (h' : D.Ev ((a : F) * y)) :
    (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
  obtain ⟨b, hb⟩ := quotient_out_eq_mul_sq a
  simp only [Dat.Sel, Set.mem_setOf_eq]
  rw [hb]
  constructor
  · intro σ
    rw [map_mul, map_pow]
    have hne : σ (b : F) ≠ 0 := (map_ne_zero σ).mpr b.ne_zero
    exact mul_pos (h σ) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)
  · intro v hv
    rw [show (a : F) * (b : F) ^ 2 * y = ((a : F) * y) * (b : F) ^ 2 by ring, map_mul, map_pow]
    exact ev_mul (h' v hv) (ev_sq ((map_ne_zero _).mpr b.ne_zero))

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.selCard :
    UpperTheory.V.Z.Sym.Glob.SelCard := by
  intro F _ _ Δ D hOk
  haveI := hOk.real
  have hfin1 : (D.Sel 1).Finite := by
    refine (fin_sel D.Sg).subset ?_
    intro c hc v hv
    exact dvd_of_ev v _ (by simpa using hc.2 v (by simpa using hv))
  have hnon : (D.Sel 1).Nonempty :=
    ⟨_, mem_sel D 1 1 (fun σ => by simp)
      (fun v _ => by simpa using ev_sq (O := Ov v) (one_ne_zero (α := Kv v)))⟩
  refine ⟨hfin1, hnon, ?_⟩
  intro y hy
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have σ0 := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy σ0
    simp [h0] at this
  obtain ⟨yU, hyU⟩ : ∃ u : Fˣ, (u : F) = y := ⟨Units.mk0 y hy0, rfl⟩
  have hmul : ∀ c ∈ D.Sel 1, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D y
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      have h1 := hc.2 v hv
      rw [show ((c.out * yU : Fˣ) : F) * y = ((c.out : F) * 1) * y ^ 2 by rw [Units.val_mul, hyU]; ring,
        map_mul (cv v), map_pow]
      exact ev_mul h1 (ev_sq ((map_ne_zero _).mpr hy0))
  have hback : ∀ c ∈ D.Sel y, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel 1 := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D 1
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      rw [Units.val_mul, hyU, mul_one]
      exact hc.2 v hv
  have hsq : (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨yU, sq yU⟩
  have himg : (fun c => c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) '' D.Sel 1 = D.Sel y := by
    ext c
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact hmul c' hc'
    · intro hc
      refine ⟨c * yU, hback c hc, ?_⟩
      show c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = c
      rw [mul_assoc, hsq, mul_one]
  have hinj : Function.Injective (fun c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range =>
      c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) := mul_left_injective _
  rw [← himg]
  exact ⟨hfin1.image _, Set.ncard_image_of_injective _ hinj⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Stable
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.PStable
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.pStable :
    UpperTheory.V.Z.Sym.Loc.PStable := by
  intro O K _ _ _ _ _ Δ τ L hr j χ hj hχ a ha
  haveI := L.frac
  have hnω : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha, QuadraticAlgebra.norm_def]
    simp
  have hR : gOrb O j χ a = ((PS.Fv O τ).ncard : ℂ) := by
    rw [gLat O K Δ τ L hr j χ hj hχ a 1 1 (by rw [hnω]; simp), ← PS.vcount_eq L hr]
    simp [ha]
  rw [hR]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  set p : Kˣ := Units.mk0 _ hp0 with hpdef
  have hpv : ((p : Kˣ) : K) = algebraMap O K π := rfl
  have hpe : ¬ EvenVal O ((p : Kˣ) : K) := by
    rw [hpv]
    exact PS.not_even_irr L hπ
  have hfv : ∀ t : Kˣ, (PS.Fv O τ).ncard = (PS.Gs O τ (↑t) 1).ncard + (PS.Gs O τ (↑(t * p)) 1).ncard :=
    fun t => PS.fv_card L hr t p hpe
  by_cases hD : IsSquare (τ ^ 2 - 4)
  · have hI := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hr hD
    have hall : ∀ x : Kˣ, x ∈ NE τ := fun x =>
      (hsNE O K Δ τ L hr x).2 ((hsLaw O K Δ L).2.2.2 (τ ^ 2 - 4) x hr hD)
    obtain ⟨r, hrr⟩ := hD
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hr
      rw [hrr, mul_zero]
    have h2 : (2 : K) ≠ 0 := by
      have h := L.two.map (algebraMap O K)
      rw [map_ofNat] at h
      exact h.ne_zero
    set β : K := (τ - r) / 2 with hβdef
    set u : K := (((p : Kˣ) : K) - 1) / r with hudef
    have hb : β ^ 2 - τ * β + 1 = 0 := by
      rw [hβdef]
      field_simp
      linear_combination (-1 : K) * hrr
    have hτβ : τ - 2 * β = r := by
      rw [hβdef]
      field_simp
      ring
    have hru : r * u = ((p : Kˣ) : K) - 1 := by
      rw [hudef]
      field_simp
    set w : Etau K τ := ⟨1 - β * u, u⟩ with hwdef
    have hw : QuadraticAlgebra.norm w = ((p : Kˣ) : K) := by
      rw [QuadraticAlgebra.norm_def, hwdef]
      simp only
      linear_combination u ^ 2 * hb + u * hτβ + hru
    obtain ⟨y0, hy0⟩ : IsUnit w :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hw]; exact p.isUnit)
    have hy0n : QuadraticAlgebra.norm (y0 : Etau K τ) = ((p : Kˣ) : K) := by rw [hy0, hw]
    have hy0u : PS.nU y0 = p := Units.ext (by rw [PS.nU_val, hy0n])
    have hy0C : y0 ∉ Cint O τ := by
      intro h
      have := hI.1 y0 h
      rw [hy0n] at this
      exact hpe this
    have hpc : ∀ t : Kˣ, pcount O τ ↑t = ((PS.Fv O τ).ncard : ℂ) := by
      intro t
      have c1 : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = y0 * c * z ^ 2 := by
        intro y
        have hyne : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
          rw [← PS.nU_val]
          exact Units.ne_zero _
        rcases PS.even_or L hyne hp0 hpe with he | he
        · obtain ⟨z, c, hc, hyc⟩ := hI.2 y he
          exact ⟨z, c, hc, Or.inl (by rw [one_mul, hyc])⟩
        · have e : QuadraticAlgebra.norm ((y * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
              QuadraticAlgebra.norm (y : Etau K τ) / ((p : Kˣ) : K) := by
            rw [← PS.nU_val, map_mul, map_inv, hy0u, Units.val_mul, Units.val_inv_eq_inv_val,
              PS.nU_val, div_eq_mul_inv]
          obtain ⟨z, c, hc, hyc⟩ := hI.2 (y * y0⁻¹) (e ▸ he)
          refine ⟨z, c, hc, Or.inr ?_⟩
          rw [mul_assoc, ← hyc, mul_comm, inv_mul_cancel_right]
      have c2 : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * y0⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
        intro z hz
        exfalso
        have hE := hI.1 _ hz
        have hzn : ((PS.nU z : Kˣ) : K) ≠ 0 := Units.ne_zero _
        have e : QuadraticAlgebra.norm ((z ^ 2 * 1 * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
            ((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K) := by
          rw [← PS.nU_val, map_mul, map_mul, map_pow, map_one, mul_one, map_inv, hy0u, Units.val_mul,
            Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, div_eq_mul_inv]
        rw [e] at hE
        have hsq : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, (PS.nU z : K), hzn, by simp⟩
        apply hpe
        have := PS.even_mul hsq (PS.even_inv hE)
        have hp' : ((PS.nU z : Kˣ) : K) ^ 2 * (((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K))⁻¹ =
            ((p : Kˣ) : K) := by
          field_simp
        rwa [hp'] at this
      rw [PS.pcount_eq L hr t 1 y0 c1 c2]
      have hdisj : Disjoint (PS.Gs O τ (↑t) 1) (PS.Gs O τ (↑t) y0) := by
        rw [Set.disjoint_left]
        rintro S ⟨-, c, hc, hg⟩ ⟨-, c', hc', hg'⟩
        have hu := PS.gen_uniq hg hg'
        apply hy0C
        have e : y0 = (1 * c) * ((1 * c)⁻¹ * (y0 * c')) * c'⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (by rw [one_mul]; exact hc) hu) (inv_mem hc')
      rw [Set.ncard_union_eq hdisj (PS.gs_fin L hr t 1) (PS.gs_fin L hr t y0), PS.gs_ncard ((t : Kˣ) : K) y0,
        hy0u, hfv t, Units.val_mul]
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : Kˣ ⧸ NE τ), hpc]
    intro t ht
    exfalso
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ht (QuotientGroup.eq.2 (hall _))
  · have hC := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hr hD
    have hpc : ∀ (t : Kˣ) (b : (Etau K τ)ˣ), pcount O τ ↑t = ((PS.Gs O τ (↑t) b).ncard : ℂ) := by
      intro t b
      rw [PS.pcount_eq L hr t b b (fun y => ⟨1, b⁻¹ * y, by rw [hC]; trivial, Or.inl (by group)⟩)
        (fun z _ => by rw [hC]; trivial), Set.union_self]
    have hinv : ∀ t ∈ NE τ, ∀ x : Kˣ, pcount O τ ↑(t * x) = pcount O τ ↑x := by
      rintro t ⟨b, rfl⟩ x
      rw [hpc x b, PS.gs_ncard, hpc _ 1, Units.val_mul, mul_comm]
      rfl
    obtain ⟨⟨g0, hg0⟩, hsum⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hr hD
    have e : ∀ t : Kˣ, ((PS.Fv O τ).ncard : ℂ) = pcount O τ ↑t + pcount O τ ↑(t * p) := by
      intro t
      rw [hfv t, Nat.cast_add, hpc t 1, hpc (t * p) 1]
    by_cases hpN : p ∈ NE τ
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑g0 :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv g0 hg0
      rw [hS]
      have e1 := e 1
      have e2 := e g0
      rw [mul_comm, hinv p hpN] at e1 e2
      linear_combination (-1 / 2 : ℂ) * e1 + (-1 / 2 : ℂ) * e2
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑p :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv p hpN
      rw [hS, e 1, one_mul]
end

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.stable : UpperTheory.V.Z.Sym.Loc.Stable := by
  unfold Stable
  intro O K _ _ _ _ _ Δ τ hL c d m hD hev j hj χ hχ a ha
  have hreg := hD.reg
  have hc := hD.c_ne
  have h2K : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hshift : ∀ (f : Kˣ → ℂ), (∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x) → ∀ g : Kˣ,
      (∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)) → stabSum O c d m = ∑ᶠ t : Kˣ ⧸ NE τ, f (Quotient.out t) := by
    intro f hf g hk
    unfold stabSum
    rw [finsum_congr (fun t => hk _)]
    exact (sumShift O K Δ τ hL hreg f hf g).1
  by_cases hτ : τ ∈ (algebraMap O K).range
  swap
  · have h0 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0 := by
      intro t
      by_contra hne
      exact hτ (vanish O K Δ τ hL c d _ (datSmul K Δ τ c d m hD t) hne).1
    have hg : gOrb O j χ a = 0 := by
      by_contra hne
      exact hτ (gVanish O K Δ τ hL j hj χ a (Or.inl ha) hne)
    rw [hg]
    unfold stabSum
    simp only [h0, finsum_zero]
  obtain ⟨τ₀, hτ₀⟩ := hτ
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator hreg
  rcases tri hL τ₀ with ⟨hm, hu⟩ | ⟨hm, hu⟩ | ⟨hu1, hu2⟩
  · have hx : (2 + τ₀) - 2 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      have e : (2 + τ₀) - 2 ^ 2 = τ₀ - 2 := by ring
      rw [e]
      exact hm
    obtain ⟨r, hr2, hrm⟩ := sqrtO O K Δ hL (2 + τ₀) 2 hL.two hx
    have hrK : (algebraMap O K) r ^ 2 = 2 + τ := by
      rw [← map_pow, hr2, map_add (f := _), map_ofNat, hτ₀]
    have hlam : QuadraticAlgebra.norm ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) = 2 + τ := by
      rw [QuadraticAlgebra.norm_algebraMap, hrK]
    have hD0 := datLam K Δ τ c hreg hc _ hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c _ hlam z hz m' hm'
    have hP := caseP O K Δ τ hL hreg r hrm hrK c hev j χ hj hχ a ha z hz
    let f : Kˣ → ℂ := fun y => lcount O c (dLam ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk]
    have hc2 : -2 * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2K) hc
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hP ⟨Units.mk0 _ hc2, by rw [Units.val_mk0]⟩).1
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hm2 : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) = τ₀ + 2 := by push_cast; ring
      rw [e]
      exact hm
    obtain ⟨x, y, _, hsq, hn⟩ := rootEx O K Δ τ hL τ₀ (-1) hτ₀ hm2
    set u : Etau K τ := { re := (algebraMap O K) x, im := (algebraMap O K) y } with hu_def
    have hu2' : u ^ 2 = -ω := by
      rw [hsq]
      push_cast
      ring
    obtain ⟨ν, hνI, hνN⟩ := normEx O K Δ hL (-1)
    have hνN' : QuadraticAlgebra.norm ν = -1 := by
      rw [hνN]
      simp
    obtain ⟨ε, s, hs0, hΔ⟩ := hL.even
    have hΔ' : Δ * (s⁻¹) ^ 2 = (algebraMap O K) ↑ε := by
      rw [hΔ]
      field_simp
    obtain ⟨hdn, hform⟩ := datFormM O K Δ τ hL c u hu2' hn ν hνN' s⁻¹ (inv_ne_zero hs0)
    obtain ⟨m', hm'', hmove⟩ := dat_move hL hD hdn
    obtain ⟨t₁, rfl⟩ := hform m' hm''
    have hM := caseM O K Δ τ hL hreg τ₀ hτ₀ hm c hevc u hu2' hn ν hνI hνN' s⁻¹ ε hΔ'
    let g : Kˣ := t₁ * Units.mk0 _ hreg
    let f : Kˣ → ℂ := fun y => pcount O τ (y : K)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := by
      intro t ht x
      simp only [f, Units.val_mul]
      exact pNorm O K Δ τ hL t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g) := by
      intro k
      rw [hmove, ← smul_assoc, smul_smul, ← Units.val_mul, hM]
      simp only [f, g, Units.val_mul, Units.val_mk0, mul_assoc]
    rw [hshift f hf g hk]
    exact pStable O K Δ τ hL hreg j χ hj hχ a ha
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu2
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hU : (algebraMap O K) ↑(-(hu1.unit * hu2.unit)) = τ ^ 2 - 4 := by
      rw [Units.val_neg, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_neg, map_mul, map_add (f := _), map_sub,
        map_ofNat, hτ₀]
      ring
    obtain ⟨lam, hlamI, hlamN⟩ := normEx O K Δ hL hu1.unit
    have hlam : QuadraticAlgebra.norm lam = 2 + τ := by
      rw [hlamN, IsUnit.unit_spec, map_add (f := _), map_ofNat, hτ₀]
    have hD0 := datLam K Δ τ c hreg hc lam hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c lam hlam z hz m' hm'
    have hG := caseG O K Δ τ hL ⟨_, hU⟩ c hevc lam hlamI hlam z hz
    have hga := (gVals O K Δ τ hL hreg ⟨τ₀, hτ₀⟩ j χ hj hχ a ha z hz).2.1 ⟨_, hU⟩
    let f : Kˣ → ℂ := fun y => lcount O c (dLam lam z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk, hga]
    have h1 : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
      rw [Units.val_one]
      unfold hs
      rw [if_pos ⟨1, 0, by ring⟩]
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hG ⟨1, h1⟩).1
end

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Loc QuadraticAlgebra

private theorem two_add_ne {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := by
  intro h0
  apply h
  have : τ ^ 2 - 4 = (2 + τ) * (τ - 2) := by ring
  rw [this, h0, zero_mul]

private theorem unit_one_add {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) :
    ((toUnit (1 + ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = 1 + ω := by
  have h' := two_add_ne h
  have : IsUnit (1 + ω : Etau K τ) := by
    refine IsUnit.of_mul_eq_one (⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ : Etau K τ) ?_
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  simp [toUnit, this]

private theorem unit_om {K : Type} [Field K] (τ : K) :
    ((toUnit (ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = ω := by
  have : IsUnit (ω : Etau K τ) := by
    refine IsUnit.of_mul_eq_one (⟨τ, -1⟩ : Etau K τ) ?_
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  simp [toUnit, this]

private theorem jstd_tr {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

private theorem mem_int {F : Type} [Field F] [NumberField F] (v : Pl F) (y : F) (hy : v.valuation F y ≤ 1) :
    cv v y ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (y : v.adicCompletion F) ≤ 1
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

private theorem ae_int {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ (algebraMap (Ov v) (Kv v)).range := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
  by_contra hn
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  exact hv ⟨⟨_, mem_int v x hn⟩, rfl⟩

private theorem ae_unit {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  filter_upwards [ae_int x, ae_int x⁻¹] with v ⟨a, ha⟩ ⟨b, hb⟩
  have : a * b = 1 := by
    apply Subtype.ext
    change algebraMap (Ov v) (Kv v) (a * b) = 1
    rw [map_mul, ha, hb, ← map_mul, mul_inv_cancel₀ hx, map_one]
  exact ⟨⟨a, b, this, by rw [mul_comm, this]⟩, ha⟩

private theorem fp_zero {I : Type} (S : Finset I) (g : I → ℂ) (hg : ∀ᶠ v in Filter.cofinite, g v = 1) (v₀ : I) (h₀ : v₀ ∉ S)
    (h : g v₀ = 0) : (∏ᶠ (v : I) (_ : v ∉ S), g v) = 0 := by
  classical
  have hg' : (Function.mulSupport fun v => ∏ᶠ (_ : v ∉ S), g v).Finite := by
    refine (show {v | ¬ g v = 1}.Finite from hg).subset fun v hv h => hv ?_
    simp [h]
  exact finprod_eq_zero _ v₀ (by simp [h₀, h]) hg'

private theorem loc_ne {F : Type} [Field F] [NumberField F] {τ : F} (h : τ ^ 2 - 4 ≠ 0) (v : Pl F) : cv v τ ^ 2 - 4 ≠ 0 := by
  have := (map_ne_zero (cv v)).2 h
  simpa [map_ofNat] using this

private theorem unr_one (O K : Type) [CommRing O] [Field K] [Algebra O K] : Unr O (1 : Kˣ →* ℂˣ) := fun _ => rfl

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

theorem sg_vanish (hD : D.Ok) {τ : F} (h : τ ^ 2 - 4 ≠ 0) (hi : ¬ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) :
    D.nS τ = 0 ∧ D.nK τ = 0 := by
  push Not at hi
  obtain ⟨w, hw, hi⟩ := hi
  have ae : ∀ᶠ v : Pl F in Filter.cofinite, gOrb (Ov v) (jstd (cv v τ)) 1 (toUnit ω) = 1 ∧
      gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + ω)) = 1 := by
    filter_upwards [ae_unit h, ae_unit (two_add_ne h), ae_int τ, D.Sg.eventually_cofinite_notMem] with v h1 h2 h4 h3
    obtain ⟨a, b, -⟩ := gVals (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v h3) (loc_ne h v) h4 (jstd _) (D.χ v) (jstd_tr _) (hD.chi v).1
      _ (unit_om _) _ (unit_one_add (loc_ne h v))
    obtain ⟨-, b', -⟩ := gVals (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v h3) (loc_ne h v) h4 (jstd _) 1 (jstd_tr _) (unr_one _ _)
      _ (unit_om _) _ (unit_one_add (loc_ne h v))
    refine ⟨b' (by simpa [map_ofNat] using h1), ?_⟩
    rw [a (by simpa [map_ofNat] using h2), b (by simpa [map_ofNat] using h1)]
  constructor
  · refine fp_zero D.Sg _ (ae.mono fun _ h => h.1) w hw ?_
    by_contra hn
    exact hi (gVanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ (jstd_tr _) _ _ (Or.inl (unit_om _)) hn)
  · refine fp_zero D.Sg _ (ae.mono fun _ h => h.2) w hw ?_
    by_contra hn
    exact hi (gVanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ (jstd_tr _) _ _ (Or.inr (unit_one_add (loc_ne h w))) hn)

theorem sg_ev (hD : D.Ok) {τ c : F} {d m : EL Δ τ} (h : IsDat c d m) (hn : D.nL c d m ≠ 0) : D.Ev (c * (2 - τ)) := by
  intro w hw
  have hl : lcount (Ov w) (cv w c) (elmap (cv w) d) (elmap (cv w) m) ≠ 0 := by
    intro h0
    refine hn (fp_zero D.Sg _ ?_ w hw h0)
    filter_upwards [genPl F Δ D hD τ c d m h] with v hv
    have := hv 1
    rw [Units.val_one, one_smul] at this
    rw [this]
    exact if_pos (one_mem _)
  have := (vanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ _ _ (modelMap F (Kv w) (cv w) Δ τ c d m h).1 hl).2
  rw [map_mul, map_sub, map_ofNat]
  exact this

theorem sg_stab (hD : D.Ok) {τ c : F} {d m : EL Δ τ} (h : IsDat c d m) (he : D.Ev (c * (2 - τ))) :
    (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = D.nS τ := by
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  have e := he v hv
  rw [map_mul, map_sub, map_ofNat] at e
  exact stable (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hv) _ _ _ (modelMap F (Kv v) (cv v) Δ τ c d m h).1 e _ (jstd_tr _) _
    (unr_one _ _) _ (unit_om _)

theorem sg_inner (hD : D.Ok) {τ : F} {e : ℝ} {d m : EL Δ τ} (hτ : IsCM τ) (hs : D.Spl τ) (h : IsDat 1 d m)
    (hk : ∀ c : F, TPos c → D.Ev (c * (2 - τ)) →
      (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = e * D.nK τ) :
    (Function.support fun x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ) =>
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m))).Finite ∧
    ∑ᶠ x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ),
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m)) =
      ((D.Sel 1).ncard : ℂ) * (1 / 2 * (D.nS τ + e * D.nK τ)) := by
  classical
  have hp : TPos (2 - τ) := fun σ => by
    have := hτ σ
    simp only [map_sub, map_pow, map_ofNat] at this ⊢
    nlinarith
  obtain ⟨hfin, hcard⟩ := (selCard F Δ D hD).2.2 _ hp
  have hd : ∀ c : Fˣ, IsDat (c : F) d m := fun c => { h with c_ne := c.ne_zero }
  have hT := fun c : Fˣ => sumT F Δ D hD τ c d m hτ hs (hd c)
  have hf : (Function.support fun x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ) =>
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m))).Finite := by
    refine (hfin.biUnion fun c _ => (hT c.out).1.image (Prod.mk c)).subset ?_
    rintro ⟨c, u⟩ hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    have h3 := left_ne_zero_of_mul h2
    simp only [Set.mem_iUnion]
    refine ⟨c, ?_, u, ⟨?_, right_ne_zero_of_mul h2⟩, rfl⟩
    · by_contra hn; exact h1 (if_neg hn)
    · by_contra hn; exact h3 (if_neg hn)
  refine ⟨hf, ?_⟩
  rw [finsum_curry _ hf, ← hcard]
  have e1 : ∀ c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range, (∑ᶠ u : Fˣ ⧸ NE τ,
      one (c ∈ D.Sel (2 - τ)) * (one (TPos (u.out : F)) * D.nL (c.out : F) d ((u.out : F) • m))) =
      ∑ᶠ (_ : c ∈ D.Sel (2 - τ)), (1 / 2 * (D.nS τ + e * D.nK τ)) := fun c => by
    by_cases hc : c ∈ D.Sel (2 - τ)
    · have : one (c ∈ D.Sel (2 - τ)) = 1 := if_pos hc
      simp only [this, one_mul]
      rw [(hT c.out).2, sg_stab D hD (hd _) hc.2, hk _ hc.1 hc.2, finsum_eq_if, if_pos hc]
    · have : one (c ∈ D.Sel (2 - τ)) = 0 := if_neg hc
      simp only [this, zero_mul, finsum_zero]
      rw [finsum_eq_if, if_neg hc]
  rw [finsum_congr e1, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]

theorem sg_sigma {T : Type} [Finite T] {β : T → Type} (g : (Σ i, β i) → ℂ)
    (hg : ∀ i, (Function.support fun x => g ⟨i, x⟩).Finite) : ∑ᶠ j, g j = ∑ᶠ i, ∑ᶠ x, g ⟨i, x⟩ := by
  classical
  haveI := Fintype.ofFinite T
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun i => (hg i).toFinset), Finset.sum_sigma, finsum_eq_sum_of_fintype]
  · exact Finset.sum_congr rfl fun i _ => (finsum_eq_sum _ (hg i)).symm
  · rintro ⟨i, x⟩ hx
    simpa using hx

section Scale

variable {K : Type} [Field K] {Δ τ : K}

private theorem ofE_mul' (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_inv (z : (Etau K τ)ˣ) : ofE Δ (z : Etau K τ) * ofE Δ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
  rw [← ofE_mul', Units.mul_inv]
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private noncomputable def scaleEq (Δ : K) (s : Kˣ) (z : (Etau K τ)ˣ) : Sp Δ τ ≃ₗ[Lsq K Δ] Sp Δ τ where
  toFun x := (algebraMap K (Lsq K Δ) s * x.1, ofE Δ (z : Etau K τ) * x.2)
  invFun x := (algebraMap K (Lsq K Δ) (s⁻¹ : Kˣ) * x.1, ofE Δ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2)
  map_add' x y := by simp [mul_add]
  map_smul' a x := by simp [mul_left_comm]
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp only []
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · simp only []
      rw [← mul_assoc, mul_comm _ (ofE Δ (z : Etau K τ)), ofE_inv, one_mul]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · simp only []
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    · simp only []
      rw [← mul_assoc, ofE_inv, one_mul]

private theorem sigL_ofE (z : Etau K τ) (x : EL Δ τ) : sigL (ofE Δ z * x) = ofE Δ z * sigL x := by
  ext <;> simp [ofE, sigL] <;> ring

private theorem ofE_norm (z : Etau K τ) (m : EL Δ τ) : QuadraticAlgebra.norm z • m = m * (ofE Δ z * star (ofE Δ z)) := by
  ext <;> simp [ofE, QuadraticAlgebra.norm_def] <;> ring

theorem sg_scale {c : K} {d m : EL Δ τ} {δ ι P} (h : Models c d m δ ι P) (s : Kˣ) (z : (Etau K τ)ˣ) :
    ∃ P', Models (c * s ^ 2) d (QuadraticAlgebra.norm (z : Etau K τ) • m) δ ι P' := by
  refine ⟨(scaleEq Δ s z).trans P, fun x y => ?_, fun x => ?_, fun w x => ?_⟩
  · simp only [LinearEquiv.trans_apply]
    rw [← h.form]
    change _ = algebraMap K (Lsq K Δ) c * (algebraMap K (Lsq K Δ) s * x.1) * star (algebraMap K (Lsq K Δ) s * y.1) +
      QuadraticAlgebra.trace (m * (ofE Δ (z : Etau K τ) * x.2) * star (sigL (ofE Δ (z : Etau K τ) * y.2)))
    have e : star (algebraMap K (Lsq K Δ) s) = algebraMap K (Lsq K Δ) s := by ext <;> simp
    rw [sigL_ofE, star_mul', star_mul', e, herm, ofE_norm, map_mul, map_pow]
    congr 1
    · ring
    · congr 1
      ring
  · simp only [LinearEquiv.trans_apply]
    rw [← h.semi]
    congr 1
    have e : star (algebraMap K (Lsq K Δ) s) = algebraMap K (Lsq K Δ) s := by ext <;> simp
    refine Prod.ext ?_ ?_
    · change algebraMap K (Lsq K Δ) s * star x.1 = star (algebraMap K (Lsq K Δ) s * x.1)
      rw [star_mul', e]
    · change ofE Δ (z : Etau K τ) * (d * sigL x.2) = d * sigL (ofE Δ (z : Etau K τ) * x.2)
      rw [sigL_ofE, mul_left_comm]
  · simp only [LinearEquiv.trans_apply]
    rw [← h.tor]
    congr 1
    refine Prod.ext rfl ?_
    change ofE Δ (z : Etau K τ) * (ofE Δ (quo w) * x.2) = ofE Δ (quo w) * (ofE Δ (z : Etau K τ) * x.2)
    rw [mul_left_comm]

theorem sg_out {c t : Kˣ} {d m : EL Δ τ} {δ ι P} (h : Models (c : K) d ((t : K) • m) δ ι P) :
    ∃ (x : (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) × (Kˣ ⧸ NE τ)), ∃ P',
      Models (x.1.out : K) d ((x.2.out : K) • m) δ ι P' := by
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom 2 : Kˣ →* Kˣ).range c
  obtain ⟨⟨_, z, rfl⟩, hz⟩ := QuotientGroup.mk_out_eq_mul (NE τ) t
  obtain ⟨P', h'⟩ := sg_scale h s z
  refine ⟨(c, t), P', ?_⟩
  simp only [hs, hz]
  rw [smul_smul, mul_comm _ (t : K)] at h'
  exact h'

end Scale

end UpperTheory.V.Z.Sym.Glob
