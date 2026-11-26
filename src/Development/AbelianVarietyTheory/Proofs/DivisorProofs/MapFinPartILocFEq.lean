module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.AlphaSplit

open Formalism.L2.Host GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal GlobalTheory.Mem.Col2.SplitChar
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt IsUnifAt exists_unif ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

variable {D : D7}

def mulU {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (hN : Even ((N₁ : ℤ) + N₂ - N)) : HeckeU D N where
  f := χ₁.f * χ₂.f
  n := χ₁.n + χ₂.n
  unitary x := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, χ₁.unitary, χ₂.unitary, mul_one]
  cont := by
    obtain ⟨m₁, hm₁, h₁⟩ := χ₁.cont
    obtain ⟨m₂, hm₂, h₂⟩ := χ₂.cont
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun u hu ⟨s, hs, e⟩ => ?_⟩
    rw [Nat.cast_mul] at e
    rw [MonoidHom.mul_apply, h₁ u hu ⟨m₂ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; ring⟩,
      h₂ u hu ⟨m₁ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; ring⟩, one_mul]
  aut a := by
    have h1 := χ₁.aut a
    have h2 := χ₂.aut a
    have hne : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ≠ 0 := fun τ => by
      have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
      exact div_ne_zero h (by simpa using h)
    rw [MonoidHom.mul_apply, Units.val_mul]
    simp only [Pi.add_apply, zpow_add₀ (hne _), Finset.prod_mul_distrib]
    calc _ = (((χ₁.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ)) *
        (((χ₂.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  norm x := by rw [MonoidHom.mul_apply, χ₁.norm, χ₂.norm, one_mul]
  par τ := by
    have e : (χ₁.n + χ₂.n) τ - (N : ℤ) = (χ₁.n τ - N₁) + (χ₂.n τ - N₂) + ((N₁ : ℤ) + N₂ - N) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    exact ((χ₁.par τ).add (χ₂.par τ)).add hN
  unr u hu hz := by rw [MonoidHom.mul_apply, χ₁.unr u hu hz, χ₂.unr u hu hz, one_mul]

theorem mulU_f {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (hN : Even ((N₁ : ℤ) + N₂ - N)) (x : (AE D)ˣ) :
    (mulU N χ₁ χ₂ hN).f x = χ₁.f x * χ₂.f x := rfl

theorem eq_one_of_unr {χ : HChar D.host.E} (hχ : ∀ v, χ.UnrAt v) {u : (AE D)ˣ} (hu : IntU D u) :
    χ.1 (finIdl D u) = 1 := by
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) fun v x hx => ?_
  · exact congrFun (finIdl_fst D u) w
  · have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx]
      exact finIdl_unit hu v
    exact hχ v x hxu

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

open Neutral.B1 hiding locF
open Formalism.L2.Host GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal GlobalTheory.Mem.Col2.SplitChar
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt IsUnifAt exists_unif ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

variable {D : D7}

theorem map_finPartI_locF_eq (χ : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ) :
    χ.1 (finPartI D.host.E (locF (L := D.host.E) D.host.F v k)) = χ.resFin v k := by
  unfold Formalism.L2.Host.HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem even_log_norm (z : (AE D)ˣ) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ConjPl D.host.conj.toRingEquiv w w) : Even (WithZero.log (valAt w (finIdl D (z * sgU D z)))) := by
  have e : valAt w (finIdl D (z * sgU D z)) = vl D w (z : AE D) * vl D w (z : AE D) := by
    change vl D w ((z : AE D) * sgA D z) = _
    rw [map_mul, vl_sgA hw]
  have h0 : vl D w (z : AE D) ≠ 0 := valAt_ne_zero w (finIdl D z)
  rw [e, WithZero.log_mul h0 h0]
  exact ⟨_, rfl⟩

theorem eta_norm {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) (z : (AE D)ˣ) :
    χ.1 (finIdl D (z * sgU D z)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a := finIdl D (z * sgU D z) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced z
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles D.host.E := ∏ v ∈ T, locF (L := D.host.E) D.host.F v (unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dite_eq_left hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (locF (L := D.host.E) D.host.F v (unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl]
      change WithZero.exp (-Formalism.L2.Host.ordF w (Formalism.L2.Host.upF (↥D.host.F) (unif (w.under (𝓞 D.host.F))))) ^ _ = _
      rw [hu, ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hunit : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  have hfac : ∀ v, χ.1 (finPartI D.host.E (locF (L := D.host.E) D.host.F v (unif v) ^ m v)) = 1 := fun v => by
    rw [map_zpow, map_zpow, map_finPartI_locF_eq, hχ.res.1 v, etaFin]
    split_ifs with h1
    · have hev : Even (m v) := by
        simp only [m]
        split_ifs with hex
        · set w := hex.choose
          have hwv : w.under (𝓞 D.host.F) = v := hex.choose_spec
          obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
          have hu' : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
            (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
          obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
          have m1 : w ∈ aboveF (L := D.host.E) D.host.F v := by simp [aboveF, hwv]
          have m2 : w' ∈ aboveF (L := D.host.E) D.host.F v := by simp [aboveF, hu', hwv]
          rw [hx, Finset.mem_singleton] at m1 m2
          have e : w' = w := m2.trans m1.symm
          rw [e] at hw'
          exact (even_log_norm z w hw').neg
        · exact ⟨0, by simp⟩
      rw [← zpow_mul, mul_comm, zpow_mul, hev.neg_one_zpow, one_zpow]
    · exact one_zpow _
  have hb : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    exact Finset.prod_eq_one fun v _ => hfac v
  have hr : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 := by
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hunit) (fun _ => rfl)
      fun v x hx => ?_
    have hx' : (x : v.adicCompletion D.host.E) = ((b⁻¹ * a : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := hx
    have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact hunit v
    exact hχ.unr v x hxu
  have key : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e1 : χ.1 a = χ.1 (finPartI D.host.E a) := by rw [ha_def, finPartI_finIdl]
  rw [e1, key, map_mul, map_mul, hb, hr, one_mul]

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

variable {D : D7}

def invU {N : ℕ} (χ : HeckeU D N) : HeckeU D N where
  f := χ.f⁻¹
  n := -χ.n
  unitary x := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary, inv_one]
  cont := by
    obtain ⟨m, hm, h⟩ := χ.cont
    exact ⟨m, hm, fun u hu hs => by rw [MonoidHom.inv_apply, h u hu hs, inv_one]⟩
  aut a := by
    have h1 := χ.aut a
    have hne : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ≠ 0 := fun τ => by
      have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
      exact div_ne_zero h (by simpa using h)
    have hf : ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    rw [← mul_inv, h1, inv_one]
  norm x := by rw [MonoidHom.inv_apply, χ.norm, inv_one]
  par τ := by
    have e : (-χ.n) τ - (N : ℤ) = -(χ.n τ - N) - 2 * N := by simp only [Pi.neg_apply]; ring
    rw [e]
    exact (χ.par τ).neg.sub (even_two_mul _)
  unr u hu hz := by rw [MonoidHom.inv_apply, χ.unr u hu hz, inv_one]

theorem invU_f {N : ℕ} (χ : HeckeU D N) (x : (AE D)ˣ) : (invU χ).f x = (χ.f x)⁻¹ := rfl

end GlobalTheory.AlphaSplit

noncomputable section

namespace GlobalTheory.AlphaSplit

open Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Col2.SplitChar
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt IsUnifAt exists_unif ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

variable {D : D7}

def etaU {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) : HeckeU D 1 where
  f := χ.1.comp (finIdl D)
  n := fun _ => 1
  unitary := fun _ => hχ.unitary _
  cont := ⟨1, one_pos, fun _ hu _ => eq_one_of_unr hχ.unr hu⟩
  aut := fun a => by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
    have h2 := hχ.inf a
    rw [← D.eTau.prod_comp] at h2
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ h2.symm
  norm := eta_norm hχ
  par := fun _ => by simp
  unr := fun _ hu _ => eq_one_of_unr hχ.unr hu

theorem etaU_f {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) (x : (AE D)ˣ) : (etaU hχ).f x = χ.1 (finIdl D x) := rfl

end GlobalTheory.AlphaSplit
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductions
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeFrameCover

open GlobalTheory.LevDesc

section Primes

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem typePrime_isPrime {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (v : Sq D.host) :
    (typePrime l v).IsPrime := by
  refine halfPrime_isPrime l v.2.1.isMaximal ?_
  obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
  rw [hM, hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ v.2.2

theorem typePrime_eq {l l₂ : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (hl₂ : IsTypeLevel l₂)
    (hle : l₂.Mb ≤ l.Mb) (v : Sq D.host) : typePrime l₂ v = typePrime l v := by
  obtain ⟨hP, hN⟩ := hl₂.typePrime_spec v
  have hne : typePrime l₂ v ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact (D.host.g_prime v.1).ne_zero hN.symm
  exact (hP.isMaximal hne).eq_of_le (typePrime_isPrime hM v).ne_top (sup_le_sup_right hle _)

theorem exists_mem_eq {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) (v : Sq D.host) : ∃ PP ∈ Pg, PP.asIdeal = typePrime l v := by
  have hP := typePrime_isPrime hM v
  have h1 : ∏ PP ∈ Pg, PP.asIdeal ≤ typePrime l v := hMb ▸ le_sup_left
  obtain ⟨PP, hPP, h2⟩ := (hP.prod_le).1 h1
  exact ⟨PP, hPP, PP.isMaximal.eq_of_le hP.ne_top h2⟩

theorem exists_equiv {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) : ∃ e : Sq D.host ≃ Pg, ∀ v, (e v).1.asIdeal = typePrime l v := by
  choose f hf hfe using exists_mem_eq hM hMb
  have hinj : Function.Injective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    intro v w h
    have h' : typePrime l v = typePrime l w := by
      rw [← hfe v, ← hfe w]; exact congrArg (fun x : Pg ↦ x.1.asIdeal) h
    by_contra hvw
    have hc := typePrime_coprime (l := l) hvw
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq, h', sup_idem] at hc
    exact (typePrime_isPrime hM w).ne_top hc
  have hsurj : Function.Surjective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    rintro ⟨PP, hPP⟩
    have hle : l.Mb ≤ PP.asIdeal := hMb ▸ Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    have hm : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Nat.cast_mul, ← hM]; exact hle (natCast_M_mem l)
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rcases PP.isPrime.mem_or_mem hm with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal := by
      rw [Ideal.mem_comap, map_natCast]; exact hk
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal, inferInstance, fun e ↦ by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime k).ne_zero (by exact_mod_cast hg)⟩
    have he : typePrime l ⟨k, ⟨w, hg⟩⟩ = PP.asIdeal :=
      halfPrime_eq l w.isMaximal PP.isPrime (sup_le hle Ideal.map_comap_le)
    refine ⟨⟨k, ⟨w, hg⟩⟩, Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)⟩
    exact (hfe _).trans he
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun v ↦ hfe v⟩

theorem nonempty_iso {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (v : Sq D.host) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : PP.asIdeal = typePrime l₂ v) : Nonempty (ZMod (D.host.g v.1) ≃+* kP PP) := by
  have hc : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (kP PP)
  exact ⟨ZMod.ringEquivOfPrime (kP PP) (D.host.g_prime v.1) (by rw [← Nat.card_eq_fintype_card, hc])⟩

end Primes

section Frame

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem exists_frame {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (hr : Dw.p + Dw.q = D.R.r) (v : Sq D.host)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP.asIdeal = typePrime l₂ v) (iso : ZMod (D.host.g v.1) ≃+* kP PP)
    {n : ℕ} (hn : n = D.R.r) (φ : Dw.La →ₗ[𝓞 D.host.E] (Fin n → kP PP)) (hφ : Function.Surjective φ) :
    ∃ f : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)),
      ∀ x : Dw.La, f (Submodule.Quotient.mk x) = fun j ↦ iso.symm (φ x (Fin.cast hn.symm j)) := by
  subst hn
  have hker : typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ≤ LinearMap.ker φ := by
    rw [← hPP, Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let ψ := (typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).liftQ φ hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l₂ v) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l₂ v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l₂ v)) = D.host.g v.1 ^ D.R.r := by
    rw [GlobalTheory.natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  have hc' : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN' : Nat.card (Fin D.R.r → kP PP) = D.host.g v.1 ^ D.R.r := by
    rw [Nat.card_fun, hc', Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Finite (QMod Dw.La (typePrime l₂ v)) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero _ (D.host.g_prime _).ne_zero)
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hN, hN'])
  let e1 : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → kP PP) := AddEquiv.ofBijective ψ.toAddMonoidHom hψb
  let e2 : (Fin D.R.r → kP PP) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)) :=
    AddEquiv.piCongrRight (fun _ ↦ iso.symm.toAddEquiv)
  exact ⟨e1.trans e2, fun x ↦ rfl⟩

end Frame

section Main

theorem mulVec_reindex {K : Type} [CommRing K] {n r : ℕ} (h : n = r) (hr : r ≤ n) (Mn : Matrix (Fin n) (Fin n) K)
    (y z : Fin n → K)
    (hyz : (fun j ↦ y (Fin.cast h.symm j)) = Mn.submatrix (Fin.castLE hr) (Fin.castLE hr) *ᵥ fun j ↦ z (Fin.cast h.symm j)) :
    y = Mn *ᵥ z := by
  subst h
  exact hyz

theorem typeFrame_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hβ H Dw l l₂ ι hι hr hA hM hl₂ hle hMb lev hlev
  obtain ⟨e, he⟩ := exists_equiv hM hMb
  have htp : ∀ v, typePrime l₂ v = typePrime l v := typePrime_eq hM hl₂ hle
  have he₂ : ∀ v, (e v).1.asIdeal = typePrime l₂ v := fun v ↦ (he v).trans (htp v).symm
  let iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1 := fun v ↦ (nonempty_iso hl₂ v _ (he₂ v)).some
  have hφ := fun v : Sq D.host ↦ GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) (R.βW i) (R.ΛW i) hβ Dw.La ι hι (e v).1
  choose φ hφs hφk using hφ
  have hfr0 := fun v ↦ exists_frame hl₂ hr v (e v).1 (he₂ v) (iso v) (rank_Wc i) (φ v) (hφs v)
  choose fr hfr using hfr0
  refine ⟨fr, e, iso, ?_, ?_⟩
  · intro γ g hg a
    obtain ⟨κ, hκ, hκa⟩ := hlev g
    have hSt : Lev.finE (Wc D i) κ ∈ St (R.βW i) := parLev_St hκ.2.1
    have hin : ∀ v, l.Mb ≤ (e v).1.asIdeal := fun v ↦ by rw [he v]; exact le_sup_left
    have hkill : ∀ v, ∀ u ∈ l.Mb, ∀ x : Dw.La, φ v (u • x) = 0 := by
      intro v u hu x
      rw [map_smul]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hin v hu), zero_mul]
    have hcop : l.Mb ⊔ Mfr l = ⊤ := l.coprime
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l)
    have ha : a = u • a + w • a := by rw [← add_smul, huw, one_smul]
    have hlevφ : ∀ v, φ v (lev g a) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)).1 *ᵥ φ v a := by
      intro v
      have h1 := hφk v κ hSt l.M (hin v (natCast_M_mem l)) (w • a) (lev g (w • a))
        (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
      have h2 : φ v (w • a) = φ v a := by
        conv_rhs => rw [ha]
        rw [map_add (f := _), hkill v u hu, zero_add]
      have h3 : φ v (lev g a) = φ v (lev g (w • a)) := by
        conv_lhs => rw [ha]
        rw [map_add (f := _), map_add (f := _), map_smul, hkill v u hu, zero_add]
      rw [h3, h1, h2]
    have hliftφ : ∀ v, φ v (liftLa γ a) = φ v (lev g a) := by
      intro v
      have hγa : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
      have h0 : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) *ᵥ
          fr v (Submodule.Quotient.mk a) = fr v (Submodule.Quotient.mk (liftLa γ a)) := by
        have h00 := GlobalTheory.LevDesc.typeRed_mulVec fr γ v (Submodule.Quotient.mk a)
        rw [hγa] at h00
        exact h00
      rw [hfr, hfr] at h0
      have h1 := GlobalTheory.LevelActionPinned.equiv_mulVec (iso v)
        (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)))
        (fun j ↦ (iso v).symm (φ v a (Fin.cast (rank_Wc i).symm j)))
      rw [h0] at h1
      simp only [RingEquiv.apply_symm_apply] at h1
      have hT : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).map (iso v) =
          (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ) : Matrix _ _ _).submatrix
            (Fin.castLE (R.datWp i R.triv).hr) (Fin.castLE (R.datWp i R.triv).hr) := by
        have h5 : R.eG g (e v) = upperLeftBlock (R.datWp i R.triv).hr (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)) :=
          (congrFun hκ.2.2 (e v)).symm
        have h6 := upper_block_val_submatrix (R.datWp i R.triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (e v).2))
        rw [← h5, hg v] at h6
        exact h6
      rw [hT] at h1
      rw [hlevφ v]
      exact mulVec_reindex (rank_Wc i) _ _ _ _ h1
    have hall : ∀ v, liftLa γ a - lev g a ∈ typePrime l v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      intro v
      have hx : φ v (liftLa γ a - lev g a) = 0 := by rw [map_sub, sub_eq_zero, hliftφ v]
      have h4 : fr v (Submodule.Quotient.mk (liftLa γ a - lev g a)) = 0 := by
        rw [hfr, hx]
        funext j
        simp
      have h5 := (AddEquiv.map_eq_zero_iff (fr v)).1 h4
      rw [Submodule.Quotient.mk_eq_zero, htp] at h5
      exact h5
    have h3 := mem_iInf_smul_top (typePrime_coprime (l := l)) hall
    have hle' : ⨅ v, typePrime l v ≤ l.Mb := iInf_typePrime_le.trans
      (sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (by rw [← hM]; exact natCast_M_mem l)))
    exact Submodule.smul_mono_left hle' h3
  · intro γ hγ
    rw [typeRed_eq_one, mem_grpR_iff]
    intro v q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
    rw [h1, ← Submodule.Quotient.mk_sub]
    have h2 : liftLa γ a - a ∈ typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mono_left ((le_sup_left : l.Mb ≤ typePrime l v).trans (htp v).ge) (hγ a)
    exact map_mem_smul_top (l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ h2

end Main

end GlobalTheory.TypeFrameCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductionsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  first | exact @GlobalTheory.TypeFrameCover.typeFrame_cover | exact GlobalTheory.TypeFrameCover.typeFrame_cover | (intros; apply GlobalTheory.TypeFrameCover.typeFrame_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameter
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section
namespace GlobalTheory.HoweD
open scoped Matrix
open GlobalTheory.RealLift.OneParam GlobalTheory.RealLift.CharTrace

theorem prod_charD {ι : Type} [Fintype ι] [DecidableEq ι] {R S : ι → ℕ} (χ : (∀ w, Mat (R w) (S w)) → ℂ)
    (hmul : ∀ g h : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → (∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)) →
      χ (g * h) = χ g * χ h)
    (hc : ContinuousOn χ {g | ∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)})
    (hne : ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g ≠ 0) :
    ∃ n : ι → ℤ, ∀ g : ∀ w, Mat (R w) (S w), (∀ w, (g w)ᴴ * Jm (R w) (S w) * g w = Jm (R w) (S w)) → χ g = ∏ w, (g w).det ^ n w := by
  have upd : ∀ w (a : Mat (R w) (S w)), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) → ∀ v,
      (Function.update (1 : ∀ w, Mat (R w) (S w)) w a v)ᴴ * Jm (R v) (S v) * Function.update (1 : ∀ w, Mat (R w) (S w)) w a v = Jm (R v) (S v) := by
    intro w a ha v
    by_cases hv : v = w
    · subst hv; simpa using ha
    · rw [Function.update_of_ne hv]; exact mem_one
  have key : ∀ w, ∃ n : ℤ, ∀ a : Mat (R w) (S w), aᴴ * Jm (R w) (S w) * a = Jm (R w) (S w) →
      χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a) = a.det ^ n := by
    intro w
    refine charUpq (R w) (S w) (fun a => χ (Function.update (1 : ∀ w, Mat (R w) (S w)) w a)) ?_ ?_ ?_
    · intro a b ha hb
      have e : Function.update (1 : ∀ w, Mat (R w) (S w)) w (a * b) =
          Function.update (1 : ∀ w, Mat (R w) (S w)) w a * Function.update (1 : ∀ w, Mat (R w) (S w)) w b := by
        funext v
        by_cases hv : v = w
        · subst hv; simp
        · simp [Function.update_of_ne hv]
      rw [e]
      exact hmul _ _ (upd w a ha) (upd w b hb)
    · exact hc.comp (show Continuous (Function.update (1 : ∀ w, Mat (R w) (S w)) w) from continuous_const.update w continuous_id).continuousOn
        fun a ha => upd w a ha
    · intro a ha; exact hne _ (upd w a ha)
  choose n hn using key
  refine ⟨n, fun g hg => ?_⟩
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (fun _ => mem_one) (fun _ => mem_one)
    rw [mul_one] at e
    have hz := hne 1 (fun _ => mem_one)
    exact mul_left_cancel₀ hz (e.symm.trans (mul_one _).symm)
  have pc : ∀ (s : Finset ι) v, (s.piecewise g 1 v)ᴴ * Jm (R v) (S v) * s.piecewise g 1 v = Jm (R v) (S v) := by
    intro s v
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hg v
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact mem_one
  have ind : ∀ s : Finset ι, χ (s.piecewise g 1) = ∏ w ∈ s, (g w).det ^ n w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      have e : (insert a s).piecewise g 1 = Function.update (1 : ∀ w, Mat (R w) (S w)) a (g a) * s.piecewise g 1 := by
        funext v
        by_cases hv : v = a
        · subst hv; simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hv, Function.update_of_ne hv]
      rw [e, hmul _ _ (upd a (g a) (hg a)) (pc s), hn a (g a) (hg a), ih, Finset.prod_insert ha]
  simpa using ind Finset.univ

theorem deriv_charD :
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC ν hmul hcont hne
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  set U : Set (∀ w : InfinitePlace F, Mat (R w) (S w)) := {h | ∀ w, (h w)ᴴ * Jm (R w) (S w) * h w = Jm (R w) (S w)} with hU
  set Λ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → Matrix β β (AE F E) :=
    fun h => 1 + liftM τ ξ (fun w => C w * h w * C' w - 1) with hΛ
  have Λπ : ∀ h w, (Λ h).map (piInf (τ w)) = C w * h w * C' w := fun h w => by
    rw [hΛ, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have Λat : ∀ h, At (evI F) (Λ h - 1) := fun h => by
    rw [hΛ, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have Λmul : ∀ h h', Λ (h * h') = Λ h * Λ h' := fun h h' => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : Λ h * Λ h' - Λ (h * h') = (Λ h - 1) * Λ h' + (Λ h' - 1) - (Λ (h * h') - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (Λat h) _) (Λat h')) (Λat _)
    · rw [Matrix.map_mul, Λπ, Λπ, Λπ, Pi.mul_apply]
      calc C w * h w * C' w * (C w * h' w * C' w) = C w * h w * (C' w * C w) * h' w * C' w := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have Λone : Λ 1 = 1 := eq_of_at hCM τ (Λat 1) fun w => by
    rw [Λπ, Pi.one_apply, Matrix.mul_one, hC' w, Matrix.map_one _ (map_zero _) (map_one _)]
  have ΛU : ∀ h ∈ U, (Λ h)ᵀ * J * (Λ h).map (cA σ) = J := fun h hh => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (Λ h)ᵀ * J * (Λ h).map (cA σ) - J =
          (Λ h - 1)ᵀ * J * (Λ h).map (cA σ) + J * (Λ h - 1).map (cA σ) := by
        have e1 : (Λ h - 1).map (cA σ) = (Λ h).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (Λat h)) _) _)
        (at_mul_left (at_map_cA σ (Λat h)) _)
    · have hc : ((Λ h).map (cA σ)).map (piInf (τ w)) = (C w * h w * C' w).map star := by
        rw [← Λπ h w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, Λπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unit (hC w).1 (hC' w) ((form_iff (h w)).1 (hh w))
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  set hinv : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ∀ w : InfinitePlace F, Mat (R w) (S w) :=
    fun h w => Jm (R w) (S w) * (h w)ᴴ * Jm (R w) (S w) with hhinv
  have inv_mul : ∀ h ∈ U, hinv h * h = 1 := fun h hh => by
    funext w
    rw [Pi.mul_apply, hhinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm (R w) (S w)) (h w), hh w,
      jm_mul_self, Pi.one_apply]
  have mul_inv : ∀ h ∈ U, h * hinv h = 1 := fun h hh => by
    funext w
    have := congrFun (inv_mul h hh) w
    rw [Pi.mul_apply, Pi.one_apply] at this ⊢
    exact mul_eq_one_comm.1 this
  have Λinv1 : ∀ h ∈ U, Λ h * Λ (hinv h) = 1 := fun h hh => by rw [← Λmul, mul_inv h hh, Λone]
  have Λinv2 : ∀ h ∈ U, Λ (hinv h) * Λ h = 1 := fun h hh => by rw [← Λmul, inv_mul h hh, Λone]
  let G : U → UG (cA σ) J := fun h => ⟨⟨Λ h, Λ (hinv h), Λinv1 h h.2, Λinv2 h h.2⟩, ΛU h h.2⟩
  have LevelValuationRings : ∀ h, At (evI F) (((G h).1 : Matrix β β (AE F E)) - 1) := fun h => Λat h
  have Gmul : ∀ h h' : U, ∀ hm : (h : ∀ w : InfinitePlace F, Mat (R w) (S w)) * h' ∈ U, G ⟨_, hm⟩ = G h * G h' :=
    fun h h' hm => Subtype.ext (Units.ext (Λmul h h'))
  have Λc : Continuous Λ := continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
    (((continuous_const.matrix_mul (continuous_apply w)).matrix_mul continuous_const).sub continuous_const)))
  have hinvc : Continuous hinv := continuous_pi fun w =>
    (continuous_const.matrix_mul (continuous_apply w).matrix_conjTranspose).matrix_mul continuous_const
  have Gc : Continuous G := by
    have hu : Continuous fun h : U => ((G h).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨Λc.comp continuous_subtype_val, (Λc.comp hinvc).comp continuous_subtype_val⟩
    exact hu.subtype_mk _
  classical
  let χ : (∀ w : InfinitePlace F, Mat (R w) (S w)) → ℂ := fun h => if hh : h ∈ U then ν (G ⟨h, hh⟩) else 0
  have χG : ∀ h : U, χ h = ν (G h) := fun h => by simp only [χ, dif_pos h.2]
  have memU : ∀ h h' : ∀ w : InfinitePlace F, Mat (R w) (S w), h ∈ U → h' ∈ U → h * h' ∈ U := fun h h' hh hh' w =>
    mem_mul (hh w) (hh' w)
  obtain ⟨n, hn⟩ := prod_charD (R := R) (S := S) χ
    (fun g h hg hh => by
      rw [χG ⟨g, hg⟩, χG ⟨h, hh⟩, χG ⟨g * h, memU g h hg hh⟩, Gmul ⟨g, hg⟩ ⟨h, hh⟩]
      exact hmul _ _ (LevelValuationRings _) (LevelValuationRings _))
    (by
      rw [continuousOn_iff_continuous_restrict]
      convert hcont.comp_continuous Gc LevelValuationRings using 1
      funext h
      exact χG h)
    (fun g hg => by rw [χG ⟨g, hg⟩]; exact hne _ (LevelValuationRings _))
  refine ⟨fun w => (n w : ℂ), fun γ hγ Y hY => ?_⟩
  set e : ℝ → ∀ w : InfinitePlace F, Mat (R w) (S w) := fun t w => NormedSpace.exp (t • Y w) with he
  have hγw : ∀ t w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = C w * e t w * C' w :=
    fun t w => by
      rw [he]; simp only
      rw [← hY t w, Matrix.mul_assoc, hC' w, Matrix.mul_one]
      rfl
  have heU : ∀ t, e t ∈ U := fun t w => by
    rw [form_iff]
    set g := ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hg
    have hgU : gᵀ * (b • J.map (piInf (τ w))) * g.map star = b • J.map (piInf (τ w)) := by
      have hu : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))ᵀ * J *
          ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ) = J := (γ (Multiplicative.ofAdd t)).2
      have := congrArg (fun X => X.map (piInf (τ w))) hu
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have hc : (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (cA σ)).map (piInf (τ w)) = g.map star := by
        rw [hg, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [hc] at this
      rw [Matrix.mul_smul, Matrix.smul_mul, this]
    have hee : e t w = C' w * g * C w := by
      rw [hg, hγw, Matrix.mul_assoc, Matrix.mul_assoc, hL, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]
    have t1 : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC' w, Matrix.transpose_one]
    have t2 : (C w).map star * (C' w).map star = 1 := by
      rw [← map_star_mul, hC' w]; exact Matrix.map_one _ (star_zero _) (star_one _)
    rw [hee, ← (hC w).1]
    calc (C' w * g * C w)ᵀ * ((C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star) * (C' w * g * C w).map star
        = (C w)ᵀ * (gᵀ * (((C' w)ᵀ * (C w)ᵀ) * (b • J.map (piInf (τ w))) * ((C w).map star * (C' w).map star)) *
            g.map star) * (C w).map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (C w)ᵀ * (b • J.map (piInf (τ w))) * (C w).map star := by
          rw [t1, t2, Matrix.one_mul, Matrix.mul_one, hgU]
  have hγe : ∀ t, γ (Multiplicative.ofAdd t) = G ⟨e t, heU t⟩ := fun t => by
    refine Subtype.ext (Units.ext (eq_of_at hCM τ ?_ fun w => ?_))
    · have e1 : ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t) =
          (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) - (Λ (e t) - 1) := by abel
      show At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - Λ (e t))
      rw [e1]
      exact at_sub (hγ.2 _) (Λat _)
    · show ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) = (Λ (e t)).map (piInf (τ w))
      rw [hγw, Λπ]
  have hval : ∀ t : ℝ, ν (γ (Multiplicative.ofAdd t)) =
      Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace) := fun t => by
    rw [hγe t, ← χG, hn _ (heU t), Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [he]; simp only
    rw [GlobalTheory.DetSqrtCover.det_exp, ← Complex.exp_int_mul, Matrix.trace_smul]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ∑ w, (n w : ℂ) * (Y w).trace))
      (∑ w, (n w : ℂ) * (Y w).trace) 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (∑ w, (n w : ℂ) * (Y w).trace)).cexp
    simpa using h0
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall hval)

end GlobalTheory.HoweD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameterStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → At (evI F) ((h.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @GlobalTheory.HoweD.deriv_charD | exact GlobalTheory.HoweD.deriv_charD | (intros; apply GlobalTheory.HoweD.deriv_charD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystem
set_option autoImplicit false

namespace GlobalTheory.HSShort.FormRatio

open MvPolynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Adelic GlobalTheory.Points GlobalTheory.Twist

theorem exists_forms_of_mem_closure {F K : Type} [Field F] [Field K] {N : ℕ} (φ : F →+* K) (c : Fin N → K) {r : K}
    (hr : r ∈ Subfield.closure (Set.range φ ∪ {r | ∃ i j, r = c i / c j})) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      r * eval₂ φ c Q = eval₂ φ c P := by
  have h0 : ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      0 * eval₂ φ c Q = eval₂ φ c P :=
    ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  induction hr using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨i, j, rfl⟩
    · exact ⟨0, C a, 1, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · by_cases hj : c j = 0
      · rwa [hj, div_zero]
      · exact ⟨1, X i, X j, isHomogeneous_X _ _, isHomogeneous_X _ _, by simpa using hj, by simp [hj]⟩
  | one => exact ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * Q' + Q * P', Q * Q', (hP.mul hQ').add (hQ.mul hP'), hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h2, ← h2']; ring
  | neg x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    exact ⟨d, -P, Q, hP.neg, hQ, h1, by rw [eval₂_neg, ← h2, neg_mul]⟩
  | inv x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    by_cases hx0 : x = 0
    · rwa [hx0, inv_zero]
    · refine ⟨d, Q, P, hQ, hP, h2 ▸ mul_ne_zero hx0 h1, ?_⟩
      rw [← h2, inv_mul_cancel_left₀ hx0]
  | mul x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * P', Q * Q', hP.mul hP', hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_mul, eval₂_mul, ← h2, ← h2']; ring

theorem eq_zero_of_valR_generic {Y : Scheme.{0}} [IsReduced Y] {η : Y} (hη : IsGenericPoint η Set.univ)
    {U : Y.Opens} (f : Γ(Y, U)) (h : valR (resPt η) U f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro y hy
  have h1 : ptOf (resPt η) ∈ Y.basicOpen f := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (Y.basicOpen f).isOpen).2 ⟨y, trivial, hy⟩
  exact ((valR_ne_zero_iff _ (Y.basicOpen_le f h1) f).2 h1 h).elim

theorem exists_forms (F : Type) [Field F] (S : LinSys F) (hS : S.IsVariety) (_ : S.BasePointFree)
    (hb : S.Birational) (W : S.Y.Opens) (a : Γ(S.Y, W)) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧
      (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W →
        valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  have := hS.isIntegral
  obtain ⟨η, hη, hr⟩ := hb
  obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := exists_forms_of_mem_closure (S.baseHom (resPt η)) (S.coords (resPt η))
    (r := valR (resPt η) W a) (hr.ge (Subfield.mem_top _))
  refine ⟨d, P, Q, hP, hQ, fun h => h1 (S.eval₂_coords_eq_zero _ h), fun ha h => ?_, fun K _ _ x hx => ?_⟩
  · rw [S.eval₂_coords_eq_zero _ h] at h2
    exact ha (eq_zero_of_valR_generic hη a ((mul_eq_zero.1 h2).resolve_right h1))
  · set j := S.chartAt (ptOf x.1)
    have hxV : ptOf x.1 ∈ W ⊓ S.L.U j := ⟨hx, S.mem_chartAt _⟩
    have hηV : ptOf (resPt η) ∈ W ⊓ S.L.U j := by
      rw [ptOf_resPt]
      exact (hη.mem_open_set_iff (W ⊓ S.L.U j).isOpen).2 ⟨_, trivial, hxV⟩
    let f : Γ(S.Y, W ⊓ S.L.U j) :=
      (S.Y.presheaf.map (homOfLE inf_le_left).op).hom a *
        (S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hQ) j) +
        -(S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hP) j)
    have hf : ∀ {Ω : Type} [Field Ω] (z : Sp Ω ⟶ S.Y), ptOf z ∈ W ⊓ S.L.U j → valR z _ f =
        valR z W a * valR z _ (zfun (S.form hQ) j) - valR z _ (zfun (S.form hP) j) := fun z hz => by
      have h := (le_iff_ptOf_mem z _).2 hz
      rw [valR_add z _ h, valR_neg z _ h, valR_mul z _ h, valR_res z _ h, valR_res z _ h, valR_res z _ h,
        sub_eq_add_neg]
    have hf0 : f = 0 := by
      obtain ⟨c, -, -, hc⟩ := S.exists_frame_change (resPt η) j hηV.2
      refine eq_zero_of_valR_generic hη f ?_
      rw [hf _ hηV, hc, hc, S.powVal_form, S.powVal_form, ← h2]
      ring
    have h3 := hf x.1 hxV
    rw [hf0, valR_zero _ _ ((le_iff_ptOf_mem _ _).2 hxV), eq_comm, sub_eq_zero] at h3
    have e : ∀ {g : MvPolynomial (Fin S.N) F} (hg : g.IsHomogeneous d),
        valR x.1 _ (zfun (S.form hg) j) = aeval (S.coords x.1) g := fun hg =>
      (S.powVal_form x.1 hg).trans (by rw [LinSys.baseHom_ptOver, aeval_def])
    rwa [e, e] at h3

end GlobalTheory.HSShort.FormRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystemStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∀ (W : S.Y.Opens) (a : Γ(S.Y, W)), ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧ (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W → valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  first | exact @GlobalTheory.HSShort.FormRatio.exists_forms | exact GlobalTheory.HSShort.FormRatio.exists_forms | (intros; apply GlobalTheory.HSShort.FormRatio.exists_forms <;> assumption)
end
end
