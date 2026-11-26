module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemWpNormSubLtOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
noncomputable section
namespace GlobalTheory.MemLoc.FrobLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Polynomial

theorem endo_root {k : Type} [CommRing k] [IsDomain k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (φ : k →+* k) {a : k} {m : ℕ} (hm : 0 < m) (hpm : ¬ p ∣ m) (ha : a ^ m = 1) :
    ∃ n : ℕ, φ a = a ^ (p ^ n) := by
  have hf : 0 < m.totient := Nat.totient_pos.2 hm
  have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm
  let F : Subring k := RingHom.eqLocus (iterateFrobenius k p m.totient) (RingHom.id k)
  have hF : ∀ y : k, y ∈ F ↔ y ^ (p ^ m.totient) = y := fun y => Iff.rfl
  have haF : a ∈ F := by
    rw [hF]
    have h1 := Nat.ModEq.pow_totient hcop
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.out.pos)).1 h1.symm
    have : p ^ m.totient = m * c + 1 := by
      have := Nat.one_le_pow m.totient p hp.out.pos
      omega
    rw [this, pow_succ, pow_mul, ha, one_pow, one_mul]
  have hfin : (F : Set k).Finite := by
    have hne : (X ^ (p ^ m.totient) - X : k[X]) ≠ 0 :=
      (monic_X_pow_sub (by
        rw [degree_X]
        exact_mod_cast Nat.one_lt_pow hf.ne' hp.out.one_lt)).ne_zero
    refine (Polynomial.rootSet_finite (X ^ (p ^ m.totient) - X : k[X]) k).subset fun y hy => ?_
    rw [Polynomial.mem_rootSet]
    refine ⟨hne, ?_⟩
    have := (hF y).1 hy
    simp [this]
  haveI : Finite F := hfin
  letI : Field F := (Finite.isField_of_domain F).toField
  haveI : CharP F p := F.subtype.charP F.subtype_injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →+* F := (φ.comp F.subtype).codRestrict F fun y => by
    rw [hF]
    show φ y ^ _ = φ y
    rw [← map_pow, (hF y).1 y.2]
  let ψ' : F →ₐ[ZMod p] F :=
    { ψ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 ψ'
  refine ⟨j, ?_⟩
  have h1 : ψ' ⟨a, haF⟩ = (⟨a, haF⟩ : F) ^ (p ^ (j : ℕ)) := by
    rw [← hj]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  exact congrArg Subtype.val h1

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := (spectralNorm_eq_of_equiv g x).symm

def OO (l : ℕ) [Fact l.Prime] : Subring (Om l) := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (Om l)

def MM (l : ℕ) [Fact l.Prime] : Ideal (OO l) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (Om l)

theorem mem_MM (x : OO l) : x ∈ MM l ↔ ‖(x : Om l)‖ < 1 := Iff.rfl

instance MM_prime : (MM l).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_MM]; simp
  mem_or_mem' := fun {a b} h => by
    rw [mem_MM] at h
    by_contra hc
    rw [not_or, mem_MM, mem_MM, not_lt, not_lt] at hc
    have : ‖(a : Om l) * b‖ < 1 := h
    rw [norm_mul] at this
    exact absurd this (not_lt.2 (one_le_mul_of_one_le_of_one_le hc.1 hc.2))

abbrev kk (l : ℕ) [Fact l.Prime] : Type := OO l ⧸ MM l

abbrev res : OO l →+* kk l := Ideal.Quotient.mk (MM l)

theorem res_eq_iff (a b : OO l) : res a = res b ↔ ‖(a : Om l) - b‖ < 1 := Ideal.Quotient.eq

instance kk_char : CharP (kk l) l := by
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (res (l := l)), Ideal.Quotient.eq_zero_iff_mem, mem_MM]
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

def galO (g : GQ l) : OO l →+* OO l :=
  ((g : Om l →+* Om l).comp (OO l).subtype).codRestrict (OO l) fun x => by
    show ‖g x‖ ≤ 1
    rw [norm_gal]; exact x.2

def galK (g : GQ l) : kk l →+* kk l :=
  Ideal.quotientMap (MM l) (galO g) fun x hx => by
    show ‖g x‖ < 1
    rw [norm_gal]; exact hx

theorem galK_res (g : GQ l) (x : OO l) : galK g (res x) = res (galO g x) := rfl

theorem norm_root {ζ : Om l} {m : ℕ} (hm : 0 < m) (h : ζ ^ m = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem res_inj {a b : OO l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1) (hb : b ^ m = 1)
    (h : res a = res b) : a = b := by
  by_contra hne
  have h1 := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg res h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_zero, ← h] at h3
  rw [geom_sum₂_self] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact hlm ((CharP.cast_eq_zero_iff (kk l) l m).1 h4)
  · have h5 : res a ^ m = 1 := by rw [← map_pow, ha, map_one]
    have h6 : res a = 0 := eq_zero_of_pow_eq_zero h4
    rw [h6, zero_pow hm.ne'] at h5
    exact zero_ne_one h5

theorem gal_root (h : GQ l) {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ n : ℕ, ∀ ζ : Om l, ζ ^ m = 1 → h ζ = ζ ^ (l ^ n) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  let a : OO l := ⟨ξ, (norm_root hm hξ.pow_eq_one).le⟩
  have ha : a ^ m = 1 := Subtype.ext hξ.pow_eq_one
  obtain ⟨n, hn⟩ := endo_root l (galK h) (a := res a) hm hlm (by rw [← map_pow, ha, map_one])
  rw [galK_res, ← map_pow] at hn
  have h1 := res_inj hm hlm (by rw [← map_pow, ha, map_one])
    (by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]) hn
  have h2 : h ξ = ξ ^ (l ^ n) := congrArg Subtype.val h1
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hζ
  rw [map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_root (x : Om l) (hx : ‖x‖ = 1) :
    ∃ (ζ : Om l) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  obtain ⟨n, hn, h⟩ := GlobalTheory.ResidueRoot.exists_pow_alg x hx
  obtain ⟨e, m, hlm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hlm)
  let a : OO l := ⟨x, hx.le⟩
  have h1 : res a ^ (l ^ e * m) = 1 := by
    rw [← map_pow, ← map_one (res (l := l)), res_eq_iff]; exact h
  rw [ExpChar.pow_prime_pow_mul_eq_one_iff] at h1
  have h2 : ‖x ^ m - 1‖ < 1 := by
    rw [← map_pow, ← map_one (res (l := l)), res_eq_iff] at h1; exact h1
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h2
  by_contra hc
  push Not at hc
  refine absurd h2 (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ m hm hlm ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_level {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h x = h' x := by
  have key : ∀ {a b : Om l}, (∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h a = h' a) →
      (∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h b = h' b) →
      ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
      ∀ h h' : GQ l, (∀ ζ : Om l, ζ ^ m = 1 → h ζ = h' ζ) → h a = h' a ∧ h b = h' b := by
    rintro a b ⟨m, hm, hlm, ha⟩ ⟨n, hn, hln, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln,
      fun h h' H => ⟨ha h h' fun ζ hζ => H ζ ?_, hb h h' fun ζ hζ => H ζ ?_⟩⟩
    · rw [pow_mul, hζ, one_pow]
    · rw [mul_comm, pow_mul, hζ, one_pow]
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact ⟨m, hm, hlm, fun h h' H => H x hx⟩
  | algebraMap c =>
    exact ⟨1, one_pos, hl.out.not_dvd_one, fun h h' _ => by rw [h.commutes, h'.commutes]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, hlm, H⟩ := key ha hb
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_add (f := _), map_add (f := _), (H h h' H').1, (H h h' H').2]⟩
  | inv a _ ha =>
    obtain ⟨m, hm, hlm, H⟩ := ha
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_inv₀, map_inv₀, H h h' H']⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm, hlm, H⟩ := key ha hb
    exact ⟨m, hm, hlm, fun h h' H' => by rw [map_mul, map_mul, (H h h' H').1, (H h h' H').2]⟩

theorem exists_ext (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) :
    ∃ g : GQ l, ∀ x : ↥(MaximalUnramifiedExtension l), g x = (σ x : Om l) := by
  let f : Om l →ₐ[ℚ_[l]] Om l := σ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f), fun x => ?_⟩
  exact σ.liftNormal_commutes (Om l) x

end GlobalTheory.MemLoc.FrobLaws

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc FrobLaws

theorem frob_laws (l : ℕ) [hl : Fact l.Prime] (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) :
    (∀ x : ↥(MaximalUnramifiedExtension l), ‖(x : Om l)‖ ≤ 1 → ‖((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) - (x : Om l) ^ l‖ < 1) ∧
    (∀ (K : FinExt l) (x : ↥(MaximalUnramifiedExtension l)), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
    (∀ x : ↥(MaximalUnramifiedExtension l), σ x = x → ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c = x) := by
  obtain ⟨g, hg⟩ := exists_ext σ
  have hroot : ∀ (ζ : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → ζ ^ m = 1 → g ζ = ζ ^ l := by
    intro ζ m hm hlm hζ
    let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
    have := hσ c m hm hlm (Subtype.ext hζ)
    rw [show ζ = (c : Om l) from rfl, hg, this]; rfl
  refine ⟨fun x hx => ?_, fun K x hx => ?_, fun x hx => ?_⟩
  · rw [← hg]
    let a : OO l := ⟨x, hx⟩
    refine (res_eq_iff (galO g a) (a ^ l)).1 ?_
    rw [← galK_res, map_pow]
    rcases hx.lt_or_eq with h | h
    · have : res a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ((mem_MM a).2 h)
      rw [this, map_zero, zero_pow hl.out.ne_zero]
    · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) (x : Om l) h
      let b : OO l := ⟨ζ, (norm_root hm hζ).le⟩
      have : res a = res b := (res_eq_iff a b).2 hn
      rw [this, galK_res, ← map_pow]
      have e : galO g b = b ^ l := Subtype.ext (hroot ζ m hm hlm hζ)
      rw [e]
  · rw [← hg, ← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨m, hm, hlm, H⟩ := exists_level x.2
    have h1 := H (h * g) (g * h) fun ζ hζ => by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hroot ζ m hm hlm hζ, map_pow,
        hroot (h ζ) m hm hlm (by rw [← map_pow, hζ, map_one])]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h1
    rw [h1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx]
  · have hgx : g x = x := by rw [hg, hx]
    have hpow : ∀ n : ℕ, (g ^ n) x = x := fun n => by
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hgx, ih]
    obtain ⟨m, hm, hlm, H⟩ := exists_level x.2
    have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (g ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hroot ζ m hm hlm hζ, ← pow_mul, pow_succ']
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l]) (x : Om l)).2
      fun h => by
        obtain ⟨n, hn⟩ := gal_root h hm hlm
        rw [H h (g ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]
    exact ⟨c, Subtype.ext hc⟩

end GlobalTheory.MemLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists

namespace GlobalTheory.Mem.ChiLaws

theorem infDiag_mul_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
      ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem phase_sq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem chi_laws (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsChiPsi H χ) :
    (∀ x ∈ UOT H, tildeD H χ x = 1) ∧
    (letI := H.cmStar; ∀ z : unitary H.E,
      ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_UOT H).1 hx
    rw [tildeD_mk H hK]
    refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_
    refine hχ.unr v y ?_
    unfold IsUnitAt
    rw [hy]
    exact ha v
  · letI := H.cmStar
    intro z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H
    obtain ⟨k, hk⟩ := h2 z
    rw [← h1 k z hk, tildeD_mk H hK]
    have e := congrArg χ.1 (infDiag_mul_finPart k)
    rw [map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv] at e
    have hi : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := hχ.inf k
    rw [e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine phase_sq ((map_ne_zero _).2 k.ne_zero) ?_
    have hc : embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (embPsi H τ (k : H.E)) :=
      H.conjE_apply _ _
    rw [← hc]
    exact (map_mul (embPsi H τ) _ _).symm.trans (congrArg _ hk)

end GlobalTheory.Mem.ChiLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLaws
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.RelDet

open IdlFact

section General

variable {L : Type} [Field L] [NumberField L]

def ordI (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ℤ := -WithZero.log (valAt w a)

theorem valAt_eq (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a = WithZero.exp (-ordI w a) := by
  rw [ordI, neg_neg, WithZero.exp_log (valAt_ne_zero w a)]

theorem ordI_mul (w : HeightOneSpectrum (𝓞 L)) (a b : Ideles L) : ordI w (a * b) = ordI w a + ordI w b := by
  unfold ordI
  rw [map_mul, WithZero.log_mul (valAt_ne_zero w a) (valAt_ne_zero w b)]
  ring

theorem ordI_inv (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ordI w a⁻¹ = -ordI w a := by
  unfold ordI
  rw [map_inv, WithZero.log_inv]

theorem ordI_diag (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ordI w (diagUnits L k) = ordF w k := by
  have h : valAt w (diagUnits L k) = w.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
  rw [ordI, h, ordF]

def powI (n : HeightOneSpectrum (𝓞 L) → ℕ) : Ideles L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L), localIdele L w (atFin w (unif w)) ^ n w

theorem ordI_powI (n : HeightOneSpectrum (𝓞 L) → ℕ) (hn : {w | n w ≠ 0}.Finite) (w : HeightOneSpectrum (𝓞 L)) :
    ordI w (powI n) = n w := by
  classical
  have e : powI n = ∏ v ∈ hn.toFinset, localIdele L v (atFin v (unif v)) ^ (n v : ℤ) := by
    unfold powI
    rw [finprod_eq_prod_of_mulSupport_subset (s := hn.toFinset)]
    · simp only [zpow_natCast]
    · intro v hv
      by_contra h
      have h0 : n v = 0 := by simpa using h
      exact hv (by simp [h0])
  have h := valAt_prod hn.toFinset (fun v => (n v : ℤ)) w
  change valAt w (∏ v ∈ hn.toFinset, localIdele L v (atFin v (unif v)) ^ (n v : ℤ)) = _ at h
  rw [ordI, e, h, WithZero.log_exp, neg_neg]
  split_ifs with hw
  · rfl
  · have h0 : n w = 0 := by simpa using hw
    simp [h0]

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mk_mk_eq {a b : Ideles H.E}
    (h : ∀ w w', IsConjPl H w w' → ordI w a - ordI w' a = ordI w b - ordI w' b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtT H ⧸ UOT H) = QuotientGroup.mk (QuotientGroup.mk b) := by
  have h1 : a⁻¹ * b ∈ KD H ⊔ unitIdl H.E := by
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
    rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv]
    have := h w w' hw
    congr 1
    omega
  obtain ⟨k, hk, u, hu, e⟩ := Subgroup.mem_sup.1 h1
  refine QuotientGroup.eq.2 ⟨u, hu, ?_⟩
  have hk1 : (QuotientGroup.mk k : DtT H) = 1 := (QuotientGroup.eq_one_iff k).2 hk
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e, QuotientGroup.mk_mul, hk1, one_mul]
  rfl

def repI (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : Ideles H.E :=
  powI fun w => (ordSub w (detSub M') - ordSub w (detSub M)).toNat

theorem relDetT_eq (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    relDetT H N M M' = QuotientGroup.mk (QuotientGroup.mk (repI H N M M')) := rfl

theorem ordI_repI (N : ℕ) : letI := H.cmStar; ∀ (M M' : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)),
    IsConjPl H w w' → ordI w (repI H N M.1 M'.1) - ordI w' (repI H N M.1 M'.1) =
      ordSub w (detSub M'.1) - ordSub w (detSub M.1) := by
  letI := H.cmStar
  intro M M' w w' hw
  have f1 := (ordSub_detSub_lattice H.E N M.1 M.2.1 M.2.2.1).1
  have f2 := (ordSub_detSub_lattice H.E N M'.1 M'.2.1 M'.2.2.1).1
  have hf : {w | (ordSub w (detSub M'.1) - ordSub w (detSub M.1)).toNat ≠ 0}.Finite := by
    refine (f1.union f2).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    exact hv (by simp [hn.1, hn.2])
  have h1 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M w w' hw
  have h2 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M' w w' hw
  unfold repI
  rw [ordI_powI _ hf, ordI_powI _ hf]
  omega

end GlobalTheory.Mem.Chr.RelDet

namespace GlobalTheory.Mem.Chr

open RelDet


open Classical in
theorem relDetT_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H N
  letI := H.cmStar
  refine ⟨fun L => relDetT_self H N L.1, fun L L' L'' => ?_, fun L L' γ hγ => ?_⟩
  · rw [relDetT_eq, relDetT_eq, relDetT_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_mk_eq H fun w w' hw => ?_
    have h1 := ordI_repI H N L L' w w' hw
    have h2 := ordI_repI H N L' L'' w w' hw
    have h3 := ordI_repI H N L L'' w w' hw
    rw [ordI_mul, ordI_mul]
    omega
  · obtain ⟨he, hk⟩ := GlobalTheory.Mem.RatPts.rat_points R H
    obtain ⟨k, hk⟩ := hk ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
    rw [← he k _ hk, relDetT_eq]
    refine mk_mk_eq H fun w w' hw => ?_
    have hk' : (γ : Matrix (Fin N) (Fin N) H.E).det * H.conj (k : H.E) = k := hk
    have hd : (γ : Matrix (Fin N) (Fin N) H.E).det ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, zero_mul])
    have hc : H.conj (k : H.E) ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, mul_zero])
    have e : k = Units.mk0 _ hd * Units.mk0 _ hc := Units.ext hk'.symm
    have h1 : ordF w' k = ordF w' (Units.mk0 _ hd) + ordF w' (Units.mk0 _ hc) := by
      change Formalism.L2.Host.ordF w' k = Formalism.L2.Host.ordF w' (Units.mk0 _ hd) + Formalism.L2.Host.ordF w' (Units.mk0 _ hc)
      rw [← DetOrd.ordF_mul', ← e]
    have h2 : ordF w' (Units.mk0 _ hc) = ordF w k := by
      have := (conjPl_main.2.1 R H w w').1 hw (k : H.E)
      unfold ordF
      rw [← this]
      rfl
    have h3 := (ordSub_detSub_lattice H.E N L.1 L.2.1 L.2.2.1).2.2 (γ : Matrix (Fin N) (Fin N) H.E)
      (Units.mk0 _ hd) rfl w'
    have h4 : ordSub w' (detSub L'.1) = ordF w' (Units.mk0 _ hd) + ordSub w' (detSub L.1) := by
      rw [hγ]
      exact h3
    have h5 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L w w' hw
    have h6 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L' w w' hw
    change ordI w (repI H N L.1 L'.1) - ordI w' (repI H N L.1 L'.1) = ordI w (diagUnits H.E k) - ordI w' (diagUnits H.E k)
    rw [ordI_repI H N L L' w w' hw, ordI_diag, ordI_diag]
    omega

end GlobalTheory.Mem.Chr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLawsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Classical
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeLatticeDeterminantClass_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  first | exact @GlobalTheory.Mem.Chr.relDetT_laws | exact GlobalTheory.Mem.Chr.relDetT_laws | (intros; apply GlobalTheory.Mem.Chr.relDetT_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
noncomputable section

namespace GlobalTheory.CoefSpace

section Poly

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial Matrix
open scoped ComplexOrder InnerProductSpace

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fockL_eq {σ : Type} (f g : MvPolynomial σ ℂ) : fockL f g = Formalism.REAL.fockF g f := by
  have h := Formalism.L2.Col.map_fockS (RingHom.id ℂ) f g (fun _ => rfl)
  simp only [RingHom.id_apply, MvPolynomial.map_id] at h
  exact h

theorem map_fockL {K σ : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (f g : MvPolynomial σ K) : φ (fockL f g) = fockL (map φ f) (map φ g) := by
  rw [fockL_eq]
  exact Formalism.L2.Col.map_fockS φ f g fun _ => hφ _

theorem map_pairP {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (hφ : ∀ x, φ (star x) = star (φ x))
    (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    φ (pairP lam G F F') = pairP lam (fun τ => (G τ).map φ) (map φ F) (map φ F') := by
  have h1 : φ (gramTw lam G) = gramTw lam (fun τ => (G τ).map φ) := by
    simp only [gramTw, map_prod, map_zpow₀, RingHom.map_det]
    rfl
  have h2 : φ (extNorm K lam) = extNorm ℂ lam := by
    simp only [extNorm, map_prod, ← fockL_apply, map_fockL φ hφ, map_extremal]
  rw [pairP_apply, pairP_apply, map_mul, map_div₀, h1, h2, map_fockL φ hφ, Formalism.L2.Col.map_blockAct]
  rfl

theorem map_actP {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (map φ F) := by
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h3, trAct,
    Formalism.L2.Col.map_blockAct]
  rfl

def bcVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) : VV K lam →ₛₗ[φ] VV ℂ lam where
  toFun x := ⟨map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by simp [smul_eq_C_mul])

theorem bcVV_span {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    Submodule.span ℂ (Set.range fun i => bcVV φ lam (bVV K lam i)) = ⊤ := by
  rw [eq_top_iff, ← (bVV ℂ lam).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨F, hF, e⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam i
  have : bVV ℂ lam i = bcVV φ lam ⟨F, hF⟩ := Subtype.ext ((bVV_coe ℂ lam i).trans e)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, ← (bVV K lam).sum_repr ⟨F, hF⟩, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem bcVV_indep {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) :
    LinearIndependent ℂ fun i => bcVV φ lam (bVV K lam i) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (bcVV_span φ lam).ge
    (Module.finrank_eq_card_basis (bVV ℂ lam)).symm

theorem continuous_actP {X : Type} [TopologicalSpace X] (lam : ι → DomWeight n) (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (l : Pol ℂ ι n →ₗ[ℂ] ℂ) (F : Pol ℂ ι n) :
    Continuous fun x => l (actP lam (g x) F) := by
  let G : ι → Matrix (Fin n) (Fin n) C(X, ℂ) := fun τ a b => ⟨fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ) b a,
    (continuous_apply_apply b a).comp (hg τ)⟩
  let P := Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) G (map (algebraMap ℂ C(X, ℂ)) F)
  have key : ∀ x, trAct (g x) F = map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ) P := by
    intro x
    have : ((trAct (g x) : Pol ℂ ι n →ₐ[ℂ] Pol ℂ ι n) : Pol ℂ ι n →+* Pol ℂ ι n) =
        (map (ContinuousMap.evalAlgHom ℂ ℂ x : C(X, ℂ) →+* ℂ)).comp
          ((Formalism.GradedWeylDivisibility.blockAct C(X, ℂ) (n := n) G).toRingHom.comp (map (algebraMap ℂ C(X, ℂ)))) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [trAct]
      · intro v
        simp [trAct, Formalism.GradedWeylDivisibility.blockAct, G]
    exact DFunLike.congr_fun this F
  have h2 : ∀ x, l (trAct (g x) F) = ∑ m ∈ P.support, (P.coeff m) x * l (monomial m 1) := by
    intro x
    rw [key]
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_monomial]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul, h2, detTw_eq]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hg τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_finsetSum _ fun m _ => (P.coeff m).continuous.mul continuous_const)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit).ne_zero

def gramOf (B : ι → GL (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * (B τ : Matrix (Fin n) (Fin n) ℂ)

theorem pairK_pos (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ) (x : VV ℂ lam) (hx : x ≠ 0) :
    0 < pairK lam (gramOf B) x x := by
  have h := pairTransport ℂ ι n lam (fun _ => 1) B B x.1 x.1
  simp only [Matrix.mul_one] at h
  have hne : actP lam B x.1 ≠ 0 := fun h0 => hx (Subtype.ext (by
    have := congrArg (fun φ : Module.End ℂ (Pol ℂ ι n) => φ x.1) ((rhoP lam).map_mul B⁻¹ B)
    rw [inv_mul_cancel, map_one] at this
    refine this.trans ?_
    show actP lam B⁻¹ (actP lam B x.1) = 0
    rw [h0, map_zero]))
  obtain ⟨q, hq, e⟩ := extNormPos ℂ ι n lam
  rw [pairK_apply]
  unfold gramOf
  rw [← h, pairP_apply, pb_gramTw_one, pb_blockAct_one_tr, fockL_eq, e]
  refine mul_pos (one_div_pos.2 ?_) (ps_fockF_pos _ hne)
  rw [eq_ratCast, ← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.2 (by exact_mod_cast hq)

def HV (lam : ι → DomWeight n) (_B : ι → GL (Fin n) ℂ) : Type := VV ℂ lam

variable (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)

instance : AddCommGroup (HV lam B) := inferInstanceAs (AddCommGroup (VV ℂ lam))

instance : Module ℂ (HV lam B) := inferInstanceAs (Module ℂ (VV ℂ lam))

@[reducible] def core : InnerProductSpace.Core ℂ (HV lam B) where
  inner x y := pairK lam (gramOf B) x y
  conj_inner_symm x y := (pairSymm ℂ ι n lam (gramOf B) fun τ => by simp [gramOf]).eq _ _
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · subst hx
      exact le_of_eq (congrArg Complex.re (map_zero (pairK lam (gramOf B) 0))).symm
    · exact (Complex.lt_def.1 (pairK_pos lam B x hx)).1.le
  add_left x y z := LinearMap.map_add₂ (pairK lam (gramOf B)) x y z
  smul_left x y r := LinearMap.map_smulₛₗ₂ (pairK lam (gramOf B)) r x y
  definite x hx := by
    by_contra h
    exact (pairK_pos lam B x h).ne' hx

instance : NormedAddCommGroup (HV lam B) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core lam B)

instance : InnerProductSpace ℂ (HV lam B) := InnerProductSpace.ofCore (core lam B).toCore

instance : FiniteDimensional ℂ (HV lam B) := (bVV ℂ lam).finiteDimensional_of_finite

theorem inner_HV (x y : HV lam B) : inner ℂ x y = pairK lam (gramOf B) x y := rfl

instance : Nontrivial (HV lam B) :=
  ⟨⟨_, (0 : VV ℂ lam), fun h => GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => extremal ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _) (congrArg Subtype.val (h : (⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam _
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone _)⟩ : VV ℂ lam) = 0))⟩⟩

theorem continuous_HV {X : Type} [TopologicalSpace X] (g : X → ι → GL (Fin n) ℂ)
    (hg : ∀ τ, Continuous fun x => (g x τ : Matrix (Fin n) (Fin n) ℂ)) (v : HV lam B) :
    Continuous (X := X) (Y := HV lam B) fun x => rhoK lam (g x) v := by
  have : (fun x => (rhoK lam (g x) v : HV lam B)) = fun x => ∑ i,
      pairP lam (gramOf B) (Subtype.val (stdOrthonormalBasis ℂ (HV lam B) i)) (actP lam (g x) (Subtype.val v)) •
        stdOrthonormalBasis ℂ (HV lam B) i := by
    funext x
    exact ((stdOrthonormalBasis ℂ (HV lam B)).sum_repr' _).symm
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_actP lam g hg _ _).smul continuous_const

end Poly

end GlobalTheory.CoefSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


open Classical in
def patchAt (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  ⨅ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (if Q = P then A else B)

end GlobalTheory.InertExchange
end
end
