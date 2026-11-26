module

public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open Formalism.UG (IsInertAt)
open GlobalTheory.LFun.InertChart (under_eq_iff)

namespace EvInv

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locChar_one {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : IsInertAt F E v w) {χ : Chr F E}
    (h1 : ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χ z = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  rw [PT.locChar_eq hw h H y, MonoidHom.one_apply]
  exact h1 _ (PT.locIdele_spec hw h y).1

end EvInv

open EvInv in
theorem evInvSt : EvInvSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hWl v w hw hχ ω ρ hR m Cy hL _ l hl h0 g hg φ hφ
  have hσ := hP.base.cm
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW hP hWl v
  obtain rfl : χWv = 1 := locChar_one hw hχ L.chW
  obtain ⟨c1, c2⟩ := PT.psi_good hP.base.std (hP.base.inert v w hw).2.2 L.psi
  have a1 := PT.isHerm_loc (v := v) hX
  have a2 := PT.isSkew_loc (v := v) hW
  have a3 := PT.isLagr_loc hσ hw hW hL
  have a4 := PT.isEv_of L hL.supp hl h0
  have fix := split_character_fixes_evaluation _ _ _ ψv (PT.isField_Ev hw) (PT.isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ l a1 a2 a3 L.weil a4
  obtain ⟨gv, -, e1, -, -⟩ := L.loc g hg 1 (one_mem_UAt W v)
  have e : ω (g, 1) φ = omv.comp (MonoidHom.inl _ _) gv φ :=
    (PT.actsX L hg e1 hφ _).1 ((hR.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)
  rw [e]
  exact fix gv φ hφ

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  PositivityTheory.ThK.PT

namespace FunSieg

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locField {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

local instance charZeroFv {F : Type} [Field F] [NumberField F] (v : Pl F) : CharZero (Fv F v) :=
  charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv {F : Type} [Field F] [NumberField F] (v : Pl F) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero two_ne_zero

local instance modTopEv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

theorem siegSt : SiegSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW P hW v w hw _ ω ρ hR m Cy hL _ l hl p hp t hpt z hz hzt u hu φ hφ
  obtain ⟨ψv, dv, χXv, χWv, omv, L⟩ := ThKH.Locpair.locPairEx F E σ n d B X W M om χX χW P hW v
  have hσ := P.base.cm
  obtain ⟨r, s, hX⟩ := P.herm
  obtain ⟨r', s', hWs⟩ := P.skew
  obtain ⟨c1, c2⟩ := psi_good P.base.std (P.base.inert v w hw).2.2 L.psi
  have a1 := isHerm_loc (v := v) hX
  have a2 := isSkew_loc (v := v) hWs
  have a3 := isLagr_loc hσ hw hWs hL
  have R := siegel_transport _ _ _ ψv (isField_Ev hw) (isQuad_Ev hσ v) c1 c2 _ _ _ _ _ _ dv _ _ _ a1 a2 a3 L.weil.1
  obtain ⟨hv, ehv⟩ := exW L hp
  have eω : ω (1, p) φ = omv.comp (MonoidHom.inr _ _) hv φ :=
    (actsW L hp ehv hφ _).1 ((hR.acts 1 (one_mem_UAt X v) p hp φ hφ (ω (1, p) φ)).2 rfl)
  by_cases h0 : ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l φ ≠ 0
  · have hdet : IsUnit (t.map (compFin F E v)).det := by
      rw [← hzt]; exact (Units.map (compFin F E v).toMonoidHom z).isUnit
    let tv : GL (Fin m) (Ev E v) := ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit
    have htv : (tv : Matrix (Fin m) (Fin m) (Ev E v)) = t.map (compFin F E v) := rfl
    have hdt : Matrix.GeneralLinearGroup.det tv = Units.map (compFin F E v).toMonoidHom z :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, htv]; exact hzt.symm)
    have hpv : ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) * Cy.map (compFin F E v) =
        Cy.map (compFin F E v) * (tv : Matrix (Fin m) (Fin m) (Ev E v)) := by
      rw [show ((hv : GL (Fin d) (Ev E v)) : Matrix (Fin d) (Fin d) (Ev E v)) = hv.1.1 from rfl, ← ehv, htv,
        ← Matrix.map_mul, ← Matrix.map_mul, hpt]
    have hu' : Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (Matrix.GeneralLinearGroup.det tv) = u :=
      Units.ext (by rw [hdt, hu]; rfl)
    have key := R l (Set.mem_univ _) (isEv_of L hL.supp hl h0).2 hv tv hpv φ hφ
    rw [eω, key, hu', hdt, L.chX z hz, Fintype.card_fin]
  · push Not at h0
    rw [h0 _ (hR.pres 1 (one_mem_UAt X v) p hp φ hφ), h0 φ hφ, mul_zero]

end FunSieg

theorem siegSt : SiegSt := FunSieg.siegSt

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunChar
noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem unrAt_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 E)) : UnrAt (1 : Chr F E) w := fun x _ => by
  simp [locChar]

theorem charSt : CharSt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hX v w hw hv z hz
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have hwT : w ∉ above E (X.T : Set (Pl F)) := fun hm => hv (h ▸ hm)
  have hev : Even (a' + a) := by rw [add_comm]; exact hX.geo.even
  have hres : ∀ b : (AF F)ˣ, (X.α * X.β) (ideleMap F E b) = (1 : Chr F E) (ideleMap F E b) := by
    intro b
    have hA : ((X.α (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resα b
    have hB : ((X.β (ideleMap F E b) : Circle) : ℂ) = _ := hX.chars.resβ b
    rw [MonoidHom.mul_apply, MonoidHom.one_apply, ← Circle.coe_eq_one, Circle.coe_mul, hA, hB]
    split_ifs
    · simp
    · rw [← pow_add, hev.neg_one_pow]
  have key := GlobalTheory.InertChars.locIdele_eq_of_inert hw (X.α * X.β) 1 hres
    ((hX.chars.unrα w hwT).mul (hX.chars.unrβ w hwT)) (unrAt_one w)
  refine ⟨?_, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hX v w hw hv z hz⟩
  rw [GlobalTheory.InertChars.eq_ideleAt_of_at z hz, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw, ← MonoidHom.mul_apply, key,
    MonoidHom.one_apply]

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunCount
noncomputable section

namespace PositivityTheory.Sph

section Count

variable {G : Type} [Group G]

theorem mem_map_conj {H : Subgroup G} {y z : G} : z ∈ H.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ H := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show y⁻¹ * (y * b * y⁻¹) * y = b by group]
  · intro hz
    refine ⟨_, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mk_mul_mem {H : Subgroup G} (x : G) {b : G} (hb : b ∈ H) : ((x * b : G) : G ⧸ H) = (x : G ⧸ H) :=
  QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact H.inv_mem hb)

def orb (H : Subgroup G) (y : G) : Set (G ⧸ H) := {c | ∃ a ∈ H, c = ((a * y : G) : G ⧸ H)}

theorem ncard_orb (H : Subgroup G) (y : G) : (orb H y).ncard = (H.map (MulAut.conj y).toMonoidHom).relIndex H := by
  classical
  set M := H.map (MulAut.conj y).toMonoidHom with hM
  let Φ : H ⧸ M.subgroupOf H → G ⧸ H := fun q => ((((Quotient.out q : H) : G) * y : G) : G ⧸ H)
  have hinj : Function.Injective Φ := fun q q' e => by
    have e' := QuotientGroup.eq.1 e
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mem_map_conj]
    convert e' using 1
    group
  have hrange : Set.range Φ = orb H y := by
    ext c
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨_, (Quotient.out q).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨((⟨a, ha⟩ : H) : H ⧸ M.subgroupOf H), ?_⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf H) (⟨a, ha⟩ : H)
      have hm' : ((m : H) : G) ∈ M := Subgroup.mem_subgroupOf.1 m.2
      rw [mem_map_conj] at hm'
      change ((((Quotient.out ((⟨a, ha⟩ : H) : H ⧸ M.subgroupOf H) : H) : G) * y : G) : G ⧸ H) = _
      rw [hm, Subgroup.coe_mul, show a * ((m : H) : G) * y = a * y * (y⁻¹ * ((m : H) : G) * y) by group]
      exact mk_mul_mem _ hm'
  rw [← hrange, Set.ncard_range_of_injective hinj, Subgroup.relIndex, Subgroup.index_eq_card]

theorem orb_mul {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) (y : G) : orb H (a * y * b) = orb H y := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x * a, H.mul_mem hx ha, ?_⟩
    rw [show x * (a * y * b) = x * a * y * b by group]
    exact mk_mul_mem _ hb
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x * a⁻¹, H.mul_mem hx (H.inv_mem ha), ?_⟩
    rw [show x * a⁻¹ * (a * y * b) = x * y * b by group]
    exact (mk_mul_mem _ hb).symm

theorem orb_symm (H : Subgroup G) {d e : G ⧸ H} (h : e ∈ orb H (Quotient.out d)⁻¹) : d ∈ orb H (Quotient.out e)⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul H (a * (Quotient.out d)⁻¹)
  refine ⟨m, m.2, ?_⟩
  rw [hm, show (m : G) * (a * (Quotient.out d)⁻¹ * m)⁻¹ = Quotient.out d * a⁻¹ by group, mk_mul_mem _ (H.inv_mem ha),
    QuotientGroup.out_eq']

def dblK (K : Subgroup G) (x : G) : Set G := {y | ∃ a ∈ K, ∃ b ∈ K, y = a * x * b}

def cosT (P K : Subgroup G) (x : G) : Set (G ⧸ (P ⊓ K)) := {d | ∃ p ∈ P, p ∈ dblK K x ∧ d = (p : G ⧸ (P ⊓ K))}

theorem out_cosT {P K : Subgroup G} {x : G} {d : G ⧸ (P ⊓ K)} (hd : d ∈ cosT P K x) :
    Quotient.out d ∈ P ∧ Quotient.out d ∈ dblK K x := by
  obtain ⟨p, hp, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := hd
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (a * x * b)
  rw [hm]
  exact ⟨P.mul_mem hp m.2.1, a, ha, b * m, K.mul_mem hb m.2.2, by group⟩

theorem orb_sub_cosT {P K : Subgroup G} {x : G} {d : G ⧸ (P ⊓ K)} (hd : d ∈ cosT P K x) :
    orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ cosT P K x⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨h1, b, hb, c, hc, e⟩ := out_cosT hd
  refine ⟨_, P.mul_mem ha.1 (P.inv_mem h1), ⟨a * c⁻¹, K.mul_mem ha.2 (K.inv_mem hc), b⁻¹, K.inv_mem hb, ?_⟩, rfl⟩
  rw [e]
  group

theorem count_core {U P K : Subgroup G} (hPU : P ≤ U) {f f' : G → ℂ} (f1 : f 1 = 1) (f1' : f' 1 = 1)
    (hf : ∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f (p * g * k) = f p * f g)
    (hf' : ∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f' (p * g * k) = f' p * f' g)
    (hmod : ∀ p ∈ P, f p * f' p * (((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) : ℂ) =
      (((P ⊓ K).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (P ⊓ K) : ℂ))
    {A B : Set (G ⧸ (P ⊓ K))} (hA : A.Finite) (hB : B.Finite)
    (hBP : ∀ e ∈ B, Quotient.out e ∈ P)
    (hAB : ∀ d ∈ A, orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ B) (hBA : ∀ e ∈ B, orb (P ⊓ K) (Quotient.out e)⁻¹ ⊆ A) :
    ∑ᶠ d ∈ A, f' (Quotient.out d) = ∑ᶠ e ∈ B, f (Quotient.out e) := by
  classical
  have bi' : ∀ a ∈ P ⊓ K, ∀ g ∈ U, ∀ b ∈ P ⊓ K, f' (a * g * b) = f' g := fun a ha g hg b hb => by
    rw [hf' a ha.1 g hg b hb.2]
    have : f' a = 1 := by simpa [f1'] using hf' 1 P.one_mem 1 U.one_mem a ha.2
    rw [this, one_mul]
  have finv : ∀ p ∈ P, f p * f p⁻¹ = 1 := fun p hp => by
    have := hf p hp p⁻¹ (hPU (P.inv_mem hp)) 1 K.one_mem
    rwa [mul_one, mul_inv_cancel, f1, eq_comm] at this
  have hN : ∀ y : G, (orb (P ⊓ K) y).Finite → ((orb (P ⊓ K) y).ncard : ℂ) ≠ 0 := fun y hy =>
    Nat.cast_ne_zero.2 ((Set.ncard_pos hy).2 ⟨_, 1, (P ⊓ K).one_mem, rfl⟩).ne'
  have finA : ∀ d ∈ A, (orb (P ⊓ K) (Quotient.out d)⁻¹).Finite := fun d hd => hB.subset (hAB d hd)
  have finB : ∀ e ∈ B, (orb (P ⊓ K) (Quotient.out e)).Finite := fun e he => by
    have hd : (((Quotient.out e)⁻¹ : G) : G ⧸ (P ⊓ K)) ∈ A := hBA e he ⟨1, (P ⊓ K).one_mem, by rw [one_mul]⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (Quotient.out e)⁻¹
    have h2 := finA _ hd
    rwa [hm, mul_inv_rev, inv_inv, show ((m : G))⁻¹ * Quotient.out e = ((m : G))⁻¹ * Quotient.out e * 1 by rw [mul_one],
      orb_mul ((P ⊓ K).inv_mem m.2) (P ⊓ K).one_mem] at h2
  let w : G ⧸ (P ⊓ K) → ℂ := fun d => f' (Quotient.out d) / ((orb (P ⊓ K) (Quotient.out d)⁻¹).ncard : ℂ)
  have s1 : ∀ d ∈ A, f' (Quotient.out d) =
      ∑ e ∈ hB.toFinset, if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0 := fun d hd => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have e : ((hB.toFinset.filter (· ∈ orb (P ⊓ K) (Quotient.out d)⁻¹) : Finset (G ⧸ (P ⊓ K))) : Set (G ⧸ (P ⊓ K))) =
        orb (P ⊓ K) (Quotient.out d)⁻¹ := by
      ext c
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hAB d hd h, h⟩⟩
    rw [← Set.ncard_coe_finset, e]
    simp only [w]
    field_simp [hN _ (finA d hd)]
  have s2 : ∀ e ∈ B, (∑ d ∈ hA.toFinset, if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) = f (Quotient.out e) :=
    fun e he => by
    have hr : (Quotient.out e)⁻¹ ∈ P := P.inv_mem (hBP e he)
    have hcond : ∀ d ∈ hA.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) =
        if d ∈ orb (P ⊓ K) (Quotient.out e)⁻¹ then f' (Quotient.out e)⁻¹ / ((orb (P ⊓ K) (Quotient.out e)).ncard : ℂ) else 0 :=
      fun d _ => by
      by_cases h1 : e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹
      · have h2 := orb_symm (P ⊓ K) h1
        rw [if_pos h1, if_pos h2]
        obtain ⟨a, ha, hd'⟩ := h2
        obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (a * (Quotient.out e)⁻¹)
        have hod : Quotient.out d = a * (Quotient.out e)⁻¹ * m := by rw [hd', hm]
        simp only [w]
        rw [hod, bi' a ha _ (hPU hr) m m.2, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc,
          orb_mul ((P ⊓ K).inv_mem m.2) ((P ⊓ K).inv_mem ha)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (orb_symm (P ⊓ K) h2))]
    rw [Finset.sum_congr rfl hcond, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have e1 : ((hA.toFinset.filter (· ∈ orb (P ⊓ K) (Quotient.out e)⁻¹) : Finset (G ⧸ (P ⊓ K))) : Set (G ⧸ (P ⊓ K))) =
        orb (P ⊓ K) (Quotient.out e)⁻¹ := by
      ext c
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hBA e he h, h⟩⟩
    rw [← Set.ncard_coe_finset, e1, ncard_orb, ncard_orb]
    have hm := hmod _ hr
    rw [inv_inv] at hm
    have hn2 : ((((P ⊓ K).map (MulAut.conj (Quotient.out e)).toMonoidHom).relIndex (P ⊓ K) : ℕ) : ℂ) ≠ 0 := by
      rw [← ncard_orb]; exact hN _ (finB e he)
    have hfr := finv _ hr
    rw [inv_inv] at hfr
    rw [eq_comm, ← mul_div_assoc, eq_div_iff hn2, ← hm]
    linear_combination ((((((P ⊓ K).map (MulAut.conj (Quotient.out e)⁻¹).toMonoidHom).relIndex (P ⊓ K) : ℕ) : ℂ)) *
      f' (Quotient.out e)⁻¹) * hfr
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  calc ∑ d ∈ hA.toFinset, f' (Quotient.out d)
      = ∑ d ∈ hA.toFinset, ∑ e ∈ hB.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) :=
        Finset.sum_congr rfl fun d hd => s1 d (hA.mem_toFinset.1 hd)
    _ = ∑ e ∈ hB.toFinset, ∑ d ∈ hA.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) := Finset.sum_comm
    _ = ∑ e ∈ hB.toFinset, f (Quotient.out e) := Finset.sum_congr rfl fun e he => s2 e (hB.mem_toFinset.1 he)

theorem sum_eq_cosT {U K P : Subgroup G} (hKU : K ≤ U) (hPU : P ≤ U) (hIw : ∀ g ∈ U, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    {h : G} (hh : h ∈ U) (hfin : (conjInf K h).relIndex K ≠ 0) {φ : G → ℂ} (hr : ∀ g ∈ U, ∀ k ∈ K, φ (g * k) = φ g) :
    (cosT P K h).Finite ∧
      ∑ᶠ q : K ⧸ (conjInf K h).subgroupOf K, φ (((Quotient.out q : K) : G) * h) = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out d) := by
  classical
  have hKPK : P ⊓ K ≤ K := inf_le_right
  let μ : K ⧸ (conjInf K h).subgroupOf K → G ⧸ K := fun q => ((((Quotient.out q : K) : G) * h : G) : G ⧸ K)
  let ι : G ⧸ (P ⊓ K) → G ⧸ K := Subgroup.quotientMapOfLE hKPK
  have hι : ∀ x : G, ι (x : G ⧸ (P ⊓ K)) = (x : G ⧸ K) := fun x => Subgroup.quotientMapOfLE_apply_mk hKPK x
  have hμ : Function.Injective μ := fun q q' e => by
    have e' := QuotientGroup.eq.1 e
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨((Quotient.out q)⁻¹ * Quotient.out q').2, mem_map_conj.2 ?_⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    convert e' using 1
    group
  have hrange : Set.range μ = ι '' cosT P K h := by
    ext c
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨p, hp, k, hk, e⟩ := hIw _ (U.mul_mem (hKU (Quotient.out q).2) hh)
      refine ⟨(p : G ⧸ (P ⊓ K)), ⟨p, hp, ⟨_, (Quotient.out q).2, k⁻¹, K.inv_mem hk, by rw [e, mul_inv_cancel_right]⟩, rfl⟩, ?_⟩
      rw [hι]
      change _ = ((((Quotient.out q : K) : G) * h : G) : G ⧸ K)
      rw [e, mk_mul_mem _ hk]
    · rintro ⟨_, ⟨p, hp, ⟨a, ha, b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K), ?_⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((conjInf K h).subgroupOf K) (⟨a, ha⟩ : K)
      have hm' : ((m : K) : G) ∈ K.map (MulAut.conj h).toMonoidHom := (Subgroup.mem_subgroupOf.1 m.2).2
      rw [mem_map_conj] at hm'
      have key : ((Quotient.out ((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K) : K) : G) = a * ((m : K) : G) := by
        rw [hm]; rfl
      rw [hι]
      change ((((Quotient.out ((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K) : K) : G) * h : G) : G ⧸ K) = _
      rw [key, show a * ((m : K) : G) * h = a * h * (h⁻¹ * ((m : K) : G) * h) by group, mk_mul_mem _ hm', mk_mul_mem _ hb]
  have hinj : Set.InjOn ι (cosT P K h) := by
    rintro _ ⟨p, hp, -, rfl⟩ _ ⟨p', hp', -, rfl⟩ e
    rw [hι, hι] at e
    exact QuotientGroup.eq.2 ⟨P.mul_mem (P.inv_mem hp) hp', QuotientGroup.eq.1 e⟩
  have hfinT : (cosT P K h).Finite := by
    have : Finite (K ⧸ (conjInf K h).subgroupOf K) := Subgroup.index_ne_zero_iff_finite.1 hfin
    exact Set.Finite.of_finite_image (hrange ▸ Set.finite_range μ) hinj
  refine ⟨hfinT, ?_⟩
  have e1 : ∀ q, φ (((Quotient.out q : K) : G) * h) = φ (Quotient.out (μ q)) := fun q => by
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (((Quotient.out q : K) : G) * h)
    change _ = φ (Quotient.out ((((Quotient.out q : K) : G) * h : G) : G ⧸ K))
    rw [hm, hr _ (U.mul_mem (hKU (Quotient.out q).2) hh) _ m.2]
  have e2 : ∀ d ∈ cosT P K h, φ (Quotient.out (ι d)) = φ (Quotient.out d) := fun d hd => by
    have hιd : ι d = ((Quotient.out d : G) : G ⧸ K) := by
      rw [← hι]
      congr 1
      exact (QuotientGroup.out_eq' d).symm
    rw [hιd]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (Quotient.out d)
    rw [hm, hr _ (hPU (out_cosT hd).1) _ m.2]
  calc ∑ᶠ q, φ (((Quotient.out q : K) : G) * h) = ∑ᶠ q, φ (Quotient.out (μ q)) := finsum_congr e1
    _ = ∑ᶠ c ∈ Set.range μ, φ (Quotient.out c) := (finsum_mem_range hμ (f := fun c => φ (Quotient.out c))).symm
    _ = ∑ᶠ c ∈ ι '' cosT P K h, φ (Quotient.out c) := by rw [hrange]
    _ = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out (ι d)) := finsum_mem_image hinj
    _ = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out d) := finsum_mem_congr rfl e2

end Count

theorem countSt : CountSt := by
  classical
  intro G _ U K P f f' hKU hPU hIw hC hfin f1 f1' hf hf' hmod h hh
  have rK : ∀ φ : G → ℂ, φ 1 = 1 → (∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, φ (p * g * k) = φ p * φ g) →
      ∀ g ∈ U, ∀ k ∈ K, φ (g * k) = φ g := fun φ h1 hφ g hg k hk => by
    simpa [h1] using hφ 1 P.one_mem g hg k hk
  obtain ⟨hT, e1⟩ := sum_eq_cosT hKU hPU hIw hh (hfin h hh) (rK f f1 hf)
  obtain ⟨-, e1'⟩ := sum_eq_cosT hKU hPU hIw hh (hfin h hh) (rK f' f1' hf')
  obtain ⟨k₁, hk₁, k₂, hk₂, eC⟩ := hC h hh
  have hD : ∀ y, y ∈ dblK K h⁻¹ ↔ y ∈ dblK K h := fun y => by
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * k₁, K.mul_mem ha hk₁, k₂ * b, K.mul_mem hk₂ hb, by rw [eC]; group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * k₁⁻¹, K.mul_mem ha (K.inv_mem hk₁), k₂⁻¹ * b, K.mul_mem (K.inv_mem hk₂) hb, ?_⟩
      rw [eC]; group
  have hTi : cosT P K h⁻¹ = cosT P K h := Set.ext fun d =>
    ⟨fun ⟨p, hp, hp', e⟩ => ⟨p, hp, (hD p).1 hp', e⟩, fun ⟨p, hp, hp', e⟩ => ⟨p, hp, (hD p).2 hp', e⟩⟩
  have hsub : ∀ d ∈ cosT P K h, orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ cosT P K h := fun d hd => by
    rw [← hTi]; exact orb_sub_cosT hd
  have core := count_core hPU f1 f1' hf hf' hmod hT hT (fun e he => (out_cosT he).1) hsub hsub
  unfold avgK
  rw [e1, e1', core]

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Abstract

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_map_cart2 (n : ℕ) : (antiJ L n).map c = antiJ L n := by
  ext i j
  simp only [Matrix.map_apply, antiJ]
  split_ifs <;> simp

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem iso_cT_cart2 (hc : ∀ x, c (c x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) L) :
    Iso c (antiJ L n) (antiJ L n) M ↔ cT c M * antiJ L n * M = antiJ L n := by
  have hcc : ∀ N : Matrix (Fin n) (Fin n) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2] at this
    rw [cT, Matrix.transpose_map, hcc] at this
    exact this

theorem inv_mem_KgK_cart2 {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {n : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin n) (Fin n) L) (hiso : ∀ g, Iso c (antiJ L n) (antiJ L n) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (antiJ L n) (antiJ L n) M → ∃ g ∈ U, Φ g = M) (K : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1) :
    ∀ h ∈ U, ∃ k₁ ∈ K, ∃ k₂ ∈ K, h⁻¹ = k₁ * h * k₂ := by
  have hcc : ∀ x, c (c x) = x := hU.1
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  have hherm : ∀ i j, c ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp
  intro h hh
  let g : GL (Fin n) L := Φ.toHomUnits h
  have eg : ∀ x : G, ((Φ.toHomUnits x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Φ x := fun _ => rfl
  have hg : g ∈ UJ c (J : Matrix (Fin n) (Fin n) L) := by
    show cT c (g : Matrix (Fin n) (Fin n) L) * _ * (g : Matrix (Fin n) (Fin n) L) = _
    rw [hJe, eg]
    exact (iso_cT_cart2 hcc _).1 (hiso h)
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ hherm hg
  have hkU : ∀ k ∈ UJ c (J : Matrix (Fin n) (Fin n) L), Iso c (antiJ L n) (antiJ L n) (k : Matrix (Fin n) (Fin n) L) :=
    fun k hk => (iso_cT_cart2 hcc _).2 (by rw [← hJe]; exact hk)
  obtain ⟨g₁, hg₁, e₁⟩ := surj _ (hkU k₁ hk₁.1)
  obtain ⟨g₂, hg₂, e₂⟩ := surj _ (hkU k₂ hk₂.1)
  have memK : ∀ (x : G) (k : GL (Fin n) L), x ∈ U → Φ x = k → k ∈ GLint (Fin n) (intL L) → x ∈ K := by
    intro x k hx ex hk
    have einv : Φ x⁻¹ = ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      calc Φ x⁻¹ = Φ x⁻¹ * (Φ x * ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [ex, Units.mul_inv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    refine (hK x).2 ⟨hx, fun i j => ?_, fun i j => ?_⟩
    · rw [ex]; exact P.cartan_entries_of_mem _ _ hk i j
    · rw [einv]; exact P.cartan_entries_of_mem _ _ (inv_mem hk) i j
  refine ⟨g₁, memK _ _ hg₁ e₁ hk₁.2, g₂, memK _ _ hg₂ e₂ hk₂.2,
    inj _ (inv_mem hh) _ (mul_mem (mul_mem hg₁ hh) hg₂) ?_⟩
  have e' := congrArg (fun x : GL (Fin n) L => (x : Matrix (Fin n) (Fin n) L)) e
  simp only [Units.val_mul] at e'
  rw [map_mul, map_mul, e₁, e₂, ← eg h⁻¹, map_inv]
  exact e'

end Abstract

theorem cartanSt2 : CartanSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW _ v w hw hh
  have hσ := hB.cm
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw hu hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ d) a.1 := hg
  have one : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (piE hu) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let Φ : UA σ W.J →* Matrix (Fin d) (Fin d) (w.adicCompletion E) :=
    { toFun := fun g => (a⁻¹).1 * (mat g).map (piE hu) * a.1
      map_one' := by
        rw [show mat (1 : UA σ W.J) = 1 from rfl, one, Matrix.mul_one, Units.inv_mul]
      map_mul' := fun g g' => by
        rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.map_mul]
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left] }
  have hΦ : ∀ g, Φ g = (a⁻¹).1 * (mat g).map (piE hu) * a.1 := fun _ => rfl
  have hint : ∀ g, (∀ i j, Valued.v (Φ g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := fun g => by
    rw [stab_iff hw hu ha]
    exact Iff.rfl
  refine inv_mem_KgK_cart2 hU (USub σ W v) Φ (fun g => ?_) (fun g hg g' hg' e => ?_) (fun N hN => ?_) _ (fun g => ?_) hh
  · have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE hu)) := by
      unfold Iso
      rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
      exact Matrix.ext fun i j => piE_incl hu _
    rw [hΦ]
    exact (iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai)
  · have e1 : (mat g).map (piE hu) = (mat g').map (piE hu) := by
      have e2 := congrArg (fun N => a.1 * N * (a⁻¹).1) e
      simpa [hΦ, Matrix.mul_assoc] using e2
    refine Subtype.ext (Units.ext (mat_inj hw hu ?_ e1))
    have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
    rwa [sub_sub_sub_cancel_right] at this
  · have h2 := (hai.mul ((iso_smul_iff hl _ _).2 hN)).mul (hai.inv a.mul_inv)
    have h3 := h2.isUnit_det (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((map_ne_zero _).2 (PositivityTheory.ThKH.Iwas.det_ne_zero hW)).isUnit)
    obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
    refine ⟨k, hk, ?_⟩
    rw [hΦ, ek]
    simp [Matrix.mul_assoc]
  · rw [hint, hint]
    exact and_congr Iff.rfl ⟨fun H => ⟨fun y hy => (H y hy).1, fun y hy => (H y hy).2⟩, fun H y hy => ⟨H.1 y hy, H.2 y hy⟩⟩

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.UnitLiftSt
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas

theorem unitLiftSt : UnitLiftSt := by
  intro F E _ _ _ _ _ v y
  have hab : ∀ a b : Ev E v, sgE E v a * sgE E v b = sgE E v (a * b) := fun a b => by
    have e := GlobalTheory.EmbChart.tensAt_mul_right (E := E) v a (sgE E v b)
    rw [comp_sgE] at e
    exact e
  have key : ∀ a b : Ev E v, (1 + sgE E v a) * (1 + sgE E v b) = 1 + sgE E v ((1 + a) * (1 + b) - 1) := fun a b => by
    have e : (1 + a) * (1 + b) - 1 = a + b + a * b := by ring
    rw [e, map_add (f := _), map_add (f := _), ← hab]
    ring
  refine ⟨⟨1 + sgE E v ((y : Ev E v) - 1), 1 + sgE E v (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1), ?_, ?_⟩, ?_, ?_⟩
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.mul_inv, sub_self, map_zero, add_zero]
  · rw [key, show (1 : Ev E v) + ((y : Ev E v) - 1) = y by ring, show (1 : Ev E v) + (((y⁻¹ : (Ev E v)ˣ) : Ev E v) - 1) = _ by ring,
      Units.inv_mul, sub_self, map_zero, add_zero]
  · change At (evFin F v) (1 + sgE E v _ - 1)
    rw [add_sub_cancel_left]
    exact at_sgE _
  · change compFin F E v (1 + sgE E v _) = _
    rw [map_add (f := _), map_one, comp_sgE]
    ring

theorem pInvSt : PInvSt := by
  intro F E _ _ _ _ _ σ d W v w hw m Cy hL p hp
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨hpU, t₀, ht₀⟩ := hp
  set φ := piE (F := F) (E := E) h with hφ
  have hpinv : (mat p⁻¹).map φ * (mat p).map φ = 1 := by
    rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

  have hfree : ∀ s : Fin m → w.adicCompletion E, Cy.map φ *ᵥ s = 0 → s = 0 := fun s hs => by
    obtain ⟨s', hs', e⟩ := vec_surj h s
    have h0 : Cy *ᵥ s' = 0 := vec_inj hw h (by rw [sub_zero]; exact at_mulVec_left hL.supp _) (by
      rw [piE_mulVec, e, hs]; funext i; simp)
    rw [← e, hL.free s' hs' h0]; funext i; simp
  have hdet : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → (t.map φ).det ≠ 0 := fun t ht hdt => by
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdt
    refine hs0 (hfree s ?_)
    have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t.map φ := by rw [← Matrix.map_mul, ht, Matrix.map_mul]
    have e2 : Cy.map φ *ᵥ s = (mat p⁻¹).map φ *ᵥ ((Cy.map φ * t.map φ) *ᵥ s) := by
      rw [← e1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hpinv, Matrix.one_mul]
    rw [e2, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hunit : ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → IsUnit (t.map (compFin F E v)).det := fun t ht => by
    have e : (t.map (compFin F E v)).map (toCompl h) = t.map φ := by rw [Matrix.map_map]; rfl
    have hne : toCompl h (t.map (compFin F E v)).det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, e]; exact hdet t ht
    exact (MulEquiv.isUnit_map (RingEquiv.ofBijective (toCompl h) (toCompl_bijective hw h)).toMulEquiv).1
      (isUnit_iff_ne_zero.2 hne)
  refine ⟨⟨inv_mem_UAt hpU, ?_⟩, hunit⟩
  have hu : IsUnit (t₀.map φ).det := isUnit_iff_ne_zero.2 (hdet t₀ ht₀)
  obtain ⟨t', ht'a, ht'⟩ := mat_surj h (t₀.map φ)⁻¹
  refine ⟨t', mat_inj hw h (at_sub (at_mul_right _ hL.supp) (at_mul_left hL.supp _)) ?_⟩
  have e1 : (mat p).map φ * Cy.map φ = Cy.map φ * t₀.map φ := by rw [← Matrix.map_mul, ht₀, Matrix.map_mul]
  rw [Matrix.map_mul, Matrix.map_mul, ht']
  calc (mat p⁻¹).map φ * Cy.map φ = (mat p⁻¹).map φ * (Cy.map φ * (t₀.map φ * (t₀.map φ)⁻¹)) := by
        rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Cy.map φ * (t₀.map φ)⁻¹ := by
        rw [← Matrix.mul_assoc (Cy.map φ), ← e1, Matrix.mul_assoc, ← Matrix.mul_assoc ((mat p⁻¹).map φ), hpinv, Matrix.one_mul]

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunFin
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK

theorem finSt_relIndex_le {G : Type} [Group G] {H K L : Subgroup G} (hKL : K ≤ L) (h : H.relIndex L ≠ 0) :
    H.relIndex K ≠ 0 := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_relIndex_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (b : GL (Fin n) (w.adicCompletion E)) :
    (KGL w (n := n) ⊓ (KGL w (n := n)).map (MulAut.conj b).toMonoidHom).relIndex (KGL w (n := n)) ≠ 0 := by
  obtain ⟨ho, hc⟩ := SatCompare.isOpen_isCompact_KGL w n
  have hcont : Continuous fun x : GL (Fin n) (w.adicCompletion E) => b⁻¹ * x * b :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine finSt_relIndex_nhds hc (U := (KGL w (n := n) : Set _) ∩ (fun x => b⁻¹ * x * b) ⁻¹' (KGL w (n := n) : Set _))
    ((ho.inter (ho.preimage hcont)).mem_nhds ⟨one_mem _, by simp [one_mem]⟩) fun k _ hk => ⟨hk.1, ?_⟩
  refine ⟨b⁻¹ * k * b, hk.2, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem finSt : FinSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw g hg
  classical
  have hv : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hv
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKH.Iwas.exists_frame hB.cm hw hv hc hW
  let Φ : UA σ W.J →* GL (Fin d) (w.adicCompletion E) :=
    (MulAut.conj a⁻¹).toMonoidHom.comp
      ((Units.map (RingHom.mapMatrix (PositivityTheory.ThKH.Iwas.piE hv)).toMonoidHom).comp (Subgroup.subtype _))
  have hΦ : ∀ x, ((Φ x : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (a⁻¹).1 * (mat x).map (PositivityTheory.ThKH.Iwas.piE hv) * a.1 := fun x => by
    simp [Φ, mat]
  have memK : ∀ x ∈ UAt σ W (evFin F v), x ∈ KSub σ W v ↔ Φ x ∈ KGL w (n := d) := fun x hx => by
    rw [mem_GLint_iff, ← map_inv, hΦ, hΦ]
    change (x ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat x *ᵥ y ∈ latW W v ∧ mat x⁻¹ *ᵥ y ∈ latW W v) ↔ _
    rw [← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha, ← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha]
    exact ⟨fun H => ⟨fun y hy => (H.2 y hy).1, fun y hy => (H.2 y hy).2⟩, fun H => ⟨hx, fun y hy => ⟨H.1 y hy, H.2 y hy⟩⟩⟩
  set K := KSub σ W v
  set H' := KGL w (n := d) ⊓ (KGL w (n := d)).map (MulAut.conj (Φ g)).toMonoidHom
  have h1 : (H'.comap Φ).relIndex K ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    refine finSt_relIndex_le ?_ (finSt_KGL w d (Φ g))
    rintro _ ⟨k, hk, rfl⟩
    exact (memK k hk.1).1 hk
  have h2 : H'.comap Φ ⊓ K ≤ conjInf K g := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨hk2, g⁻¹ * k * g, ?_, ?_⟩
    · have hx : g⁻¹ * k * g ∈ UAt σ W (evFin F v) := mul_mem_UAt (mul_mem_UAt (inv_mem_UAt hg) hk2.1) hg
      refine (memK _ hx).2 ?_
      obtain ⟨y, hy, ey⟩ := hk1.2
      have : Φ (g⁻¹ * k * g) = y := by
        rw [map_mul, map_mul, map_inv, ← ey]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]; exact hy
    · simp [MulAut.conj_apply, mul_assoc]
  have h3 : (H'.comap Φ ⊓ K).relIndex K ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
  intro h0
  exact h3 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K h2))

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
noncomputable section

namespace PositivityTheory.Sph

section AvgAbs

variable {Γ : Type} [Group Γ]

def avgQ (H : Subgroup Γ) (f : Γ → ℂ) : ℂ := (H.index : ℂ)⁻¹ * ∑ᶠ q : Γ ⧸ H, f (Quotient.out q)

theorem out_mk_inv {H : Subgroup Γ} {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) (g : Γ) :
    f (Quotient.out (g : Γ ⧸ H)) = f g := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [e, hf g h h.2]

theorem avgQ_le {H H' : Subgroup Γ} (hle : H' ≤ H) (h0 : H'.index ≠ 0) {f : Γ → ℂ}
    (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) : avgQ H' f = avgQ H f := by
  classical
  have hH0 : H.index ≠ 0 := ne_zero_of_dvd_ne_zero h0 (Subgroup.index_dvd_of_le hle)
  have hmul := Subgroup.relIndex_mul_index hle
  have hR0 : H'.relIndex H ≠ 0 := fun h => h0 (by rw [← hmul, h, zero_mul])
  have : Finite (Γ ⧸ H') := Subgroup.index_ne_zero_iff_finite.1 h0
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 hH0
  have : Finite (H ⧸ H'.subgroupOf H) := Subgroup.index_ne_zero_iff_finite.1 hR0
  let _ := Fintype.ofFinite (Γ ⧸ H')
  let _ := Fintype.ofFinite (Γ ⧸ H)
  let _ := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  have hf' : ∀ x, ∀ h ∈ H', f (x * h) = f x := fun x h hh => hf x h (hle hh)
  have hg : ∀ q' : Γ ⧸ H', f (Quotient.out q') = f (Quotient.out ((Subgroup.quotientEquivProdOfLE hle q').1)) := fun q' => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q'
    have e : ((Subgroup.quotientEquivProdOfLE hle (g : Γ ⧸ H')).1 : Γ ⧸ H) = (g : Γ ⧸ H) := rfl
    rw [e, out_mk_inv hf', out_mk_inv hf]
  have hcard : (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) = (H'.relIndex H : ℂ) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  unfold avgQ
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ (fun p => f (Quotient.out p.1)) hg, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [← Finset.mul_sum, ← hmul, Nat.cast_mul]
  have a : (H'.relIndex H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR0
  have b : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hH0
  field_simp

theorem avgQ_mul {N : Subgroup Γ} [N.Normal] {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ N, f (x * h) = f x) (k : Γ) :
    avgQ N (fun x => f (x * k)) = avgQ N f := by
  unfold avgQ
  congr 1
  have e : ∀ q : Γ ⧸ N, f (Quotient.out q * k) = f (Quotient.out (q * (k : Γ ⧸ N))) := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]
    rw [out_mk_inv hf]
  simp only [e]
  exact finsum_comp_equiv (Equiv.mulRight (k : Γ ⧸ N)) (f := fun q => f (Quotient.out q))

theorem avgQ_add {H : Subgroup Γ} (h0 : H.index ≠ 0) (f g : Γ → ℂ) :
    avgQ H (fun x => f x + g x) = avgQ H f + avgQ H g := by
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 h0
  unfold avgQ
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]

theorem avgQ_smul (H : Subgroup Γ) (c : ℂ) (f : Γ → ℂ) : avgQ H (fun x => c * f x) = c * avgQ H f := by
  unfold avgQ
  rw [← mul_finsum, mul_left_comm]

end AvgAbs

theorem avgSt : AvgSt := by
  classical
  intro G S _ _ _ K V ω l₀ hV h1 hmul hst
  let f : S → K → ℂ := fun φ x => l₀ (ω x φ)
  have hfe : ∀ φ (x : K), f φ x = l₀ (ω x φ) := fun _ _ => rfl
  have hinvH : ∀ φ ∈ V, ∀ H : Subgroup G, (∀ k ∈ H, ω k φ = φ) → ∀ (x : K), ∀ h ∈ H.subgroupOf K, f φ (x * h) = f φ x :=
    fun φ hφ H hH x h hh => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 h h.2 φ hφ, hH h (Subgroup.mem_subgroupOf.1 hh)]
  choose Hc hHcK hHc0 hHcfix using hst
  have fin1 : ∀ φ (hφ : φ ∈ V), ((Hc φ hφ).subgroupOf K).FiniteIndex := fun φ hφ => ⟨hHc0 φ hφ⟩
  let N : ∀ φ, φ ∈ V → Subgroup K := fun φ hφ => ((Hc φ hφ).subgroupOf K).normalCore
  have hNn : ∀ φ hφ, (N φ hφ).Normal := fun φ hφ => Subgroup.normalCore_normal _
  have hN0 : ∀ φ hφ, (N φ hφ).index ≠ 0 := fun φ hφ => by
    haveI := fin1 φ hφ
    exact (Subgroup.finiteIndex_normalCore _).index_ne_zero
  have hNinv : ∀ φ hφ, ∀ (x : K), ∀ h ∈ N φ hφ, f φ (x * h) = f φ x := fun φ hφ x h hh =>
    hinvH φ hφ _ (hHcfix φ hφ) x h (Subgroup.normalCore_le _ hh)

  have key : ∀ φ (hφ : φ ∈ V) (H' : Subgroup K), H'.index ≠ 0 → (∀ (x : K), ∀ h ∈ H', f φ (x * h) = f φ x) →
      avgQ H' (f φ) = avgQ (N φ hφ) (f φ) := fun φ hφ H' h0 hH' => by
    have hM := Subgroup.index_inf_ne_zero h0 (hN0 φ hφ)
    rw [← avgQ_le inf_le_left hM hH', avgQ_le inf_le_right hM (hNinv φ hφ)]
  let lamF : S → ℂ := fun φ => if hφ : φ ∈ V then avgQ (N φ hφ) (f φ) else 0
  have hlamF : ∀ φ (hφ : φ ∈ V), lamF φ = avgQ (N φ hφ) (f φ) := fun φ hφ => dif_pos hφ
  let lamV : V →ₗ[ℂ] ℂ :=
    { toFun := fun φ => lamF φ
      map_add' := fun φ ψ => by
        have hφ := φ.2
        have hψ := ψ.2
        have hs := V.add_mem hφ hψ
        have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
        change lamF (φ.1 + ψ.1) = lamF φ.1 + lamF ψ.1
        have e : f (φ.1 + ψ.1) = fun x => f φ.1 x + f ψ.1 x := funext fun x => by rw [hfe, hfe, hfe, map_add (f := _), map_add (f := _)]
        rw [hlamF _ hs, hlamF _ hφ, hlamF _ hψ, ← key _ hs _ h0 (fun x h hh => by
            rw [e]; exact congrArg₂ (· + ·) (hNinv _ hφ x h hh.1) (hNinv _ hψ x h hh.2)),
          ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2), e,
          avgQ_add h0]
      map_smul' := fun c φ => by
        have hφ := φ.2
        have hs := V.smul_mem c hφ
        change lamF (c • φ.1) = c • lamF φ.1
        have e : f (c • φ.1) = fun x => c * f φ.1 x := funext fun x => by rw [hfe, hfe, map_smul, map_smul, smul_eq_mul]
        rw [hlamF _ hs, hlamF _ hφ, ← key _ hs _ (hN0 _ hφ) (fun x h hh => by rw [e]; exact congrArg (c * ·) (hNinv _ hφ x h hh)),
          e, avgQ_smul, smul_eq_mul] }
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  have hπ' : ∀ φ (hφ : φ ∈ V), π φ = ⟨φ, hφ⟩ := fun φ hφ => LinearMap.congr_fun hπ ⟨φ, hφ⟩
  have hlam : ∀ φ (hφ : φ ∈ V), (lamV ∘ₗ π) φ = avgQ (N φ hφ) (f φ) := fun φ hφ => by
    rw [LinearMap.comp_apply, hπ' φ hφ]
    exact hlamF φ hφ
  refine ⟨lamV ∘ₗ π, fun k hk φ hφ => ?_, fun φ hφ H hHK hH0 hH => ?_⟩
  · have hψ := hV k hk φ hφ
    haveI := hNn φ hφ
    haveI := hNn _ hψ
    have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
    have e : f (ω k φ) = fun x => f φ (x * ⟨k, hk⟩) := funext fun x => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 k hk φ hφ]
    rw [hlam _ hψ, hlam _ hφ, ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2),
      ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), e]
    exact avgQ_mul (N := N φ hφ ⊓ N (ω k φ) hψ) (fun x h hh => hNinv _ hφ x h hh.1) _
  · rw [hlam φ hφ, ← key φ hφ (H.subgroupOf K) hH0 (hinvH φ hφ H hH)]
    rfl

end PositivityTheory.Sph

end
end

namespace PositivityTheory.Sph

theorem sphFun_of_modSt (hM : ModSt) : SphFun :=
  sphFun_of countSt avgSt pInvSt unitLiftSt charSt evInvSt siegSt hM cartanSt2 finSt

end PositivityTheory.Sph
