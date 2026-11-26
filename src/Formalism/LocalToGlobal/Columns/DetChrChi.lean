module

public import Formalism.LocalToGlobal.Columns.MtHeckeSum
public import Formalism.LocalToGlobal.Columns.InputsGenus
public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.TiedXpT
section -- merged from Formalism.LocalToGlobal.Columns.TiedXpV
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xp_half (R : Ranks) : R.m * (R.t + 1) / 2 = R.m * ((R.t + 1) / 2) := by
  obtain ⟨b, hb⟩ := R.t_odd
  have h : R.t + 1 = 2 * (b + 1) := by omega
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem xp_sgTrue_eq {R : Ranks} (S : RowPar R) : S.sgTrue = shW S.sg ((R.m * (R.t + 1) / 2 : ℕ) : ℤ) := by
  unfold RowPar.sgTrue shiftW shW
  congr 1
  funext i
  rw [xp_half]
  push_cast
  ring

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_mulLat_L (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)} {H : Subgroup (GLG (E := E) (n := n) (SG := SG))} (g : UF E n × H)
    (e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    Formalism.L2.Forms.mulLat (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) e.1.L = (g • e).1.L := by
  rw [rlc_smul_val, Deco.L_act]
  unfold Formalism.L2.Forms.mulLat gmap
  congr 1
  apply LinearMap.ext
  intro x
  show (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = g.1.1 x
  rw [← rlc_ratHom_apply hc n]
  have : ratHom hc n ((ratEquiv hc n).symm g.1) = g.1 := (ratEquiv hc n).apply_symm_apply g.1
  rw [this]

def padL (E : Type) [Field E] (n N : ℕ) : (Fin n → E) →ₗ[E] (Fin N → E) where
  toFun x j := if h : (j : ℕ) < n then x ⟨j, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]

theorem padL_apply (E : Type) [Field E] (n N : ℕ) (x : Fin n → E) (j : Fin N) :
    padL E n N x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0 := rfl

theorem xp_tilH_L {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (hpi : ∀ P : ST, pi ∈ P.1.asIdeal)
    (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r)
    (iX : (Fin n → E) →ₗ[E] (Fin N → E))
    (hiX : ∀ x (j : Fin N), iX x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0) :
    (DecoSet.tilH (ST := ST) hN pi d).1.L = d.1.N.map (iX.restrictScalars (𝓞 E)) ⊔
      Submodule.span (𝓞 E) {(Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E)} := by
  subst hN
  show (DecoSet.til (ST := ST) pi d).1.L = _
  rw [DecoSet.til_val d hT hG, d.2.til_L hT hG hpi hdvd]
  have e1 : iX = incl E n := by
    apply LinearMap.ext
    intro x
    funext j
    rw [hiX]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [incl]
    · simp [incl]
  have e2 : z0 E n (algebraMap (𝓞 E) E pi) = (Pi.single (lastIdx (n + 1)) (algebraMap (𝓞 E) E pi) : Fin (n + 1) → E) := by
    have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
    rw [hl]
    funext j
    simp [z0, eLast, Pi.single_apply]
  rw [e1, e2]

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem xp_crd_frame (i : ℕ) (hi : i ≤ d.R.m) (b : Fin (d.sp.X i).rank) :
    d.crd i hi ((d.sp.X i).frame b) = Pi.single (finCongr (d.sp.X_rank i hi) b) (1 : d.host.E) := by
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame b) ((finCongr (d.sp.X_rank i hi)).symm j) = _
  simp only [Basis.equivFun_self, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

def ColDat.z0 (d : ColDat) (u : d.what₂.Word) : Fin (d.R.N d.R.m) → d.host.E :=
  Pi.single (lastIdx (d.R.N d.R.m)) (d.piT u : d.host.E)

theorem zc_eq (hS : SpStd d.toColBase) :
    ∃ c : d.host.E, c ≠ 0 ∧ CF.zc (d.colRec a) = Pi.single (lastIdx (d.R.N d.R.m)) c := by
  obtain ⟨c, hc⟩ := hS.z
  have hr := d.sp.X_rank d.R.m le_rfl
  set b₀ : Fin (d.sp.X d.R.m).rank := (finCongr hr).symm (lastIdx (d.R.N d.R.m)) with hb₀
  have hb : (b₀ : ℕ) + 1 = (d.sp.X d.R.m).rank := by
    have h1 : (b₀ : ℕ) = d.R.N d.R.m - 1 := rfl
    have := d.R.N_pos d.R.m
    omega
  have hz := hc b₀ hb
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply d.sp.z_anis
    rw [hz, zero_smul, map_zero]
  · show d.crd d.R.m le_rfl d.sp.z = _
    rw [hz, map_smul, xp_crd_frame, hb₀, Equiv.apply_symm_apply]
    funext j
    simp [Pi.single_apply]

theorem lastCoordinateUniformizerVector_spans_orthogonal_line (hS : SpStd d.toColBase) (u : d.what₂.Word) : ∃ c : d.host.E, d.z0 u = c • CF.zc (d.colRec a) := by
  obtain ⟨c, hc0, hc⟩ := zc_eq a hS
  refine ⟨(d.piT u : d.host.E) / c, ?_⟩
  rw [hc]
  funext j
  unfold ColDat.z0
  by_cases h : j = lastIdx (d.R.N d.R.m)
  · subst h
    simp [div_mul_cancel₀ _ hc0]
  · simp [h]

theorem hermitianForm_lastCoordinateUniformizerVector_self (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    hform (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) (d.z0 u) (d.z0 u) =
      (((d.colRec a).mem u).A.T : d.host.E) := by
  rw [gramN_eq a hS]
  have h1 := rf_hform_one (X := d.X) (d.z0 u) (d.z0 u)
  refine Eq.trans h1 ?_
  rw [hStd_apply, Finset.sum_eq_single (lastIdx (d.R.N d.R.m))]
  · unfold ColDat.z0
    rw [Pi.single_eq_same]
    have h2 := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h2
    rw [mul_comm]
    exact h2
  · intro j _ hj
    unfold ColDat.z0
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def ColDat.tilPt (d : ColDat) (u : d.what₂.Word) (c : PCl d) : DecoSet (E := d.X.E) (n := d.R.N d.R.m) (ST := d.Pr.vT u) (SG := d.Pr.vGs) :=
  tilR (Pr := d.Pr) (R := d.R) (Finset.Subset.refl _) u (d.reprP c)

def ColDat.tilMv (d : ColDat) (u : d.what₂.Word) (c : PCl d) : (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).G :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv (d.tilPt u c)

theorem tilMv_smul (u : d.what₂.Word) (c : PCl d) :
    d.tilMv u c • d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c) = d.tilPt u c :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv_smul (d.tilPt u c)

def ColDat.tilGa (d : ColDat) (u : d.what₂.Word) (c : PCl d) : URat d.sp.cm (d.R.N d.R.m) :=
  (ratEquiv d.sp.cm (d.R.N d.R.m)).symm (d.tilMv u c).1

def tieGa (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    UJ (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) :=
  ⟨(d.tilGa u c).1, by rw [gramN_eq a hS]; exact (d.tilGa u c).2⟩

theorem coordinates_frame_eq_single (b : Fin d.sp.X'.rank) :
    CF.crdP (d.colRec a) (d.sp.X'.frame b) = Pi.single (finCongr (CF.rankP (d.colRec a)) b) (1 : d.host.E) := by
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame b) ((finCongr (CF.rankP (d.colRec a))).symm j) = _
  simp only [Basis.equivFun_self, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

theorem iXc_eq (hS : SpStd d.toColBase) : CF.iXc (d.colRec a) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) := by
  apply (Pi.basisFun d.host.E (Fin (d.R.N d.R.m - 1))).ext
  intro k
  rw [Pi.basisFun_apply]
  have hk : (k : ℕ) < d.R.N d.R.m := lt_of_lt_of_le k.2 (Nat.sub_le _ _)
  have h1 : (CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)) =
      d.sp.X'.frame ((finCongr (CF.rankP (d.colRec a))).symm k) := by
    rw [LinearEquiv.symm_apply_eq, coordinates_frame_eq_single, Equiv.apply_symm_apply]
  show d.crd d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)))) = _
  rw [h1, hS.iX' _ ((finCongr (d.sp.X_rank d.R.m le_rfl)).symm ⟨k, hk⟩) rfl, xp_crd_frame, Equiv.apply_symm_apply]
  funext j
  rw [padL_apply, Pi.single_apply]
  by_cases h : (j : ℕ) < d.R.N d.R.m - 1
  · rw [dite_eq_left h, Pi.single_apply]
    congr 1
    exact propext ⟨fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m) => (z : ℕ)) e),
      fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m - 1) => (z : ℕ)) e)⟩
  · rw [dite_eq_right h, if_neg]
    rintro rfl
    exact h k.2

theorem til_lat (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1 (CF.clsCrd (d.colRec a) u d.R.m le_rfl
              (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c)) =
      ((d.reprP c).1.N).map ((CF.iXc (d.colRec a)).restrictScalars (𝓞 d.host.E)) ⊔ Submodule.span (𝓞 d.host.E) {d.z0 u} := by
  rw [iXc_eq a hS]
  refine (congrArg (Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1) (clsCrd_eq a u d.R.m le_rfl _)).trans ?_
  refine (xp_mulLat_L d.sp.cm (d.tilMv u c) _).trans ?_
  have h := tilMv_smul u c
  refine (congrArg (fun e : DecoSet (E := d.X.E) (n := d.R.N d.R.m) (ST := d.Pr.vT u) (SG := d.Pr.vGs) => e.1.L) h).trans ?_
  exact xp_tilH_L (N_m_succ d.R) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P) (a.piT_off u)
    (fun P => decoFin_mem_of_mem_divs P.2) (fun r hr => piT_dvd_of_mem d.hX d.hPr u r hr) _ (padL_apply _ _ _)

end Rec

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TiedXpU
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lastVector_eq_single (n : ℕ) (p : E) : z0 E n p = (Pi.single (lastIdx (n + 1)) p : Fin (n + 1) → E) := by
  have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
  rw [hl]
  funext j
  simp [z0, eLast, Pi.single_apply]

theorem xp_tilH_f {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (P : ST)
    (y : Sp E N) (hy : y ∈ (DecoSet.tilH (ST := ST) hN pi d).1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) y) :
    (DecoSet.tilH (ST := ST) hN pi d).1.f P y = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hN
  have hy' : y ∈ (DecoSet.til (ST := ST) pi d).1.Lsh := hy
  have h1 : y ∈ localization₂ P.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N := by
    rw [← (DecoSet.til (ST := ST) pi d).2.locP_Lsh hb P]
    exact le_locP _ _ hy'
  show (DecoSet.til (ST := ST) pi d).1.f P y = _
  rw [DecoSet.til_val d hT hG] at h1 ⊢
  have h2 : (d.1.til (ST := ST) pi).f P y = redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) y) := if_pos h1
  rw [h2, lastVector_eq_single, ← hr, reduction_coe]

theorem xp_til_f_core {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG') {H : Subgroup (GLG (E := E) (n := N) (SG := SG))}
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG')) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E}
    (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet (E := E) (n := N) (ST := ST) (SG := SG)) (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST)
    (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) (g.1.1 x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  have h1 : e.1.f P x = (g • e).1.f P (g.1.1 x) := by
    show _ = e.1.f P (g.1.1.symm (g.1.1 x))
    rw [LinearEquiv.symm_apply_apply]
  have h2 : g.1.1 x ∈ (g • e).1.Lsh := by
    rw [rlc_smul_val, Deco.Lsh_act _ g.1.2]
    exact Submodule.mem_map_of_mem hx
  rw [h1]
  rw [hge] at h2 ⊢
  exact xp_tilH_f hN d hT hG hb P _ h2 r hr

end Gen

section GenJ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_hform_one (hc : CMData F E) {N : ℕ} (x y : Fin N → E) :
    hform (hc.sig : E →+* E) (1 : Matrix (Fin N) (Fin N) E) x y = hStd E N x y := by
  unfold hform
  rw [hStd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
    rfl
  · intro j _ hj
    simp only [Matrix.one_apply_ne' hj, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem xp_til_f_coreJ (hc : CMData F E) {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG')
    {H : Subgroup (GLG (E := E) (n := N) (SG := SG))} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG')) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal)
    (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet (E := E) (n := N) (ST := ST) (SG := SG))
    (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST) (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1)
    (hr : algebraMap (𝓞 E) E r = hform (hc.sig : E →+* E) J (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi))
      ((((ratEquiv hc N).symm g.1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hJ
  refine xp_til_f_core hN hSG d hT hG hb g e hge P x hx r ?_
  rw [hr, xp_hform_one, ← rlc_ratHom_apply hc N]
  have : ratHom hc N ((ratEquiv hc N).symm g.1) = g.1 := (ratEquiv hc N).apply_symm_apply g.1
  rw [this]

end GenJ

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

section Step

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

theorem xp_clsG_U : (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U = levU hc n (Pr.vT u) Pr.vGs Λ.grp := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

theorem xp_clsG_y (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) :
    ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1 = (ptOfD hc n (Pr.vT u) Pr.vGs c₀ (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end Step

section P

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := (∅ : Finset (Pl X.E))) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.N)

theorem xp_clsPG_y (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp) :
    ((clsPG hc σ₀ Λ s hS hs Q).y c).1 = (ptOfD hc n ∅ Pr.vGs 1 (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end P

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

abbrev ColDat.tilC (d : ColDat) (u : d.what₂.Word) (c : PCl d) : StCl (Pr := d.Pr) d.W d.lev u d.R.m :=
  tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c


include hS hH in
set_option maxHeartbeats 1000000 in
theorem xp_Ld_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u d.R.m) :
    CF.Ld (d.colRec a) u d.R.m le_rfl c = (d.repr u d.R.m c).1.Lsh :=
  tie_Ld_eq (X := d.X) (Pr := d.Pr) d.sp.cm d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) c

variable (hP : PtSurjP d)


set_option maxHeartbeats 2000000 in
def tildeLatticeAgreement (u : d.what₂.Word) :
    CF.TilTied (D := d.colRec a) u (atTTied a hH u) (parabolicClassAgreement a hS hH hP u) (levelAgreement a hS hH u d.R.m le_rfl) where
  z0 := d.z0 u
  lastCoordinateUniformizerVector_spans_orthogonal_line := lastCoordinateUniformizerVector_spans_orthogonal_line a hS u
  hermitianForm_lastCoordinateUniformizerVector_self := hermitianForm_lastCoordinateUniformizerVector_self a hS u
  ga := tieGa a hS u
  til_lat := til_lat a hS u
  til_fv := fun v c x r hr =>
    (tie_fv d.sp.cm d.hPr d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) v (d.tilC u c) x).trans
      (xp_til_f_coreJ d.sp.cm (N_m_succ d.R) (Finset.Subset.refl _) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P)
        (a.piT_off u) (sepElt_of_ok d.hPr u) (d.tilMv u c) _ (tilMv_smul u c) v x.1 ((xp_Ld_eq a hS hH u (d.tilC u c)).le x.2) r
        (gramN_eq a hS d.R.m le_rfl) hr)

def TilMove (u : d.what₂.Word) : Prop :=
  ∀ c : PCl d, ∃ κ : levU d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp,
    levRed d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp κ = (d.tilMv u c).2 ∧
    ∀ g : GL (Fin (d.R.N d.R.m)) (d.host.E ⊗[d.host.F] FiniteAdeleRing (𝓞 d.host.F) d.host.F),
      CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 →
      bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 *
        (ptOfD d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m)
          (d.repr u d.R.m (d.tilC u c))).1 = g * κ.1

variable (hQ : PtSurj d)

def tilAd (u : d.what₂.Word) (hM : TilMove a u) :
    CF.TilAd (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) where
  ka := fun c => ⟨(hM c).choose.1, (Subgroup.ext_iff.1 (xp_clsG_U d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m)
    (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m) (hQ u d.R.m)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)) _).2 (hM c).choose.2⟩
  til_ad := fun c g hg => by
    have h1 := xp_clsPG_y d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c)
      (crdPr a hS hH) c
    have h2 := xp_clsG_y d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
      (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl) (d.tilC u c)
    have hg' : CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 := by
      rw [← h1]; exact hg
    have h3 := (hM c).choose_spec.2 g hg'
    exact (congrArg (fun t => bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 * t) h2).trans h3

end Rec

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.LastVectorMemSpan
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem hq_toGLb_mulVec {n : ℕ} (b : Basis (Fin n) E V) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Herm.toGLb b γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ b.equivFun x = b.equivFun (γ x) :=
  LinearMap.toMatrix_mulVec_repr b b (γ : V →ₗ[E] V) x

def hqCrd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) : V ≃ₗ[E] (Fin N → E) :=
  b.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem hq_reGL_mulVec {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (γ : V ≃ₗ[E] V) (x : V) :
    ((Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x = hqCrd b h (γ x) := by
  subst h
  rw [Formalism.L2.Forms.reGL_rfl]
  exact hq_toGLb_mulVec b γ x

def hqLin {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) : V ≃ₗ[E] V :=
  (Formalism.L2.Herm.toGLb b).symm ((Formalism.L2.Forms.reGL h E).symm g)

theorem hqLin_re {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) :
    Formalism.L2.Forms.reGL h E (Formalism.L2.Herm.toGLb b (hqLin b h g)) = g := by
  unfold hqLin
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem hqLin_crd {n N : ℕ} (b : Basis (Fin n) E V) (h : n = N) (g : GL (Fin N) E) (x : V) :
    hqCrd b h (hqLin b h g x) = (g : Matrix (Fin N) (Fin N) E) *ᵥ hqCrd b h x := by
  have := hq_reGL_mulVec b h (hqLin b h g) x
  rw [hqLin_re] at this
  exact this.symm

end Mat

section Form

variable {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]

theorem hq_hform_dot (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem hq_hform_UJ (σ : A →+* A) (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) (x y : n → A) :
    hform σ J ((g : Matrix n n A) *ᵥ x) ((g : Matrix n n A) *ᵥ y) = hform σ J x y := by
  have hτ : σ ∘ ((g : Matrix n n A) *ᵥ x) = (g : Matrix n n A).map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ (g : Matrix n n A) x i
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  rw [hq_hform_dot, hq_hform_dot, hτ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  show _ ⬝ᵥ ((cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *ᵥ y) = _
  rw [hg']

end Form

variable {D : ColRec}

theorem hq_crdN (i : ℕ) (hi : i ≤ D.R.m) : CF.crdN D i hi = hqCrd (D.sp.X i).frame (CF.rankN D i hi) := rfl

def hqG (i : ℕ) (hi : i ≤ D.R.m) (g : UJ (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi)) : CH.GX D i :=
  ⟨hqLin (D.sp.X i).frame (CF.rankN D i hi) g.1, fun x y => by
    rw [hx_hform i hi, hx_hform i hi, hq_crdN, hqLin_crd, hqLin_crd]
    exact hq_hform_UJ _ _ g.1 g.2 _ _⟩

variable {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} {K : CF.ClsPTied u}

variable (T : CF.TilTied u A K (P D.R.m le_rfl))




end Formalism.L2.Col
end
end

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    simpa using (single_mem_stdLat (E := E) (n := n) i 1)
  have hlat := Formalism.UG.P.csGlob_lattice (F := F) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.toIsLattice.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rel

end DetChrChi

end Formalism.L2.Col
