module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftUnpacking

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFiniteOrder
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.QkActPf
namespace ReciprocityTheory.ChartRestriction.G.H1

theorem qkActExists_of (hG : Out.GlobalFnsSt) : QkActExistsStatement := by
  intro E _ _ _ H V _ _ _ t P
  letI := H.starRing
  intro F _ _ _ k a p
  exact Geo.Tor.qkAct_exists hG P.D.tau_bimult P.oD a p

end ReciprocityTheory.ChartRestriction.G.H1
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J := by
  unfold val
  show gm r z _ (res le_top c * t.s _) = gm r z ⊤ c * gm r z _ (t.s _)
  refine (MonoidHom.map_mul (gm r z _) _ _).trans ?_
  congr 1
  exact gm_res r z le_top (hJ.mem φ r) c

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

def zUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := V) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_scale (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΦr : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s)
    (ζ : F) (hζ : ζ ≠ 0) (s t : Fam D.toPre F k) :
    PhiRel D.toPre F k p (scaleGen (zUnit (V := V) ζ hζ) w) s t ↔ t = ζ • Φ s := by
  have hw' := scaleGen_isGen (zUnit (V := V) ζ hζ) w hw
  have key : ∀ s : Fam D.toPre F k, PhiVal p (scaleGen (zUnit (V := V) ζ hζ) w) s.s (ζ • Φ s).s := by
    intro s a' β hβ T ρ z' J hJ
    have h1 := (phiRel_iff hG p w hw s (Φ s)).1 ((hΦr s (Φ s)).2 rfl) a' β hβ T ρ z' J hJ
    have hu : gs (ρ.left ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z' ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
        (gm (ρ ≫ fst (TF (R := V) F) D.toPre.P.A).left z' ⊤ (zUnit (V := V) ζ hζ)).val :=
      gs_unit _ z' ⊤ trivial (zUnit (V := V) ζ hζ)
    rw [sval_smul ζ (Φ s) β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scaleGen hJ, hu]
    simp only [Units.val_mul]
    ring
  constructor
  · intro h
    exact phi_unique p _ ((phiRel_iff hG p _ hw' s t).1 h) (key s)
  · rintro rfl
    exact (phiRel_iff hG p _ hw' s _).2 (key s)

theorem finOrd_of_pow {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)))
    (Ψ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k) (hΨ : ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Ψ s)
    (hpow : ∀ s, (Ψ ^ k) s = s) : FinOrd D F k p w 1 := by
  have hext : ∀ a b : Fam D.toPre F k, (∀ α j, (a.s α).f j = (b.s α).f j) → a = b := by
    rintro ⟨sa, fa⟩ ⟨sb, fb⟩ h
    have hs : sa = sb := by
      funext α
      have h1 : (sa α).f = (sb α).f := funext (h α)
      rcases hx : sa α with ⟨xf, xc⟩
      rcases hy : sb α with ⟨yf, yc⟩
      rw [hx, hy] at h1
      simp only at h1
      subst h1
      rfl
    subst hs
    rfl
  have hone : ∀ W, DegPre.constBF D.toPre F (1 : F) W = 1 := by
    intro W
    simp [DegPre.constBF]
  refine ⟨k, hk, fun ss ts h α j => ?_⟩
  have hstep : ∀ i : Fin k, ss i.succ = Ψ (ss i.castSucc) := by
    intro i
    obtain ⟨h1, h2⟩ := h i
    rw [← (hΨ _ _).mp h1]
    apply hext
    intro α j
    rw [h2 α j, hone, _root_.one_mul]
  have hall : ∀ n (hn : n ≤ k), ss ⟨n, by omega⟩ = (Ψ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Module.End.one_apply]
      rfl
    | succ n ih =>
      intro hn
      have h3 := hstep ⟨n, by omega⟩
      rw [pow_succ', Module.End.mul_apply, ← ih (by omega)]
      exact h3
  have hlast : ss (Fin.last k) = ss 0 := by
    rw [show Fin.last k = ⟨k, by omega⟩ from rfl, hall k le_rfl]
    exact hpow (ss 0)
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFiniteOrder
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem canonLiftFix_of_laws (hL : Out.Laws) : CanonLiftFixStatement := by
  intro E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro α N hN hαN _hco _hNu F _ _ _ θ θα hpull p x hx hxα
  have hQ : QkActExistsStatement := qkActExists_of hL.globalFns
  have hUnpack : ∃ (z : P.D.toPre.X) (q : QkPt P.D.toPre F (1 * N))
      (h g0 : GtPtF P.D.toPre F),
      p.y = -(star α • z) ∧ GtAct P.oD α p.g q.g ∧ GtPtF.IsIota z h ∧
      q.g.IsAdd h g0 ∧ g0.IsZero := by
    have hαN' : α * star α = (N : 𝓞 E) := hαN
    have hB : P.D.toPre.TauBimult := P.D.tau_bimult
    obtain ⟨p0, hy0, hz0, hadd0⟩ := CanonicalLiftUnpacking.exists_zero_qk (F := F) hB (1 * N)
    obtain ⟨f, hf1, -, hf3, hf4, hf5, -⟩ := hT F (1 * N) (by omega)
    obtain ⟨p', hp'⟩ := hQ E H V t P F (1 * N) α p
    have hfp' := hf5 α p p' hp'
    obtain ⟨q, hqy, hGt, hqe⟩ := hp'
    have hf0 : f p0 = 1 := by
      have h := hf4 p0 p0 p0 ⟨p0, by rw [hy0, add_zero], hadd0, qk_equiv_refl hB p0⟩
      exact (mul_left_cancel ((_root_.mul_one _).trans h)).symm
    have hfq : f q = f p0 := by
      rw [(hf3 q p').2 hqe, hfp', ← (hf1 p x).1 hx, hxα, hf0]
    obtain ⟨z, hz, h, hIota, hAdd⟩ := (hf3 q p0).1 hfq
    refine ⟨z, q, h, p0.g, ?_, hGt, hIota, hAdd, hz0⟩
    have e : α • p.y + (1 * N) • z = 0 := by rw [← hqy, ← hz, hy0]
    have e' := congrArg (fun w => star α • w) e
    simp only [smul_add, smul_zero, smul_smul] at e'
    have key : ∀ w : P.D.toPre.X, (1 * N) • w = N • w := fun w => by rw [Nat.one_mul]
    rw [smul_comm (star α) (1 * N) z, _root_.mul_comm (star α) α, hαN', Nat.cast_smul_eq_nsmul,
      ← key p.y, ← smul_add] at e'
    haveI : Module.Free ℤ P.D.toPre.X := P.D.toPre.freeX
    rw [← Nat.cast_smul_eq_nsmul ℤ] at e'
    have e3 : p.y + star α • z = 0 := (smul_eq_zero.1 e').resolve_left (by omega)
    exact eq_neg_of_add_eq_zero_left e3
  obtain ⟨z, q, h, g0, hy, hgt, hι, hadd, hz⟩ := hUnpack
  haveI := P.oD.onB.hom (star α)
  haveI := P.oD.onB.hom α
  obtain ⟨r, hr, hr0⟩ := Geo.Tor.exists_ros (A := P.D.toPre.P.A) (L := P.D.toPre.P.L)
    hL.globalFns P.D.toPre.P.isAb P.D.toPre.P.isLB (P.oD.onB.act (star α)) (P.oD.onB.act α)
    (by have hR := P.oD.onB.rosati (star α); rwa [star_star] at hR)
  obtain ⟨hb, hrel⟩ := ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftOrigin.gt_rel P.oD α p.g q.g h g0 z hgt hι hadd hz r hr hr0
  obtain ⟨u0, hu0, hc0, -⟩ := hpull.1 0
  obtain ⟨w, hw, hwv⟩ := CanonicalLiftTraces.exists_w P.oD α N hN p.g.b z hb u0 hu0
  have hfix : PhiRel P.D.toPre F (1 * N) p w θα θα :=
    CanonicalLiftFrobenius.phi_fixes hL.globalFns P.oD α N p z hy hb r hr hr0 hrel u0 hu0 hc0 w hw hwv θ θα hpull
  have hk : 1 ≤ 1 * N := by omega
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw
  obtain ⟨c, hc0', hcpow⟩ := phiPow_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw

  have hpowc : ∀ s, (Φ ^ (1 * N)) s = c • s := by
    intro s
    have h1 := hcpow (fun i => (Φ ^ (i : ℕ)) s) (by
      intro i
      rw [hΦ]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ']
      rfl)
    rw [isSmul_iff] at h1
    simpa using h1
  have hΦθ : Φ θα = θα := ((hΦ θα θα).1 hfix).symm
  by_cases hc1 : c = 1
  · subst hc1
    refine ⟨w, hw, ?_, hfix⟩
    exact CanonicalLiftFiniteOrder.finOrd_of_pow hk p w Φ hΦ (fun s => by rw [hpowc, one_smul])
  ·
    have hθ : θα = 0 := by
      have hfixpow : ∀ n : ℕ, (Φ ^ n) θα = θα := by
        intro n
        induction n with
        | zero => rw [pow_zero]; rfl
        | succ n ih =>
          rw [pow_succ']
          show Φ ((Φ ^ n) θα) = θα
          rw [ih, hΦθ]
      have h3 : θα = c • θα := by rw [← hpowc θα, hfixpow]
      have h4 : (c - 1) • θα = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
      have h5 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
      calc θα = (c - 1)⁻¹ • ((c - 1) • θα) := by rw [smul_smul, inv_mul_cancel₀ h5, one_smul]
        _ = 0 := by rw [h4, smul_zero]

    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (show 0 < 1 * N by omega)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega : 1 * N ≠ 0)] at hζ
      exact inv_ne_zero hc0' hζ.symm
    have hsc := CanonicalLiftFiniteOrder.phiRel_scale hL.globalFns p w hw Φ hΦ ζ hζ0
    refine ⟨DVR.scaleGen (CanonicalLiftFiniteOrder.zUnit (V := V) ζ hζ0) w, DVR.scaleGen_isGen _ _ hw, ?_, ?_⟩
    · refine CanonicalLiftFiniteOrder.finOrd_of_pow hk p _ (ζ • Φ) (fun s t => by rw [hsc]; rfl) ?_
      intro s
      rw [smul_pow, LinearMap.smul_apply, hpowc, smul_smul, hζ, inv_mul_cancel₀ hc0', one_smul]
    · rw [hsc, hθ, map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.H1
