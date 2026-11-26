module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OffZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsFrBorOfMatches
section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.OpenImmersionCompStructureEqGeneric
section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsChartFrBor
section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.NV
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def NV (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ (a' : (E →+* ℂ) × ℕ → ℕ) (n' : ℕ), Dom a' n' ∧ ∃ g ∈ sec Xo c a' n',
    ∃ f ∈ sec Xo c (a + a') (n + n'), evR Xo c g y ≠ 0 ∧ evR Xo c f y ≠ 0

end DifferentiableLines
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

def chr (e : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : ℂ := by
  classical exact toC (∏ ix, t ix ^ e ix).val

theorem chr_ne_zero (e : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : chr e t ≠ 0 := by
  classical
  exact Units.ne_zero (M₀ := ℂ) (∏ ix, t ix ^ e ix : (CAt σ)ˣ)

theorem chr_mul (e : Ix D → ℤ) (t t' : Ix D → (CAt σ)ˣ) : chr e (t * t') = chr e t * chr e t' := by
  classical
  have : (∏ ix, (t * t') ix ^ e ix) = (∏ ix, t ix ^ e ix) * ∏ ix, t' ix ^ e ix := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ix _ => mul_zpow _ _ _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem chr_add (e e' : Ix D → ℤ) (t : Ix D → (CAt σ)ˣ) : chr (e + e') t = chr e t * chr e' t := by
  classical
  have : (∏ ix, t ix ^ (e + e') ix) = (∏ ix, t ix ^ e ix) * ∏ ix, t ix ^ e' ix := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ix _ => zpow_add _ _ _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem chr_zero (t : Ix D → (CAt σ)ˣ) : chr 0 t = 1 := by
  classical
  have : (∏ ix, t ix ^ (0 : Ix D → ℤ) ix) = 1 := Finset.prod_eq_one fun ix _ => zpow_zero _
  exact congrArg (fun u : (CAt σ)ˣ => toC u.val) this

theorem ex_add_int (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) : (fun i => (ex D (a + a') (n + n') i : ℤ)) =
    (fun i => (ex D a n i : ℤ)) + fun i => (ex D a' n' i : ℤ) := by
  funext i
  rw [ex_add]
  simp

theorem dom_add {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n) (h' : Dom a' n') : Dom (a + a') (n + n') :=
  ⟨fun τ _ _ hij => Nat.add_le_add (h.1 τ hij) (h'.1 τ hij), h.2.add h'.2⟩

theorem laU_add' (V : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) {n n' : ℕ} (hn : Even n) (hn' : Even n') (k : V.Comp) :
    laU V (a + a') (n + n') k = laU V a n k + laU V a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  funext τ j
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem evR_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {t : Ix D → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (h : FrBor t y y') :
    toC (evR Xo c f y') = chr (fun i => (ex D a n i : ℤ)) t * toC (evR Xo c f y) := by
  classical
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c).1
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have e : evR Xo c f y' = wchar (ex D a n) t * evR Xo c f y :=
    hL.wt a n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) h
  have e' : (wchar (ex D a n) t : CAt σ) = (∏ ix, t ix ^ (ex D a n ix : ℤ)).val := by
    simp only [wchar, zpow_natCast, Units.coe_prod, Units.val_pow_eq_pow_val]
  rw [e, e']
  rfl

theorem rdU_eq (V : Unf Xo c σ r) (f : Rul Xo c) (k : V.Comp) (x : (V.X k).dom) :
    rdU V f k x.1 = toC (evR Xo c f (V.un k x)) := dif_pos x.2

theorem sec_frBor {V : Unf Xo c σ r} (hU : IsUnf V) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n)
    (hN : NV Xo c σ a n) {k : V.Comp} {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec (laU V a n k) P)
    {x x' : (V.X k).dom} {t : Ix D → (CAt σ)ˣ} (ht : FrBor t (V.un k x) (V.un k x')) :
    P x'.1 = chr (fun i => (ex D a n i : ℤ)) t * P x.1 := by
  obtain ⟨γ, hγ, b, hb, hx⟩ := (hU.2.2.2.1 k k x x').1 ⟨t, ht⟩
  have hx' : x'.1 = rmul (lact γ x.1) b := eq_of_heq (Sigma.mk.inj hx).2
  have hd := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact (V.X k) hγ x.2
  have key : ∀ la Q, (V.X k).IsSec la Q → Q x'.1 = (bchar la b * (V.X k).χ la γ) * Q x.1 := fun la Q hQ => by
    rw [hx', hQ.2.1 _ hd b hb, hQ.2.2 γ hγ _ x.2, mul_assoc]
  obtain ⟨a', n', hD', g, hg, f, hf, hg0, hf0⟩ := hN (V.un k x)
  have e₁ := key _ _ (hU.2.2.2.2.1 a' n' hD' g hg k)
  have e₂ := key _ _ (hU.2.2.2.2.1 _ _ (dom_add hD hD') f hf k)
  rw [rdU_eq, rdU_eq, evR_frBor hg ht] at e₁
  rw [rdU_eq, rdU_eq, evR_frBor hf ht, ex_add_int, chr_add, laU_add' V a a' hD.2 hD'.2, (V.X k).χ_add _ _ γ hγ] at e₂
  have a₁ := mul_right_cancel₀ (show toC (evR Xo c g (V.un k x)) ≠ 0 from hg0) e₁
  have a₂ := mul_right_cancel₀ (show toC (evR Xo c f (V.un k x)) ≠ 0 from hf0) e₂
  have hdiag : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hdet := (hb τ).1
    rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hadd : bchar (laU V a n k + laU V a' n' k) b = bchar (laU V a n k) b * bchar (laU V a' n' k) b := by
    simp only [bchar, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
  rw [key _ _ hP]
  congr 1
  refine mul_right_cancel₀ (chr_ne_zero (fun i => (ex D a' n' i : ℤ)) t) ?_
  rw [a₂, hadd, a₁]
  ring

theorem exists_chart_frBor (T : TorFlag Xo c) (y : FrPt Xo c (CAt σ)) (i : T.X.F.J) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : T.X.ptY y = z) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr i z hz Q ∧ FrBor t Q y := by
  subst e
  have hl := T.X.lies_ptY y
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hl.1 i hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  exact ⟨Q, t, hQ, ht⟩

end DifferentiableLines
end
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology

theorem openImmersion_comp_structure_eq_generic (Y : Model Xo c (RingHom.id c.F)) : Y.j ≫ Y.s = pullback.snd _ _ := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

theorem exists_chartFr_alg (T : TorFlag Xo c) {S : Type} [CommRing S] [Algebra c.F S] (z : Sp S ⟶ T.X.YY)
    (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X) (hs : z ≫ flagStr T.X = spMap (algebraMap c.F S)) (k : T.X.F.J)
    (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) : ∃ Q : FrPt Xo c S, T.X.F.ChartFr k z hz Q := by
  have hr : Set.range z ⊆ Set.range T.X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc T.X).ge (hO (Set.mem_univ s))
  obtain ⟨w, rfl⟩ : ∃ w, w ≫ T.X.inc = z := ⟨_, IsOpenImmersion.lift_fac T.X.inc z hr⟩
  refine (T.X.exists_chartFr w ?_ k hz).imp fun _ => And.left
  rw [← hs, ← openImmersion_comp_structure_eq_generic T.Y, ← pullback.condition_assoc, Category.assoc]

def zOf {T : TorFlag Xo c} (y : GlobalTheory.CxPts (flagStr T.X) σ) : Sp (CAt σ) ⟶ T.X.YY := y.1

theorem exists_fun_chart (T : TorFlag Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (i : T.X.F.J) : ∃ u : Γ(T.X.YY, flagOpen T.X ⊓ T.X.F.U i), ∀ (y : GlobalTheory.CxPts (flagStr T.X) σ)
      (hz : ⊤ ≤ zOf y ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)), y ∈ ptsIn _ σ (flagOpen T.X) →
      T.X.F.ChartFr i (zOf y) hz Q → toC (evR Xo c f Q) = ev _ σ _ u y := by
  have hf' := (GlobalTheory.AllWt.secZ_nat Xo c a n).ge hf
  refine ⟨(secOf T.X _ ⟨f, hf'⟩).loc i, fun y hz Q hO hQ => ?_⟩
  have : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have a := evR_eq_val_secOf (z := zOf y) ⟨f, hf'⟩ hO hQ ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)).1 Q)
  simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a
  exact (congrArg toC a).trans (ev_eq (mem_ptsIn_inf.2 ⟨hO, hz⟩) _).symm

theorem differentiableAt_reads {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) (hN : NV Xo c σ a n) {k : V.Comp} {P : Frame (V.X k).Ψ r → ℂ}
    (hP : (V.X k).IsSec (laU V a n k) P)
    {h : (T.X.LL fun i => (ex D a n i : ℤ)).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T (fun i => (ex D a n i : ℤ)) k P h) (hZ : OffZero V T k h) (i : T.X.F.J) {m : ℕ}
    {B : Set (Fin m → ℂ)} (s : (Fin m → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ)
    (ho : ∀ W, IsOpen (B ∩ s ⁻¹' ptsIn _ σ W))
    (hd : ∀ W (u : Γ(T.X.YY, W)), DifferentiableOn ℂ (fun b => ev _ σ W u (s b)) (B ∩ s ⁻¹' ptsIn _ σ W))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hi : s b₀ ∈ ptsIn _ σ (flagOpen T.X ⊓ T.X.F.U i)) :
    DifferentiableAt ℂ (fun b => h i (s b)) b₀ := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  obtain ⟨W, hW, hbW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (s b₀).1 hi
  set B' := B ∩ s ⁻¹' ptsIn _ σ W with hB'
  have hb₀' : b₀ ∈ B' := ⟨hb₀, hbW⟩
  let A : Type := Γ(T.X.YY, W)
  let α : c.F →+* A := (GlobalTheory.FlagMod.ev (GlobalTheory.FlagMod.tau hW ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  letI : Algebra c.F A := α.toAlgebra
  have hα : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap (algebraMap c.F A) := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hτi : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_right)
  obtain ⟨yA, hyA⟩ := exists_chartFr_alg T (S := A) (GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.tau_le hW (hWle.trans inf_le_left)) hα i hτi
  have hφ : ∀ y : GlobalTheory.CxPts (flagStr T.X) σ, y ∈ ptsIn _ σ W → ∃ φ : A →ₐ[c.F] CAt σ,
      (∀ u, toC (φ u) = ev _ σ W u y) ∧ spMap φ.toRingHom ≫ GlobalTheory.FlagMod.tau hW = zOf y := by
    intro y hy
    let ψ : A →+* CAt σ := GlobalTheory.FlagMod.ev (zOf y) W hy
    have e₁ : spMap ψ ≫ GlobalTheory.FlagMod.tau hW = zOf y := GlobalTheory.FlagMod.spMap_ev (zOf y) hW hy
    have e₂ : spMap (ψ.comp (algebraMap c.F A)) = spMap (algebraMap c.F (CAt σ)) := by
      have e : spMap (ψ.comp (algebraMap c.F A)) = spMap ψ ≫ spMap (algebraMap c.F A) := Spec.map_comp _ _
      rw [e, ← hα, ← Category.assoc, e₁]
      exact y.2
    have e₃ : ψ.comp (algebraMap c.F A) = algebraMap c.F (CAt σ) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
    exact ⟨⟨ψ, fun x => RingHom.congr_fun e₃ x⟩, fun u => (ev_eq hy u).symm, e₁⟩
  choose φ' hφ₁ hφ₂ using hφ
  let φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b => if hb : b ∈ B' then φ' (s b) hb.2 else φ' (s b₀) hbW
  have hφb : ∀ b (hb : b ∈ B'), φ b = φ' (s b) hb.2 := fun b hb => dif_pos hb
  choose y hy using fun b => GlobalTheory.FlagMod.exists_frMap (φ b) yA
  have hsub : ∀ b ∈ B', s b ∈ ptsIn _ σ (flagOpen T.X) ∧ s b ∈ ptsIn _ σ (T.X.F.U i) := fun b hb =>
    mem_ptsIn_inf.1 (ptsIn_mono hWle hb.2)
  have hQ : ∀ b (hb : b ∈ B'), T.X.F.ChartFr i (zOf (s b)) (hsub b hb).2 (y b) := fun b hb =>
    hyA.frMap (hy b) (by rw [hφb b hb]; exact hφ₂ _ _) _
  obtain ⟨k₀, x₀, t₀, ht₀⟩ := hU.2.2.1 (y b₀)
  obtain ⟨B₁, z, hB₁, hb₁, hs₁, hz, hz₀, hl⟩ := GlobalTheory.HolChartLift.exists_hol_lift E H D l Xo c σ r V hσ hU A yA m B' φ y
    (ho W) (fun u => (hd W u).congr fun b hb => by rw [hφb b hb]; exact hφ₁ _ _ u) (fun b _ => hy b) b₀ hb₀' k₀ x₀ t₀ ht₀
  by_cases hk : k₀ = k
  swap
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hB₁.mem_nhds hb₁] with b hb
    refine hZ i (s b) fun x hx e => hk ?_
    obtain ⟨hc, t, ht⟩ := hl b hb
    have e' : T.X.ptY (V.un k ⟨x, hx⟩) = zOf (s b) := e
    have hlx : T.X.F.Lies (zOf (s b)) (V.un k ⟨x, hx⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := (hQ b (hs₁ hb)).exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k₀ k _ _).1 ⟨_, g1 _ _ _ _ _ ht ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨a', n', hD', g, hg, f, hf, hg0, hf0⟩ := hN (y b₀)
  obtain ⟨ug, hug⟩ := exists_fun_chart (σ := σ) T hg i
  obtain ⟨uf, huf⟩ := exists_fun_chart (σ := σ) T hf i
  let x : (Fin m → ℂ) → Frame (V.X k₀).Ψ r := fun b => ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt (V.X k₀) x₀.1 (z b)
  have hx₀ : x b₀ = x₀.1 := by
    simp only [x, hz₀]
    exact ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.cpt_zero _ _
  have hn := hB₁.mem_nhds hb₁
  have hxd : DifferentiableOn ℂ x B₁ := (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.diff_cpt _ _).comp_differentiableOn hz
  have hsec : ∀ {la Q}, (V.X k₀).IsSec la Q → DifferentiableAt ℂ (fun b => Q (x b)) b₀ := fun hQ =>
    (hQ.1.comp hxd fun b hb => (hl b hb).1).differentiableAt hn
  have hfun : ∀ u : Γ(T.X.YY, flagOpen T.X ⊓ T.X.F.U i), DifferentiableAt ℂ (fun b => ev _ σ _ u (s b)) b₀ := fun u =>
    (hd _ u).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)
  have d₁ := hsec hP
  have d₂ := hsec (hU.2.2.2.2.1 a' n' hD' g hg k₀)
  have d₃ := hsec (hU.2.2.2.2.1 _ _ (dom_add hD hD') f hf k₀)
  have n₃ : rdU V f k₀ (x b₀) ≠ 0 := by
    rw [hx₀, rdU_eq, evR_frBor hf (g2 _ _ _ ht₀)]
    exact mul_ne_zero (chr_ne_zero _ _) hf0
  have n₂ : ev _ σ _ ug (s b₀) ≠ 0 := by
    rw [← hug _ _ _ (hsub b₀ hb₀').1 (hQ b₀ hb₀')]
    exact hg0
  have hq : DifferentiableAt ℂ (fun b => P (x b) * rdU V g k₀ (x b) * ev _ σ _ uf (s b) *
      (rdU V f k₀ (x b) * ev _ σ _ ug (s b))⁻¹) b₀ :=
    ((d₁.mul d₂).mul (hfun uf)).mul ((d₃.mul (hfun ug)).inv (mul_ne_zero n₃ n₂))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hn, (d₃.mul (hfun ug)).continuousAt.eventually_ne (mul_ne_zero n₃ n₂)] with b hb hne
  obtain ⟨hc, t, ht⟩ := hl b hb
  have hb' := hs₁ hb
  have ht' := g2 _ _ _ ht
  have e₁ : P (x b) = chr (fun i => (ex D a n i : ℤ)) t⁻¹ * h i (s b) :=
    hR (x b) hc i (s b) (hsub b hb').2 (y b) t⁻¹
      (GlobalTheory.FlagMod.FlagCover.eq_ptY ((hQ b hb').lies.frBor ht')).symm (hQ b hb') ht'
  have e₂ : rdU V g k₀ (x b) = _ := (rdU_eq V g k₀ ⟨_, hc⟩).trans (evR_frBor hg ht')
  have e₃ : rdU V f k₀ (x b) = _ := (rdU_eq V f k₀ ⟨_, hc⟩).trans (evR_frBor hf ht')
  rw [hug _ _ _ (hsub b hb').1 (hQ b hb')] at e₂
  rw [huf _ _ _ (hsub b hb').1 (hQ b hb'), ex_add_int, chr_add] at e₃
  replace hne : rdU V f k₀ (x b) * ev _ σ _ ug (s b) ≠ 0 := hne
  refine (eq_mul_inv_iff_mul_eq₀ hne).2 ?_
  rw [e₁, e₂, e₃]
  ring

end DifferentiableLines
end
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions MonObj GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop GlobalTheory.HSApp in
theorem exists_frBor_of_matches (T : TorFlag Xo c) {A : Type} [CommRing A] (q : Sp A ⟶ T.X.YY) (k : T.X.F.J)
    (hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U k) {φ : c.F →+* A} {x : Sp A ⟶ gen T.Y} (hx : q ≫ T.X.π = x ≫ genι T.Y)
    (fr : EigFrame T.Y φ (x ≫ genι T.Y))
    (hfr : ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k q hz hx τ j)).left) (ψ : A →+* CAt σ)
    {y : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : spMap ψ ≫ q = z) (hz' : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr k z hz' Q ∧ FrBor t Q y ∧ ∀ s, t (some s) = 1 := by
  subst e
  let z' : Sp (CAt σ) ⟶ T.X.YY := spMap ψ ≫ q
  have ex : spMap ψ ≫ (x ≫ genι T.Y) = z' ≫ T.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ T.Y.j = z' ≫ T.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ T.Y.j = (GlobalTheory.AllWt.ptF y ≫ T.Y.jQ) ≫ genι T.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ ≫ (x ≫ genι T.Y) := (congrArg (· ≫ genι T.Y) hm.1).trans (Category.assoc _ _ _)
    _ = z' ≫ T.X.π := ex
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec T.Y y hxy τ j = GlobalTheory.FlagMod.frVec T.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← T.X.F.tanPull_vecAt k ψ q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := T.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := GlobalTheory.CompHS.BridgeValue.exists_gen_unit Q y eQ
  let t : Ix D → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  refine ⟨Q, t, hQ, GlobalTheory.FlagMod.frBor_of_frVec (T.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => ?_) (fun _ => hu0), fun _ => rfl⟩
  rw [hv τ j]
  refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j' j • _ = 0
    rw [Matrix.one_apply_ne hj', zero_smul]
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j j • _ = _
    rw [Matrix.one_apply_eq, one_smul]

theorem matches_of_sameLie {Z : Model Xo c (RingHom.id c.F)} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    {fr : EigFrame Z φ (x ≫ genι Z)} {ψ : A →+* ℂ} {y y' : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y)
    (h : SameLie y' y) : Matches fr ψ y' := by
  have e : GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (h.1.trans (pullback.lift_fst _ _ _).symm)
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨e ▸ hm.1, fun τ i => ?_⟩
  rw [e, h.2 τ i]
  exact hm.2 τ i

theorem chr_of_some {e : Ix D → ℤ} {t : Ix D → (CAt σ)ˣ} (h : ∀ s, t (some s) = 1) :
    chr e t = toC (t none).val ^ e none := by
  classical
  have : (∏ ix, t ix ^ e ix) = t none ^ e none := by
    rw [Fintype.prod_option, Finset.prod_eq_one fun s _ => by rw [h, one_zpow], mul_one]
  exact (congrArg (fun u : (CAt σ)ˣ => toC u.val) this).trans (@Units.val_zpow_eq_zpow_val ℂ _ (t none) (e none))

theorem tendsto_punctured {f : ℂ → ℂ} (h : Tendsto (fun w => f (eTwoPi w)) imTop (𝓝 0)) :
    Tendsto f (𝓝[≠] 0) (𝓝 0) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have t₁ : Tendsto (fun u : ℂ => Complex.log u / (2 * Real.pi * Complex.I)) (𝓝[≠] 0) imTop := by
    refine tendsto_comap_iff.2 ?_
    have h₁ : Tendsto (fun u : ℂ => ‖u‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    have h₂ := (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h₁)).atTop_div_const hπ
    refine h₂.congr fun u => ?_
    have e : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [Function.comp_apply]
    rw [e, ← div_div (Complex.log u), Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.div_ofReal_re, Complex.log_re, neg_div]
  refine (h.comp t₁).congr' (eventually_mem_nhdsWithin.mono fun u hu => ?_)
  simp only [Function.comp_apply, eTwoPi]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]


set_option maxHeartbeats 800000 in
theorem exists_eigFrame_tau (T : TorFlag Xo c) {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)]
    {φ : c.F →+* Γ(T.X.YY, W)} (hφ : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap φ) (k : T.X.F.J)
    (hz : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U k) {x' : Sp Γ(T.X.YY, W) ⟶ T.Y.X} (hx : GlobalTheory.FlagMod.tau hW ≫ T.X.π = x') :
    ∃ fr : EigFrame T.Y φ x', ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k _ hz hx τ j)).left := by
  subst hx
  let A : Type := Γ(T.X.YY, W)
  let K : Type := FractionRing A
  letI : Algebra c.F K := ((algebraMap A K).comp φ).toAlgebra
  let z : Sp K ⟶ T.X.YY := spMap (algebraMap A K) ≫ GlobalTheory.FlagMod.tau hW
  have hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X := by
    intro s _
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hs : spMap (algebraMap A K) s = η := by
      refine PrimeSpectrum.ext ?_
      let s' : PrimeSpectrum K := s
      have h0 : s'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      show Ideal.comap (algebraMap A K) s'.asIdeal = ⊥
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)
    obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen
      ⟨_, GlobalTheory.FlagMod.tau_le hW le_rfl (Set.mem_univ η)⟩
    obtain ⟨p', rfl⟩ : p ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hpW
    have hsp : η ⤳ (p' : PrimeSpectrum A) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    show GlobalTheory.FlagMod.tau hW (spMap (algebraMap A K) s) ∈ flagOpen T.X
    rw [hs]
    exact (hsp.map (GlobalTheory.FlagMod.tau hW).continuous).mem_open (flagOpen T.X).isOpen hpO
  have hr : Set.range (z ≫ T.X.π) ⊆ Set.range T.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hO (Set.mem_univ s)
  have hf := IsOpenImmersion.lift_fac T.Y.j (z ≫ T.X.π) hr
  refine GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H D l Xo c _ _ T.Y T.X A K φ rfl _ k hz
    (IsOpenImmersion.lift T.Y.j (z ≫ T.X.π) hr) ?_ hf.symm
  rw [← openImmersion_comp_structure_eq_generic T.Y, ← Category.assoc, hf, Category.assoc, Category.assoc]
  exact (congrArg (_ ≫ ·) hφ).trans (Spec.map_comp _ _).symm


end DifferentiableLines
end
end

section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.DifferentiableAtOfLines
namespace DifferentiableLines

open Metric Filter Topology Set Complex
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic

open scoped Real

theorem differentiableAt_of_lines {k : ℕ} {U O : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hO : IsOpen O) (hg : DifferentiableOn ℂ g U) (hgO : ∀ t ∈ U, g t ≠ 0 → t ∈ O)
    (hf : DifferentiableOn ℂ f O)
    (hl : ∀ τ ∈ U, τ ∉ O → ∀ v : Fin k → ℂ, (∀ᶠ z : ℂ in 𝓝[≠] 0, τ + z • v ∈ O) →
      Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] 0) (𝓝 (f τ)))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) (hne : ∀ r > 0, ∃ t ∈ ball τ₀ r, g t ≠ 0) : DifferentiableAt ℂ f τ₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU τ₀ hτ₀
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne (r / 2) (by linarith)
  set v : Fin k → ℂ := t₁ - τ₀ with hvdef
  have hv : ‖v‖ < r / 2 := by
    rw [hvdef, ← dist_eq_norm]
    exact ht₁
  have hline : ∀ τ ∈ ball τ₀ (r / 4), ∀ z : ℂ, ‖z‖ < 3 / 2 → τ + z • v ∈ U := by
    intro τ hτ z hz
    apply hrU
    rw [mem_ball, dist_eq_norm] at hτ ⊢
    have h1 : ‖τ + z • v - τ₀‖ ≤ ‖τ - τ₀‖ + ‖z‖ * ‖v‖ := by
      rw [← norm_smul]
      calc ‖τ + z • v - τ₀‖ = ‖(τ - τ₀) + z • v‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z‖ * ‖v‖ ≤ 3 / 2 * (r / 2) := mul_le_mul hz.le hv.le (norm_nonneg _) (by norm_num)
    linarith
  have hlined : ∀ (τ : Fin k → ℂ) (z : ℂ), DifferentiableAt ℂ (fun z : ℂ => τ + z • v) z := by
    intro τ z
    fun_prop
  have hga : ∀ τ ∈ ball τ₀ (r / 4), AnalyticOnNhd ℂ (fun z : ℂ => g (τ + z • v)) (ball 0 (3 / 2)) := by
    intro τ hτ
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have h1 : DifferentiableAt ℂ g (τ + z • v) :=
      hg.differentiableAt (hU.mem_nhds (hline τ hτ z (mem_ball_zero_iff.mp hz)))
    exact (h1.comp z (hlined τ z)).differentiableWithinAt
  have hiso : ∀ τ ∈ ball τ₀ (r / 4), ∀ z₁ ∈ ball (0 : ℂ) (3 / 2), g (τ + z₁ • v) ≠ 0 →
      ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), ∀ᶠ z in 𝓝[≠] z₀, g (τ + z • v) ≠ 0 := fun τ hτ z₁ hz₁ h z₀ hz₀ =>
    (hga τ hτ z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h' =>
      h ((hga τ hτ).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hz₀ h' hz₁)
  have hτ₀b : τ₀ ∈ ball τ₀ (r / 4) := mem_ball_self (by linarith)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := mem_ball_self (by norm_num)
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by
    rw [mem_ball_zero_iff]
    norm_num
  obtain ⟨ε, hε, hεφ⟩ : ∃ ε > 0, ∀ z : ℂ, dist z 0 < ε → z ≠ 0 → g (τ₀ + z • v) ≠ 0 :=
    Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp
      (hiso τ₀ hτ₀b 1 h1 (by simpa [hvdef] using hgt₁) 0 h0))
  set ρ : ℝ := min ε 1 / 2 with hρdef
  have hm : 0 < min ε 1 := lt_min hε one_pos
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε 1
    linarith
  have hρ1 : ρ < 3 / 2 := by
    have := min_le_right ε 1
    linarith
  have hO' : IsOpen (U ∩ {t | g t ≠ 0}) := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hsph₀ : ∀ z ∈ sphere (0 : ℂ) ρ, τ₀ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    intro z hz
    have hz' : ‖z‖ = ρ := mem_sphere_zero_iff_norm.mp hz
    refine ⟨hline τ₀ hτ₀b z (by linarith), hεφ z (by rw [dist_zero_right]; linarith) ?_⟩
    rintro rfl
    rw [norm_zero] at hz'
    linarith
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun z hz => ?_
    have hPc : Continuous fun p : (Fin k → ℂ) × ℂ => p.1 + p.2 • v := by fun_prop
    exact hPc.continuousAt.preimage_mem_nhds (hO'.mem_nhds (hsph₀ z hz))
  obtain ⟨δ₀, hδ₀, hδ₀K⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (r / 8) with hδdef
  have hδ : 0 < δ := by positivity
  have hδcl : closedBall τ₀ δ ⊆ ball τ₀ δ₀ := closedBall_subset_ball (by
    have := min_le_left (δ₀ / 2) (r / 8)
    linarith)
  have hδr : ball τ₀ δ ⊆ ball τ₀ (r / 4) := ball_subset_ball (by
    have := min_le_right (δ₀ / 2) (r / 8)
    linarith)
  have hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ U ∩ {t | g t ≠ 0} :=
    fun τ hτ => hδ₀K (hδcl hτ)
  have hdiff := differentiableOn_circleAverage hO hf hρ.le fun τ hτ z hz => hgO _ (hK τ hτ z hz).1 (hK τ hτ z hz).2
  refine (((hdiff.const_mul I).const_mul (2 * π * I : ℂ)⁻¹).differentiableAt (ball_mem_nhds τ₀ hδ)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds τ₀ hδ] with τ hτ
  have hτr := hδr hτ
  have hρs : (ρ : ℂ) ∈ sphere (0 : ℂ) ρ := by simp [abs_of_pos hρ]
  have hρb : (ρ : ℂ) ∈ ball (0 : ℂ) (3 / 2) := by simpa [abs_of_pos hρ] using hρ1
  have hin : ∀ z, τ + z • v ∈ O → DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z := fun z hz =>
    (hf.differentiableAt (hO.mem_nhds hz)).comp z (hlined τ z)
  have hH : ∀ z₀ ∈ ball (0 : ℂ) (3 / 2), DifferentiableAt ℂ (fun z : ℂ => f (τ + z • v)) z₀ := by
    intro z₀ hz₀
    by_cases hz : τ + z₀ • v ∈ O
    · exact hin z₀ hz
    have e₁ : ∀ᶠ z in 𝓝[≠] z₀, τ + z • v ∈ O := by
      filter_upwards [hiso τ hτr ρ hρb (hK τ (ball_subset_closedBall hτ) ρ hρs).2 z₀ hz₀,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz₀)] with z h h'
      exact hgO _ (hline τ hτr z (mem_ball_zero_iff.mp h')) h
    have t₁ : Tendsto (fun w : ℂ => z₀ + w) (𝓝[≠] 0) (𝓝[≠] z₀) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((show Continuous (fun w : ℂ => z₀ + w) by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa using hw⟩
    have t₂ : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa using ((continuous_sub_right z₀).tendsto z₀).mono_left (nhdsWithin_le_nhds (s := {z₀}ᶜ)),
        eventually_mem_nhdsWithin.mono fun w hw => by simpa [sub_eq_zero] using hw⟩
    have e₂ := hl _ (hline τ hτr z₀ (mem_ball_zero_iff.mp hz₀)) hz v
      ((t₁.eventually e₁).mono fun w hw => by rwa [add_smul, ← add_assoc] at hw)
    have e₃ : Tendsto (fun z : ℂ => f (τ + z • v)) (𝓝[≠] z₀) (𝓝 (f (τ + z₀ • v))) :=
      (e₂.comp t₂).congr fun z => by simp only [Function.comp_apply, add_assoc, ← add_smul, add_sub_cancel]
    exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt (e₁.mono hin)
      (continuousAt_iff_punctured_nhds.2 e₃)).differentiableAt
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 (3 / 2) := closedBall_subset_ball hρ1
  have hC := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := ∅) countable_empty (mem_ball_self hρ)
    (fun z hz => (hH z (hcl hz)).continuousAt.continuousWithinAt)
    (fun z hz => hH z (hcl (ball_subset_closedBall hz.1)))
  simp only [sub_zero, zero_smul, add_zero] at hC
  rw [circleIntegral_inv_smul_eq hρ.ne' (fun z => f (τ + z • v)), smul_eq_mul] at hC
  exact hC.symm

end DifferentiableLines
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

theorem frequently_ne_zero {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [Smooth p] {σ : F →+* ℂ} {W : Y.Opens}
    (hW : IsAffineOpen W) [IsDomain Γ(Y, W)] {g : Γ(Y, W)} (hg : g ≠ 0) {y : GlobalTheory.CxPts p σ} (hy : y ∈ ptsIn p σ W)
    {N : Set (GlobalTheory.CxPts p σ)} (hN : N ∈ 𝓝 y) : ∃ y' ∈ N, ev p σ W g y' ≠ 0 := by
  classical
  letI : Algebra F Γ(Y, W) := (algX p W).toAlgebra
  have hs : (algX p W).Smooth :=
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top)
  obtain ⟨ψ, ρ, hψ, h0, hσ, hne⟩ := GlobalTheory.HolArc.exists_holPts_ne_zero F Γ(Y, W) hs (evHom hy) g hg
  have ha : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ a, ψ u (algX p W a) = σ a := fun u hu a =>
    (RingHom.congr_fun (hσ u hu) a).trans ((ev_eq hy _).symm.trans (ev_algX hy a))
  let e : ℂ → GlobalTheory.CxPts p σ := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then ofHom hW (ψ u) (ha u hu) else y
  have hb := Metric.ball_mem_nhds (0 : ℂ) hψ.1
  have hev : ∀ u ∈ Metric.ball (0 : ℂ) ρ, e u ∈ ptsIn p σ W ∧ ∀ f, ev p σ W f (e u) = ψ u f := fun u hu => by
    simp only [e, dif_pos hu]
    exact ⟨ofHom_mem _ _ _, ev_ofHom _ _ _⟩
  have ht : Tendsto e (𝓝 0) (𝓝 y) := by
    refine tendsto_subtype_rng.2 (GlobalTheory.Points.tendsto_of_isAffineOpen hW hy
      (eventually_of_mem hb fun u hu => (hev u hu).1) fun f => ?_)
    have h₁ := ((hψ.2 f).differentiableAt hb).continuousAt.tendsto
    rw [h0, ← ev_eq hy] at h₁
    exact h₁.congr' (eventually_of_mem hb fun u hu => ((hev u hu).2 f).symm)
  obtain ⟨u, ⟨h₁, h₂⟩, h₃⟩ := (((ht.eventually hN).and hb).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
    |>.and eventually_mem_nhdsWithin).exists
  exact ⟨e u, h₁, by rw [(hev u h₂).2]; exact hne u h₂ h₃⟩

theorem mem_open_of_ptY (T : TorFlag Xo c) (x : FrPt Xo c (CAt σ)) (y : GlobalTheory.CxPts (flagStr T.X) σ)
    (e : T.X.ptY x = zOf y) : y ∈ ptsIn _ σ (flagOpen T.X) := by
  have : ⊤ ≤ T.X.ptY x ⁻¹ᵁ flagOpen T.X := by
    rw [← T.X.pt_inc]
    exact GlobalTheory.FlagMod.le_preimage_map T.X.inc (top_le_inc T.X) le_top
  rw [e] at this
  exact this

end DifferentiableLines
