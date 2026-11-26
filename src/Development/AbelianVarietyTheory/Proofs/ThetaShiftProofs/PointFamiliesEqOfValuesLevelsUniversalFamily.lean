module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FibrePull

section Val
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {A : Type} [CommRing A] [IsLocalRing A]

abbrev wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) : A :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, k)) (w.s (fun _ => j, k)).val

omit [IsLocalRing A] in
theorem le_div_iff (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ L'.U k :=
  ⟨fun h => ⟨fun _ hz => mem_pull.1 (h hz).1, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨mem_pull.2 (h.1 hz), h.2 hz⟩⟩

theorem exists_chart_pt (hL : L.IsLB) (x : Sp A ⟶ X) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := exists_chart hL (x (cpt A))
  exact ⟨j, (top_le_iff_cpt x _).2 hj⟩

omit [IsLocalRing A] in
theorem toStkA_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (z : Sp A) : toStkA z (wv w x j k) = (gw w x z j k).val :=
  by
    have toStkA_valR {B : Type} [CommRing B] {Z : Scheme.{0}} (f : Sp B ⟶ Z) (U : Z.Opens)
        (z : Sp B) (ht : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
        toStkA z (valR f U a.val) = (gm f z U a).val := by
      rw [FormalValue.toStkA_valR_eq_gs f U z ht, gm_val f z U (ht trivial), gs_eq f z U (ht trivial)]
    exact toStkA_valR x _ z ((le_div_iff x j k).2 ⟨hj, hk⟩) _

omit [IsLocalRing A] in
theorem isUnit_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) : IsUnit (wv w x j k) :=
  FormalValue.isUnit_valR x _ ((le_div_iff x j k).2 ⟨hj, hk⟩) _

theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp A ⟶ X') {j j' : L.ι} {k k' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k') :
    wv w x j k * valR x (L'.U k ⊓ L'.U k') (L'.g k k').val =
      valR (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w x j' k' := by
  have toStkA_valR {B : Type} [CommRing B] {Z : Scheme.{0}} (f : Sp B ⟶ Z) (U : Z.Opens)
      (z : Sp B) (ht : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
      toStkA z (valR f U a.val) = (gm f z U a).val := by
    rw [FormalValue.toStkA_valR_eq_gs f U z ht, gm_val f z U (ht trivial), gs_eq f z U (ht trivial)]
  apply toStkA_injective
  rw [map_mul, map_mul, toStkA_wv w x hj hk, toStkA_wv w x hj' hk',
    toStkA_valR x (L'.U k ⊓ L'.U k') _ (fun _ hz => ⟨hk hz, hk' hz⟩) (L'.g k k'),
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U j') _ (fun _ hz => ⟨hj hz, hj' hz⟩) (L.g j j'),
    (isGen_iff w).1 hw _ x (cpt A) j j' k k' (hj trivial) (hj' trivial) (hk trivial) (hk' trivial),
    ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

theorem valR_g_self (hL : L.IsLB) (x : Sp A ⟶ X) {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  have toStkA_valR {B : Type} [CommRing B] {Z : Scheme.{0}} (f : Sp B ⟶ Z) (U : Z.Opens)
      (z : Sp B) (ht : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
      toStkA z (valR f U a.val) = (gm f z U a).val := by
    rw [FormalValue.toStkA_valR_eq_gs f U z ht, gm_val f z U (ht trivial), gs_eq f z U (ht trivial)]
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩) (L.g j j), gm_self hL x _ (hj trivial), map_one, Units.val_one]

theorem exists_frm {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (x : Sp A ⟶ X')
    (τ : L.ι → A) (hτ : IsFrm L (x ≫ F) τ) : ∃ τ' : L'.ι → A, IsFrm L' x τ' ∧
      ∀ j k, ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j = wv w x j k * τ' k := by
  obtain ⟨j₀, h₀⟩ := exists_chart_pt hL (x ≫ F)
  have key : ∀ k, ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j₀ = wv w x j₀ k * (Ring.inverse (wv w x j₀ k) * τ j₀) := fun k hk => by
    rw [Ring.mul_inverse_cancel_left _ _ (isUnit_wv w x h₀ hk)]
  refine ⟨fun k => Ring.inverse (wv w x j₀ k) * τ j₀, ⟨fun k hk => ?_, fun k k' hkk => ?_⟩, fun j k hj hk => ?_⟩
  · exact (isUnit_ringInverse.2 (isUnit_wv w x h₀ hk)).mul (hτ.1 _ h₀)
  · have hk : ⊤ ≤ x ⁻¹ᵁ L'.U k := fun _ hz => (hkk hz).1
    have hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k' := fun _ hz => (hkk hz).2
    refine (isUnit_wv w x h₀ hk).mul_left_cancel ?_
    rw [← key k hk, ← _root_.mul_assoc, wv_trans hw x h₀ h₀ hk hk', valR_g_self hL _ h₀, _root_.one_mul, ← key k' hk']
  · have e := wv_trans hw x hj h₀ hk hk
    rw [valR_g_self hL' _ hk, _root_.mul_one] at e
    rw [e, _root_.mul_assoc, ← key k hk]
    exact hτ.2 j j₀ (fun _ hz => ⟨hj hz, h₀ hz⟩)

variable {w : LB.Iso L' (L.pull F)} {p' : Y' ⟶ X'} {p : Y ⟶ X} {h : Y' ⟶ Y} {n : ℕ}

abbrev TransportedAlt (w : LB.Iso L' (L.pull F)) (a : SecP L' p' n) (t : SecP L p n) (h : Y' ⟶ Y) : Prop :=
  ConstFam.SecThrough w (K := Fin 1) (fun _ => p') (fun _ => p) (fun _ => (n : ℤ)) a t h

theorem TransportedAlt.sval_eq (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h) (r : Sp A ⟶ Y')
    {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k) :
    ArcPts.sval t (r ≫ h) j = wv w (r ≫ p') j k ^ n * ArcPts.sval a r k := by
  have hj' : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j := by rwa [Category.assoc, ← hp, ← Category.assoc]
  apply toStkA_injective
  have e := H _ r (cpt A) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at e
  rw [map_mul, map_pow, toStkA_wv w _ hj hk]
  exact (FormalValue.toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) _
    (fun _ hz => Set.mem_iInter.2 fun _ => hj' hz) _).trans (e.trans (congrArg _
      (FormalValue.toStkA_valR_eq_gs r (LB.wchart L' (fun _ : Fin 1 => p') (fun _ => k)) _
        (fun _ hz => Set.mem_iInter.2 fun _ => hk hz) _).symm))

theorem TransportedAlt.hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n}
    (H : TransportedAlt w a t h) (r : Sp A ⟶ Y') {τ : L.ι → A} {τ' : L'.ι → A}
    (hτ : ∀ j k, ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k → τ j = wv w (r ≫ p') j k * τ' k) (c : A) :
    HasVal a r τ' c ↔ HasVal t (r ≫ h) τ c := by
  have e : (r ≫ h) ≫ p = (r ≫ p') ≫ F := by rw [Category.assoc, ← hp, ← Category.assoc]
  constructor
  · intro Ha j hj
    rw [e] at hj
    obtain ⟨k, hk⟩ := exists_chart_pt hL' (r ≫ p')
    rw [H.sval_eq hp r hj hk, Ha k hk, hτ j k hj hk]
    ring
  · intro Ht k hk
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((r ≫ p') ≫ F)
    refine ((isUnit_wv w _ hj hk).pow n).mul_left_cancel ?_
    rw [← H.sval_eq hp r hj hk, Ht j (by rwa [e]), hτ j k hj hk]
    ring

theorem TransportedAlt.eq_zero (hL : L.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h)
    (ht : ∀ i, t.f i = 0) (i) : a.f i = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (p' y))
  have e := H _ (𝟙 _) y (fun _ => j) i (fun _ => hj) (fun k => Set.mem_iInter.1 hy k)
  have hm : (𝟙 Y' ≫ h) y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := Set.mem_iInter.2 fun _ => by
    show (h ≫ p) y ∈ L.U j
    rw [← hp]; exact hj
  have z₁ : gs (𝟙 Y' ≫ h) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (t.f fun _ => j) = 0 := by
    refine (congrArg (gs _ _ _) (ht fun _ => j)).trans ((gs_eq _ _ _ hm _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [z₁] at e
  refine ((Units.mul_right_eq_zero _).1 e.symm).trans ?_
  exact ((gs_eq _ _ _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem exists_thr_up (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) [IsIso h] (hp : p' ≫ F = h ≫ p)
    (a : SecP L' p' n) : ∃ t : SecP L p n, TransportedAlt w a t h := by
  obtain ⟨t₀, h₀⟩ := ConstFam.exists_sec_up ((isGen_iff w).1 hw) hL hL' a
  obtain rfl : p = inv h ≫ p' ≫ F := by rw [hp, IsIso.inv_hom_id_assoc]
  refine ⟨DVR.pullSec L (fun _ => p' ≫ F) _ t₀ (inv h), fun Z r z P Q hP hQ => ?_⟩
  have e : (r ≫ h) ≫ inv h = r := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm : (r ≫ h) z ∈ LB.wchart L (fun _ : Fin 1 => inv h ≫ p' ≫ F) P := Set.mem_iInter.2 fun k => by
    show ((r ≫ h) ≫ inv h ≫ p' ≫ F) z ∈ L.U (P k)
    rw [← Category.assoc, e]; exact hP k
  refine ((gs_res (r ≫ h) z _ hm _).trans
    (gs_pull (r ≫ h) (inv h) z _ (Out.wchart_comp_le L (fun _ => p' ≫ F) (inv h) P hm) _)).trans ?_
  rw [e]
  exact h₀ Z r z P Q (Set.mem_iInter.2 hP) (Set.mem_iInter.2 hQ)

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]


omit [StarRing (𝓞 E)] in
theorem exists_fpts {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : IsRigIso m.cm t'.PP t.PP w) {F : Type} [Field F] {V : Type}
    [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S') (y : Sp F ⟶ S)
    (hy : y' ≫ f = y) (Θ : FPts act t y φ) : ∃ Θ' : FPts act t' y' φ,
      (∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧
      ∀ k ψ (p : Over.mk y ⟶ t.G) (p' : Over.mk y' ⟶ t'.G), p'.left ≫ m.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  subst hy
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have inj : Function.Injective ρ := fun a b e => Over.OverMorphism.ext (m.cart.1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective ρ := fun b =>
    ⟨Over.homMk (m.cart.1.lift b.left y' (Over.w b)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  choose x hx using fun v => surj (Θ.x v)
  have hxl : ∀ v, (x v).left ≫ m.φ = (Θ.x v).left := fun v => congrArg (fun q => q.left) (hx v)
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have f₁ : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ pullback.fst t'.G.hom y' = a.left := fun a => pullback.lift_fst _ _ _
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, f₁]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  choose τ hτ hτw using fun v => exists_frm hw.1 hL hL' (x v).left (Θ.τ v) (by rw [hxl]; exact Θ.frm v)
  choose sig hsig using fun j i => ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
    hw.1 hL hL' (fun _ => hp) (Θ.sig j i)
  have hv : ∀ {n : ℕ} {a : SecP t'.PP.L (pullback.fst t'.G.hom y') n} {b : SecP t.PP.L (pullback.fst t.G.hom (y' ≫ f)) n},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (x v)) (τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by rw [f₁]; exact hτw v) c
  have add : ∀ v v', x (v + v') = x v * x v' := fun v v' => inj (by rw [map_mul, hx, hx, hx, Θ.add])
  have x0 : (x 0).left = y' ≫ eSec t'.G := by
    have : x 0 = 1 := by
      have e := add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    rw [this]
    show (toUnit _ ≫ η[t'.G]).left = _
    simp [eSec]
  refine ⟨⟨x, add, fun e v => inj ?_, τ, hτ, fun k hk => ?_, sig, fun n hn i v => (hv (hsig n i) v _).2 (Θ.val n hn i v),
    fun n hn s => ?_, fun n hn s hs => ?_⟩, fun v => ⟨hxl v, fun j k hjk => ?_⟩, fun k ψ p p' hpp ⟨l₁, l₂, l₃⟩ => ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [hx, Θ.lin, ρl, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hxl]
  · obtain ⟨j, hj⟩ := exists_chart_pt hL ((x 0).left ≫ m.φ)
    refine (isUnit_wv w _ hj hk).mul_left_cancel ?_
    rw [← hτw 0 j k hj hk, Θ.rig j (by rw [← hxl]; exact hj)]
    have P := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
      (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
    rw [x0] at hj hk ⊢
    have e := P _ y' (cpt F) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
    rw [Fintype.prod_unique, zpow_one, m.base] at e
    have hj' : ⊤ ≤ ((y' ≫ f) ≫ eSec t.G) ⁻¹ᵁ t.PP.L.U j := by
      have := m.cm.e_comm
      rw [m.base] at this
      rw [Category.assoc, ← this, ← Category.assoc]; exact hj
    have toStkA_valR {B : Type} [CommRing B] {Z : Scheme.{0}} (f : Sp B ⟶ Z) (U : Z.Opens)
        (z : Sp B) (ht : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
        toStkA z (valR f U a.val) = (gm f z U a).val := by
      rw [FormalValue.toStkA_valR_eq_gs f U z ht, gm_val f z U (ht trivial), gs_eq f z U (ht trivial)]
    apply toStkA_injective
    rw [map_mul, toStkA_wv w _ hj hk]
    refine (toStkA_valR (y' ≫ f) _ _ (fun _ hz => mem_pull.2 (hj' hz)) _).trans ((congrArg Units.val e).trans ?_)
    rw [Units.val_mul]
    exact congrArg _ (toStkA_valR y' _ _ (fun _ hz => mem_pull.2 (hk hz)) _).symm
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    obtain ⟨N, r, i, hi⟩ := Θ.span n hn b
    exact ⟨N, r, i, fun v => (hv hb v _).2 (hi v)⟩
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    exact hb.eq_zero hL hp (Θ.sep n hn b fun v => (hv hb v _).1 (hs v))
  · exact hτw v j k ((le_div_iff _ j k).1 hjk).1 ((le_div_iff _ j k).1 hjk).2
  · obtain rfl : ρ p' = p := Over.OverMorphism.ext hpp
    refine ⟨inj (by rw [map_pow, l₁, map_one]), l₂, fun i i' z j' hj' => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((x z * p').left ≫ m.φ)
    have e := l₃ i i' z j (by rw [← hx, ← map_mul]; exact hj)
    have hj₁ : ⊤ ≤ ((fib (x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ t.PP.L.U j := by rw [f₁]; exact hj
    have hj₂ : ⊤ ≤ (fib (x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [f₁]; exact hj'
    rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp (hsig k i) _ hj₁ hj₂, TransportedAlt.sval_eq hp (hsig k i') _ hj₁ hj₂,
      _root_.mul_assoc, _root_.mul_assoc] at e
    exact ((isUnit_wv w _ hj₁ hj₂).pow k).mul_left_cancel e

theorem exists_fpts_pull : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l bb s) (y : Sp F ⟶ S) (s' : Sp F ⟶ Sp B) (Θ : FPts act o.t y φ), y ≫ s = s' → ∃ (o' : Obj D l bb s') (m : ObjMap o' o y) (w : LB.Iso o'.t.PP.L (o.t.PP.L.pull m.toSABMap.φ)) (Θ' : FPts act o'.t (𝟙 _) φ), IsRigIso m.toSABMap.cm o'.t.PP o.t.PP w ∧ (∀ v, (Θ'.x v).left ≫ m.toSABMap.φ = (Θ.x v).left ∧ ∀ j j', ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.toSABMap.φ) o'.t.PP.L).U (fun _ => j, j') → Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧ ∀ k ψ (p : Over.mk y ⟶ o.t.G) (p' : Over.mk (𝟙 (Sp F)) ⟶ o'.t.G), 1 ≤ k → p'.left ≫ m.toSABMap.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  intro _ _ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ S s o y s' Θ hy
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l B B bb bb (RingHom.id B) S (Sp F) s s' y rfl rfl (by
    rw [hy]; exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) o
  obtain ⟨w, h₁, h₂, -⟩ := m.toSABMap.lin
  obtain ⟨Θ', r₁, r₂⟩ := exists_fpts m.toSABMap w ⟨h₁, h₂⟩ (𝟙 _) y (Category.id_comp _) Θ
  exact ⟨o', m, w, Θ', ⟨h₁, h₂⟩, r₁, fun k ψ p p' _ => r₂ k ψ p p'⟩

end GlobalTheory.FibrePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPoints
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelRespect

open GlobalTheory.FibrePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

theorem valR_zero {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem sval_of_zero {A : Type} [CommRing A] {X Z : Scheme.{0}} {L : LB Z} {π : X ⟶ Z} {n : ℕ} (u : SecP L π n)
    (hu : ∀ i, u.f i = 0) (x : Sp A ⟶ X) (j : L.ι) : ArcPts.sval u x j = 0 :=
  (congrArg (valR x _) (hu fun _ => j)).trans (valR_zero _ _)

section One
variable {S : Scheme.{0}} {t : SAB H S} {F : Type} [Field F] {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V}
  {I : ℕ → Type} {φ : ∀ j, I j → V → F} {y : Sp F ⟶ S}

omit [StarRing (𝓞 E)] in
theorem fib_fst (a : Over.mk y ⟶ t.G) : fib a ≫ pullback.fst t.G.hom y = a.left := pullback.lift_fst _ _ _


omit [StarRing (𝓞 E)] in
theorem sval_eq_sum (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι) (hj : ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib q) j = ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j := by
  have key : ∀ (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι), ⊤ ≤ (fib q ≫ pullback.fst t.G.hom y) ⁻¹ᵁ t.PP.L.U j →
      ArcPts.sval (FibreFrame.comb (pullback.snd t.G.hom y) (Fin.cons (-1) r : Fin (n + 1) → F)
        (Fin.cons s fun a => Θ.sig k (i a)) : SecP t.PP.L (pullback.fst t.G.hom y) k) (fib q) j =
      ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j - ArcPts.sval s (fib q) j := fun q j hj => by
    rw [FibreFrame.sval_comb _ _ _ (RingHom.id F) (fib q)
      ((pullback.lift_snd _ _ _).trans (Spec.map_id _).symm) hj, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, RingHom.id_apply]
    ring
  have h0 := Θ.sep k hk _ fun v j hj => by
    rw [key _ j hj, hs v j hj, Finset.sum_mul, MulZeroClass.zero_mul, sub_eq_zero]
    exact Finset.sum_congr rfl fun a _ => by rw [Θ.val k hk (i a) v j hj, _root_.mul_assoc]
  have e := key q j (by rw [fib_fst]; exact hj)
  rw [sval_of_zero _ h0] at e
  exact (sub_eq_zero.1 e.symm).symm


omit [StarRing (𝓞 E)] in
theorem sval_lev (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) {p : Over.mk y ⟶ t.G} {ψ : I k → V → F}
    (hp : Θ.Lev k p ψ) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (i₀ : I k) (z : V) (j : t.PP.L.ι) (hj : ⊤ ≤ (Θ.x z * p).left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib (Θ.x z * p)) j * ψ i₀ z =
      ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j * ∑ a, r a * ψ (i a) z := by
  rw [sval_eq_sum Θ hk s r i hs _ j hj, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [_root_.mul_assoc, hp.2.2 (i a) i₀ z j hj]; ring

end One

theorem level_eq (h₁ : Out.Laws) (h₂ : Out.Laws2) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l bb s) {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' o.t f)
    (w : LB.Iso t'.PP.L (o.t.PP.L.pull m.φ)) (hw : w.IsGen) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S')
    (y : Sp F ⟶ S) (hy : y' ≫ f = y) (Θ' : FPts act t' y' φ) (Θ : FPts act o.t y φ) {k : ℕ} (hk : 1 ≤ k)
    {ψ : I k → V → F} {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ o.t.G}
    (rel : ∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j')
    (l' : Θ'.Lev k p' ψ) (l₀ : Θ.Lev k p ψ) : p'.left ≫ m.φ = p.left := by
  subst hy
  have hL := o.t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ o.t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have hx : ∀ v, ρ (Θ'.x v) = Θ.x v := fun v => Over.OverMorphism.ext (rel v).1
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') o.t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback o.t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst o.t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, fib_fst]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  have hv : ∀ {a : SecP t'.PP.L (pullback.fst t'.G.hom y') k} {b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (Θ'.x v)) (Θ'.τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by
      rw [fib_fst]; exact fun j j' hj hj' => (rel v).2 j j' ((le_div_iff _ j j').2 ⟨hj, hj'⟩)) c
  obtain ⟨-, i₀, i₁, hgood, z₀, hz₀⟩ := l₀.2.1
  have main := LevelUnique.torsion_eq_of_same_ratios h₁ h₂ E H D l B bb S s o F (y' ≫ f) V Θ.x k (ρ p') p
    (fun z => ψ i₀ z ≠ 0) (Θ.sig k i₁) hk (by rw [← map_pow, l'.1, map_one]) l₀.1
    (fun n hn u hu => Θ.sep n hn u fun v j hj => by
      rw [MulZeroClass.zero_mul]; exact hu v j (by rwa [fib_fst] at hj))
    (by
      by_contra hne
      push_neg at hne
      obtain ⟨j, hj⟩ := exists_chart_pt hL (Θ.x z₀).left
      have e := Θ.val k hk i₁ z₀ j (by rw [fib_fst]; exact hj)
      rw [sval_of_zero _ hne] at e
      exact mul_ne_zero hz₀ (pow_ne_zero _ ((Θ.frm z₀).1 j hj).ne_zero) e.symm)
    (fun v j hj hne => hgood v fun h0 => hne (by
      rw [Θ.val k hk i₁ v j (by rw [fib_fst]; exact hj), h0, MulZeroClass.zero_mul]))
    (fun z hz t₁ t₂ j j₂ hj hj₂ => by
      obtain ⟨j', hj'⟩ := exists_chart_pt hL' (Θ'.x z * p').left
      have hj₁ : ⊤ ≤ ((fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ o.t.PP.L.U j := by
        rw [fib_fst, ← ρl, map_mul, hx]; exact hj
      have hj₃ : ⊤ ≤ (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [fib_fst]; exact hj'
      have both : ∀ b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k, ∃ c : F,
          ArcPts.sval b (fib (Θ.x z * ρ p')) j * ψ i₀ z =
            wv w (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') j j' ^ k *
              ArcPts.sval (Θ'.sig k i₀) (fib (Θ'.x z * p')) j' * c ∧
          ArcPts.sval b (fib (Θ.x z * p)) j₂ * ψ i₀ z = ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j₂ * c := fun b => by
        obtain ⟨n, r, i, hi⟩ := Θ.span k hk b
        obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
          hw hL hL' (fun _ => hp) b
        refine ⟨∑ a, r a * ψ (i a) z, ?_, sval_lev Θ hk l₀ b r i hi i₀ z j₂ hj₂⟩
        rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp ha _ hj₁ hj₃, _root_.mul_assoc,
          sval_lev Θ' hk l' a r i (fun v => (hv ha v _).2 (hi v)) i₀ z j' hj', _root_.mul_assoc]
      obtain ⟨c₁, a₁, b₁⟩ := both t₁
      obtain ⟨c₂, a₂, b₂⟩ := both t₂
      refine mul_right_cancel₀ (mul_ne_zero hz hz) ?_
      rw [_root_.mul_mul_mul_comm, a₁, b₂, _root_.mul_mul_mul_comm (ArcPts.sval t₂ _ j), a₂, b₁]
      ring)
  exact congrArg (fun q => q.left) main

theorem level_pt_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  intro h₁ h₂ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂ m w k ψ p₁ p₂ hk hw rel l₁ l₂
  exact level_eq h₁ h₂ o₂ m w hw (𝟙 _) (𝟙 _) (Category.id_comp _) Θ₁ Θ₂ hk rel l₁ l₂

end GlobalTheory.LevelRespect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_iso_respects_level_ratio_points : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  first | exact @GlobalTheory.LevelRespect.level_pt_eq | exact GlobalTheory.LevelRespect.level_pt_eq | (intros; apply GlobalTheory.LevelRespect.level_pt_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValues
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValues
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyIso

open GlobalTheory.MatchCoord GlobalTheory.AmpleSpan

section General

variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X}

def pullP {p : Y ⟶ X} {p' : Y' ⟶ X} (h : Y' ⟶ Y) (e : p' = h ≫ p) {m : ℕ} (σ : SecP L p m) : SecP L p' m :=
  chartSec (chartPullSame L _ _ _ h fun _ => e) σ

theorem hasVal_pullP {p : Y ⟶ X} {p' : Y' ⟶ X} (h : Y' ⟶ Y) (e : p' = h ≫ p) {m : ℕ} (σ : SecP L p m)
    (x : Sp F ⟶ Y') (τ : L.ι → F) (c : F) : HasVal (pullP h e σ) x τ c ↔ HasVal σ (x ≫ h) τ c := by
  subst e
  unfold HasVal
  rw [Category.assoc]
  refine forall_congr' fun j => forall_congr' fun hj => Eq.congr_left ?_
  have hm : x (pt F) ∈ LB.wchart L (fun _ : Fin 1 => h ≫ p) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (show (h ≫ p) (x (pt F)) ∈ L.U j from mem_of_le hj)
  exact valF_appLE h _ _ (le_of_mem hm) _

theorem hasVal_id {m : ℕ} (s : Out.H0 L m) (x : Sp F ⟶ X) (τ : L.ι → F) (c : F) :
    HasVal (p := 𝟙 X) s x τ c ↔ HasValueAt s x τ c := by
  unfold HasVal
  rw [Category.comp_id]
  rfl

theorem isFrameAt_of_isFrm {x : Sp F ⟶ X} {τ : L.ι → F} (h : IsFrm L x τ) : IsFrameAt L x τ :=
  ⟨fun a ha => (h.1 a ha).ne_zero, fun a b ha hb => h.2 a b (le_of_mem ⟨mem_of_le ha, mem_of_le hb⟩)⟩

theorem inSpan_of_comp {f : X ⟶ Y} {H : LB X} {I K : Type} [Fintype I] [Fintype K] (t : K → LB.Sec H) (e : I → K)
    {s : LB.Sec H} (h : InSpan f (fun a => t (e a)) s) : InSpan f t s := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨fun l => ∑ a, if e a = l then c a else 0, fun k => (hc k).trans ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (e a) (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul]) (by simp),
    if_pos rfl]

theorem valF_const (c : F) : valF (𝟙 (Sp F)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = c := by
  rw [valF_eq le_rfl]
  simp [valHom, Scheme.Hom.appLE]

variable {J : Type} {x : J → (Sp F ⟶ X)} {τ : J → L.ι → F}

theorem inSpan_of_values [IsReduced X] (hx : MeetsOpens x) (f : X ⟶ Sp F) (hf : ∀ j, x j ≫ f = 𝟙 _) {N n : ℕ}
    (t : Fin n → Out.H0 L N) (φ : Fin n → J → F) (ht : ∀ a j, HasValueAt (t a) (x j) (τ j) (φ a j)) (r : Fin n → F)
    (u : Out.H0 L N) (hu : ∀ j, HasValueAt u (x j) (τ j) (∑ a, r a * φ a j)) : InSpan f t u := by
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r a), fun k => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = fun _ => b := ⟨k 0, funext fun i => congrArg k (Subsingleton.elim _ _)⟩
  refine hx.fn_ext (U := chart L b) fun j hj => ?_
  have hb : ⊤ ≤ x j ⁻¹ᵁ L.U b := le_of_mem (Set.mem_iInter.1 (mem_of_le hj) 0)
  refine (hu j b hb).trans (Eq.trans ?_ ((valF_eq hj _).trans (map_sum _ _ _)).symm)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Eq.symm (((valF_eq hj _).symm.trans (valF_mul hj _ _)).trans ?_)
  rw [_root_.mul_assoc]
  exact congrArg₂ (· * ·) ((valF_appLE f ⊤ le_top hj _).trans (by rw [hf]; exact valF_const _)) (ht a j b hb)

theorem embedsBy_of_values [IsReduced X] (hx : MeetsOpens x) (f : X ⟶ Sp F) [UniversallyClosed f]
    (hf : ∀ j, x j ≫ f = 𝟙 _) {N : ℕ} {K I : Type} [Fintype K] {s : K → Out.H0 L N} (hs : EmbedsBy f s)
    (t : I → Out.H0 L N) (φ : I → J → F) (ht : ∀ a j, HasValueAt (t a) (x j) (τ j) (φ a j))
    (hu : ∀ u : Out.H0 L N, ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I),
      ∀ j, HasValueAt u (x j) (τ j) (∑ a, r a * φ (i a) j)) : EmbedsBy f t := by
  choose n r i hu using hu
  let e : (Σ k, Fin (n (s k))) → I := fun p => i _ p.2
  have hst : ∀ k, InSpan f (fun p => t (e p)) (s k) := fun k => inSpan_of_comp _ (Sigma.mk k)
    (inSpan_of_values hx f hf _ (fun a => φ (i _ a)) (fun a => ht _) _ _ (hu _))
  refine ⟨top_le_iff.1 ((iSup_nonzeroLocus_of_inSpan hs.1 hst).ge.trans
    (iSup_le fun p => le_iSup (fun l => Out.nonzeroLocus (t l)) (e p))), fun l => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs.affine_and_surjective hst (t l)
  choose q hq using fun a => exists_isRatio (t a) (t l)
  refine ⟨h₁, q, hq, fun y => ?_⟩
  obtain ⟨P, rfl⟩ := h₂ (fun p => q (e p)) (fun p => hq _) y
  exact ⟨MvPolynomial.rename e P, MvPolynomial.eval₂Hom_rename _ _ _ _⟩

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {F : Type} [Field F]
  {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F}

section Triple

variable {t : SAB H (Sp F)} (Θ : FPts act t (𝟙 _) φ)

theorem fib_fst (v : V) : fib (Θ.x v) ≫ pullback.fst t.G.hom (𝟙 _) = (Θ.x v).left := pullback.lift_fst _ _ _

theorem x_zero : Θ.x 0 = 1 := mul_eq_left.1 ((Θ.add 0 0).symm.trans (congrArg Θ.x (add_zero 0)))

theorem x_zero_left : (Θ.x 0).left = eSec t.G := by
  rw [x_zero, Hom.one_def, Over.comp_left]
  exact (congrArg (· ≫ _) ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (𝟙 (Sp F))))))).trans
    (Category.id_comp _)

theorem separates : SeparatesSections t.PP.L fun v => (Θ.x v).left := by
  intro m hm u hu a
  have e : pullback.fst t.G.hom (𝟙 _) = pullback.fst t.G.hom (𝟙 _) ≫ 𝟙 _ := (Category.comp_id _).symm
  have h0 := Θ.sep m hm (pullP _ e u) (fun v => (hasVal_pullP _ e u _ _ _).2 (by
    rw [fib_fst, hasVal_id]
    exact fun b hb => (hu v _ (top_le_chart hb)).trans (zero_mul _).symm)) a
  refine fn_ext fun y hy => ?_
  have hz : inv (pullback.fst t.G.hom (𝟙 _)) y ∈
      LB.wchart t.PP.L (fun _ : Fin 1 => pullback.fst t.G.hom (𝟙 _)) a := Set.mem_iInter.2 fun k => by
    show (inv (pullback.fst t.G.hom (𝟙 _)) ≫ pullback.fst t.G.hom (𝟙 _)) y ∈ t.PP.L.U (a k)
    rw [IsIso.inv_hom_id]
    exact Set.mem_iInter.1 hy k
  have := gs_chartSec (chartPullSame t.PP.L _ _ _ _ fun _ => e) u (inv (pullback.fst t.G.hom (𝟙 _))) y a hz
  rw [IsIso.inv_hom_id] at this
  refine this.symm.trans ((congrArg (gs _ y _) h0).trans ?_)
  exact ((gs_eq _ y _ hz _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).trans
    ((gs_eq (𝟙 _) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem exists_sections {N : ℕ} (hN : 1 ≤ N) : ∃ s : I N → Out.H0 t.PP.L N,
    (∀ i v, HasValueAt (s i) (Θ.x v).left (Θ.τ v) (φ N i v)) ∧
    ∀ u : Out.H0 t.PP.L N, ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I N),
      ∀ v, HasValueAt u (Θ.x v).left (Θ.τ v) (∑ a, r a * φ N (i a) v) := by
  refine ⟨fun i => pullP (inv (pullback.fst t.G.hom (𝟙 _))) (IsIso.inv_hom_id _).symm (Θ.sig N i),
    fun i v => ?_, fun u => ?_⟩
  · rw [← hasVal_id, hasVal_pullP, ← fib_fst, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact Θ.val N hN i v
  · obtain ⟨n, r, i, h⟩ := Θ.span N hN (pullP _ (Category.comp_id _).symm u)
    refine ⟨n, r, i, fun v => ?_⟩
    have := (hasVal_pullP _ _ _ _ _ _).1 (h v)
    rwa [fib_fst, hasVal_id] at this

end Triple

variable {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B} {s : Sp F ⟶ Sp B}

theorem exists_embedding (hA : Out.AmpleSt) (o : Obj D l bb s) (Θ : FPts act o.t (𝟙 _) φ) {N : ℕ} (hN : 4 ≤ N) :
    ∃ t : I N → Out.H0 o.t.PP.L N, EmbedsBy o.t.G.hom t ∧
      ∀ i v, HasValueAt (t i) (Θ.x v).left (Θ.τ v) (φ N i v) := by
  obtain ⟨t, ht, hu⟩ := exists_sections Θ (N := N) (by omega)
  have := o.proper
  have : IsIntegral o.t.G.left := isIntegral_left_of_isAbelianScheme_field _ (objPolAV o).isAb
  obtain ⟨M, u, hs⟩ := exists_embedsBy_of_isPullback o.t.G o.t.PP.isLB (hA _ (objPolAV o) N hN).2
    (isAffineOpen_top _) (φ := 𝟙 _) (f' := o.t.G.hom) (g := 𝟙 _ ≫ (Sp F).topIso.inv)
    (by rw [comp_topIso_inv_ι]; exact IsPullback.of_id_fst) (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  exact ⟨t, embedsBy_of_values (X := o.t.G.left) (meetsOpens_of_separatesSections (objPolAV o) (separates Θ)) o.t.G.hom
    (fun v => Over.w (Θ.x v)) hs t _ ht hu, ht⟩

theorem isRigIso_of_value {G G' : Over (Sp F)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (β : G ⟶ G') [IsMonHom β] (L : RigLB G) (L' : RigLB G') (w : LB.Iso L.L (L'.L.pull β.left)) (hw : w.IsGen)
    (h : ∀ a a', ⊤ ≤ (show Sp F ⟶ _ from eSec G) ⁻¹ᵁ L.L.U a → ⊤ ≤ (show Sp F ⟶ _ from eSec G') ⁻¹ᵁ L'.L.U a' →
      valF (F := F) (eSec G) _ (w.s (fun _ => a', a)).val * valF (𝟙 (Sp F)) _ (L.rig.s fun _ => a).val =
        valF (𝟙 (Sp F)) _ (L'.rig.s fun _ => a').val) : IsRigIso (CubeMap.ofHom β) L L' w := by
  have he : eSec G ≫ β.left = 𝟙 _ ≫ eSec G' := (CubeMap.ofHom β).e_comm
  refine ⟨hw, maps_of_good ((isGen_iff w).1 hw) L'.isLB L.isLB (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G') (ε := fun _ => 1) L.rig L.rigGen L'.rig L'.rigGen (fun _ => he) fun y J J' hJ hJ' => ?_⟩
  have m := hJ (eSec G ≫ β.left)
  have m' := hJ' (eSec G)
  have m₀ : eSec G' y ∈ L'.L.U (J (eSec G ≫ β.left)) := by
    have := hJ (𝟙 _ ≫ eSec G')
    rw [he]; exact this
  have e := congrArg (toStk (F := F) y) (h _ _ ((top_le_iff_mem (F := F) _ _ y).2 m')
    ((top_le_iff_mem (F := F) _ _ y).2 m₀))
  rw [val_of _ _ y J (fun _ => J (eSec G ≫ β.left)) (fun _ => congrArg J he.symm),
    val_of _ _ y J' (fun _ => J' (eSec G)) (fun _ => congrArg J' (Category.id_comp _)), Fintype.prod_unique, zpow_one]
  refine Units.ext ((toStk_valF (F := F) (𝟙 _) _ y (mem_pull.2 m₀) _).symm.trans (e.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (toStk_valF (F := F) (𝟙 _) _ y (mem_pull.2 m') _)))))
  exact toStk_valF (F := F) (eSec G) ((L'.L.pull β.left).U (fun _ => J (eSec G ≫ β.left)) ⊓ L.L.U (J' (eSec G))) y
    ⟨mem_pull.2 m, m'⟩ _

theorem exists_sabMap_of_same_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ), ∃ (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)), IsRigIso m.cm o₁.t.PP o₂.t.PP w ∧ ∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j' := by
  intro hL _ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂
  obtain ⟨s₁, e₁, v₁⟩ := exists_embedding hL.ample o₁ Θ₁ (N := 4) le_rfl
  obtain ⟨s₂, e₂, v₂⟩ := exists_embedding hL.ample o₂ Θ₂ (N := 4) le_rfl
  obtain ⟨t₁, e₁', v₁'⟩ := exists_embedding hL.ample o₁ Θ₁ (N := 5) (by norm_num)
  obtain ⟨t₂, e₂', v₂'⟩ := exists_embedding hL.ample o₂ Θ₂ (N := 5) (by norm_num)
  have f₁ := fun v => isFrameAt_of_isFrm (Θ₁.frm v)
  have f₂ := fun v => isFrameAt_of_isFrm (Θ₂.frm v)
  have d₁ := separates Θ₁
  have d₂ := separates Θ₂
  obtain ⟨β, hβ⟩ : ∃ β : o₁.t.G ⟶ o₂.t.G, ∀ v, Θ₁.x v ≫ β = Θ₂.x v :=
    exists_over_hom (P := objPolAV o₁) (P' := objPolAV o₂) f₁ f₂ s₁ s₂ e₁ e₂ (fun i v => ⟨_, v₁ i v, v₂ i v⟩) d₁
  obtain ⟨δ, hδ⟩ : ∃ δ : o₂.t.G ⟶ o₁.t.G, ∀ v, Θ₂.x v ≫ δ = Θ₁.x v :=
    exists_over_hom (P := objPolAV o₂) (P' := objPolAV o₁) f₂ f₁ s₂ s₁ e₂ e₁ (fun i v => ⟨_, v₂ i v, v₁ i v⟩) d₂
  have ext : ∀ (o o' : Obj D l bb s) (Θ : FPts act o.t (𝟙 _) φ) (f g : o.t.G ⟶ o'.t.G),
      (∀ v, Θ.x v ≫ f = Θ.x v ≫ g) → f = g := fun o o' Θ f g h =>
    hom_ext_of_separatesSections (objPolAV o) (objPolAV o') (separates Θ) h
  let ψ : o₁.t.G ≅ o₂.t.G := ⟨β, δ,
    ext _ _ Θ₁ _ _ fun v => by rw [← Category.assoc, hβ, hδ, Category.comp_id],
    ext _ _ Θ₂ _ _ fun v => by rw [← Category.assoc, hδ, hβ, Category.comp_id]⟩
  have hm : IsMonHom β := hL.rigidity _ _ _ (objPolAV o₁).isAb (objPolAV o₂).isAb β (by
    have e : (Θ₁.x 0).left ≫ β.left = (Θ₂.x 0).left := congrArg CommaMorphism.left (hβ 0)
    rw [x_zero_left, x_zero_left] at e
    exact Over.OverMorphism.ext e)
  have : IsMonHom ψ.hom := hm
  have a₁ : IsAbelianScheme o₁.t.G := (objPolAV o₁).isAb
  have hact : ∀ a, o₁.t.act.act a ≫ β = β ≫ o₂.t.act.act a := fun a => ext _ _ Θ₁ _ _ fun v => by
    rw [← Category.assoc, ← Θ₁.lin, hβ, ← Category.assoc, hβ, Θ₂.lin]
  have hx : ∀ v, (Θ₁.x v).left ≫ β.left = (Θ₂.x v).left := fun v => congrArg CommaMorphism.left (hβ v)
  have : IsIntegral o₁.t.G.left := isIntegral_left_of_isAbelianScheme_field _ (objPolAV o₁).isAb
  obtain ⟨w, hw, hv⟩ := (meetsOpens_of_separatesSections (objPolAV o₁) d₁).exists_lbIso (X := o₁.t.G.left)
    (x' := fun v => (Θ₂.x v).left) β.left hx f₁ f₂ rfl s₁ s₂ t₁ t₂ e₁.1 e₂.1 e₁'.1 e₂'.1
    (fun i v => ⟨_, v₁ i v, v₂ i v⟩) (fun i v => ⟨_, v₁' i v, v₂' i v⟩)
  refine ⟨⟨CubeMap.ofHom β, isGrpPullback_of_iso ψ, rfl, fun a => congrArg CommaMorphism.left (hact a),
    HeckePoint.isPullCubical_of_iso hL.globalFns a₁ β o₁.t.cub o₂.t.cub ⟨w, hw⟩⟩, w,
    ?_, fun v => ⟨hx v, fun j j' hj => ?_⟩⟩
  · refine isRigIso_of_value (G := o₁.t.G) (G' := o₂.t.G) β o₁.t.PP o₂.t.PP w hw fun a a' ha ha' => ?_
    rw [← x_zero_left Θ₁] at ha
    rw [← x_zero_left Θ₂] at ha'
    have e := hv 0 a a' ha ha'
    rw [Θ₁.rig a ha, Θ₂.rig a' ha', x_zero_left] at e
    exact e
  · have hj' := mem_of_le hj
    refine (hv v j' j (le_of_mem hj'.2) ?_).symm
    rw [← hx]
    exact le_of_mem (x := (Θ₁.x v).left ≫ β.left) (mem_pull.1 hj'.1)

end GlobalTheory.FamilyIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ), ∃ (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)), IsRigIso m.cm o₁.t.PP o₂.t.PP w ∧ ∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j' := by
  first | exact @GlobalTheory.FamilyIso.exists_sabMap_of_same_values | exact GlobalTheory.FamilyIso.exists_sabMap_of_same_values | (intros; apply GlobalTheory.FamilyIso.exists_sabMap_of_same_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamily
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyUnique

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F)) (hw : IsRigIso m L' L w) (hw' : IsRigIso m' L'' L' w') :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F), IsRigIso n L'' L w'' ∧
      ∀ (F : Type) [Field F] (x : Sp F ⟶ G''.left) (x' : Sp F ⟶ G'.left) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        x ≫ m'.F = x' →
        ⊤ ≤ x' ⁻¹ᵁ (LB.div (L.L.pull m.F) L'.L).U (fun _ => j, i) →
        ⊤ ≤ x ⁻¹ᵁ (LB.div (L'.L.pull m'.F) L''.L).U (fun _ => i, k) →
        valR x _ (w''.s (fun _ => j, k)).val =
          valR x' _ (w.s (fun _ => j, i)).val * valR x _ (w'.s (fun _ => i, k)).val := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw'
  obtain ⟨g, r⟩ := hw
  obtain ⟨g', r'⟩ := hw'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  refine ⟨w'', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_comp L'.isLB g g', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r'⟩, ?_⟩
  rintro F _ x x' j i k rfl h₁ h₂
  have a₁ := h₁ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have a₂ := h₂ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have hj : m.F (m'.F (x (cpt F))) ∈ L.L.U j := mem_pull.1 a₁.1
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (LB.div (L.L.pull (m'.F ≫ m.F)) L''.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull₂.2 hj, a₂.2⟩
  apply toStkA_injective
  rw [map_mul]
  exact (toStkA_valR x _ _ h₃ _).trans ((congrArg Units.val (T _ x (cpt F) j i k hj a₁.2 a₂.2)).trans
    (congrArg₂ (· * ·) (toStkA_valR _ _ _ h₁ _).symm (toStkA_valR _ _ _ h₂ _).symm))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_eq {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap = m := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem points_frames_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  intro hL hL2 E _ _ _ H _ D l Xo F _ _ _ V _ act I φ y₁ y₂ Θ₁ Θ₂ hy hA hM
  obtain ⟨o₁, m₁, w₁, Θ₁', rw₁, p₁, lev₁⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₁ _ Θ₁ hy
  obtain ⟨o₂, m₂, w₂, Θ₂', rw₂, p₂, lev₂⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₂ _ Θ₂ rfl
  obtain ⟨m, w, rw₀, p⟩ := GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂'
  have key : ∀ (k : ℕ) (x₁ : 𝟙_ (Over (Sp F)) ⟶ o₁.t.G) (x₂ : 𝟙_ (Over (Sp F)) ⟶ o₂.t.G)
      (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G), 1 ≤ k → x₁.left ≫ m₁.φ = y₁ ≫ x.left → x₂.left ≫ m₂.φ = y₂ ≫ x.left →
      (∃ ψ, Θ₁.Lev k (toUnit _ ≫ x) ψ ∧ Θ₂.Lev k (toUnit _ ≫ x) ψ) → x₁.left ≫ m.φ = x₂.left := by
    rintro k x₁ x₂ x hk k₁ k₂ ⟨ψ, a₁, a₂⟩
    exact GlobalTheory.T.triple_iso_respects_level_ratio_points hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂' m w k ψ x₁ x₂ hk rw₀.1 p
      (lev₁ k ψ _ x₁ hk k₁ a₁) (lev₂ k ψ _ x₂ hk k₂ a₂)
  obtain ⟨n, rfl⟩ := exists_objMap_eq o₁ o₂ m
    (fun a ha => key l.M _ _ _ (le_trans (by norm_num) l.three_le) (m₁.eta a) (m₂.eta a) (hM a ha))
    (fun a => key l.A _ _ _ l.A_pos (m₁.etaA a) (m₂.etaA a) (hA a))
  obtain ⟨n', hn'⟩ := ObjComp.objMap_comp m₂ n
  have e : y₁ = 𝟙 _ ≫ y₂ := (Xo.rep _ _ inferInstance o₁).unique ⟨hy, ⟨m₁⟩⟩ ⟨by rw [Category.id_comp], ⟨n'⟩⟩
  subst e
  have hφ : m₁.toSABMap.φ = n.toSABMap.φ ≫ m₂.toSABMap.φ := (objMap_unique_of_field hL.serre m₁ n').trans hn'
  obtain ⟨w', rw', hval⟩ := exists_rigIso_comp m₂.cm n.cm m₁.cm hφ
    (m₁.base.trans (congrArg₂ (· ≫ ·) n.base m₂.base).symm) _ _ _ w₂ w rw₂ rw₀
  intro v
  have hx : (Θ₁.x v).left = (Θ₂.x v).left := by
    rw [← (p₁ v).1, ← (p₂ v).1, ← (p v).1, hφ, Category.assoc]
  refine ⟨hx, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart o₁.t.PP.isLB ((Θ₁'.x v).left (cpt F))
  obtain ⟨i, hi⟩ := exists_chart o₂.t.PP.isLB ((Θ₂'.x v).left (cpt F))
  have hj₀ := (top_le_iff_cpt _ _).1 hj
  have c₁ : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₁.toSABMap.φ) o₁.t.PP.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p₁ v).1] at hj₀; exact hj₀), hk⟩
  have c₂ : ⊤ ≤ (Θ₂'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₂.toSABMap.φ) o₂.t.PP.L).U (fun _ => j, i) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [hx, ← (p₂ v).1] at hj₀; exact hj₀), hi⟩
  have c : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull n.toSABMap.φ) o₁.t.PP.L).U (fun _ => i, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p v).1] at hi; exact hi), hk⟩
  have := o₁.proper
  have u := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t o₁.t _ m₁.toSABMap).2 w₁ w' rw₁ rw' F (𝟙 _) (Θ₁'.x v)
    inferInstance j k c₁
  rw [(p₁ v).2 j k c₁, (p₂ v).2 j i c₂, (p v).2 i k c, ← _root_.mul_assoc]
  exact congrArg (· * _) (u.trans (hval F _ _ j i k (p v).1 c₂ c))

end GlobalTheory.FamilyUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  first | exact @GlobalTheory.FamilyUnique.points_frames_eq | exact GlobalTheory.FamilyUnique.points_frames_eq | (intros; apply GlobalTheory.FamilyUnique.points_frames_eq <;> assumption)
end
