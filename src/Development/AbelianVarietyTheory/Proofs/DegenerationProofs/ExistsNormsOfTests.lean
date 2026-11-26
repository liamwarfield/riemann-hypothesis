module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsRigNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnEqOfFineCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime] {X Y Z : Scheme.{0}}

abbrev z₀ (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)

def sn (p : ℕ) [Fact p.Prime] : (Sp (PadicAlgCl p)).presheaf.stalk (z₀ p) →* ℝ :=
  (normHom : PadicAlgCl p →*₀ ℝ).toMonoidHom.comp (ev (z₀ p)).toRingHom.toMonoidHom

def un (p : ℕ) [Fact p.Prime] : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ →* ℝ :=
  (sn p).comp (Units.coeHom _)

theorem sn_val (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : sn p u.val = un p u := rfl

theorem un_pos (u : ((Sp (PadicAlgCl p)).presheaf.stalk (z₀ p))ˣ) : 0 < un p u :=
  norm_pos_iff.2 (u.isUnit.map (ev (z₀ p))).ne_zero

theorem sn_gs (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)) :
    sn p (gs x (z₀ p) U a) = ‖valF x U a‖ := congrArg norm (ev_gs x _ h a)

theorem un_gm (x : Sp (PadicAlgCl p) ⟶ X) {U : X.Opens} (h : x (z₀ p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm x (z₀ p) U a) = ‖valF x U a.val‖ := congrArg norm (ev_gm x _ h a)

theorem gs_comp (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem mem_of_cPt (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : ⊤ ≤ b ⁻¹ᵁ U :=
  fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (b ⁻¹ᵁ U).isOpen h

theorem gen_mem (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) : (gPt p ≫ b) (z₀ p) ∈ U :=
  mem_of_cPt b h (show gPt p (z₀ p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)

theorem isUnit_iff_norm (v : OO p) : IsUnit v ↔ ‖(v : PadicAlgCl p)‖ = 1 := by
  have le : ∀ u : OO p, ‖(u : PadicAlgCl p)‖ ≤ 1 := fun u =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have e : ‖(v : PadicAlgCl p)‖ * ‖(u : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun t : OO p => ‖(t : PadicAlgCl p)‖) hu).trans norm_one
    have := le u
    have := le v
    have := norm_nonneg (v : PadicAlgCl p)
    nlinarith
  · intro h
    have h0 : (v : PadicAlgCl p) ≠ 0 := norm_pos_iff.1 (by rw [h]; exact one_pos)
    refine IsUnit.of_mul_eq_one ⟨(v : PadicAlgCl p)⁻¹,
      (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).2 (by rw [norm_inv, h, inv_one])⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)

theorem sn_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)) :
    sn p (gs (gPt p ≫ b) (z₀ p) U a) ≤ 1 ∧
      (sn p (gs (gPt p ≫ b) (z₀ p) U a) = 1 ↔ b (cPt p) ∈ X.basicOpen a) := by
  have h' := mem_of_cPt b h
  have hg := gen_mem b h
  let v : OO p := (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom.hom ((b.appLE U ⊤ h').hom a)
  have e : valF (gPt p ≫ b) U a = (v : PadicAlgCl p) := by
    rw [valF, dite_eq_left ((top_le_iff_mem _ U _).2 hg)]
    have e₁ := Scheme.Hom.appLE_comp_appLE (gPt p) b U ⊤ ⊤ h' le_top
    have e₂ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (OO p).subtype)
    have e₃ : (gPt p).appLE ⊤ ⊤ le_top = (gPt p).appTop := (Scheme.Hom.app_eq_appLE _).symm
    rw [← e₁, e₃]
    exact congrArg (fun q => q.hom ((b.appLE U ⊤ h').hom a)) e₂
  rw [sn_gs _ hg, e]
  refine ⟨(mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 v.2, (isUnit_iff_norm v).symm.trans ?_⟩
  have e₄ : (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) = PrimeSpectrum.basicOpen v :=
    basicOpen_eq_of_affine' _
  have e₅ := Scheme.basicOpen_appLE b ⊤ U h' a
  have e₆ : cPt p ∈ (Sp (OO p)).basicOpen ((b.appLE U ⊤ h').hom a) ↔ b (cPt p) ∈ X.basicOpen a := by
    erw [e₅]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  rw [← e₆, e₄]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem un_integral (b : Sp (OO p) ⟶ X) {U : X.Opens} (h : b (cPt p) ∈ U) (a : Γ(X, U)ˣ) :
    un p (gm (gPt p ≫ b) (z₀ p) U a) = 1 := by
  rw [← sn_val, ← gs_unit _ _ _ (gen_mem b h)]
  refine (sn_integral b h a.val).2.2 ?_
  rw [Scheme.basicOpen_of_isUnit _ a.isUnit]
  exact h

theorem un_eq_of_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (r : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ)
    (hU : ∀ x, ∃ a, x ∈ U a)
    (hr : ∀ a a' x, j x ∈ U a → j x ∈ U a' →
      gm (𝟙 HK) x _ (r a) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a')) :
    ∃ u : Γ(Sp K, ⊤)ˣ, ∀ (c : Sp (OO p) ⟶ H) (cK : Sp (PadicAlgCl p) ⟶ HK), cK ≫ j = gPt p ≫ c → ∀ a,
      c (cPt p) ∈ U a → un p (gm cK (z₀ p) _ (r a)) = un p (gm (cK ≫ fK) (z₀ p) ⊤ u) := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let eK : Sp K ⟶ HK := hK.lift (spMap (algebraMap V K) ≫ e) (𝟙 _) (by simp [he])
  have h₁ : eK ≫ j = spMap (algebraMap V K) ≫ e := hK.lift_fst _ _ _
  have h₂ : eK ≫ fK = 𝟙 _ := hK.lift_snd _ _ _
  obtain ⟨a₀, ha₀⟩ := hU (e (IsLocalRing.closedPoint V))
  have hA : ⊤ ≤ e ⁻¹ᵁ U a₀ := fun y _ => (IsLocalRing.specializes_closedPoint y).mem_open (e ⁻¹ᵁ U a₀).isOpen ha₀
  have hA'' : ⊤ ≤ eK ⁻¹ᵁ (j ⁻¹ᵁ U a₀) := fun y _ => by
    show (eK ≫ j) y ∈ U a₀
    rw [h₁]
    exact hA (show spMap (algebraMap V K) y ∈ (⊤ : (Sp V).Opens) from trivial)
  let u : Γ(Sp K, ⊤)ˣ := res hA'' (pullU eK _ (r a₀))
  let r' : ∀ a, Γ(HK, j ⁻¹ᵁ U a)ˣ := fun a => r a * res (le_top : j ⁻¹ᵁ U a ≤ fK ⁻¹ᵁ ⊤) (pullU fK ⊤ u⁻¹)
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a, j (q z) ∈ U a →
      gm q z _ (r' a) = gm q z _ (r a) * (gm (q ≫ fK) z ⊤ u)⁻¹ := fun Z q z a h =>
    (map_mul _ _ _).trans (congrArg (_ * ·) (((gm_res q z _ h _).trans (gm_pull q fK z ⊤ trivial _)).trans
      (map_inv _ _)))
  obtain ⟨s, ⟨hs₁, -, hs₂⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U) (g := fun a b => (g a b).val)
    (W := fun a => j ⁻¹ᵁ U a) (fun _ => rfl) hU (fun a b => (g a b).isUnit) (r := fun a => (r' a).val)
    (fun a b => fn_ext fun x hx => by
      refine (gs_res (𝟙 HK) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 HK) x _ hx _ _).trans
        (congrArg₂ (· * ·) (gs_appLE j _ _ _ (𝟙 HK) x hx _) (gs_res (𝟙 HK) x _ hx _))).symm)
      rw [Category.id_comp, gs_unit (𝟙 HK) x _ hx.1, gs_unit (𝟙 HK) x _ hx.2, gs_unit j x (U a ⊓ U b) hx,
        v _ (𝟙 HK) x a hx.1, v _ (𝟙 HK) x b hx.2, hr a b x hx.1 hx.2, _root_.mul_assoc, Units.val_mul])
    (fun a => (r' a).isUnit) he h₁ (A := ⊤) trivial hA (A' := ⊤) rfl hA'' (u := 1) isUnit_one (by
      rw [map_one]
      refine fn_ext fun y hy => ?_
      refine Eq.trans ?_ (gs_appLE eK _ _ _ (𝟙 _) y hy _).symm
      rw [Category.id_comp, gs_unit eK y _ (hA'' hy), v _ eK y a₀ (hA'' hy), h₂]
      have : gm (𝟙 (Sp K)) y ⊤ u = gm eK y _ (r a₀) := by
        refine ((gm_res _ y _ hy _).trans (gm_pull (𝟙 _) eK y _ (hA'' hy) _)).trans ?_
        rw [Category.id_comp]
      rw [this, mul_inv_cancel, gs_eq _ y ⊤ hy, map_one, map_one, Units.val_one])
  refine ⟨u, fun c cK hc a ha => ?_⟩
  have hm : j (cK (z₀ p)) ∈ U a := by
    show (cK ≫ j) _ ∈ U a
    rw [hc]
    exact gen_mem c ha
  have e₁ : un p (gm cK (z₀ p) _ (r' a)) = 1 := by
    rw [← un_integral c ha (hs₁ a).unit, ← hc]
    refine congrArg (un p) (Units.ext ?_)
    rw [← gs_unit cK _ _ hm, ← gs_unit (cK ≫ j) _ _ hm, ← hs₂ a]
    exact gs_appLE j _ _ _ cK _ hm _
  rw [v _ cK _ a hm, map_mul, map_inv] at e₁
  exact (mul_inv_eq_one₀ (un_pos _).ne').1 e₁

theorem un_eq_of_fine_charts {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
    [Algebra V K] [IsFractionRing V K] {H HK : Scheme.{0}} {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f]
    {j : HK ⟶ H} {fK : HK ⟶ Sp K} (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H)
    (he : e ≫ f = 𝟙 _) {α κ : Type} (U : α → H.Opens) (g : ∀ a b, Γ(H, U a ⊓ U b)ˣ) (W : α → κ → HK.Opens)
    (r : ∀ a b, Γ(HK, W a b)ˣ) (hU : ∀ x, ∃ a, x ∈ U a) (hW : ∀ a x, j x ∈ U a ↔ ∃ b, x ∈ W a b)
    (hr : ∀ a b a' b' x, x ∈ W a b → x ∈ W a' b' →
      gm (𝟙 HK) x _ (r a b) = gm j x _ (g a a') * gm (𝟙 HK) x _ (r a' b'))
    {c c' : Sp (OO p) ⟶ H} {cK cK' : Sp (PadicAlgCl p) ⟶ HK} (hc : cK ≫ j = gPt p ≫ c) (hc' : cK' ≫ j = gPt p ≫ c')
    (h : c ≫ f = c' ≫ f) {a a' : α} {b b' : κ} (ha : c (cPt p) ∈ U a) (ha' : c' (cPt p) ∈ U a')
    (hb : cK (z₀ p) ∈ W a b) (hb' : cK' (z₀ p) ∈ W a' b') :
    un p (gm cK (z₀ p) _ (r a b)) = un p (gm cK' (z₀ p) _ (r a' b')) := by
  have le : ∀ a b, W a b ≤ j ⁻¹ᵁ U a := fun a b x hx => (hW a x).2 ⟨b, hx⟩
  choose R hR using fun a => glue_unit (j ⁻¹ᵁ U a) (W a) (le a)
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ((hW a x).1 hx)) (r a) (fun b b' x hx => by
      rw [hr a b a b' x hx.1 hx.2, mul_eq_right.1 (hr a b a b x hx.1 hx.1).symm, _root_.one_mul])
  have v : ∀ (Z : Scheme.{0}) (q : Z ⟶ HK) (z : Z) a b, q z ∈ W a b → gm q z _ (r a b) = gm q z _ (R a) :=
    fun Z q z a b h => by rw [← hR a b, gm_res q z _ h]
  obtain ⟨u, hu⟩ := un_eq_of_charts (p := p) hK e he U g R hU fun a a' x hx hx' => by
    obtain ⟨b, hb⟩ := (hW a x).1 hx
    obtain ⟨b', hb'⟩ := (hW a' x).1 hx'
    rw [← v _ (𝟙 HK) x a b hb, ← v _ (𝟙 HK) x a' b' hb', hr a b a' b' x hb hb']
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_id_snd (f := spMap (algebraMap V K)))
  rw [v _ _ _ _ _ hb, v _ _ _ _ _ hb', hu c cK hc a ha, hu c' cK' hc' a' ha']
  refine congrArg (fun q => un p (gm q (z₀ p) ⊤ u)) ?_
  rw [← cancel_mono (spMap (algebraMap V K)), Category.assoc, Category.assoc, ← hK.w, ← Category.assoc, hc,
    ← Category.assoc, hc', Category.assoc, Category.assoc, h]

theorem exists_norm_ext {L : LB X} (hL : L.IsLB) (x : Sp (PadicAlgCl p) ⟶ X) (S : L.ι → ℝ → Prop)
    (hS : ∀ j t, S j t → 0 < t ∧ x (z₀ p) ∈ L.U j)
    (hS' : ∀ j t j' t', S j t → S j' t' → un p (gm x (z₀ p) _ (L.g j j')) * t = t') :
    ∃ n : L.ι → ℝ, (∀ j, 0 < n j) ∧ (∀ j j', x (z₀ p) ∈ L.U j → x (z₀ p) ∈ L.U j' →
      un p (gm x (z₀ p) _ (L.g j j')) * n j = n j') ∧ ∀ j t, S j t → n j = t := by
  classical
  obtain ⟨i, t₀, h₀, hi, H⟩ : ∃ i t₀, 0 < t₀ ∧ x (z₀ p) ∈ L.U i ∧
      ∀ j t, S j t → un p (gm x (z₀ p) _ (L.g i j)) * t₀ = t := by
    by_cases h : ∃ j t, S j t
    · obtain ⟨i, t₀, h⟩ := h
      exact ⟨i, t₀, (hS _ _ h).1, (hS _ _ h).2, fun j t h' => hS' _ _ _ _ h h'⟩
    · obtain ⟨i, hi⟩ := exists_chart hL (x (z₀ p))
      exact ⟨i, 1, one_pos, hi, fun j t h' => absurd ⟨j, t, h'⟩ h⟩
  refine ⟨fun j => un p (gm x (z₀ p) _ (L.g i j)) * t₀, fun j => mul_pos (un_pos _) h₀, fun j j' hj hj' => ?_, H⟩
  rw [← _root_.mul_assoc, ← map_mul, _root_.mul_comm (gm x _ _ _), gm_cocycle hL x _ hi hj hj']

end GlobalTheory.ZJ.TestNorm
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Bundle

variable {H HK A : Scheme.{0}} {M : LB H} {L : LB A} {j : HK ⟶ H} {φ : HK ⟶ A}

def wg (w : LB.Iso (L.pull φ) (M.pull j)) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z) (a : M.ι) (b : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm q z ((M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b)) (w.s (fun _ => a, fun _ => b))

theorem wg_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {Z : Scheme.{0}} (q : Z ⟶ HK) (z : Z)
    {a a' : M.ι} {b b' : L.ι} (ha : j (q z) ∈ M.U a) (ha' : j (q z) ∈ M.U a') (hb : φ (q z) ∈ L.U b)
    (hb' : φ (q z) ∈ L.U b') :
    wg w q z a b = gm (q ≫ j) z _ (M.g a a') * (gm (q ≫ φ) z _ (L.g b b'))⁻¹ * wg w q z a' b' := by
  have hm : q z ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b) ⊓
      ((M.pull j).U (fun _ => a') ⊓ (L.pull φ).U (fun _ => b')) :=
    ⟨⟨mem_pull.2 ha, mem_pull.2 hb⟩, mem_pull.2 ha', mem_pull.2 hb'⟩
  have e := congrArg (gm q z _) (hw (fun _ => a, fun _ => b) (fun _ => a', fun _ => b'))
  refine (gm_res q z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div (L.pull φ) (M.pull j) q z (fun _ => a, fun _ => b) (fun _ => a', fun _ => b') hm).trans ?_)
    (gm_res q z _ hm _))))
  exact congrArg₂ (fun s t => s * t⁻¹) (gm_pull_g M j q z _ _ hm.1.1 hm.2.1) (gm_pull_g L φ q z _ _ hm.1.2 hm.2.2)

def wv (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) : ℝ :=
  un p (wg w q (z₀ p) a b)

theorem wv_pos (w : LB.Iso (L.pull φ) (M.pull j)) (q : Sp (PadicAlgCl p) ⟶ HK) (a : M.ι) (b : L.ι) :
    0 < wv w q a b := un_pos _

theorem wv_trans {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen) {c : Sp (OO p) ⟶ H}
    {q : Sp (PadicAlgCl p) ⟶ HK} (h : q ≫ j = gPt p ≫ c) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c (cPt p) ∈ M.U a') (hb : (q ≫ φ) (z₀ p) ∈ L.U b) (hb' : (q ≫ φ) (z₀ p) ∈ L.U b') :
    un p (gm (q ≫ φ) (z₀ p) _ (L.g b b')) * wv w q a b = wv w q a' b' := by
  have m : ∀ {a}, c (cPt p) ∈ M.U a → j (q (z₀ p)) ∈ M.U a := fun {a} ha => by
    show (q ≫ j) _ ∈ M.U a
    rw [h]
    exact gen_mem c ha
  rw [wv, wg_trans hw q _ (m ha) (m ha') hb hb', map_mul, map_mul, map_inv, h,
    un_integral c (U := M.U a ⊓ M.U a') ⟨ha, ha'⟩, _root_.one_mul, mul_inv_cancel_left₀ (un_pos _).ne']
  rfl

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem wv_eq_of_extends (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {f : H ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {fK : HK ⟶ Sp K}
    (hK : IsPullback j fK f (spMap (algebraMap V K))) (e : Sp V ⟶ H) (he : e ≫ f = 𝟙 _) (ψ : H ⟶ A)
    (hψ : j ≫ ψ = φ) {c c' : Sp (OO p) ⟶ H} {q q' : Sp (PadicAlgCl p) ⟶ HK} (hc : q ≫ j = gPt p ≫ c)
    (hc' : q' ≫ j = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : M.ι} {b b' : L.ι} (ha : c (cPt p) ∈ M.U a)
    (ha' : c' (cPt p) ∈ M.U a') (hb : (c ≫ ψ) (cPt p) ∈ L.U b) (hb' : (c' ≫ ψ) (cPt p) ∈ L.U b') :
    wv w q a b = wv w q' a' b' := by
  subst hψ
  have m : ∀ {c : Sp (OO p) ⟶ H} {q : Sp (PadicAlgCl p) ⟶ HK}, q ≫ j = gPt p ≫ c → ∀ {a b},
      c (cPt p) ∈ M.U a → (c ≫ ψ) (cPt p) ∈ L.U b →
      q (z₀ p) ∈ (M.pull j).U (fun _ => a) ⊓ (L.pull (j ≫ ψ)).U (fun _ => b) := fun {c q} hc {a b} ha hb => by
    have : (q ≫ j) (z₀ p) ∈ M.U a ⊓ ψ ⁻¹ᵁ L.U b := by
      rw [hc]
      exact gen_mem c ⟨ha, hb⟩
    exact ⟨mem_pull.2 this.1, mem_pull.2 this.2⟩
  refine un_eq_of_fine_charts hK e he (α := M.ι × L.ι) (κ := PUnit) (fun s => M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2)
    (fun s t => res (inf_le_inf inf_le_left inf_le_left) (M.g s.1 t.1) *
      (res (inf_le_inf inf_le_right inf_le_right : _ ≤ ψ ⁻¹ᵁ L.U s.2 ⊓ ψ ⁻¹ᵁ L.U t.2)
        (pullU ψ (L.U s.2 ⊓ L.U t.2) (L.g s.2 t.2)))⁻¹)
    (fun s _ => (M.pull j).U (fun _ => s.1) ⊓ (L.pull (j ≫ ψ)).U (fun _ => s.2))
    (fun s _ => w.s (fun _ => s.1, fun _ => s.2)) (fun x => ?_) (fun s x => ?_) (fun s _ t _ x hs ht => ?_)
    hc hc' h (a := (a, b)) (a' := (a', b')) (b := ⟨⟩) (b' := ⟨⟩) ⟨ha, hb⟩ ⟨ha', hb'⟩ (m hc ha hb) (m hc' ha' hb')
  · obtain ⟨a, ha⟩ := exists_chart hM x
    obtain ⟨b, hb⟩ := exists_chart hL (ψ x)
    exact ⟨(a, b), ha, hb⟩
  · exact ⟨fun h => ⟨⟨⟩, mem_pull.2 h.1, mem_pull.2 h.2⟩, fun ⟨_, h⟩ => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩⟩
  · have hm : j x ∈ M.U s.1 ⊓ ψ ⁻¹ᵁ L.U s.2 ⊓ (M.U t.1 ⊓ ψ ⁻¹ᵁ L.U t.2) :=
      ⟨⟨mem_pull.1 hs.1, mem_pull.1 hs.2⟩, mem_pull.1 ht.1, mem_pull.1 ht.2⟩
    refine (wg_trans hw (𝟙 HK) x hm.1.1 hm.2.1 hm.1.2 hm.2.2).trans (congrArg (· * _) ?_)
    rw [Category.id_comp, Category.id_comp]
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res j x _ hm _) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res j x _ hm _).trans (gm_pull j ψ x (L.U s.2 ⊓ L.U t.2) ⟨hm.1.2, hm.2.2⟩ _)))))).symm

theorem gen_wv_eq (hM : M.IsLB) (hL : L.IsLB) {w : LB.Iso (L.pull φ) (M.pull j)} (hw : w.IsGen)
    {Y YK B : Scheme.{0}} {f : Y ⟶ Sp V} [Smooth f] [GeometricallyIntegral f] {i : YK ⟶ Y} {fK : YK ⟶ Sp K}
    (hK : IsPullback i fK f (spMap (algebraMap V K))) (e : Sp V ⟶ Y) (he : e ≫ f = 𝟙 _)
    {I : Type} [Fintype I] (α : I → (Y ⟶ H)) (ψ : I → (YK ⟶ HK)) (β : I → (B ⟶ A)) (Φ : YK ⟶ B)
    (h₁ : ∀ k, ψ k ≫ j = i ≫ α k) (h₂ : ∀ k, ψ k ≫ φ = Φ ≫ β k) {ε : I → ℤ} {t : LB.Gen (LB.LinComb L β ε)}
    (ht : t.IsGen) {c c' : Sp (OO p) ⟶ Y} {q q' : Sp (PadicAlgCl p) ⟶ YK} (hc : q ≫ i = gPt p ≫ c)
    (hc' : q' ≫ i = gPt p ≫ c') (h : c ≫ f = c' ≫ f) {a a' : I → M.ι} {b b' : I → L.ι}
    (ha : ∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) (ha' : ∀ k, (c' ≫ α k) (cPt p) ∈ M.U (a' k))
    (hb : ∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) (hb' : ∀ k, ((q' ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b' k)) :
    un p (gm (q ≫ Φ) (z₀ p) (LB.wchart L β b) (t.s b)) * ∏ k, wv w (q ≫ ψ k) (a k) (b k) ^ ε k =
      un p (gm (q' ≫ Φ) (z₀ p) (LB.wchart L β b') (t.s b')) * ∏ k, wv w (q' ≫ ψ k) (a' k) (b' k) ^ ε k := by
  let D := LB.div (M.pull j) (L.pull φ)
  let s : (I → M.ι) → (I → L.ι) → I → D.ι := fun a b k => (fun _ => a k, fun _ => b k)
  have p₁ : ∀ k x, j (ψ k x) = α k (i x) := fun k x => congrArg (fun g => g x) (h₁ k)
  have p₂ : ∀ k x, φ (ψ k x) = β k (Φ x) := fun k x => congrArg (fun g => g x) (h₂ k)
  have mem : ∀ a b x, x ∈ LB.wchart D ψ (s a b) ↔
      (∀ k, α k (i x) ∈ M.U (a k)) ∧ ∀ k, β k (Φ x) ∈ L.U (b k) := fun a b x => by
    refine Set.mem_iInter.trans (Iff.trans (forall_congr' fun k => ?_) forall_and)
    rw [← p₁, ← p₂]
    exact and_congr mem_pull mem_pull
  have le : ∀ a b, LB.wchart D ψ (s a b) ≤ Φ ⁻¹ᵁ LB.wchart L β b := fun a b x hx =>
    Set.mem_iInter.2 ((mem a b x).1 hx).2
  let r : ∀ a b, Γ(YK, LB.wchart D ψ (s a b))ˣ := fun a b => res (le a b) (pullU Φ _ (t.s b)) *
    ∏ k, res (LB.wchart_le D ψ (s a b) k) (pullU (ψ k) _ (w.s (s a b k))) ^ ε k
  have v : ∀ (Z : Scheme.{0}) (u : Z ⟶ YK) (z : Z) a b, u z ∈ LB.wchart D ψ (s a b) →
      gm u z _ (r a b) = gm (u ≫ Φ) z (LB.wchart L β b) (t.s b) * ∏ k, wg w (u ≫ ψ k) z (a k) (b k) ^ ε k :=
    fun Z u z a b hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res u z _ hz _).trans (gm_pull u Φ z _ (le a b hz) _))
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
        ((gm_res u z _ hz _).trans (gm_pull u (ψ k) z _ (LB.wchart_le D ψ (s a b) k hz) _))))))
  have m : ∀ {c : Sp (OO p) ⟶ Y} {q : Sp (PadicAlgCl p) ⟶ YK}, q ≫ i = gPt p ≫ c → ∀ {a b},
      (∀ k, (c ≫ α k) (cPt p) ∈ M.U (a k)) → (∀ k, ((q ≫ Φ) ≫ β k) (z₀ p) ∈ L.U (b k)) →
      q (z₀ p) ∈ LB.wchart D ψ (s a b) := fun {c q} hc {a b} ha hb => (mem a b _).2 ⟨fun k => by
    show ((q ≫ i) ≫ α k) _ ∈ M.U (a k)
    rw [hc, Category.assoc]
    exact gen_mem _ (ha k), hb⟩
  have key := un_eq_of_fine_charts hK e he (LB.wchart M α) (LB.LinComb M α ε).g (fun a b => LB.wchart D ψ (s a b)) r
    (fun x => by
      choose a ha using fun k => exists_chart hM (α k x)
      exact ⟨a, Set.mem_iInter.2 ha⟩)
    (fun a x => by
      choose b hb using fun k => exists_chart hL (β k (Φ x))
      exact ⟨fun h => ⟨b, (mem a b x).2 ⟨Set.mem_iInter.1 h, hb⟩⟩,
        fun ⟨b, h⟩ => Set.mem_iInter.2 ((mem a b x).1 h).1⟩)
    (fun a b a' b' x hx hx' => by
      obtain ⟨m₁, m₂⟩ := (mem a b x).1 hx
      obtain ⟨m₁', m₂'⟩ := (mem a' b' x).1 hx'
      rw [v _ (𝟙 YK) x a b hx, v _ (𝟙 YK) x a' b' hx', Category.id_comp,
        gen_trans ht Φ x (Set.mem_iInter.2 m₂) (Set.mem_iInter.2 m₂')]
      erw [gm_linComb M α ε i x a a' (Set.mem_iInter.2 m₁) (Set.mem_iInter.2 m₁')]
      rw [trF, mul_left_comm, _root_.mul_assoc, mul_left_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
      rw [← mul_zpow, ← mul_zpow, Category.id_comp, wg_trans hw (ψ k) x (a := a k) (a' := a' k) (b := b k) (b' := b' k)
        (by rw [p₁]; exact m₁ k) (by rw [p₁]; exact m₁' k) (by rw [p₂]; exact m₂ k) (by rw [p₂]; exact m₂' k),
        h₁, h₂, _root_.mul_assoc, mul_left_comm, mul_inv_cancel_left])
    hc hc' h (Set.mem_iInter.2 ha) (Set.mem_iInter.2 ha') (m hc ha hb) (m hc' ha' hb')
  rw [v _ _ _ _ _ (m hc ha hb), v _ _ _ _ _ (m hc' ha' hb')] at key
  simpa only [map_mul, map_prod, map_zpow, wv] using key

end Bundle

theorem ext_gPt {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] {b b' : Sp (OO p) ⟶ X} (h : b ≫ s = b' ≫ s)
    (h' : gPt p ≫ b = gPt p ≫ b') : b = b' := by
  have := InvExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated s h (gPt p) h'

theorem isPullback_cube {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {A : Over U} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left} (gp : IsGrpPullback A G j F) :
    IsPullback (cubeMapOf gp).F3 (G3 A).hom (G3 G).hom j := by
  have hp := gp.1
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have w : (cubeMapOf gp).F3 ≫ (G3 G).hom = (G3 A).hom ≫ j :=
    Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2))))
  have ex : ∀ s : PullbackCone (G3 G).hom j, ∃ l : s.pt ⟶ (G3 A).left,
      l ≫ (cubeMapOf gp).F3 = s.fst ∧ l ≫ (G3 A).hom = s.snd := by
    intro s
    let P : Over U := Over.mk s.snd
    let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
      (hp.lift (s.fst ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact s.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ F = s.fst ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
    have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
    refine ⟨l.left, hom_ext_triple _ fun i => ?_, Over.w l⟩
    rw [Category.assoc, f3, ← hx, ← lx]
    exact (Category.assoc _ _ _).symm
  choose l h₁ h₂ using ex
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l h₁ h₂ fun s m m₁ m₂ => hom_ext_triple _ fun i => hp.hom_ext ?_ ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← f3, ← Category.assoc, ← Category.assoc, m₁, h₁]
  · rw [Category.assoc, Category.assoc, Over.w, m₂, h₂]

theorem sum_thε : ∑ I : thK.{0}, thε I = 0 := by decide

theorem prod_thε {t : ℝ} (ht : 0 < t) : ∏ I : thK.{0}, t ^ thε I = 1 := by
  have : ∀ s : Finset thK.{0}, ∏ I ∈ s, t ^ thε I = t ^ ∑ I ∈ s, thε I := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ ht.ne']
  rw [this, sum_thε, zpow_zero]

section Test

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem base_ext {y y' : Sp (OO p) ⟶ C.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' :=
  have := C.sep
  ext_gPt C.π (specZIsTerminal.hom_ext _ _) h

abbrev jg : pullback τ.H.hom (Out.jK τ.V) ⟶ τ.H.left := pullback.fst τ.H.hom (Out.jK τ.V)

def IsLift (c : Sp (OO p) ⟶ τ.H.left) (q : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)) : Prop :=
  c ≫ τ.H.hom = spMap τ.j ∧ q ≫ jg τ = gPt p ≫ c

theorem exists_frac : ∃ r, gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := by
  obtain ⟨r, hr⟩ := spMap_factor_jK ((OO p).subtype.comp τ.j) (Subtype.val_injective.comp τ.j_inj)
  exact ⟨r, (Spec.map_comp _ _).symm.trans hr⟩

variable {τ} {c c' : Sp (OO p) ⟶ τ.H.left} {q q' : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V)}

theorem IsLift.gen (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.a = gPt p ≫ c ≫ τ.f := by
  rw [Category.assoc, τ.φ_f, ← Category.assoc, h.2, Category.assoc]

theorem IsLift.over (h : IsLift τ c q) : (c ≫ τ.f) ≫ C.GG.hom = y := by
  rw [Category.assoc, τ.f_over, ← Category.assoc, h.1, τ.fac]

theorem IsLift.base (h : IsLift τ c q) : (q ≫ τ.φ) ≫ C.A.hom ≫ C.U.ι = gPt p ≫ y := by
  rw [← C.isPullback_a.w, ← Category.assoc, h.gen, Category.assoc, h.over]

theorem IsLift.centre (h : IsLift τ c q) : τ.H.hom (c (cPt p)) = IsLocalRing.closedPoint τ.V := by
  have := τ.j_loc
  exact (congrArg (fun g => g (cPt p)) h.1).trans (IsLocalRing.comap_closedPoint τ.j)

theorem IsLift.unique (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (h : IsLift τ c q) (h' : IsLift τ c' q')
    (e : q ≫ τ.φ = q' ≫ τ.φ) : c = c' ∧ q = q' := by
  have := τ.sep
  have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
  have e₁ : c = c' := ext_gPt τ.H.hom (h.1.trans h'.1.symm) (hp.hom_ext
    (by rw [Category.assoc, Category.assoc, ← h.gen, ← h'.gen, e])
    (by rw [Category.assoc, Category.assoc, h.1, h'.1]))
  exact ⟨e₁, (cancel_mono (jg τ)).1 (by rw [h.2, h'.2, e₁])⟩

variable (τ) in
theorem exists_lift {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left} (hb : b ≫ C.GG.hom = y)
    (hx : gPt p ≫ b = x ≫ C.a) : ∃ c q, IsLift τ c q ∧ c ≫ τ.f = b ∧ q ≫ τ.φ = x := by
  have := C.isOpenImmersion_a
  obtain ⟨c, h₁, h₂⟩ := τ.lift b hb
  obtain ⟨r, hr⟩ := exists_frac τ
  have h : IsLift τ c (pullback.lift (gPt p ≫ c) r (by rw [Category.assoc, h₁, hr])) :=
    ⟨h₁, pullback.lift_fst _ _ _⟩
  exact ⟨c, _, h, h₂, (cancel_mono C.a).1 (by rw [h.gen, h₂, hx])⟩

variable (E : T.Ext τ)

theorem IsLift.theta (h : IsLift τ c q) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b) :
    ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b ≤ 1 ∧
      (‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = 1 ↔ c (cPt p) ∈ Out.nonzeroLocus E.θ) := by
  have ha' : jg τ (q (z₀ p)) ∈ E.L.L.U a := by
    show (q ≫ jg τ) _ ∈ _
    rw [h.2]
    exact gen_mem c ha
  have hm : q (z₀ p) ∈ (E.L.L.pull (jg τ)).U (fun _ => a) ⊓ (T.L.L.pull τ.φ).U (fun _ => b) :=
    ⟨mem_pull.2 ha', mem_pull.2 hb⟩
  have e := congrArg (q.stalkMap (z₀ p)).hom (E.θ_eq _ a b ha' hb)
  rw [map_mul, ← gs_comp q _ _ _ ha', ← gs_comp q _ _ _ hb, h.2] at e
  have e₁ := (gs_stalkMap q (z₀ p) _ hm (E.w.s (fun _ => a, fun _ => b)).val).symm.trans (gs_unit q _ _ hm _)
  have e₂ : ‖valF (q ≫ τ.φ) _ (T.θ.f b)‖ * wv E.w q a b = sn p (gs (gPt p ≫ c) (z₀ p) _ (E.θ.f a)) := by
    rw [e, map_mul, ← sn_gs _ hb, _root_.mul_comm]
    exact congrArg (· * _) (congrArg (sn p) e₁).symm
  rw [e₂, mem_nonzeroLocus_iff E.θ c _ ha, isUnit_gs_iff c _ _ ha]
  exact sn_integral c ha _

def IsRigNorm (ρ : ℝ) : Prop :=
  ∀ c q (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q →
    q ≫ τ.φ = u ≫ eSec C.A → c (cPt p) ∈ E.L.L.U a → (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
    un p (gm u (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b) (T.L.rig.s fun _ => b)) *
      wv E.w q a b = ρ

theorem exists_isRigNorm (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) : ∃ ρ, 0 < ρ ∧ IsRigNorm E ρ := by
  by_cases h : ∃ c q, ∃ (u : Sp (PadicAlgCl p) ⟶ C.U.toScheme) (a : E.L.L.ι) (b : T.L.L.ι), IsLift τ c q ∧
    q ≫ τ.φ = u ≫ eSec C.A ∧ c (cPt p) ∈ E.L.L.U a ∧ (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b
  swap
  · exact ⟨1, one_pos, fun c q u a b h₁ h₂ h₃ h₄ => absurd ⟨c, q, u, a, b, h₁, h₂, h₃, h₄⟩ h⟩
  obtain ⟨c', q', u', a', b', k₁, k₂, k₃, k₄⟩ := h
  refine ⟨_, mul_pos (un_pos (gm u' (z₀ p) (LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b')
    (T.L.rig.s fun _ => b'))) (wv_pos E.w q' a' b'), fun c q u a b h₁ h₂ h₃ h₄ => ?_⟩
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  have base : ∀ {c q} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme}, IsLift τ c q → q ≫ τ.φ = u ≫ eSec C.A →
      u ≫ C.U.ι = gPt p ≫ y := fun {c q u} h₁ h₂ => by
    rw [← h₁.base, h₂, Category.assoc]
    exact congrArg (u ≫ ·) ((Category.id_comp _).symm.trans ((congrArg (· ≫ C.U.ι) he.symm).trans
      (Category.assoc _ _ _)))
  obtain rfl : u = u' := (cancel_mono C.U.ι).1 ((base h₁ h₂).trans (base k₁ k₂).symm)
  obtain ⟨rfl, rfl⟩ := h₁.unique hp k₁ (h₂.trans k₂.symm)
  have m : ∀ {b}, (q ≫ τ.φ) (z₀ p) ∈ T.L.L.U b →
      u (z₀ p) ∈ LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b := fun {b} hb =>
    Set.mem_iInter.2 fun _ => by rw [h₂] at hb; exact hb
  rw [gen_trans T.L.rigGen u _ (m h₄) (m k₄), trF, Fintype.prod_unique, zpow_one, map_mul, ← h₂,
    ← wv_trans E.w_gen h₁.2 h₃ k₃ h₄ k₄]
  ring

variable {E}

theorem IsRigNorm.integral {ρ : ℝ} (hρ : IsRigNorm E ρ) {s : Sp (OO p) ⟶ C.A.left} (h : IsLift τ c q)
    (hs : c ≫ τ.f = s ≫ C.a) {a : E.L.L.ι} {b : T.L.L.ι} (ha : c (cPt p) ∈ E.L.L.U a)
    (hb : s (cPt p) ∈ T.L.L.U b) : wv E.w q a b = ρ := by
  have := C.isOpenImmersion_a
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := geometricallyIntegral_of_isSemiAbelian τ.H
  have hy : (s ≫ C.A.hom) ≫ C.U.ι = y := by
    rw [Category.assoc, ← C.isPullback_a.w, ← Category.assoc, ← hs, h.over]
  obtain ⟨y₁, hy₁⟩ := exists_fac_of_closedPoint τ.y₀ C.U (by
    rw [← h.centre]
    show (c ≫ τ.H.hom ≫ τ.y₀) (cPt p) ∈ C.U
    rw [← Category.assoc, h.1, τ.fac, ← hy]
    exact ((s ≫ C.A.hom) (cPt p)).2)
  let ψ : τ.H.left ⟶ C.A.left := C.isPullback_a.lift τ.f (τ.H.hom ≫ y₁) (by rw [τ.f_over, Category.assoc, hy₁])
  have hψ : ψ ≫ C.a = τ.f := C.isPullback_a.lift_fst _ _ _
  have hφ : jg τ ≫ ψ = τ.φ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, τ.φ_f])
  have he : eSec C.A ≫ C.A.hom = 𝟙 _ := Over.w η[C.A]
  let s₀ : Sp (OO p) ⟶ C.A.left := (s ≫ C.A.hom) ≫ eSec C.A
  obtain ⟨c₀, q₀, k₁, k₂, k₃⟩ := exists_lift τ (b := s₀ ≫ C.a) (x := gPt p ≫ s₀) (by
    rw [Category.assoc, C.isPullback_a.w, ← hy, ← Category.assoc]
    exact congrArg (· ≫ C.U.ι) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) he).trans (Category.comp_id _))))
    (Category.assoc _ _ _).symm
  have e₁ : c ≫ ψ = s := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, hs])
  have e₂ : c₀ ≫ ψ = s₀ := (cancel_mono C.a).1 (by rw [Category.assoc, hψ, k₂])
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB (c₀ (cPt p))
  obtain ⟨b₀, hb₀⟩ := exists_chart T.L.isLB (s₀ (cPt p))
  have e₃ := hρ c₀ q₀ (gPt p ≫ s ≫ C.A.hom) a₀ b₀ k₁ (k₃.trans (Category.assoc _ _ _).symm) ha₀
    (by rw [k₃]; exact gen_mem s₀ hb₀)
  have e₄ := un_integral (s ≫ C.A.hom) (U := LB.wchart T.L.L (fun _ : PUnit => eSec C.A) fun _ => b₀)
    (Set.mem_iInter.2 fun _ => hb₀) (T.L.rig.s fun _ => b₀)
  rw [← ((_root_.one_mul _).symm.trans (congrArg (· * _) e₄.symm)).trans e₃]
  exact wv_eq_of_extends E.L.isLB T.L.isLB E.w_gen (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)) (eSec τ.H)
    (Over.w η[τ.H]) ψ hφ h.2 k₁.2 (h.1.trans k₁.1.symm) ha ha₀ (by rw [e₁]; exact hb) (by rw [e₂]; exact hb₀)

end Test

end GlobalTheory.ZJ.TestNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTests
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Cube

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} {τ : C.Test y} (E : T.Ext τ)

theorem cube_eq_one (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left)
    (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)) (hs : ∀ k, s k ≫ C.GG.hom = y)
    (hx : ∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) :
    ∃ (c : thK.{0} → (Sp (OO p) ⟶ τ.H.left)) (q : thK.{0} → (Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V))),
      (∀ I, IsLift τ (c I) (q I) ∧ q I ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I) ∧
      ∀ (a : thK.{0} → E.L.L.ι) (b : thK.{0} → T.L.L.ι), (∀ I, c I (cPt p) ∈ E.L.L.U (a I)) →
        (∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (b I)) →
        un p (gm x (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) b) (T.cub.t.s b)) *
          ∏ I, wv E.w (q I) (a I) (b I) ^ thε I = 1 := by
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.geomConnected
  have := smooth_cube_hom τ.H
  have := geometricallyIntegral_cube_hom τ.H
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  have : Mono (jg τ) :=
    have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
    inferInstance
  let HK := (Over.pullback (Out.jK τ.V)).obj τ.H
  have gp := isGrpPullback_pullback τ.H (Out.jK τ.V)
  have hK := isPullback_cube gp
  have h₁ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ jg τ = (cubeMapOf gp).F3 ≫ thφ τ.H (x3 τ.H) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have h₂ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ τ.φ = (cubeMapOf τ.φ_cart).F3 ≫ thφ C.A (x3 C.A) I :=
    fun I => (cubeMapOf τ.φ_cart).psum_comm I.down
  obtain ⟨r, hr⟩ := exists_frac τ
  have lifts : ∀ (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left) (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)),
      (∀ k, s k ≫ C.GG.hom = y) → (∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) →
      ∃ (c : Sp (OO p) ⟶ (G3 τ.H).left) (q : Sp (PadicAlgCl p) ⟶ (G3 HK).left), c ≫ (G3 τ.H).hom = spMap τ.j ∧
        q ≫ (cubeMapOf gp).F3 = gPt p ≫ c ∧ q ≫ (cubeMapOf τ.φ_cart).F3 = x ∧
        ∀ I : thK.{0}, IsLift τ (c ≫ thφ τ.H (x3 τ.H) I) (q ≫ thφ HK (x3 HK) I) ∧
          (q ≫ thφ HK (x3 HK) I) ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I := by
    intro x s hs hx
    choose c q k₁ k₂ k₃ using fun k => exists_lift τ (hs k) (hx k)
    let d : Fin 3 → (Over.mk (spMap τ.j) ⟶ τ.H) := fun k => Over.homMk (c k) (k₁ k).1
    let l : Over.mk (spMap τ.j) ⟶ G3 τ.H := lift (d 0) (lift (d 1) (d 2))
    have lx : ∀ k, l ≫ x3 τ.H k = d k := fun k => by fin_cases k <;> simp [l, x3]
    have lx' : ∀ k, l.left ≫ (x3 τ.H k).left = c k := fun k => congrArg (fun z => z.left) (lx k)
    have w : l.left ≫ (G3 τ.H).hom = spMap τ.j := Over.w l
    let Q : Sp (PadicAlgCl p) ⟶ (G3 HK).left := hK.lift (gPt p ≫ l.left) r
      ((Category.assoc _ _ _).trans ((congrArg (gPt p ≫ ·) w).trans hr))
    have hQ : Q ≫ (cubeMapOf gp).F3 = gPt p ≫ l.left := hK.lift_fst _ _ _
    have hQ' : ∀ k, Q ≫ (x3 HK k).left = q k := fun k => (cancel_mono (jg τ)).1
      ((Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf gp) k).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hQ).trans ((Category.assoc _ _ _).trans
          ((congrArg (gPt p ≫ ·) (lx' k)).trans (k₁ k).2.symm))))))
    have hx' : Q ≫ (cubeMapOf τ.φ_cart).F3 = x := hom_ext_triple _ fun k =>
      (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf τ.φ_cart) k)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.φ) (hQ' k)).trans (k₃ k))))
    refine ⟨l.left, Q, w, hQ, hx', fun I => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (l.left ≫ ·) (Over.w (psum τ.H (x3 τ.H) I.down))).trans w)
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₁ I)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hQ).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₂ I)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) hx')))
  obtain ⟨c, q, k₁, k₂, rfl, k₄⟩ := lifts x s hs hx
  refine ⟨_, _, k₄, fun a b ha hb => ?_⟩
  let u : Sp (PadicAlgCl p) ⟶ C.U.toScheme := r ≫ τ.yK
  have hu : u ≫ C.U.ι = gPt p ≫ y := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← hr, Category.assoc, τ.fac]
  let o : Over.mk u ⟶ C.A := 1
  have ho : o.left = u ≫ eSec C.A := by
    show (toUnit _ ≫ η[C.A]).left = _
    simp [eSec]
  have ox : ∀ k, lift o (lift o o) ≫ x3 C.A k = o := fun k => by fin_cases k <;> simp [x3]
  have oI : ∀ I : thK.{0}, (lift o (lift o o)).left ≫ thφ C.A (x3 C.A) I = o.left := fun I => by
    have e : lift o (lift o o) ≫ psum C.A (x3 C.A) I.down = psum C.A (fun _ => o) I.down :=
      (psum_hom (preHom (lift o (lift o o))) (x3 C.A) I.down).trans (congrArg (psum C.A · I.down) (funext ox))
    have e' : psum C.A (fun _ : Fin 3 => o) I.down = o := (psum_hom (1 : (Over.mk u ⟶ C.A) →* (Over.mk u ⟶ C.A))
      (fun _ => o) I.down).symm
    exact congrArg (fun z => z.left) (e.trans e')
  obtain ⟨c₀, q₀, m₁, m₂, m₃, m₄⟩ := lifts (lift o (lift o o)).left (fun _ => y ≫ C.e)
    (fun _ => (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (fun k => by
      refine Eq.trans ?_ (congrArg (fun z => z.left ≫ C.a) (ox k)).symm
      rw [ho, ← Category.assoc, ← hu, Category.assoc, C.e_zero]
      exact (Category.assoc _ _ _).symm)
  have same := fun I => (m₄ I).1.unique hp (m₄ ⟨∅⟩).1 ((m₄ I).2.trans ((oI I).trans ((m₄ _).2.trans (oI _)).symm))
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB ((c₀ ≫ thφ τ.H (x3 τ.H) (⟨∅⟩ : thK.{0})) (cPt p))
  choose J hJ using fun χ : Sp (PadicAlgCl p) ⟶ C.A.left => exists_chart T.L.isLB (χ (z₀ p))
  have key := gen_wv_eq E.L.isLB T.L.isLB E.w_gen hK (lift η[τ.H] (lift η[τ.H] η[τ.H])).left (Over.w _)
    (thφ τ.H (x3 τ.H)) (thφ HK (x3 HK)) (thφ C.A (x3 C.A)) (cubeMapOf τ.φ_cart).F3 h₁ h₂ (ε := thε) (t := T.cub.t)
    T.cub.isGen k₂ m₂ (k₁.trans m₁.symm) (a := a) (a' := fun _ => a₀) (b := b) (b' := fun _ => J o.left) ha
    (fun I => by rw [(same I).1]; exact ha₀) hb (fun I => by rw [m₃, oI]; exact hJ _)
  refine key.trans ?_
  have e₁ : gm (lift o (lift o o)).left (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) fun _ => J o.left)
      (T.cub.t.s fun _ => J o.left) = 1 :=
    (val_of (φ := thφ C.A (x3 C.A)) (ε := thε) T.cub.t _ _ J _ fun I => congrArg J (oI I)).symm.trans
      ((isCub_cubV T.cub (T := Over.mk u) hJ).face 1 1)
  rw [m₃]
  erw [e₁]
  rw [map_one, _root_.one_mul, Finset.prod_congr rfl fun I _ => by rw [(same I).2]]
  exact prod_thε (wv_pos _ _ _ _)

end Cube

end GlobalTheory.ZJ.TestNorm

namespace GlobalTheory.ZJ

open TestNorm CubeGen

theorem Core.Theta.exists_norms : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  intro hE C L T hT hB
  have hC : C.TestCart := fun p _ y τ => (L.test p y τ).1
  have sepG : IsSeparated C.GG.hom := (core_basic C).1
  have ex : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), C.Cl y →
      ∃ (τ : C.Test y) (E : T.Ext τ) (ρ : ℝ), 0 < ρ ∧ IsRigNorm E ρ := fun p _ y hy => by
    obtain ⟨τ⟩ := hT p y hy
    obtain ⟨E⟩ := Core.Theta.nonempty_ext hE C T p y τ hC
    exact ⟨τ, E, exists_isRigNorm E (hC p y τ)⟩
  choose τ E ρ hρ hR using ex
  have ex₂ : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left), ∃ n : T.L.L.ι → ℝ, (∀ j, 0 < n j) ∧
      (∀ j j', x (z₀ p) ∈ T.L.L.U j → x (z₀ p) ∈ T.L.L.U j' →
        un p (gm x (z₀ p) _ (T.L.L.g j j')) * n j = n j') ∧
      ∀ j t, (∃ (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y), ∃ c q a, IsLift (τ p y hy) c q ∧ q ≫ (τ p y hy).φ = x ∧
        c (cPt p) ∈ (E p y hy).L.L.U a ∧ x (z₀ p) ∈ T.L.L.U j ∧ t = wv (E p y hy).w q a j / ρ p y hy) → n j = t := by
    intro p _ x
    refine exists_norm_ext T.L.isLB x _ ?_ ?_
    · rintro j t ⟨y, hy, c, q, a, -, -, -, h, rfl⟩
      exact ⟨div_pos (wv_pos _ _ _ _) (hρ p y hy), h⟩
    · rintro j t j' t' ⟨y, hy, c, q, a, h₁, rfl, h₃, h₄, rfl⟩ ⟨y', hy', c', q', a', k₁, k₂, k₃, k₄, rfl⟩
      obtain rfl : y = y' := base_ext (by rw [← h₁.base, ← k₁.base, k₂])
      obtain ⟨rfl, rfl⟩ := h₁.unique (hC _ _ _) k₁ k₂.symm
      rw [← wv_trans (E p y hy).w_gen h₁.2 h₃ k₃ h₄ k₄, mul_div_assoc]
  choose ν h₁ h₂ h₃ using ex₂
  have hν : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y) c q a j, IsLift (τ p y hy) c q →
      c (cPt p) ∈ (E p y hy).L.L.U a → (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U j →
      ν p (q ≫ (τ p y hy).φ) j = wv (E p y hy).w q a j / ρ p y hy :=
    fun p _ y hy c q a j k₁ k₂ k₃ => h₃ p _ j _ ⟨y, hy, c, q, a, k₁, rfl, k₂, k₃, rfl⟩
  have cl : ∀ {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme},
      gPt p ≫ y = u ≫ C.U.ι → C.Cl y := fun {p} _ {y u} h => by
    rw [Core.Cl, h]
    exact range_comp_ι_subset _ _
  have bas : ∀ {p : ℕ} [Fact p.Prime] {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left},
      gPt p ≫ b = x ≫ C.a → gPt p ≫ b ≫ C.GG.hom = (x ≫ C.A.hom) ≫ C.U.ι := fun {p} _ {b x} h => by
    rw [← Category.assoc, h, Category.assoc, C.isPullback_a.w, Category.assoc]
  refine ⟨ν, ⟨h₁, fun p _ x i j hi hj => ?_, fun p _ s j hj => ?_⟩, fun p _ u ⟨y, hu, _⟩ J hJ => ?_,
    fun p _ x hx J hJ => ?_, fun p _ u => ?_⟩
  · have hi' := (range_subset_iff x (z₀ p) _).1 hi
    have hj' := (range_subset_iff x (z₀ p) _).1 hj
    rw [← un_gm x (U := T.L.L.U i ⊓ T.L.L.U j) ⟨hi', hj'⟩]
    exact h₂ p x i j hi' hj'
  · have e : gPt p ≫ s ≫ C.a = (gPt p ≫ s) ≫ C.a := (Category.assoc _ _ _).symm
    have hy := cl (bas e)
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p _ hy) rfl e
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    rw [← k₃, hν p _ hy c q a j k₁ ha (by rw [k₃]; exact gen_mem s hj), (hR p _ hy).integral k₁ k₂ ha hj,
      div_self (hρ p _ hy).ne']
  · have hy := cl hu
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p y hy) (b := y ≫ C.e) (x := u ≫ eSec C.A)
      ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (by
        rw [← Category.assoc, hu, Category.assoc, C.e_zero]
        exact (Category.assoc _ _ _).symm)
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hJ' := (range_subset_iff u (z₀ p) _).1 hJ
    have hb : (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U (J ⟨⟩) := by
      rw [k₃]
      exact Set.mem_iInter.1 hJ' ⟨⟩
    have e₁ := hν p y hy c q a _ k₁ ha hb
    have e₂ := hR p y hy c q u a _ k₁ k₃ ha hb
    rw [k₃] at e₁
    rw [Fintype.prod_unique, zpow_one]
    refine (congrArg₂ (· * ·) (un_gm u hJ' _).symm e₁).trans ?_
    rw [← mul_div_assoc]
    exact (div_eq_one_iff_eq (hρ p y hy).ne').2 e₂
  · choose s hs _ using hx
    have e : ∀ k, gPt p ≫ s k ≫ C.GG.hom = (x ≫ (G3 C.A).hom) ≫ C.U.ι := fun k => by
      rw [bas (hs k), Category.assoc x, Over.w]
    have hy := cl (e 0)
    obtain ⟨c, q, k₁, k₂⟩ := cube_eq_one (E p _ hy) (hC _ _ _) x s (fun k => base_ext ((e k).trans (e 0).symm)) hs
    choose a ha using fun I => exists_chart (E p _ hy).L.isLB (c I (cPt p))
    have hJ' := (range_subset_iff x (z₀ p) _).1 hJ
    have hb : ∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (J I) := Set.mem_iInter.1 hJ'
    refine (congrArg₂ (· * ·) (un_gm x hJ' _).symm (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I)
      ((congrArg (ν p · (J I)) (k₁ I).2.symm).trans
        (hν p _ hy _ _ (a I) (J I) (k₁ I).1 (ha I) (by rw [(k₁ I).2]; exact hb I))))).trans ?_
    simp only [div_zpow, Finset.prod_div_distrib]
    exact (congrArg (_ * ·) ((congrArg (_ / ·) (prod_thε (hρ p _ hy))).trans (div_one _))).trans (k₂ a J ha hb)
  · by_cases h : ∃ y : Sp (OO p) ⟶ C.Z, gPt p ≫ y = u ≫ C.U.ι
    swap
    · exact ⟨1, one_pos, fun x j hx _ ⟨b, hb, _⟩ => absurd ⟨_, hx ▸ bas hb⟩ h⟩
    obtain ⟨y, hu⟩ := h
    have hy := cl hu
    refine ⟨1 / ρ p y hy, one_div_pos.2 (hρ p y hy), fun x j hx hj ⟨b, hb, _⟩ => ?_⟩
    obtain ⟨c, q, k₁, k₂, rfl⟩ := exists_lift (τ p y hy) (base_ext ((bas hb).trans (by rw [hx, hu]))) hb
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hj' := (range_subset_iff _ (z₀ p) _).1 hj
    obtain ⟨t₁, t₂⟩ := k₁.theta (E p y hy) ha hj'
    rw [hν p y hy c q a j k₁ ha hj', ← mul_div_assoc]
    refine ⟨div_le_div_of_nonneg_right t₁ (hρ p y hy).le, (div_left_inj' (hρ p y hy).ne').trans (t₂.trans
      ((hB p y _ (E p y hy) _ k₁.centre).symm.trans ?_))⟩
    have e : (τ p y hy).f (c (cPt p)) = b (cPt p) := congrArg (fun g => g (cPt p)) k₂
    rw [e]
    refine ⟨fun h => ⟨b, hb, h⟩, fun ⟨b', hb', h⟩ => ?_⟩
    rwa [ext_gPt C.GG.hom (base_ext ((bas hb).trans (bas hb').symm)) (hb.trans hb'.symm)]

end GlobalTheory.ZJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTestsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norms_of_tests : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  first | exact @GlobalTheory.ZJ.Core.Theta.exists_norms | exact GlobalTheory.ZJ.Core.Theta.exists_norms | (intros; apply GlobalTheory.ZJ.Core.Theta.exists_norms <;> assumption)
end
