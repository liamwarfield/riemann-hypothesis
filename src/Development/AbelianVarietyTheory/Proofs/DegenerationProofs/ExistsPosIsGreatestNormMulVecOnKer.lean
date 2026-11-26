module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormConstSec
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

theorem norm_const_gen : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (nH : H ⟶ H) (nK : HK ⟶ HK) (nX : X ⟶ X), nK ≫ j = j ≫ nH → nK ≫ ψ = ψ ≫ nX → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1])), α.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l l' : M.ι) (m : Fin 2 → L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (c ≫ nH) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) → ⊤ ≤ (x ≫ ψ ≫ nX) ⁻¹ᵁ L.U (m 1) → ‖valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x l (m 0) ^ n ^ 2 * (ω (x ≫ nK) l' (m 1))⁻¹‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα
  have ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH := fun x => by
    rw [Category.assoc, hnj, Category.assoc]
  have eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX := fun x => by
    rw [Category.assoc, hnψ, Category.assoc]
  have w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0) := fun m => LB.wchart_le L ![𝟙 X, nX] m 0
  have w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1) := fun m => LB.wchart_le L ![𝟙 X, nX] m 1
  have l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) →
      ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2 := fun h => by
    rw [ej]
    exact fun _ hz => (h hz).2
  have m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m →
      ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1) := fun h => by
    rw [eψ]
    exact fun _ hz => w₁ _ (h hz)
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι)
    (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m)
    (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 *
      (ω (x ≫ nK) a.2 (m 1))⁻¹)
    (fun z => exists_chart (LB.isLB_linComb hL ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1]) (ψ z))
    (fun a m => ((Reg.pull ψ inf_le_right _).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) ⊓ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) a.1 (m 0)
        (fun _ hz => hz.1.1) fun _ hz => w₀ _ hz.2).1).pow _)).mul
      (hω.reg nK _ a.2 (m 1) (by rw [hnj]; exact fun _ hz => hz.1.2) (by rw [hnψ]; exact fun _ hz => w₁ _ hz.2)).2)
    (fun a m x _ ha hm => mul_ne_zero (mul_ne_zero (val_unit_ne_zero (x ≫ ψ) (U := LB.wchart L ![𝟙 X, nX] m) hm _)
      (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => (ha hz).1) fun _ hz => w₀ _ (hm hz))))
      (inv_ne_zero (hω.ne _ _ _ (l₁ ha) (m₁ hm))))
    (fun a m m' x _ ha hm hm' => by
      have hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) := fun _ hz => w₀ _ (hm hz)
      have hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0) := fun _ hz => w₀ _ (hm' hz)
      have e := (gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _
        (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))
      rw [Fin.prod_univ_two] at e
      change valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val =
        tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) *
        valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e
      rw [Category.comp_id, ← eψ, zpow_neg_one,
        show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]] at e
      beta_reduce
      rw [e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀',
        ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]
      ring)
    (fun a a' => by
      have e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1 :=
        inf_le_inf inf_le_left inf_le_left
      have e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2) :=
        fun _ hz => ⟨hz.1.2, hz.2.2⟩
      refine ⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ),
        fun m x _ ha ha' hm => ?_⟩
      have hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2)) :=
        fun _ hz => ⟨ha hz, ha' hz⟩
      have v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1 := valR_res _ e₁ hh _
      have v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2 := by
        rw [ej]
        exact val_res_pull _ nH e₂ hh _
      beta_reduce
      rw [Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one,
        hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz),
        hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]
      ring)
  refine ⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩)
    fun _ hz => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact hm hz
  · exact hm' hz

theorem norm_const_sec : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (Y : Scheme.{0}) (π : Y ⟶ X) (ψ' : HK ⟶ Y), ψ' ≫ π = ψ → ∀ (N : ℕ) (J : Type) [Fintype J] (s : J → (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (N : ℤ))).Sec) (t : J → (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 H) (fun _ => (N : ℤ))).Sec) (b : Matrix J J K), (∀ (x : Sp (PadicAlgCl p) ⟶ HK) v, x ≫ q = spMap σ → Crd _ s (x ≫ ψ') v → Crd _ t (x ≫ j) ((b.map σ).mulVec v)) → (∀ (c : Sp (OO p) ⟶ H) w, c ≫ f = spMap jV → Crd _ t c w → ∃ i, IsUnit (w i)) → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l : M.ι) (m : L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → IsGreatest (Set.range fun i => ‖(b.map σ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) (fun _ => m)) ((s i).f fun _ => m)) i * ω x l m ^ N‖) κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim
  subst hψ
  let v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p := fun x m i =>
    valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)
  let w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p := fun x l i =>
    valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)
  have wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l := fun l i =>
    (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)
  have wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0 :=
    fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero
  have hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i,
      (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i := by
    intro x m m' hm hm' i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := (sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm)
      (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.assoc] at e
    rw [mul_left_comm]
    exact congrArg _ e
  have hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i := by
    intro x l l' hl hl' i
    have e := (sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl)
      (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.comp_id] at e
    exact e
  have key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m →
      ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i := by
    intro x l m hx hl hm
    have h₁ := hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩
    obtain ⟨c, hc⟩ := crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l)
      ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁
    exact ⟨c, c.ne_zero, hc⟩
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι
    (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m)
    (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹)
    (fun z => exists_chart hL _)
    (fun a m => ((Reg.sum fun k => (Reg.const (b a.1 k)).mul (Reg.pull ψ' (U := LB.wchart L (fun _ : Fin 1 => π) fun _ => m)
        (W := j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m)
        (fun _ hz => Set.mem_iInter.2 fun _ => hz.2) ((s k).f fun _ => m))).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m) a.2 m (fun _ hz => wl _ _ hz.1) fun _ hz => hz.2).1).pow _)).mul
      (Reg.inv_basicOpen j _ inf_le_left))
    (fun a m x hx ha hm => by
      obtain ⟨c, hc, e⟩ := key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm
      exact mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha)))
        (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))
    (fun a m m' x _ ha hm hm' => by
      beta_reduce
      rw [hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]
      ring)
    (fun a a' => ⟨1, fun m x hx ha ha' hm => by
      have hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2 := fun _ hz => wl _ _ (ha hz)
      have hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2 := fun _ hz => wl _ _ (ha' hz)
      obtain ⟨c, -, e⟩ := key x a.2 m hx hl hm
      have h₁ := wne ha
      have h₂ := wne ha'
      beta_reduce
      rw [valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2))
        (le_inf ha ha'), Units.val_one, map_one, e, e,
        hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]
      field_simp⟩)
  refine ⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩
  have hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l := fun _ hz => Set.mem_iInter.2 fun _ => hl hz
  obtain ⟨i₀, hi₀⟩ := hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩
  have hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p) := fun i => by
    rw [hx]
    exact (valR_spMap (OO p).subtype c _ hlw).2 _
  have hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1 := fun i => by
    rw [hwc]
    exact (mem_OO_iff _).1 (Subtype.prop _)
  have h1 : ‖w (x ≫ j) l i₀‖ = 1 := by
    obtain ⟨d, hd⟩ := hi₀.exists_right_inv
    have e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1 := by
      rw [hwc]
      exact congrArg Subtype.val hd
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    exact le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  obtain ⟨d, -, e⟩ := key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm
  have h₀ := h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm
  have hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖ := fun i => by
    rw [← h₀]
    simp only [e, norm_mul, norm_inv, h1]
    ring
  refine ⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))

end GlobalTheory.ZH.FrameNorm
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

section Grp
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pow_comm (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (𝟙 G' ^ n).left ≫ φ = φ ≫ (𝟙 G ^ n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ (𝟙 G ^ n) = pushHom h G' (𝟙 G') ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e₂] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem eSec_comm (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem comp_pow_left {T : Over S} (x : T ⟶ G) (n : ℕ) (h : x ^ n = 1) :
    x.left ≫ (𝟙 G ^ n).left = T.hom ≫ eSec G := by
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, h]
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem eSec_pow (n : ℕ) : eSec G ≫ (𝟙 G ^ n).left = eSec G := by
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have := comp_pow_left (G := G) η[G] n (by rw [← e₁, one_pow])
  exact this.trans (Category.id_comp _)

end Grp

section Corr
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem corr_val {L : LB X} {I I' : Type} [Fintype I] [Fintype I'] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    {φ' : I' → (Y ⟶ X)} {ε' : I' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (x : Sp C ⟶ Y) (Jc : (Y ⟶ X) → L.ι)
    (hφ : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (Jc (φ k))) (hφ' : ∀ k, ⊤ ≤ (x ≫ φ' k) ⁻¹ᵁ L.U (Jc (φ' k))) :
    valR x (LB.wchart L φ fun k => Jc (φ k)) (t.s fun k => Jc (φ k)).val =
      valR x (LB.wchart L φ' fun k => Jc (φ' k)) (t'.s fun k => Jc (φ' k)).val := by
  have hh : ⊤ ≤ x ⁻¹ᵁ ((LB.wchart L φ fun k => Jc (φ k)) ⊓ LB.wchart L φ' fun k => Jc (φ' k)) :=
    fun _ hz => ⟨le_wchart hφ hz, le_wchart hφ' hz⟩
  have e := congrArg (fun u : Γ(Y, _)ˣ => valR x _ u.val)
    (h _ _ (fun _ _ e => congrArg Jc e) (fun _ _ e => congrArg Jc e) fun _ _ e => congrArg Jc e)
  exact (valR_res x inf_le_left hh _).symm.trans (e.trans (valR_res x inf_le_right hh _))

theorem mulGen_val (L : LB X) {I I' : Type} [Fintype I] [Fintype I'] (φ : I → (Y ⟶ X)) (ε : I → ℤ)
    (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (x : Sp C ⟶ Y) (j : I ⊕ I' → L.ι) (h : ∀ k, ⊤ ≤ (x ≫ Sum.elim φ φ' k) ⁻¹ᵁ L.U (j k)) :
    valR x (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      valR x (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)).val *
        valR x (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)).val :=
  (valR_mul x _ (le_wchart h) _ _).trans
    (congrArg₂ (· * ·) (valR_res x _ (le_wchart h) _) (valR_res x _ (le_wchart h) _))

theorem pullGen_val {Z : Scheme.{0}} (L : LB X) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) (x : Sp C ⟶ Z) (j : I → L.ι)
    (h : ∀ k, ⊤ ≤ (x ≫ g ≫ φ k) ⁻¹ᵁ L.U (j k)) :
    valR x (LB.wchart L (fun k => g ≫ φ k) j) ((LB.pullGen L φ ε t g).s j).val =
      valR (x ≫ g) (LB.wchart L φ j) (t.s j).val :=
  val_res_pull x g _ (le_wchart h) _

theorem exists_chart_pt {R : Type} [CommRing R] [IsLocalRing R] {L : LB X} (hL : L.IsLB) (x : Sp R ⟶ X) :
    ∃ l, ⊤ ≤ x ⁻¹ᵁ L.U l := by
  obtain ⟨l, hl⟩ := exists_chart hL (x (IsLocalRing.closedPoint R))
  exact ⟨l, (top_le_iff x _).2 hl⟩

variable {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (y : Sp C ⟶ S)

def rigVal (m : P.L.ι) : C :=
  valR y (LB.wchart P.L (fun _ : PUnit => eSec P.A) fun _ => m) (rig.s fun _ => m).val

theorem torsFrame_val {n : ℕ} {a : baseOver S ⟶ P.A} {τ} (h : IsTorsFrame P rig n a τ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (𝟙 P.A ^ n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      (∀ m, ⊤ ≤ (y ≫ eSec P.A) ⁻¹ᵁ P.L.U m →
        valR (y ≫ eSec P.A) (LB.wchart P.L ![𝟙 P.A.left, (𝟙 P.A ^ n).left] fun _ => m) (α.s fun _ => m).val =
          rigVal P rig y m ^ n ^ 2 * (rigVal P rig y m)⁻¹) ∧
      ∃ m : Fin 2 → P.L.ι, ⊤ ≤ (y ≫ a.left) ⁻¹ᵁ P.L.U (m 0) ∧ ⊤ ≤ (y ≫ eSec P.A) ⁻¹ᵁ P.L.U (m 1) ∧
        valR y (LB.wchart P.L (fun _ : Fin 1 => a.left) fun _ => m 0) (τ.s fun _ => m 0).val ^ n ^ 2 =
          valR (y ≫ a.left) (LB.wchart P.L ![𝟙 P.A.left, (𝟙 P.A ^ n).left] m) (α.s m).val *
            rigVal P rig y (m 1) := by
  obtain ⟨hn, -, α, hα, h₀, h₁⟩ := h
  refine ⟨α, hα, fun m hm => ?_, ?_⟩
  · have hk : ∀ k, ⊤ ≤ (y ≫ eSec P.A ≫ ![𝟙 P.A.left, (𝟙 P.A ^ n).left] k) ⁻¹ᵁ P.L.U m := by
      intro k
      fin_cases k
      · exact hm
      · show ⊤ ≤ (y ≫ eSec P.A ≫ (𝟙 P.A ^ n).left) ⁻¹ᵁ P.L.U m
        rwa [eSec_pow]
    have hk' : ∀ k, ⊤ ≤ (y ≫ Sum.elim (fun _ : PUnit => eSec P.A) (fun _ : PUnit => eSec P.A) k) ⁻¹ᵁ P.L.U m := by
      rintro (k | k) <;> exact hm
    have e := corr_val h₀ y (fun _ => m) hk hk'
    refine (pullGen_val _ _ _ α _ y _ hk).symm.trans (e.trans ((mulGen_val _ _ _ _ _ _ _ y _ hk').trans ?_))
    have hw : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (fun _ : PUnit => eSec P.A) fun _ => m := le_wchart fun _ => hm
    refine congrArg₂ (· * ·) ((val_zpow y hw _ _).trans ?_) ?_
    · rw [← zpow_natCast, Nat.cast_pow]
      rfl
    · rw [← zpow_neg_one]
      exact (congrArg (fun u : Γ(S, _)ˣ => valR y _ u.val) (zpow_neg_one _).symm).trans (val_zpow y hw _ _)
  · choose Jc hJc using fun χ : S ⟶ P.A.left => exists_chart_pt P.isLB (y ≫ χ)
    have e := corr_val h₁ y Jc (fun _ => hJc _) fun _ => hJc _
    have e₀ : a.left ≫ 𝟙 P.A.left = a.left := Category.comp_id _
    have e₁ : a.left ≫ (𝟙 P.A ^ n).left = 𝟙 S ≫ eSec P.A := comp_pow_left a n hn
    have hm : ⊤ ≤ (y ≫ eSec P.A) ⁻¹ᵁ P.L.U (Jc (𝟙 S ≫ eSec P.A)) := hJc (𝟙 S ≫ eSec P.A)
    refine ⟨fun k => Jc (a.left ≫ ![𝟙 P.A.left, (𝟙 P.A ^ n).left] k), hJc (a.left ≫ 𝟙 _), ?_, ?_⟩
    · show ⊤ ≤ (y ≫ eSec P.A) ⁻¹ᵁ P.L.U (Jc (a.left ≫ (𝟙 P.A ^ n).left))
      rwa [e₁]
    · have e' := e.trans (mulGen_val _ _ _ _ _ _ _ y _ fun _ => hJc _)
      show valR y (LB.wchart P.L (fun _ : Fin 1 => a.left) fun _ => Jc (a.left ≫ 𝟙 _))
        (τ.s fun _ => Jc (a.left ≫ 𝟙 _)).val ^ n ^ 2 = _ * rigVal P rig y (Jc (a.left ≫ (𝟙 P.A ^ n).left))
      rw [e₀, e₁]
      refine Eq.trans ?_ (e'.trans (congrArg₂ (· * ·) (pullGen_val _ _ _ α _ y _ fun _ => hJc _) ?_))
      · refine Eq.trans ?_ (val_zpow y (le_wchart fun _ => hJc _) _ _).symm
        rw [← zpow_natCast, Nat.cast_pow]
      · refine (val_zpow y (le_wchart fun _ => hJc _) _ _).trans ((zpow_one _).trans ?_)
        refine (val_res_pull y _ _ (le_wchart fun _ => hJc _) _).trans ?_
        exact congrArg (fun z => valR z _ _) (Category.comp_id y)

end Corr

section Main
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem isLocalHom_j : IsLocalHom u.j := ⟨fun a ha => by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ a) * (b : PadicAlgCl p) = 1 :=
    congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at hb'
  obtain ⟨c, hc⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) a)⁻¹).1 (by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ h0, map_one]⟩

theorem gPt_j : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_y : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ spMap u.yK = spMap y₀ := by
  rw [← Spec.map_comp]
  exact congrArg spMap u.fac

theorem four_le (ρ : S.Real) : 4 ≤ S.N := by
  rw [ρ.N_eq]
  have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  nlinarith

theorem ev_val (a : S.Gam) (m : ρ.P.L.ι) (hm : ⊤ ≤ (spMap y₀ ≫ (ρ.pt a).left) ⁻¹ᵁ ρ.P.L.U m) (i : S.J) :
    valR (spMap y₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left)
        (LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) fun _ => m) ((ρ.s i).f fun _ => m) =
      y₀ ⟨S.ev a i, S.ev_mem a i⟩ * valR (spMap y₀) (LB.wchart ρ.P.L (fun _ : Fin 1 => (ρ.pt a).left) fun _ => m)
        ((ρ.fr a).s fun _ => m).val ^ S.N := by
  have hw : ⊤ ≤ spMap y₀ ⁻¹ᵁ LB.wchart ρ.P.L (fun _ : Fin 1 => (ρ.pt a).left) fun _ => m := le_wchart fun _ => hm
  have e := congrArg (valR (spMap y₀) _) (ρ.ev_val i a fun _ => m)
  refine (GlobalTheory.Points.valR_appLE (spMap y₀) _ (val_le _ _ _ _) hw _).symm.trans (e.trans ?_)
  refine (valR_mul _ _ hw _ _).trans (congrArg₂ (· * ·) ?_ ?_)
  · exact (valR_res _ le_top hw _).trans (GlobalTheory.Points.valR_specMap (CommRingCat.ofHom y₀) _)
  · exact (val_zpow _ hw _ _).trans (zpow_natCast _ _)

theorem alg₁ {C : Type} [Field C] (w r : C) (hw : w ≠ 0) (hr : r ≠ 0) (k : ℕ) :
    r ^ k * r⁻¹ * w ^ k * w⁻¹ * (w * r) = (w * r) ^ k := by
  rw [mul_pow]
  field_simp

theorem alg₂ {C : Type} [Field C] (v a r w : C) (hw : w ≠ 0) : v * (a * r) = a * v * w⁻¹ * (w * r) := by
  field_simp

end Main

theorem exists_pos_isGreatest_norm_mulVec_on_ker : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → ∃ κ : ℝ, 0 < κ ∧ ∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b hbig _ hlink
  have hsm : Smooth u.G.hom := u.U.smooth
  have hsep : IsSeparated u.G.hom := u.U.separated
  have hgi : GeometricallyIntegral u.G.hom :=
    haveI := u.semi
    GlobalTheory.geometricallyIntegral_of_isSemiAbelian u.G
  have hmon := u.U.gen_hom
  let GK := (Over.pullback (jK u.V)).obj u.G
  let τ := algebraMap (FractionRing u.V) (PadicAlgCl p)
  let j : GK.left ⟶ u.G.left := pullback.fst u.G.hom (jK u.V)
  let ψ : GK.left ⟶ ρ.P.A.left := u.U.gen.hom.left ≫ u.φ
  have gj : IsGrpPullback GK u.G (jK u.V) j := isGrpPullback_pullback u.G (jK u.V)
  have gψ : IsGrpPullback GK ρ.P.A (spMap u.yK) ψ :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have iso : LBIso (ρ.P.L.pull ψ) (u.U.LG.L.pull j) :=
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso u.lb u.U.gen.hom.left rfl).symm.trans (pull_isLB ρ.P.isLB _)
      (pull_isLB u.A.isLB _) (pull_isLB u.U.LG.isLB _) u.U.ext
  obtain ⟨ω, hω⟩ := exists_isoVal GK.hom τ ρ.P.isLB u.U.LG.isLB iso
  let ψ' : GK.left ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    (lift (Over.homMk (GK.hom ≫ spMap u.yK) (Category.comp_id _) : Over.mk (GK.hom ≫ spMap u.yK) ⟶ baseOver _)
      (Over.homMk ψ gψ.1.w)).left
  have hψ' : ψ' ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = ψ := congrArg Over.Hom.left (lift_snd _ _)
  have hψ'' : ψ' ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = GK.hom ≫ spMap u.yK := congrArg Over.Hom.left (lift_fst _ _)
  obtain ⟨κ, hκ, hS⟩ := norm_const_sec p u.V (FractionRing u.V) τ u.j (fun _ => rfl) (isLocalHom_j u) _ _ u.G.hom j GK.hom
    hsm hgi gj.1 _ _ _ ψ ω ρ.P.isLB u.U.LG.isLB hω _ _ ψ' hψ' S.N S.J ρ.s σ b
    (fun x v hx hv => hlink (Over.homMk x hx) v ⟨x ≫ ψ', by rw [Category.assoc, hψ']; rfl, hv⟩)
    (fun c w hc hw => by
      obtain ⟨⟨i, -, hi⟩, -⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords hLL.1 hLL.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ _ σ cls md
        ⟨four_le ρ, hbig.1, hbig.2.1⟩ c w hc hw
      exact ⟨i, hi⟩)

  let c₀ : Sp (OO p) ⟶ u.G.left := spMap u.j ≫ eSec u.G
  let x₀ : Sp (PadicAlgCl p) ⟶ GK.left := spMap τ ≫ eSec GK
  have hc₀ : c₀ ≫ u.G.hom = spMap u.j := by
    rw [Category.assoc]
    exact (congrArg _ (Over.w η[u.G])).trans (Category.comp_id _)
  have hx₀q : x₀ ≫ GK.hom = spMap τ := by
    rw [Category.assoc]
    exact (congrArg _ (Over.w η[GK])).trans (Category.comp_id _)
  have hx₀j : x₀ ≫ j = gPt p ≫ c₀ := by
    rw [Category.assoc, eSec_comm gj, ← Category.assoc, ← gPt_j, Category.assoc]
  have hx₀ψ : x₀ ≫ ψ = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, eSec_comm gψ, ← Category.assoc, spMap_y]
  obtain ⟨l₀, hl₀⟩ := exists_chart_pt u.U.LG.isLB c₀
  have hl₀' : ⊤ ≤ (x₀ ≫ j) ⁻¹ᵁ u.U.LG.L.U l₀ := by
    rw [hx₀j]
    exact fun _ _ => hl₀ trivial
  obtain ⟨m₀, hm₀⟩ := exists_chart_pt ρ.P.isLB (spMap y₀ ≫ eSec ρ.P.A)
  have hrig : ∀ m, ⊤ ≤ (spMap y₀ ≫ eSec ρ.P.A) ⁻¹ᵁ ρ.P.L.U m →
      ω x₀ l₀ m * rigVal ρ.P ρ.rig (spMap y₀) m = ω x₀ l₀ m₀ * rigVal ρ.P ρ.rig (spMap y₀) m₀ := fun m hm => by
    have e := (gen_val ρ.rig_gen (x := spMap y₀) (i := fun _ => m) (j := fun _ => m₀) (le_wchart fun _ => hm)
      (le_wchart fun _ => hm₀)).trans (congrArg (· * _) (tv_linComb _ _ _ (fun _ => hm) fun _ => hm₀))
    rw [← hω.right x₀ l₀ m m₀ hl₀' (hx₀ψ ▸ hm) (hx₀ψ ▸ hm₀), _root_.mul_assoc, hx₀ψ]
    refine congrArg _ (e.trans ?_)
    exact congrArg₂ (· * ·) (by simp) rfl
  have hω₀ : ω x₀ l₀ m₀ ≠ 0 := hω.ne _ _ _ hl₀' (hx₀ψ ▸ hm₀)
  have hr₀ : rigVal ρ.P ρ.rig (spMap y₀) m₀ ≠ 0 := val_unit_ne_zero _ (le_wchart fun _ => hm₀) _
  set κ₁ := ‖ω x₀ l₀ m₀ * rigVal ρ.P ρ.rig (spMap y₀) m₀‖ with hκ₁
  have hκ₁0 : 0 < κ₁ := norm_pos_iff.2 (mul_ne_zero hω₀ hr₀)
  refine ⟨κ / κ₁ ^ S.N, div_pos hκ (pow_pos hκ₁0 _), fun a ha => ?_⟩
  obtain ⟨h, z, hh, hzj, hzq, hzψ⟩ := (l.ker_iff a).1 ha
  let n := S.r * S.N
  have hn : n ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  let c : Sp (OO p) ⟶ u.G.left := spMap u.j ≫ h
  let x : Sp (PadicAlgCl p) ⟶ GK.left := spMap τ ≫ z
  have hc : c ≫ u.G.hom = spMap u.j := by rw [Category.assoc, hh, Category.comp_id]
  have hxq : x ≫ GK.hom = spMap τ := (Category.assoc _ _ _).trans ((congrArg _ hzq).trans (Category.comp_id _))
  have hxj : x ≫ j = gPt p ≫ c := by
    rw [Category.assoc, hzj, ← Category.assoc, ← gPt_j, Category.assoc]
  have hxψ : x ≫ ψ = spMap y₀ ≫ (ρ.pt a).left := by
    rw [Category.assoc, hzψ, ← Category.assoc, spMap_y]
  have hxψn : x ≫ ψ ≫ (𝟙 ρ.P.A ^ n).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [← Category.assoc, hxψ, Category.assoc, comp_pow_left _ _ (ρ.fr_tors a).1]
    rfl
  have hxn : x ≫ (𝟙 GK ^ n).left = x₀ := by
    apply gψ.1.hom_ext
    · rw [Category.assoc, pow_comm gψ, hxψn, hx₀ψ]
    · rw [Category.assoc, Over.w, hxq, hx₀q]
  have hcn : c ≫ (𝟙 u.G ^ n).left = c₀ := by
    have : IsDominant (gPt p) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
    refine ext_of_isDominant_of_isSeparated u.G.hom ?_ (gPt p) ?_
    · rw [Category.assoc, Over.w, hc, hc₀]
    · rw [← Category.assoc, ← hxj, Category.assoc, ← pow_comm gj, ← Category.assoc, hxn, hx₀j]
  have hxψ' : x ≫ ψ' = spMap y₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg _ hψ'').trans ?_)
      rw [← Category.assoc, hxq, spMap_y, Category.assoc]
      exact ((congrArg (fun z => spMap y₀ ≫ Over.Hom.left z) (lift_fst (𝟙 _) (ρ.pt a))).trans (Category.comp_id _)).symm
    · refine (Category.assoc _ _ _).trans ((congrArg _ hψ').trans (hxψ.trans ?_))
      rw [Category.assoc]
      exact (congrArg (fun z => spMap y₀ ≫ Over.Hom.left z) (lift_snd (𝟙 _) (ρ.pt a))).symm
  obtain ⟨α, hα, hα₀, m, hm, hm', hαa⟩ := torsFrame_val ρ.P ρ.rig (spMap y₀) (ρ.fr_tors a)
  obtain ⟨κ', -, hT⟩ := norm_const_gen p u.V (FractionRing u.V) τ u.j (fun _ => rfl) (isLocalHom_j u) _ _ u.G.hom j GK.hom
    hsm hgi gj.1 _ _ _ ψ ω ρ.P.isLB u.U.LG.isLB hω _ _ _ (pow_comm gj n) (pow_comm gψ n) n α hα
  obtain ⟨l₁, hl₁⟩ := exists_chart_pt u.U.LG.isLB c
  have hx₀n : x₀ ≫ (𝟙 GK ^ n).left = x₀ := by rw [Category.assoc, eSec_pow]
  have h₀ := hT c₀ x₀ l₀ l₀ (fun _ => m₀) hc₀ hx₀j hx₀q hl₀ (by rwa [Category.assoc, eSec_pow]) (hx₀ψ ▸ hm₀)
    (by rwa [← Category.assoc, hx₀ψ, Category.assoc, eSec_pow])
  have h₁ := hT c x l₁ l₀ m hc hxj hxq hl₁ (hcn ▸ hl₀) (hxψ ▸ hm) (hxψn ▸ hm')
  rw [hx₀n, hx₀ψ, hα₀ m₀ hm₀] at h₀
  rw [hxn, hxψ] at h₁
  set e := valR (spMap y₀) (LB.wchart ρ.P.L (fun _ : Fin 1 => (ρ.pt a).left) fun _ => m 0)
    ((ρ.fr a).s fun _ => m 0).val with he
  have hfr : ‖ω x l₁ (m 0) * e‖ = κ₁ := by
    have hω₁ : ω x₀ l₀ (m 1) ≠ 0 := hω.ne _ _ _ hl₀' (hx₀ψ ▸ hm')
    refine (pow_left_inj₀ (norm_nonneg _) hκ₁0.le hn).1 ?_
    have A : κ' * κ₁ = κ₁ ^ n ^ 2 := by
      rw [← h₀, hκ₁, ← norm_mul, ← norm_pow]
      exact congrArg _ (alg₁ _ _ hω₀ hr₀ _)
    rw [← A, ← h₁, hκ₁, ← hrig _ hm', ← norm_mul, ← norm_pow, mul_pow, hαa]
    exact congrArg _ (alg₂ _ _ _ _ hω₁)
  have hG := hS c x l₁ (m 0) hc hxj hxq hl₁ (hxψ ▸ hm)
  have hval : ∀ i, ‖(b.map τ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart ρ.P.L
      (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) fun _ => m 0) ((ρ.s i).f fun _ => m 0)) i *
      ω x l₁ (m 0) ^ S.N‖ = ‖(b.map τ).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖ * κ₁ ^ S.N := fun i => by
    rw [← hfr, ← norm_pow, ← norm_mul, hxψ']
    congr 1
    simp only [ev_val a (m 0) hm, Matrix.mulVec, dotProduct, Finset.sum_mul, ← he]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hp := pow_pos hκ₁0 S.N
  obtain ⟨⟨i, hi⟩, hub⟩ := hG
  refine ⟨⟨i, ?_⟩, ?_⟩
  · exact (eq_div_iff hp.ne').2 ((hval i).symm.trans hi)
  · rintro _ ⟨k, rfl⟩
    exact (le_div_iff₀ hp).2 ((hval k).symm.trans_le (hub ⟨k, rfl⟩))

end GlobalTheory.ZH.FrameNorm
end
