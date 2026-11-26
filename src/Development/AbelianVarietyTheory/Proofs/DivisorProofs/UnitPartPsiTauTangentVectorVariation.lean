module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreEqDerivationIdentification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleSectionUnitAtClosedPointTorusChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftedSectionDivMonomialOverChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem val_zpow_eps {S : Type} [CommRing S] (ee : S) (hee : ee * ee = 0) (E : Sˣ) (a : S) (hE : E.val = 1 + ee * a)
    (n : ℤ) : (E ^ n).val = 1 + (n : S) * ee * a := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, hE]; push_cast; linear_combination ((n : S) * a * a) * hee
  | pred n ih =>
    have hi : (E⁻¹).val = 1 - ee * a :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hE]; linear_combination (-(a * a)) * hee)
    rw [zpow_sub_one, Units.val_mul, ih, hi]; push_cast; linear_combination ((n : S) * a * a) * hee

theorem gs_natCast {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℕ) :
    gs f z O (n : Γ(Y, O)) = n := by
  rw [gs_eq f z O hz, map_natCast, map_natCast]

theorem gs_ofNat {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℕ) [n.AtLeastTwo] :
    gs f z O (OfNat.ofNat n : Γ(Y, O)) = OfNat.ofNat n := by
  rw [gs_eq f z O hz, map_ofNat, map_ofNat]

theorem gs_intCast {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℤ) :
    gs f z O (n : Γ(Y, O)) = n := by
  rw [gs_eq f z O hz, map_intCast, map_intCast]

theorem gs_sum {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) {I : Type} (s : Finset I)
    (a : I → Γ(Y, O)) : gs f z O (∑ i ∈ s, a i) = ∑ i ∈ s, gs f z O (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f z O hz, map_sum]

def cstD {k : Type} [Field k] {Z : Scheme.{0}} (p : Z ⟶ Sp (DualNumber k)) (z : Z) :
    DualNumber k →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom)

theorem gs_cstD {k : Type} [Field k] {Z : Scheme.{0}} (p : Z ⟶ Sp (DualNumber k)) (z : Z) (a : DualNumber k) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom a) = cstD p z a :=
  gs_eq p z ⊤ trivial _

theorem gs_spMap {A' B'' : Type} [CommRing A'] [CommRing B''] {Z : Scheme.{0}} (p : Z ⟶ Sp B'') (g : A' →+* B'')
    (z : Z) (a : A') :
    gs (p ≫ spMap g) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom a) =
      gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B'')).inv.hom (g a)) := by
  rw [← gs_pull p (spMap g) z ⊤ trivial]
  have := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  rfl

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem prod_one_add_eps {S : Type} [CommRing S] (ee : S) (hee : ee * ee = 0) {I : Type} (s : Finset I) (b : I → S) :
    ∏ j ∈ s, (1 + ee * b j) = 1 + ee * ∑ j ∈ s, b j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (b a * ∑ j ∈ s, b j) * hee

theorem zpow_sum_u {G I : Type} [CommGroup G] (a : G) (s : Finset I) (f : I → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]

theorem prod3 {G : Type} [CommGroup G] (f g h : Fin 4 → G) (n : Fin 4 → ℤ) :
    ∏ j, (f j * (g j)⁻¹ * h j) ^ n j = (∏ j, f j ^ n j) * (∏ j, g j ^ n j)⁻¹ * ∏ j, h j ^ n j := by
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem final_alg {S : Type} [CommRing S] (T1 T1i T2 s d K Sg C H E e' : S) (hU : T1 * T1i = 1)
    (hH : H * (2 * e') = 1) (hEE : E * E = 0) :
    T1 * (s + E * d) * (T2 * T1i * (K * (1 + E * Sg))) =
      K * (1 + -C * E) * (T2 * s + H * E * (T2 * (2 * e' * (d + s * (Sg + C))))) := by
  linear_combination (T2 * K * (s + E * d) * (1 + E * Sg)) * hU + (-(T2 * K * E * (Sg * s + d + C * s))) * hH +
    (T2 * K * (d * Sg + 2 * e' * H * C * (d + s * Sg + s * C))) * hEE

theorem gm_pull_g {X X' Y : Scheme.{0}} {L : LB X} (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem core {R : Type} [CommRing R] {k : Type} [Field k] [CharZero k] (A : Over (Sp R)) (L : LB A.left)
    (B' : Over (Sp (DualNumber k))) (π₁ π₂ : B'.left ⟶ A.left) (hpt : ∀ b : B'.left, π₁ b = π₂ b)
    (A₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (pr : B'.left ⟶ A₀.left) (hpr : pr ≫ m₀ = π₂)
    (hpr' : pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    {J' : Type} (V : J' → A.left.Opens) (jj : J' → L.ι) (hV : ⨆ i, V i = ⊤) (hVU : ∀ i, V i ≤ L.U (jj i))
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hA : ∀ (W : A.left.Opens) (f : Γ(A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W))
    (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hw : w.IsGen) (κ : (DualNumber k)ˣ)
    (hκ : ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val *
      (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)))
    (e : ℕ) (he : 1 ≤ e) (fam : Fin 4 → (A.left ⟶ A.left)) (es : Fin 4 → ℤ) (hes : ∑ j, es j = e)
    (σ σ' : LB.Sec (LB.LinComb L fam es)) (T : Fin 4 → (A₀.left ⟶ A₀.left)) (hT : ∀ j, T j ≫ m₀ = m₀ ≫ fam j)
    (c0 : k)
    (hF : ∀ (i : Fin 4 → J') (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ LB.wchart L fam (fun j => jj (i j)) →
      (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => jj (i j))) O =
        2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => jj (i j)))) O + pbT m₀ (σ.f (fun j => jj (i j))) O *
          (∑ j, ((es j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O c0)))
    (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left))
    (hxs : ∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ fam j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ fam j ∧ xs j ≫ B'.hom = x ≫ B'.hom)
    (hxpr : ∀ j, xs j ≫ pr = (x ≫ pr) ≫ T j) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    sval σ (x ≫ π₁) z J *
        (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ es j).val =
      gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
        ((κ ^ e).val * (1 + TrivSqZeroExt.inr (-c0)))) *
      (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
        (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  have hpz : (x ≫ π₁) z = (x ≫ π₂) z := hpt (x z)
  choose i hi using fun j : Fin 4 =>
    TopologicalSpace.Opens.mem_iSup.1 (show ((x ≫ π₂) ≫ fam j) z ∈ ⨆ i, V i by rw [hV]; trivial)
  set t : Fin 4 → L.ι := fun j => jj (i j) with ht
  have hmem₂ : (x ≫ π₂) z ∈ LB.wchart L fam t := Set.mem_iInter.2 fun j => hVU (i j) (hi j)
  have hmem₁ : (x ≫ π₁) z ∈ LB.wchart L fam t := by rw [hpz]; exact hmem₂

  have sa : sval σ (x ≫ π₁) z J = (trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t).val *
      gs (x ≫ π₁) z (LB.wchart L fam t) (σ.f t) := sec_trans σ (x ≫ π₁) z (hJ.mem fam _) hmem₁
  have sb : sval σ (x ≫ π₂) z J = (trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t).val *
      gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) := sec_trans σ (x ≫ π₂) z (hJ.mem fam _) hmem₂
  have sc : sval σ' (x ≫ π₂) z J = (trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t).val *
      gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) := sec_trans σ' (x ≫ π₂) z (hJ.mem fam _) hmem₂

  set E : Z.presheaf.stalk z := cstD (x ≫ B'.hom) z DualNumber.eps with hE
  have hEE : E * E = 0 := by rw [hE, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have le12 : ∀ W : A.left.Opens, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := fun W b hb => by
    show π₁ b ∈ W; rw [hpt]; exact hb
  have le2p : ∀ W : A.left.Opens, π₂ ⁻¹ᵁ W ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W b hb => by
    show m₀ (pr b) ∈ W; rw [← Scheme.Hom.comp_apply, hpr]; exact hb

  have hA' : gs (x ≫ π₁) z (LB.wchart L fam t) (σ.f t) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) +
      E * gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) := by
    have h := congrArg (gs x z (π₂ ⁻¹ᵁ LB.wchart L fam t)) (hA (LB.wchart L fam t) (σ.f t))
    have hxz : x z ∈ π₂ ⁻¹ᵁ LB.wchart L fam t := hmem₂
    erw [gs_pbT x π₁ z (le12 (LB.wchart L fam t)) hxz] at h
    rw [gs_add _ _ _ hxz, gs_mul _ _ _ hxz] at h
    erw [gs_pbT x π₂ z le_rfl hxz, gs_pbT x pr z (le2p (LB.wchart L fam t)) hxz] at h
    rw [GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hxz, gs_cstD] at h
    exact h

  have hPG := (isGen_iff w).1 hw
  have p2 : ∀ j, (xs j ≫ π₂) z = ((x ≫ π₂) ≫ fam j) z := fun j => by rw [(hxs j).2.1]
  have p1 : ∀ j, (xs j ≫ π₁) z = ((x ≫ π₂) ≫ fam j) z := fun j => by
    rw [(hxs j).1]; show fam j ((x ≫ π₁) z) = fam j ((x ≫ π₂) z); rw [hpz]
  have hgw : ∀ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) =
      gm (xs j ≫ π₂) z _ (L.g (J (xs j ≫ π₂)) (t j)) * (gm (xs j ≫ π₁) z _ (L.g (J (xs j ≫ π₁)) (t j)))⁻¹ *
        gw w (xs j) z (t j) (fun _ => t j) := fun j => by
    have h4 : π₁ (xs j z) ∈ L.U (t j) := by
      show (xs j ≫ π₁) z ∈ L.U (t j); rw [p1]; exact hVU _ (hi j)
    have := hPG Z (xs j) z (J (xs j ≫ π₂)) (t j) (fun _ => J (xs j ≫ π₁)) (fun _ => t j) (hJ _)
      (by show (xs j ≫ π₂) z ∈ L.U (t j); rw [p2]; exact hVU _ (hi j)) (mem_pull.2 (hJ _)) (mem_pull.2 h4)
    rw [gm_pull_g π₁ (xs j) z _ _ (hJ _) h4] at this
    exact this
  have hK : ∀ j, (gw w (xs j) z (t j) (fun _ => t j)).val = cstD (x ≫ B'.hom) z κ.val *
      (1 + E * gs ((x ≫ pr) ≫ T j) z (m₀ ⁻¹ᵁ V (i j)) (pb (i j))) := fun j => by
    have hx : xs j z ∈ π₂ ⁻¹ᵁ V (i j) := by show (xs j ≫ π₂) z ∈ V (i j); rw [p2]; exact hi j
    have hle : π₂ ⁻¹ᵁ V (i j) ≤ (L.pull π₂).U (fun _ => t j) ⊓ (L.pull π₁).U (fun _ => t j) := fun b hb =>
      ⟨mem_pull.2 (hVU (i j) (show π₂ b ∈ V (i j) from hb)),
        mem_pull.2 (show π₁ b ∈ L.U (t j) by rw [hpt]; exact hVU (i j) hb)⟩
    have h := congrArg (gs (xs j) z (π₂ ⁻¹ᵁ V (i j))) (hκ (i j))
    erw [gs_rsT _ _ hle hx, gs_unit _ _ _ (hle hx)] at h
    rw [gs_mul _ _ _ hx, GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hx,
      gs_add _ _ _ hx, gs_one _ _ _ hx, gs_mul _ _ _ hx, GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hx] at h
    erw [gs_pbT (xs j) pr z (le2p _) hx] at h
    rw [(hxs j).2.2, hxpr j, gs_cstD, gs_cstD] at h
    exact h

  set O : A₀.left.Opens := m₀ ⁻¹ᵁ LB.wchart L fam t ⊓ T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓
    T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3)) with hO
  have hO1 : O ≤ m₀ ⁻¹ᵁ LB.wchart L fam t :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hO2 : ∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun j => by
    fin_cases j
    · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have cpr : (x ≫ pr) ≫ m₀ = x ≫ π₂ := by rw [Category.assoc, hpr]
  have cT : ∀ j, ((x ≫ pr) ≫ T j) ≫ m₀ = (x ≫ π₂) ≫ fam j := fun j => by
    rw [Category.assoc, hT j, ← Category.assoc, cpr]
  have mT : ∀ j, ((x ≫ pr) ≫ T j) z ∈ m₀ ⁻¹ᵁ V (i j) := fun j => by
    show (((x ≫ pr) ≫ T j) ≫ m₀) z ∈ V (i j); rw [cT]; exact hi j
  have hxO : (x ≫ pr) z ∈ O := by
    refine ⟨⟨⟨⟨?_, mT 0⟩, mT 1⟩, mT 2⟩, mT 3⟩
    show ((x ≫ pr) ≫ m₀) z ∈ LB.wchart L fam t; rw [cpr]; exact hmem₂
  set a : Fin 4 → Z.presheaf.stalk z := fun j => gs ((x ≫ pr) ≫ T j) z (m₀ ⁻¹ᵁ V (i j)) (pb (i j)) with ha
  have hFz : gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) = 2 * (e : Z.presheaf.stalk z) *
      (gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) + gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) *
        (∑ j, (es j : Z.presheaf.stalk z) * a j + cstD (x ≫ B'.hom) z (algebraMap k (DualNumber k) c0))) := by
    have h := congrArg (gs (x ≫ pr) z O) (hF i O hO1 hO2)
    rw [← ht] at h
    have hterm : ∀ j, gs (x ≫ pr) z O (((es j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O) =
        (es j : Z.presheaf.stalk z) * a j := fun j => by
      rw [gs_mul _ _ _ hxO, gs_intCast _ _ _ hxO, gs_pbT _ _ z (hO2 j) hxO]
    have hc : (x ≫ pr) ≫ A₀.hom = (x ≫ B'.hom) ≫ spMap (algebraMap k (DualNumber k)) := by
      rw [Category.assoc, hpr', Category.assoc]
    have e1 : gs (x ≫ pr) z O (pbT m₀ (σ'.f t) O) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) :=
      (gs_pbT (x ≫ pr) m₀ z hO1 hxO (σ'.f t)).trans (by rw [cpr])
    have e2 : gs (x ≫ pr) z O (pbT m₀ (σ.f t) O) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) :=
      (gs_pbT (x ≫ pr) m₀ z hO1 hxO (σ.f t)).trans (by rw [cpr])
    have e3 : gs (x ≫ pr) z O (rsT (ed _ (σ.f t)) O) =
        gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) := gs_rsT _ _ hO1 hxO _
    rw [e1, gs_mul _ _ _ hxO, gs_mul _ _ _ hxO, gs_ofNat _ _ _ hxO, gs_natCast _ _ _ hxO, gs_add _ _ _ hxO, e3,
      gs_mul _ _ _ hxO, e2, gs_add _ _ _ hxO, gs_sum _ _ _ hxO,
      GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hxO, hc, gs_spMap, gs_cstD] at h
    simp only [hterm] at h
    exact h

  set φ := cstD (x ≫ B'.hom) z with hφ
  have key : ∀ f g : Z ⟶ A.left, f = g → ∀ b : L.ι, gm f z (L.U (J f) ⊓ L.U b) (L.g (J f) b) =
      gm g z (L.U (J g) ⊓ L.U b) (L.g (J g) b) := by rintro f _ rfl b; rfl
  have htr1 : ∏ j, (gm (xs j ≫ π₁) z _ (L.g (J (xs j ≫ π₁)) (t j))) ^ es j =
      trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t :=
    Finset.prod_congr rfl fun j _ => by rw [key _ _ (hxs j).1]
  have htr2 : ∏ j, (gm (xs j ≫ π₂) z _ (L.g (J (xs j ≫ π₂)) (t j))) ^ es j =
      trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t :=
    Finset.prod_congr rfl fun j _ => by rw [key _ _ (hxs j).2.1]
  let κu : (Z.presheaf.stalk z)ˣ := Units.map φ.toMonoidHom κ
  have hκu : ∀ n : ℕ, (κu ^ n).val = φ (κ ^ n).val := fun n => by
    rw [← map_pow]; rfl
  set Ej : Fin 4 → (Z.presheaf.stalk z)ˣ := fun j => κu⁻¹ * gw w (xs j) z (t j) (fun _ => t j) with hEjd
  have hEj : ∀ j, (Ej j).val = 1 + E * a j := fun j => by
    rw [hEjd]
    rw [Units.val_mul, hK j]
    have h1 : (κu⁻¹).val * κu.val = 1 := Units.inv_mul κu
    have h2 : κu.val = φ κ.val := rfl
    rw [← h2]
    linear_combination (1 + E * a j) * h1
  have hKprod : (∏ j, (gw w (xs j) z (t j) (fun _ => t j)) ^ es j).val =
      φ (κ ^ e).val * (1 + E * ∑ j, (es j : Z.presheaf.stalk z) * a j) := by
    have hsplit : ∀ j, gw w (xs j) z (t j) (fun _ => t j) = κu * Ej j :=
      fun j => (mul_inv_cancel_left κu _).symm
    rw [Finset.prod_congr rfl fun j _ => by rw [hsplit j]]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [← zpow_sum_u, hes, zpow_natCast, Units.val_mul, hκu, Units.coe_prod]
    simp only [fun j => val_zpow_eps E hEE _ (a j) (hEj j) (es j)]
    rw [← prod_one_add_eps E hEE Finset.univ (fun j => (es j : Z.presheaf.stalk z) * a j)]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by ring
  have hinr : ∀ r : k, φ (TrivSqZeroExt.inr r) = φ (algebraMap k (DualNumber k) r) * E := fun r => by
    rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul]
  have h2e : (2 * (e : k)) ≠ 0 := by
    have : (e : k) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact mul_ne_zero two_ne_zero this
  have hH : φ (algebraMap k (DualNumber k) (2 * (e : k))⁻¹) * (2 * (e : Z.presheaf.stalk z)) = 1 := by
    have : φ (algebraMap k (DualNumber k) (2 * (e : k))) = 2 * (e : Z.presheaf.stalk z) := by
      simp [map_mul, map_natCast, map_ofNat]
    rw [← this, ← map_mul, ← map_mul, inv_mul_cancel₀ h2e, map_one, map_one]
  have hU : (trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t).val *
      ((trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t)⁻¹).val = 1 := Units.mul_inv _
  rw [gs_cstD, gs_cstD, sa, sb, sc, hA', hFz]
  simp only [hgw]
  rw [prod3, htr1, htr2, Units.val_mul, Units.val_mul, hKprod, map_mul, map_add (f := _), map_one, hinr, hinr]
  simp only [map_neg]
  exact final_alg _ _ _ _ _ _ _ _ _ _ _ hU hH hEE

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

theorem uconn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ (κ : ℕ → (DualNumber k)ˣ) (ℓ : ℕ → P.D.toPre.X →+ k), ∀ (e : ℕ), 1 ≤ e → ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) → ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val = gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom ((κ e).val * (1 + TrivSqZeroExt.inr (ℓ e α)))) * (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hlin hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' hπ₁ hπ₂ hcl hc' w hw
  obtain ⟨A₀, _, m₀, hA₀⟩ : ∃ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left),
      IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ :=
    ⟨_, _, _, isGrpPullback_pullback _ _⟩
  have hcs : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    unfold constHom; rw [← Spec.map_comp]; rfl
  let pr : B'.left ⟶ A₀.left := hA₀.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k))) (by
    rw [hπ₂.1.w, hcs, Category.assoc])
  have hpr : pr ≫ m₀ = π₂ := hA₀.1.lift_fst _ _ _
  have hpr' : pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hA₀.1.lift_snd _ _ _
  have hpt : ∀ b : B'.left, π₁ b = π₂ b := by
    have P0 := IsPullback.of_hasPullback B'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
    have hs : Surjective (pullback.fst B'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) :=
      MorphismProperty.of_isPullback (P := @Surjective) P0.flip GlobalTheory.ConstThickening.surjective_spMap_fst
    intro b
    obtain ⟨b0, rfl⟩ := hs.surj b
    exact congrArg (fun f => f b0) (hcl _ _ _ pullback.condition)
  have key : ∀ e : ℕ, ∃ (κ : (DualNumber k)ˣ) (ℓ : P.D.toPre.X →+ k), 1 ≤ e → ∀ (α : P.D.toPre.X)
      (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left)
      (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧
        xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) →
      ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _
          (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val =
        gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
          (κ.val * (1 + TrivSqZeroExt.inr (ℓ α)))) *
        (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
          (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
    intro e
    by_cases he : 1 ≤ e
    · obtain ⟨V, ed, pb, hconn, -, hF⟩ := GlobalTheory.T.heatOperator_connection_closedFibre E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hB
        hdef hΘ ρ hρ e he A₀ m₀ hA₀
      obtain ⟨hA, κ, hκ⟩ := GlobalTheory.T.connection_closedFibre_eq_derivation_identification k (ChartRing k m d) P.D.toPre.P ρ B' π₁ π₂ hπ₁ hπ₂ hcl A₀ m₀ hA₀ pr hpr
        hpr' V h.j ed pb hconn w hw
      obtain ⟨c, hc⟩ := hF B' π₁ π₂ c' hπ₁ hπ₂ hcl hc' pr hpr hpr' hA
      refine ⟨κ ^ e, -c, fun _ α σ σ' hTA Z x xs hxs z J hJ => ?_⟩
      have hfam : ∀ j, P.D.toPre.famφB α j ≫ P.D.toPre.P.A.hom = P.D.toPre.P.A.hom := by
        intro j
        fin_cases j <;> simp [DegPre.famφB]
      let T : Fin 4 → (A₀.left ⟶ A₀.left) := fun j => hA₀.1.lift (m₀ ≫ P.D.toPre.famφB α j) A₀.hom (by
        rw [Category.assoc, hfam, hA₀.1.w])
      have hT : ∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j := fun j => hA₀.1.lift_fst _ _ _
      have hTh : ∀ j, T j ≫ A₀.hom = A₀.hom := fun j => hA₀.1.lift_snd _ _ _
      have hxpr : ∀ j, xs j ≫ pr = (x ≫ pr) ≫ T j := fun j => hA₀.1.hom_ext
        (by
          have hprA : ∀ {W : Scheme.{0}} (f : P.D.toPre.P.A.left ⟶ W), pr ≫ m₀ ≫ f = π₂ ≫ f := fun f => by
            rw [← Category.assoc, hpr]
          simp only [Category.assoc, hpr, hT, hprA, (hxs j).2.1])
        (by rw [Category.assoc, hpr', ← Category.assoc, (hxs j).2.2, Category.assoc, Category.assoc, hTh,
          Category.assoc, hpr'])
      have hes : ∑ j, DegPre.famε e j = (e : ℤ) := by
        simp [DegPre.famε, Fin.sum_univ_four]
      have := core P.D.toPre.P.A P.D.toPre.P.L B' π₁ π₂ hpt A₀ m₀ pr hpr hpr' V h.j hconn.2.1 hconn.2.2.1 ed pb hA w hw
        κ hκ e he (P.D.toPre.famφB α) (DegPre.famε e) hes σ σ' T hT (c α)
        (fun i O h1 h2 => hc α σ σ' hTA i T hT hTh O h1 h2) Z x xs hxs hxpr z J hJ
      simpa using this
    · exact ⟨1, 0, fun h' => absurd h' he⟩
  choose κ ℓ hκℓ using key
  exact ⟨κ, ℓ, fun e he α σ σ' hT Z x xs hxs z J hJ => hκℓ e he α σ σ' hT Z x xs hxs z J hJ⟩

end GlobalTheory.HeatUConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_symbolZero_eq_connection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ (κ : ℕ → (DualNumber k)ˣ) (ℓ : ℕ → P.D.toPre.X →+ k), ∀ (e : ℕ), 1 ≤ e → ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) → ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val = gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom ((κ e).val * (1 + TrivSqZeroExt.inr (ℓ e α)))) * (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  first | exact @GlobalTheory.HeatUConn.uconn | exact GlobalTheory.HeatUConn.uconn | (intros; apply GlobalTheory.HeatUConn.uconn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitsEval

section Pts
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem c_zero_one : D.c 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  exact (mul_eq_left.1 h.symm)

theorem left_toUnit {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) :
    (toUnit (Over.mk f)).left = f := by
  have := Over.w (toUnit (Over.mk f))
  simpa using this

theorem famφB_pt {T : Scheme.{0}} (f : T ⟶ Spec (CommRingCat.of R)) (a b : D.X) :
    (f ≫ (D.c a).left) ≫ D.famφB b 0 = f ≫ (D.c a).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 1 = f ≫ (D.c (a + b)).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 2 = f ≫ (D.c b).left ∧
    (f ≫ (D.c a).left) ≫ D.famφB b 3 = f ≫ (D.c 0).left := by
  have hf : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, f ≫ x.left = (toUnit (Over.mk f) ≫ x).left := by
    intro x; rw [Over.comp_left, left_toUnit]
  refine ⟨by simp [DegPre.famφB], ?_, ?_, ?_⟩
  · change (f ≫ (D.c a).left) ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c b)).left = _
    have hp : ∀ (x y : D.P.A ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    have hp' : ∀ (x y : 𝟙_ _ ⟶ D.P.A), padd D.P.A x y = x * y := fun _ _ => rfl
    rw [hf, hf, ← Over.comp_left, D.c_add, hp, hp', comp_mul, comp_mul]
    congr 2
    all_goals simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ D.c b).left = _
    rw [hf, hf, ← Over.comp_left]; congr 1; simp [← Category.assoc]
  · change (f ≫ (D.c a).left) ≫ (toUnit D.P.A ≫ η[D.P.A]).left = _
    rw [hf, hf, ← Over.comp_left, c_zero_one]; congr 1
    rw [comp_one, ← Category.assoc, toUnit_unique ((toUnit _ ≫ D.c a) ≫ toUnit _) (toUnit _)]; rfl

end Pts
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

section Ev
variable {A : Type} [CommRing A]

noncomputable def ev (z : Sp A) : A →+* (Sp A).presheaf.stalk z where
  toFun a := gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  map_one' := by rw [map_one, gs_eq _ z ⊤ trivial, map_one, map_one]
  map_mul' a b := by rw [map_mul, gs_mul _ z ⊤ trivial]
  map_zero' := by rw [map_zero, gs_eq _ z ⊤ trivial, map_zero, map_zero]
  map_add' a b := by rw [map_add (f := _), gs_add _ z ⊤ trivial]

theorem ev_apply (z : Sp A) (a : A) : ev z a = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := rfl

theorem gs_spMap {R : Type} [CommRing R] (g : R →+* A) (z : Sp A) (r : R) :
    gs (spMap g) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = ev z (g r) := by
  have h := gs_pull (𝟙 _) (spMap g) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  rw [Category.id_comp] at h
  rw [← h, ev_apply]
  congr 1
  have := congrArg (fun f => f.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact this.symm

theorem gm_unitOn (z : Sp A) (u : Aˣ) : gm (𝟙 _) z ⊤ (unitOn u) = Units.map (ev z).toMonoidHom u := by
  ext
  rw [← gs_unit _ z ⊤ trivial]
  rfl

end Ev
end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem alg_eval {k S : Type} [Field k] [CharZero k] [CommRing S] (φ : DualNumber k →+* S) (e : ℕ) (he : 1 ≤ e)
    (κ ee : (DualNumber k)ˣ) (ℓα ℓμ s : k)
    (hee : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓμ - s))
    (Uρ Uc Wi W0 Wt : Sˣ) (Aρ Ac A'c : S) (hAc : IsUnit Ac) (hWt : Wt * W0 = Wi)
    (hi : Aρ * Wi.val = φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) *
      (Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) * A'c))
    (hii : Uρ.val * Aρ * W0.val = φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) *
      (Uc.val * Ac + φ (TrivSqZeroExt.inr ((2 * (e : k))⁻¹)) *
        (Uc.val * A'c - φ (TrivSqZeroExt.inl (2 * (e : k) * s)) * (Uc.val * Ac)))) :
    Uρ = Wt * Units.map φ.toMonoidHom ee * Uc := by
  set c₁ : k := (2 * (e : k))⁻¹ with hc₁
  have he0 : (2 * (e : k)) ≠ 0 := by
    have : (e : k) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
    exact mul_ne_zero two_ne_zero this
  have hnil : IsNilpotent (φ (TrivSqZeroExt.inr c₁) * A'c) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, pow_two, TrivSqZeroExt.inr_mul_inr, map_zero, zero_mul]
  have hX : IsUnit (Ac + φ (TrivSqZeroExt.inr c₁) * A'c) := by
    first
      | exact hnil.isUnit_add_left_of_commute hAc (Commute.all _ _)
      | exact IsUnit.add_of_isNilpotent hAc hnil
  have hK : IsUnit (φ (κ.val * (1 + TrivSqZeroExt.inr ℓα))) := by
    refine IsUnit.map φ (IsUnit.mul κ.isUnit ?_)
    refine ⟨⟨1 + TrivSqZeroExt.inr ℓα, 1 - TrivSqZeroExt.inr ℓα, ?_, ?_⟩, rfl⟩ <;>
      ext <;> simp
  have hY := hK.mul hX
  have d1 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) -
      φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) *
        φ (TrivSqZeroExt.inl (2 * (e : k) * s)) = φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_mul, hee]
    congr 1
    have h1 : c₁ * (2 * (e : k) * s) = s := by rw [hc₁, ← _root_.mul_assoc, inv_mul_cancel₀ he0, _root_.one_mul]
    ext <;> simp <;> linear_combination (-(TrivSqZeroExt.fst (κ : DualNumber k))) * h1
  have d2 : φ (κ.val * (1 + TrivSqZeroExt.inr (ℓα + (e : k) * ℓμ))) * φ (TrivSqZeroExt.inr c₁) =
      φ ee.val * φ (κ.val * (1 + TrivSqZeroExt.inr ℓα)) * φ (TrivSqZeroExt.inr c₁) := by
    rw [← map_mul, ← map_mul, ← map_mul, hee]
    congr 1
    ext <;> simp <;> ring
  have hWt' : Wt.val * W0.val = Wi.val := by rw [← Units.val_mul, hWt]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  apply hY.mul_right_cancel
  linear_combination (-Uρ.val) * hi + (-(Uρ.val * Aρ)) * hWt' + Wt.val * hii +
    (Wt.val * Uc.val * Ac) * d1 + (Wt.val * Uc.val * A'c) * d2

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem exists_acts' {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) {O : Type} [CommRing O]
    [StarRing O] [Module O Dd.toPre.X] {oa : Dd.toPre.OAct O} (Y : Ray oa) {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left) (hv : ∀ a, IsInv Y.H (v a) (dd a))
    (inst : Algebra ℤ R) (D : @Derivation ℤ R R _ _ _ inst _ _) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D)
    (hb : IsBasic Y h) (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) : ∃ σ', TActs Y h k α σ σ' := by
  obtain rfl : inst = Ring.toIntAlgebra R := Subsingleton.elim _ _
  exact heat_acts_on_terms R Dd O oa Y n v dd hv D h hb k α σ

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem prod_fam {G T : Type} [CommGroup G] (F : T → G) (p : Fin 4 → T) (e : ℕ) :
    ∏ j, F (p j) ^ DegPre.famε e j = F (p 0) ^ ((e : ℤ) - 1) * F (p 1) * (F (p 2))⁻¹ * F (p 3) := by
  simp [Fin.prod_univ_four, DegPre.famε]

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval

theorem mul_inv_mul_cancel_comm {G : Type} [CommGroup G] (a b c d x : G) (e : ℕ) :
    (a ^ ((e : ℤ) - 1) * b * c⁻¹ * d ^ (1 - (e : ℤ))) * (d ^ ((e : ℤ) - 1) * x * x⁻¹ * d) =
      a ^ ((e : ℤ) - 1) * b * c⁻¹ * d := by
  group

end GlobalTheory.UnitsEval

namespace GlobalTheory.UnitsEval


set_option maxHeartbeats 1000000 in
theorem units_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  intro E _ _ _ H k _ _ m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B' _ π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  obtain ⟨κ, ℓ, hconn⟩ := GlobalTheory.T.heatOperator_symbolZero_eq_connection E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' w hw
  refine ⟨fun e mu => (e : k) * ℓ e mu, ?_⟩
  intro mu α n ψ₀ τ₀ hψ hτ
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.exists_bundleSection_unit_at_closedPoint_torusChart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc'
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_shifted_section_div_monomial_over_chart E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' mu α n ψ₀ τ₀ hψ hτ
  refine ⟨max (max e₁ e₂) 1, fun e he ee hee zz J hJ => ?_⟩
  have he1 : 1 ≤ e := le_trans (le_max_right _ _) he
  have hle₁ : e₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) he
  have hle₂ : e₂ ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) he
  obtain ⟨σ, hσu⟩ := he₁ e hle₁ mu α
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨σ', hσσ'⟩ := exists_acts' P.D Y v' dd hdd _ D h hB e α σ
  obtain ⟨hN, hσ₁⟩ := he₂ e hle₂
  obtain ⟨σ₁, σ₁u, hS, hfac, hval⟩ := hσ₁ σ
  obtain ⟨σ₁', σ₁u', hS', hfac', hval'⟩ := hσ₁ σ'
  obtain ⟨σ₁u'', hT'', hval''⟩ := GlobalTheory.T.heatOperator_shift_div_monomial E H k m d t P gam hmono hli hab Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B'
    π₁ π₂ c' hπ₁ hπ₂ hπ12 hc' e he1 mu α (fun i => ((e : ℤ) * n i + gam i mu α).toNat) σ σ' σ₁ σ₁u σ₁' σ₁u'
    hσσ' hS hS' hfac hfac'

  have pts := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap ρ) a b
  have pts' := fun (a b : P.D.toPre.X) => famφB_pt P.D.toPre (spMap (constHom ρ)) a b
  have hB' : ∀ a b : P.D.toPre.X, c' a ≫ B'.hom = c' b ≫ B'.hom := fun a b => by rw [(hc' a).1, (hc' b).1]
  have X0 : ∀ a b : P.D.toPre.X, c' a ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 0 ∧
      c' a ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 0 := fun a b =>
    ⟨by rw [(hc' a).2.1, (pts a b).1], by rw [(hc' a).2.2, (pts' a b).1]⟩
  have X1 : ∀ a b : P.D.toPre.X, c' (a + b) ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 1 ∧
      c' (a + b) ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 1 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.1]⟩
  have X2 : ∀ a b : P.D.toPre.X, c' b ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 2 ∧
      c' b ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 2 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.1], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.1]⟩
  have X3 : ∀ a b : P.D.toPre.X, c' 0 ≫ π₁ = (c' a ≫ π₁) ≫ P.D.toPre.famφB b 3 ∧
      c' 0 ≫ π₂ = (c' a ≫ π₂) ≫ P.D.toPre.famφB b 3 := fun a b =>
    ⟨by rw [(hc' _).2.1, (hc' a).2.1, (pts a b).2.2.2], by rw [(hc' _).2.2, (hc' a).2.2, (pts' a b).2.2.2]⟩
  have hi := hconn e he1 α σ σ' hσσ' _ (c' mu) ![c' mu, c' (mu + α), c' α, c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 mu α).1, (X0 mu α).2, hB' _ _⟩
    · exact ⟨(X1 mu α).1, (X1 mu α).2, hB' _ _⟩
    · exact ⟨(X2 mu α).1, (X2 mu α).2, hB' _ _⟩
    · exact ⟨(X3 mu α).1, (X3 mu α).2, hB' _ _⟩) zz J hJ
  have hii := hconn e he1 (α + e • mu) σ₁u σ₁u'' hT'' _ (c' 0) ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] (by
    intro j; fin_cases j
    · exact ⟨(X0 0 _).1, (X0 0 _).2, hB' _ _⟩
    · have h1 := X1 0 (α + e • mu)
      rw [zero_add] at h1
      exact ⟨h1.1, h1.2, hB' _ _⟩
    · exact ⟨(X2 0 _).1, (X2 0 _).2, hB' _ _⟩
    · exact ⟨(X3 0 _).1, (X3 0 _).2, hB' _ _⟩) zz J hJ

  have vρ := hval _ (spMap ρ) zz J hJ
  have vc := hval _ (spMap (constHom ρ)) zz J hJ
  have vc' := hval' _ (spMap (constHom ρ)) zz J hJ
  have v'' := hval'' _ (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) zz J hJ
  rw [← (hc' 0).2.1, ← (hc' mu).2.1] at vρ
  rw [← (hc' 0).2.2, ← (hc' mu).2.2] at vc vc'
  have hx0 : (spMap (constHom ρ) ≫ (P.D.toPre.c 0).left) ≫ P.D.toPre.P.A.hom = spMap (constHom ρ) := by
    rw [Category.assoc, Over.w (P.D.toPre.c 0)]; simp
  rw [hx0, gs_spMap, ← (hc' 0).2.2] at v''
  rw [(hc' mu).1, ← ev_apply, ← ev_apply] at hi
  rw [(hc' 0).1, ← ev_apply, ← ev_apply, v'', vρ, vc, vc'] at hii
  have hcH : ∀ r, constHom ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) := by
    intro r; simp [constHom, hρ, TrivSqZeroExt.algebraMap_eq_inl]
  set s : k := ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) * MvPowerSeries.constantCoeff (q i) with hs
  have hcst : constHom ρ (2 * (e : ChartRing k m d) * ∑ i, ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : ChartRing k m d) * q i) =
      TrivSqZeroExt.inl (2 * (e : k) * s) := by
    rw [hcH, hs]; congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_mul, map_sum]
    simp only [map_mul, map_natCast, map_ofNat]
  rw [hcst, map_add (f := _), map_nsmul, nsmul_eq_mul] at hii

  have hee' : (ee : DualNumber k) = 1 + TrivSqZeroExt.inr ((e : k) * ℓ e mu - s) := by
    rw [hee, hs]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have h0 := Int.toNat_of_nonneg (hN i)
    have h1 : ((((e : ℤ) * n i + gam i mu α).toNat : ℕ) : k) = ((((e : ℤ) * n i + gam i mu α) : ℤ) : k) := by
      rw [← Int.cast_natCast, h0]
    rw [h1]; push_cast; ring
  have hAc : IsUnit (sval σ (c' mu ≫ π₂) zz J) := by
    have := hσu zz J hJ
    rwa [← (hc' mu).2.2] at this
  rw [gm_unitOn, alg_eval (ev zz) e he1 (κ e) ee (ℓ e α) (ℓ e mu) s hee' _ _ _ _
    (gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) *
      gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) *
      (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ *
      gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)))
    _ _ _ hAc ?_ hi hii]
  · simp only [_root_.mul_assoc]
  · have e1 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' 0, c' (α + e • mu), c' (α + e • mu), c' 0] e
    have e2 := prod_fam (fun x => gm x zz _ (w.s (fun _ => J (x ≫ π₂), fun _ => J (x ≫ π₁))))
      ![c' mu, c' (mu + α), c' α, c' 0] e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e1 e2
    rw [e1, e2]
    exact mul_inv_mul_cancel_comm _ _ _ _ _ e

end GlobalTheory.UnitsEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  first | exact @GlobalTheory.UnitsEval.units_eval | exact GlobalTheory.UnitsEval.units_eval | (intros; apply GlobalTheory.UnitsEval.units_eval <;> assumption)
end
