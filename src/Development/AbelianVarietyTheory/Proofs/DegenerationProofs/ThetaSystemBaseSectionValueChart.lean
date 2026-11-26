module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitOfVal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {X Y : Scheme.{0}} {K : Type} [Field K]

theorem le_inf' {g : Sp K ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ⊤ ≤ g ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

theorem le_wchart {I : Type} [Fintype I] (L : LB X) (φ : Y ⟶ X) (j : I → L.ι) {g : Sp K ⟶ Y}
    (h : ∀ i, ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i)) : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j :=
  fun _ hz => Set.mem_iInter.2 fun i => h i hz

theorem of_le_wchart {I : Type} [Fintype I] {L : LB X} {φ : Y ⟶ X} {j : I → L.ι} {g : Sp K ⟶ Y}
    (h : ⊤ ≤ g ⁻¹ᵁ LB.wchart L (fun _ => φ) j) (i : I) : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U (j i) :=
  fun _ hz => Set.mem_iInter.1 (h hz) i

noncomputable def vU (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) : Γ(X, U)ˣ →* Kˣ :=
  Units.map (valMap g U h).hom.toMonoidHom

theorem vU_val (g : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF g U u.val = (vU g U h u).val := valR_eq g U h _

theorem val_unit_ne (g : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : valF g U u.val ≠ 0 := by
  rw [vU_val g U h]; exact Units.ne_zero _

theorem val_junk (g : Sp K ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) : valF g U f = 0 := dif_neg h

theorem val_linComb_g {I : Type} [Fintype I] [Unique I] (L : LB X) (φ : Y ⟶ X) (n : ℤ) (a b : L.ι) (g : Sp K ⟶ Y)
    (ha : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ L.U b) :
    valF g _ ((LB.LinComb L (K := I) (fun _ => φ) (fun _ => n)).g (fun _ => a) (fun _ => b)).val =
      valF (g ≫ φ) _ (L.g a b).val ^ n := by
  have h := le_inf' (le_wchart L φ (fun _ : I => a) fun _ => ha) (le_wchart L φ (fun _ : I => b) fun _ => hb)
  have key : ∀ (W : Y.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ φ ⁻¹ᵁ (L.U a ⊓ L.U b)),
      valF g W (∏ _k : I, res e (pullU φ _ (L.g a b)) ^ n).val = valF (g ≫ φ) _ (L.g a b).val ^ n := fun W h e => by
    rw [vU_val g _ h, Fintype.prod_unique, map_zpow, Units.val_zpow_eq_zpow_val, ← vU_val]
    rw [GlobalTheory.NormGlue.val_res_pullU]
    exact congrArg (· ^ n) (valR_appLE g φ e h _)
  exact key (LB.wchart L (fun _ : I => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : I => φ) (fun _ => b)) h
    (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => a) default))
      (inf_le_right.trans (LB.wchart_le L (fun _ : I => φ) (fun _ => b) default)))

theorem val_div_g (M L : LB X) (a b : (LB.div M L).ι) (g : Sp K ⟶ X)
    (ha : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U a) (hb : ⊤ ≤ g ⁻¹ᵁ (LB.div M L).U b) :
    valF g _ ((LB.div M L).g a b).val = valF g _ (M.g a.1 b.1).val * (valF g _ (L.g a.2 b.2).val)⁻¹ := by
  have h := le_inf' ha hb
  have key : ∀ (W A B : X.Opens) (_ : ⊤ ≤ g ⁻¹ᵁ W) (e : W ≤ A) (e' : W ≤ B) (u : Γ(X, A)ˣ) (v : Γ(X, B)ˣ),
      valF g W (res e u * (res e' v)⁻¹).val = valF g A u.val * (valF g B v.val)⁻¹ := fun W A B h e e' u v => by
    rw [vU_val g _ h, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← vU_val, ← vU_val]
    exact congrArg₂ (fun x y => x * y⁻¹) (valR_res g e h _) (valR_res g e' h _)
  exact key _ _ _ h _ _ _ _

theorem val_sec {H : LB X} (s : LB.Sec H) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.f j) = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.f k) := by
  have h := le_inf' hj hk
  have e := congrArg (valR x (H.U j ⊓ H.U k)) (s.compat j k)
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

theorem val_gen {H : LB X} {s : LB.Gen H} (hs : s.IsGen) (x : Sp K ⟶ X) {j k : H.ι} (hj : ⊤ ≤ x ⁻¹ᵁ H.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ H.U k) :
    valF x (H.U j) (s.s j).val = valF x (H.U j ⊓ H.U k) (H.g j k).val * valF x (H.U k) (s.s k).val :=
  val_sec ⟨fun i => (s.s i).val, fun i j => congrArg Units.val (hs i j)⟩ x hj hk

theorem val_g_self {L : LB X} (hL : L.IsLB) (x : Sp K ⟶ X) {k : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valF x _ (L.g k k).val = 1 :=
  (valR_res x _ h _).symm.trans ((congrArg (fun u : Γ(X, L.U k)ˣ => valR x _ u.val) (hL.g_self k)).trans
    (valR_one x _ h))

theorem isUnit_of_val {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (g : Sp K ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valF g U f ≠ 0) : IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (X.mem_basicOpen f x hx).1 ?_
  let g : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hg : ∀ w, g w = x := fun w => Scheme.fromSpecResidueField_apply _ _
  have h1 : ⊤ ≤ g ⁻¹ᵁ U := fun w _ => show g w ∈ U by rw [hg]; exact hx
  have := (le_preimage_basicOpen_iff g h1 f).2 (h _ g h1).isUnit (x := IsLocalRing.closedPoint _) trivial
  exact Set.mem_of_eq_of_mem (hg _).symm this

def Reg (y : Y) (F : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K) : Prop :=
  ∃ (V : Y.Opens) (f : Γ(Y, V)), y ∈ V ∧ ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → valF g V f = F K g

section
variable {y : Y} {F F' : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}

theorem Reg.val (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ U) : Reg y fun _ _ g => valF (g ≫ m) U s :=
  ⟨m ⁻¹ᵁ U, (m.app U).hom s, h, fun _ _ g _ => (valR_comp g m U s).symm⟩

theorem Reg.inv (m : Y ⟶ X) {U : X.Opens} (s : Γ(X, U)) (h : m y ∈ X.basicOpen s) :
    Reg y fun _ _ g => (valF (g ≫ m) U s)⁻¹ := by
  obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨m ⁻¹ᵁ X.basicOpen s, (m.app _).hom (u⁻¹).val, h, fun _ _ g hg => (valR_comp g m _ _).symm.trans ?_⟩
  replace hg : ⊤ ≤ (g ≫ m) ⁻¹ᵁ X.basicOpen s := hg
  refine (vU_val (g ≫ m) _ hg _).trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val, ← vU_val, hu]
  exact congrArg (·⁻¹) (valR_res _ _ hg _)

theorem Reg.mul (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g * F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f * resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_mul g _ hg _ _).trans (congrArg₂ (· * ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.add (h : Reg y F) (h' : Reg y F') : Reg y fun K _ g => F K g + F' K g := by
  obtain ⟨V, f, hy, hf⟩ := h
  obtain ⟨V', f', hy', hf'⟩ := h'
  refine ⟨V ⊓ V', resG Y inf_le_left f + resG Y inf_le_right f', ⟨hy, hy'⟩, fun K _ g hg => ?_⟩
  exact (valR_add g _ hg _ _).trans (congrArg₂ (· + ·)
    ((valR_res g _ hg _).trans (hf K g (le_preimage_mono g inf_le_left hg)))
    ((valR_res g _ hg _).trans (hf' K g (le_preimage_mono g inf_le_right hg))))

theorem Reg.pow (h : Reg y F) (n : ℕ) : Reg y fun K _ g => F K g ^ n := by
  obtain ⟨V, f, hy, hf⟩ := h
  exact ⟨V, f ^ n, hy, fun K _ g hg => (valR_pow g _ hg _ _).trans (congrArg (· ^ n) (hf K g hg))⟩

theorem Reg.sum {I : Type} (s : Finset I) {F : I → ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K}
    (h : ∀ i, Reg y (F i)) : Reg y fun K _ g => ∑ i ∈ s, F i K g := by
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, 0, trivial, fun K _ g hg => valR_zero g _ hg⟩
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

end

theorem exists_glue [IsIntegral Y] (V : Y.Opens) (R : ∀ (K : Type) [Field K], (Sp K ⟶ Y) → K → Prop)
    {F : Type} [Field F] (ξ : Sp F ⟶ Y) (hξ : ∀ w, ξ w = genericPoint Y)
    (hu : ⊤ ≤ ξ ⁻¹ᵁ V → ∀ v v', R F ξ v → R F ξ v' → v = v')
    (hl : ∀ y ∈ V, ∃ (W : Y.Opens) (f : Γ(Y, W)), y ∈ W ∧
      ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ W → ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g W f)) :
    ∃ f : Γ(Y, V), ∀ (K : Type) [Field K] (g : Sp K ⟶ Y), ⊤ ≤ g ⁻¹ᵁ V → R K g (valF g V f) := by
  choose W f hy hf using fun y : V => hl y.1 y.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun y : V => V ⊓ W y) V (fun y => homOfLE inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hy _⟩) (fun y => resG Y inf_le_right (f y))
    (fun a b => eq_of_valF_generic ξ hξ (U := (V ⊓ W a) ⊓ (V ⊓ W b)) fun h => by
      have h1 := le_preimage_mono ξ inf_le_left h
      have h2 := le_preimage_mono ξ inf_le_right h
      have h3 := le_preimage_mono ξ inf_le_left h1
      exact ((valR_res ξ inf_le_left h _).trans (valR_res ξ _ h1 _)).trans ((hu h3 _ _
        (hf a F ξ (le_preimage_mono ξ inf_le_right h1) h3) (hf b F ξ (le_preimage_mono ξ inf_le_right h2) h3)).trans
        ((valR_res ξ inf_le_right h _).trans (valR_res ξ _ h2 _)).symm))
  refine ⟨s, fun K _ g hg => ?_⟩
  let y : V := ⟨g (IsLocalRing.closedPoint K), hg trivial⟩
  have h1 : ⊤ ≤ g ⁻¹ᵁ W y := (le_preimage_iff g _).2 (hy y)
  have h2 := le_inf' hg h1
  have e : valF g V s = valF g (W y) (f y) := (valR_res g inf_le_left h2 s).symm.trans
    ((congrArg (valR g _) (hs y)).trans (valR_res g _ h2 _))
  exact e ▸ hf y K g h1 hg

theorem exists_generic (Y : Scheme.{0}) [IsIntegral Y] :
    ∃ (F : Type) (_ : Field F) (ξ : Sp F ⟶ Y), ∀ w, ξ w = genericPoint Y :=
  ⟨Y.residueField (genericPoint Y), inferInstance, Y.fromSpecResidueField _,
    fun _ => Scheme.fromSpecResidueField_apply _ _⟩

end GlobalTheory.ZH.PowSec
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.PowSec
open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

def GV (c : S.J → Ω) (a : Q.L.L.ι) (K : Type) [Field K] (x : Sp K ⟶ Q.G.left) (v : K) : Prop :=
  ∀ (β : Ω →+* K) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left)
    (jP : ρ.P.L.ι), g ≫ Q.φ = x → g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt →
    r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ →
    ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP →
    ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v

variable {K : Type} [Field K] {c : S.J → Ω} {a a' : Q.L.L.ι}

theorem le_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a) :
    ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => a) :=
  le_inf' (le_wchart _ _ _ fun _ => h) (le_wchart _ _ _ fun _ => h')

theorem val_w {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP) (h' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a)
    (k : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP') (k' : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ Q.L.L.U a') :
    valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val =
      valF (g ≫ pullback.fst ρ.P.A.hom Q.u₀) _ (ρ.P.L.g jP jP').val * (valF (g ≫ Q.φ) _ (Q.L.L.g a a').val)⁻¹ *
        valF g _ (Q.w.s (fun _ => jP', fun _ => a')).val := by
  refine (val_gen Q.w_gen g (le_w Q h h') (le_w Q k k')).trans (congrArg (· * _) ?_)
  refine (val_div_g _ _ _ _ g (le_w Q h h') (le_w Q k k')).trans ?_
  exact congrArg₂ (fun x y => x * y⁻¹) ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h k).trans (zpow_one _))
    ((val_linComb_g (I := PUnit) _ _ 1 _ _ g h' k').trans (zpow_one _))

omit Q in
theorem thetaSystem_baseSection_value_chart {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP jP' : ρ.P.L.ι}
    (h : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP)
    (k : ⊤ ≤ (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⁻¹ᵁ ρ.P.L.U jP') (i : S.J) :
    valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) _ (ρ.P.L.g jP jP').val ^ (S.N : ℤ) *
        valF r _ ((ρ.s i).f (fun _ => jP')) :=
  (val_sec (ρ.s i) r (j := fun _ => jP) (k := fun _ => jP') (le_wchart _ _ _ fun _ => h)
    (le_wchart _ _ _ fun _ => k)).trans (congrArg (· * _) (val_linComb_g (I := Fin 1) _ _ _ _ _ r h k))

theorem exists_data (hU : (U₀ : Set M.Z).Nonempty) {Y : Scheme.{0}} (x : Y ⟶ Q.G.left) (κ : Y ⟶ Sp Ω)
    (h : x ≫ Q.G.hom = κ ≫ M.pt) : ∃ (g : Y ⟶ pullback ρ.P.A.hom Q.u₀) (r : Y ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = κ ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := by
  have hr : Set.range (κ ≫ M.pt) ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := κ w) trivial
  let y : Y ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (κ ≫ M.pt) hr
  have hy : y ≫ U₀.ι = κ ≫ M.pt := IsOpenImmersion.lift_fac _ _ _
  let g : Y ⟶ pullback ρ.P.A.hom Q.u₀ := Q.cart.1.lift x y (h.trans hy.symm)
  have hg2 : g ≫ pullback.snd _ _ = y := Q.cart.1.lift_snd x y _
  refine ⟨g, pullback.lift ((g ≫ pullback.fst _ _) ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _)
    (Category.comp_id _), Q.cart.1.lift_fst x y _, ?_, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, hg2, hy]

theorem exists_data' (hU : (U₀ : Set M.Z).Nonempty) (x : Sp K ⟶ Q.G.left) (β : Ω →+* K)
    (h : x ≫ Q.G.hom = spMap β ≫ M.pt) : ∃ (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
      (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι),
      g ≫ Q.φ = x ∧ g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt ∧
      r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ ∧
      ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP := by
  obtain ⟨g, r, h1, h2, h3⟩ := exists_data Q hU x _ h
  obtain ⟨jP, hj⟩ := exists_le_preimage_of_iSup_eq_top (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ρ.P.isLB.cover
  exact ⟨g, r, jP, h1, h2, h3, hj⟩

variable {Q} {x : Sp K ⟶ Q.G.left} {v v' : K}

theorem GV.unique (hU : (U₀ : Set M.Z).Nonempty) {β : Ω →+* K} (h : x ≫ Q.G.hom = spMap β ≫ M.pt)
    (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (H : GV Q c a K x v) (H' : GV Q c a K x v') : v = v' := by
  obtain ⟨g, r, jP, rfl, h2, h3, hj⟩ := exists_data' Q hU x β h
  exact mul_left_cancel₀ (zpow_ne_zero _ (val_unit_ne g (le_w Q hj ha) _))
    ((H β g r jP rfl h2 h3 hj).symm.trans (H' β g r jP rfl h2 h3 hj))

theorem GV.chart (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (ha' : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a') (H : GV Q c a K x v) :
    GV Q c a' K x (valF x _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * v) := by
  rintro β g r jP rfl h2 h3 hj
  have h0 := zpow_ne_zero (S.N : ℤ) (val_unit_ne _ (le_inf' ha' ha) (Q.L.L.g a' a))
  rw [H β g r jP rfl h2 h3 hj, val_w Q hj ha' hj ha, val_g_self ρ.P.isLB _ hj, _root_.one_mul, mul_zpow, inv_zpow]
  field_simp

theorem GV.of_one {β : Ω →+* K} {g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀}
    {r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left} {jP : ρ.P.L.ι} (ha : ⊤ ≤ x ⁻¹ᵁ Q.L.L.U a) (h1 : g ≫ Q.φ = x)
    (h2 : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt)
    (h3 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _)
    (hj : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP)
    (H : ∑ i, β (c i) * valF r _ ((ρ.s i).f (fun _ => jP)) =
      valF g _ (Q.w.s (fun _ => jP, fun _ => a)).val ^ (S.N : ℤ) * v) : GV Q c a K x v := by
  intro β' g' r' jP' k1 k2 k3 kj
  have : Mono Q.φ := (MorphismProperty.monomorphisms _).of_isPullback Q.cart.1.flip
    (inferInstanceAs (Mono U₀.ι))
  have := EndoExtend.isPreimmersion_pt M
  have : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left := inferInstanceAs (Mono (pullback.snd (𝟙 _) ρ.P.A.hom))
  obtain rfl : g' = g := (cancel_mono Q.φ).1 (k1.trans h1.symm)
  obtain rfl : r' = r := (cancel_mono _).1 (k3.trans h3.symm)
  obtain rfl : β' = β := congrArg (·.hom) (Spec.map_injective ((cancel_mono M.pt).1 (k2.symm.trans h2)))
  subst h1
  rw [val_w Q kj ha hj ha, val_g_self Q.L.isLB _ ha, inv_one, _root_.mul_one, mul_zpow, _root_.mul_assoc, ← H,
    Finset.mul_sum, ← h3]
  rw [← h3] at kj hj
  exact Finset.sum_congr rfl fun i _ => by rw [thetaSystem_baseSection_value_chart kj hj, mul_left_comm]

section Ratio

theorem exists_pt {X : Scheme.{0}} (y : X) : ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ X), ∀ w, g w = y :=
  ⟨X.residueField y, inferInstance, X.fromSpecResidueField _, fun _ => Scheme.fromSpecResidueField_apply _ _⟩

theorem exists_ne {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec} (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (h : Sp K ⟶ P) {k : O.ι} (hk : ⊤ ≤ h ⁻¹ᵁ O.U k) : ∃ i, valF h _ ((τ i).f k) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top h hτ
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 ((le_preimage_iff h _).1 hi)
  have h1 := (le_preimage_iff h _).2 hk'
  have h2 := le_preimage_mono h (P.basicOpen_le _) h1
  refine ⟨i, ?_⟩
  rw [val_sec (τ i) h hk h2]
  exact mul_ne_zero (val_unit_ne h (le_inf' hk h2) _) ((le_preimage_basicOpen_iff h h2 _).1 h1).ne_zero

theorem exists_mem_basicOpen {P : Scheme.{0}} {O : LB P} {I : Type} {τ : I → O.Sec}
    (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) (y : P) {k : O.ι} (hk : y ∈ O.U k) : ∃ i, y ∈ P.basicOpen ((τ i).f k) := by
  obtain ⟨F, _, g, hg⟩ := exists_pt y
  have h1 : ⊤ ≤ g ⁻¹ᵁ O.U k := fun w _ => show g w ∈ O.U k from Set.mem_of_eq_of_mem (hg w) hk
  obtain ⟨i, hi⟩ := exists_ne hτ g h1
  exact ⟨i, Set.mem_of_eq_of_mem (hg (IsLocalRing.closedPoint F)).symm
    ((le_preimage_basicOpen_iff g h1 _).2 hi.isUnit trivial)⟩

variable (Q) {P : Scheme.{0}} (ν : P ⟶ Q.G.left) {O : LB P} (τ : S.J → O.Sec) (b : S.J → S.J → Ω)

def Ratio (a : Q.L.L.ι) (k : O.ι) (K : Type) [Field K] (h : Sp K ⟶ P) (v : K) : Prop :=
  v ≠ 0 ∧ ∀ i, GV Q (b i) a K (h ≫ ν) (v * valF h _ ((τ i).f k))

variable {Q ν τ b} {k k' : O.ι} {h : Sp K ⟶ P}

theorem Ratio.unique (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤) {β : Ω →+* K}
    (e : (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt) (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (H : Ratio Q ν τ b a k K h v) (H' : Ratio Q ν τ b a k K h v') : v = v' := by
  obtain ⟨i, hi⟩ := exists_ne hτ h hk
  exact mul_right_cancel₀ hi ((H.2 i).unique hU e ha (H'.2 i))

theorem Ratio.chart (ha : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hk : ⊤ ≤ h ⁻¹ᵁ O.U k)
    (ha' : ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a') (hk' : ⊤ ≤ h ⁻¹ᵁ O.U k') (H : Ratio Q ν τ b a k K h v) :
    Ratio Q ν τ b a' k' K h
      (valF (h ≫ ν) _ (Q.L.L.g a' a).val ^ (S.N : ℤ) * (valF h _ (O.g k' k).val)⁻¹ * v) := by
  have h1 := val_unit_ne _ (le_inf' hk' hk) (O.g k' k)
  refine ⟨mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (val_unit_ne _ (le_inf' ha' ha) _)) (inv_ne_zero h1)) H.1,
    fun i => ?_⟩
  convert (H.2 i).chart ha ha' using 1
  rw [val_sec (τ i) h hk' hk]
  field_simp

theorem exists_unit (hU : (U₀ : Set M.Z).Nonempty) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤)
    (hp : ∀ (K : Type) [Field K] (β : Ω →+* K) (h : Sp K ⟶ P), (h ≫ ν) ≫ Q.G.hom = spMap β ≫ M.pt →
      ⊤ ≤ (h ≫ ν) ⁻¹ᵁ Q.L.L.U a → ⊤ ≤ h ⁻¹ᵁ O.U k → ∃ v, Ratio Q ν τ b a k K h v)
    {Y : Scheme.{0}} [IsIntegral Y] (J : Y ⟶ P) (κ : Y ⟶ Sp Ω) (hJ : (J ≫ ν) ≫ Q.G.hom = κ ≫ M.pt)
    (V : Y.Opens) (hV : V ≤ (J ≫ ν) ⁻¹ᵁ Q.L.L.U a) (hV' : V ≤ J ⁻¹ᵁ O.U k) :
    ∃ t : Γ(Y, V)ˣ, ∀ (K : Type) [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V →
      Ratio Q ν τ b a k K (h ≫ J) (valF h V t.val) := by
  have hβ : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), spMap (Spec.preimage (h ≫ κ)).hom = h ≫ κ := fun h =>
    Spec.map_preimage _
  have he : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y),
      ((h ≫ J) ≫ ν) ≫ Q.G.hom = spMap (Spec.preimage (h ≫ κ)).hom ≫ M.pt := fun h => by
    rw [hβ, Category.assoc h κ, ← hJ]; simp only [Category.assoc]
  have ha : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ ((h ≫ J) ≫ ν) ⁻¹ᵁ Q.L.L.U a :=
    fun h hh => le_preimage_mono h hV hh
  have hk : ∀ {K : Type} [Field K] (h : Sp K ⟶ Y), ⊤ ≤ h ⁻¹ᵁ V → ⊤ ≤ (h ≫ J) ⁻¹ᵁ O.U k :=
    fun h hh => le_preimage_mono h hV' hh
  obtain ⟨F, _, ξ, hξ⟩ := exists_generic Y
  obtain ⟨g, r, g1, g2, g3⟩ := exists_data Q hU _ κ hJ
  obtain ⟨f, hf⟩ := exists_glue V (fun K _ h v => Ratio Q ν τ b a k K (h ≫ J) v) ξ hξ
    (fun hh v v' H H' => H.unique hU hτ (he ξ) (ha ξ hh) (hk ξ hh) H') (fun y hy => by
      obtain ⟨jP, hj⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) y)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen hτ (J y) (hV' hy)
      have m1 : r y ∈ (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).U (fun _ => jP) :=
        Set.mem_iInter.2 fun _ => by rw [← g3] at hj; exact hj
      have m2 : g y ∈ (pullback ρ.P.A.hom Q.u₀).basicOpen (Q.w.s (fun _ => jP, fun _ => a)).val := by
        rw [Scheme.basicOpen_of_isUnit _ (Units.isUnit _)]
        have := hV hy
        rw [← g1] at this
        exact ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => this⟩
      obtain ⟨W, f, hW, hf⟩ := ((Reg.sum Finset.univ fun l => (Reg.val κ (U := ⊤)
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (b i l)) trivial).mul (Reg.val r ((ρ.s l).f _) m1)).mul
        ((Reg.inv g _ m2).pow S.N)).mul (Reg.inv J _ hi)
      refine ⟨W ⊓ ((g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP ⊓ J ⁻¹ᵁ P.basicOpen ((τ i).f k)),
        resG Y inf_le_left f, ⟨hW, hj, hi⟩, fun K _ h h1 h2 => ?_⟩
      obtain ⟨v, hv⟩ := hp K _ _ (he h) (ha h h2) (hk h h2)
      have n1 : ⊤ ≤ ((h ≫ g) ≫ pullback.fst ρ.P.A.hom Q.u₀) ⁻¹ᵁ ρ.P.L.U jP :=
        le_preimage_mono h (inf_le_right.trans inf_le_left) h1
      have n2 : ⊤ ≤ (h ≫ J) ⁻¹ᵁ P.basicOpen ((τ i).f k) := le_preimage_mono h (inf_le_right.trans inf_le_right) h1
      have n3 : (h ≫ g) ≫ Q.φ = (h ≫ J) ≫ ν := by rw [Category.assoc, g1, Category.assoc]
      have e := hv.2 i _ (h ≫ g) (h ≫ r) jP n3 (by rw [Category.assoc, g2, hβ, Category.assoc])
        (by rw [Category.assoc, g3, Category.assoc]) n1
      have z1 : valF (h ≫ J) _ ((τ i).f k) ≠ 0 := ((le_preimage_basicOpen_iff _ (hk h h2) _).1 n2).ne_zero
      have z2 := val_unit_ne (h ≫ g) (le_w Q n1 (n3 ▸ ha h h2)) (Q.w.s (fun _ => jP, fun _ => a))
      convert hv using 1
      refine (valR_res h _ h1 _).trans ((hf K h (le_preimage_mono h inf_le_left h1)).trans ?_)
      rw [zpow_natCast] at e
      have key : ∀ (A w t : K), w ≠ 0 → t ≠ 0 → A = w ^ S.N * (v * t) → A * (w⁻¹) ^ S.N * t⁻¹ = v := by
        rintro _ w t h1 h2 rfl
        rw [inv_pow]
        field_simp
      refine key _ _ _ z2 z1 (Eq.trans (Finset.sum_congr rfl fun l _ => ?_) e)
      rw [preimage_apply (h ≫ κ) (b i l)]
      rfl)
  exact ⟨(isUnit_of_val f fun K _ h hh => (hf K h hh).1).unit, hf⟩

end Ratio

end GlobalTheory.ZH.PowSec
