module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentGeneratorsHolomorphicFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetF

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}}

def vH (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valF_eq (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) : valF x U a = vH x U h a := by
  rw [valF, dite_eq_left h]; rfl

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_unit_ne (x : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : valF x U a.val ≠ 0 := by
  rw [valF_eq x U h]
  exact (a.isUnit.map _).ne_zero

variable {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem mem_wchart {r : Sp F ⟶ Y} {j : K → L.ι} :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (r ≫ φ k) ⁻¹ᵁ L.U (j k) :=
  ⟨fun h k _ hq => Set.mem_iInter.1 (h hq) k, fun h _ hq => Set.mem_iInter.2 fun k => h k hq⟩

theorem valF_sec (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (j j' : K → L.ι)
    (h : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) (h' : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j') :
    valF r (LB.wchart L φ j) (s.f j) =
      (∏ k, valF (r ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k) *
        valF r (LB.wchart L φ j') (s.f j') := by
  have h2 : ⊤ ≤ r ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have c := congrArg (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2) (s.compat j j')
  erw [map_mul] at c
  refine (valF_res inf_le_left h2 _).symm.trans ((valF_eq _ _ h2 _).trans (c.trans (congrArg₂ (· * ·) ?_
    ((valF_eq _ _ h2 _).symm.trans (valF_res inf_le_right h2 _)))))
  let ψ : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ →* F :=
    (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom.comp (Units.coeHom _)
  change ψ (∏ k, _) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  change (Units.coeHom F) ((Units.map (vH r (LB.wchart L φ j ⊓ LB.wchart L φ j') h2).toMonoidHom) _) = _
  rw [map_zpow, map_zpow]
  congr 1
  rw [← valF_appLE (φ k) _ (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k))) h2, valF_eq _ _ h2]
  rfl

end Val

section Jet
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def jet (W : E) (f : E → ℂ) (x : E) : DualNumber ℂ :=
  TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (fderiv ℂ f x W)

theorem jet_mul (W : E) {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) :
    jet W (fun z => f z * g z) x = jet W f x * jet W g x := by
  unfold jet
  rw [fderiv_fun_mul hf hg]
  ext <;> simp <;> ring

theorem jet_const (W : E) (c : ℂ) (x : E) : jet W (fun _ => c) x = TrivSqZeroExt.inl c := by
  simp [jet]

theorem jet_pow (W : E) {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (k : ℕ) :
    jet W (fun z => f z ^ k) x = jet W f x ^ k := by
  induction k with
  | zero => simp [jet_const]
  | succ k ih =>
    simp only [pow_succ]
    rw [jet_mul W (hf.fun_pow k) hf, ih]

theorem jet_congr (W : E) {f g : E → ℂ} {x : E} (h : f =ᶠ[nhds x] g) : jet W f x = jet W g x := by
  unfold jet
  rw [h.fderiv_eq, h.eq_of_nhds]

theorem jet_add (W : E) (f : E → ℂ) (c : E) : jet W (fun z => f (c + z)) 0 = jet W f c := by
  unfold jet
  rw [fderiv_comp_add_left]
  simp only [add_zero]

end Jet

section Main
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  (ν : NumOf D ℂ N) (d : AB N.toNumB g)

theorem ex_zero : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem ptB_prB (z : Fin g → ℂ) : ptB ν d z ≫ (DegPre.prB D ℂ).left = (ν.eA (d.ex z)).left :=
  congrArg (·.left) (lift_snd (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)))

theorem ptB_fam {α : N.X} {ct : Fin g → ℂ} (hc : N.c α = d.ex ct) (z : Fin g → ℂ) (k : Fin 4) :
    ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k = (ν.eA (d.ex (![z, ct + z, ct, 0] k))).left := by
  have e2 : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫ toUnit _ ≫ D.c (ν.eX α) = ν.eA (d.ex ct) := by
    rw [← hc, ν.c_eq, ← Category.assoc, comp_toUnit]
  fin_cases k
  · exact ptB_prB ν d z
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      (DegPre.prB D ℂ * (toUnit _ ≫ D.c (ν.eX α))) = ν.eA (d.ex (ct + z)))
    rw [MonObj.comp_mul, e2, lift_snd, add_comm, d.ex_add, map_mul]
  · exact congrArg (·.left) e2
  · refine congrArg (·.left) (?_ : lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) ≫
      toUnit _ ≫ η[D.P.A] = ν.eA (d.ex 0))
    rw [ex_zero, map_one, ← Category.assoc, comp_toUnit]
    rfl

variable {ν d}

theorem open_chart (G : Geo ν d) (i : D.P.L.ι) : IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := by
  have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
  simp only [← ptB_prB]
  exact this

theorem frG_diff (G : Geo ν d) (x : Fin g → ℂ) : DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x :=
  (G.fr_hol _).differentiableAt ((open_chart G _).mem_nhds (ν.good _))

theorem val_fam (G : Geo ν d) {k : ℕ} {s : Fam D ℂ k} {f : N.X → N.A → ℂ} {α : N.X} {ct : Fin g → ℂ} {φ : (Fin g → ℂ) → ℂ}
    (hs : ν.FamV s f) (hc : N.c α = d.ex ct)
    (hφ : ∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z))
    (j : Fin 4 → D.P.L.ι) (z : Fin g → ℂ) (h : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) :
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j) * G.frG (j 2) ct * G.frG (j 0) z =
      φ z * G.frG (j 0) z ^ k * G.frG (j 1) (ct + z) * G.frG (j 3) 0 := by
  have h' : ⊤ ≤ ptB ν d z ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α))
      (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k)) := mem_wchart.2 fun _ => ν.good _
  have e := valF_sec (s.s (ν.eX α)) (ptB ν d z) j _ h h'
  have e' : valF (ptB ν d z) _ ((s.s (ν.eX α)).f (fun k => ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) k))) =
    f α (d.ex z) * ν.rg ^ k := (hs α (d.ex z)).symm
  have key : ∀ l : Fin 4, ∃ u : ℂ, u ≠ 0 ∧ valF (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)
      (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l)))
      (D.P.L.g (j l) (ν.J (ptB ν d z ≫ DegPre.famφ D ℂ (ν.eX α) l))).val = u ∧
      G.frG (j l) (![z, ct + z, ct, 0] l) = u * (d.fr (![z, ct + z, ct, 0] l) * ν.rg) := fun l => by
    have h1 := mem_wchart.1 h l
    rw [ptB_fam ν d hc] at h1 ⊢
    have h2 : ⊤ ≤ (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left ⁻¹ᵁ
        (D.P.L.U (j l) ⊓ D.P.L.U (ν.J (ν.eA (d.ex (![z, ct + z, ct, 0] l))).left)) :=
      fun q hq => ⟨h1 hq, ν.good _ hq⟩
    exact ⟨_, valF_unit_ne _ _ h2 _, rfl, by rw [G.fr_compat _ _ _ h2, G.fr_eq]⟩
  choose u hu0 hu1 hu2 using key
  have e3 := e.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun l _ => congrArg (· ^ DegPre.famε k l) (hu1 l)) e')
  rw [e3, Fin.prod_univ_four]
  have a0 : G.frG (j 0) z = u 0 * (d.fr z * ν.rg) := hu2 0
  have a1 : G.frG (j 1) (ct + z) = u 1 * (d.fr (ct + z) * ν.rg) := hu2 1
  have a2 : G.frG (j 2) ct = u 2 * (d.fr ct * ν.rg) := hu2 2
  have a3 : G.frG (j 3) 0 = u 3 * (d.fr 0 * ν.rg) := hu2 3
  rw [a0, a1, a2, a3, d.fr_zero]
  change u 0 ^ ((k : ℤ) - 1) * u 1 ^ (1 : ℤ) * u 2 ^ (-1 : ℤ) * u 3 ^ (1 : ℤ) * _ * _ * _ = _
  rw [zpow_sub₀ (hu0 0), zpow_natCast]
  simp only [zpow_one, _root_.zpow_neg, Units.val_one, mul_pow]
  rw [div_eq_mul_inv]
  linear_combination (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * hφ z +
    (u 0 ^ k * u 1 * u 3 * ν.rg ^ k * ν.rg ^ 2) * (f α (d.ex z) * d.fr ct * d.fr z) *
      (u 2 * (u 2)⁻¹ * mul_inv_cancel₀ (hu0 0) + mul_inv_cancel₀ (hu0 2))

theorem red_eq (b : TE R ℂ ⟶ D.P.A) (hb : redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left) :
    redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left = ptB ν d 0 := by
  have h0 : redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) (by
    change redE ℂ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ _ = _
    rw [← Category.assoc, h0, Category.id_comp])
  refine congrArg (·.left) (?_ : ρ ≫ lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b =
    lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)))
  rw [comp_lift, ex_zero, map_one]
  congr 1
  · exact Over.OverMorphism.ext h0
  · exact Over.OverMorphism.ext hb

end Main

end GlobalTheory.MBLow.Cl.JetF

namespace GlobalTheory.MBLow.Cl
open JetF

theorem sE_fam_eq_jet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  intro R _ _ _ _ D _ _ _ N ν g d G b W hb hD k s f α ct φ hs hc hφ hf
  let j : Fin 4 → D.P.L.ι := fun l => ν.J (ptB ν d 0 ≫ DegPre.famφ D ℂ (ν.eX α) l)
  have hU : ⊤ ≤ ptB ν d 0 ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j := mem_wchart.2 fun _ => ν.good _
  have j0 : j 0 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 0)
  have j1 : j 1 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J ((ptB_fam ν d hc 0 1).trans (by simp))
  have j2 : j 2 = ν.J (ν.eA (d.ex ct)).left := congrArg ν.J (ptB_fam ν d hc 0 2)
  have j3 : j 3 = ν.J (ν.eA (d.ex 0)).left := congrArg ν.J (ptB_fam ν d hc 0 3)
  let h : (Fin g → ℂ) → ℂ := fun z =>
    valF (ptB ν d z) (LB.wchart D.P.L (DegPre.famφ D ℂ (ν.eX α)) j) ((s.s (ν.eX α)).f j)
  have e1 : sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
      TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J = jet W h 0 := by
    have ej : (fun l => ν.J (redE ℂ ≫ (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl :
        TE R ℂ ⟶ TF (R := R) ℂ) b).left ≫ DegPre.famφ D ℂ (ν.eX α) l)) = j := funext fun l =>
      congrArg ν.J ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (red_eq b hb)))
    unfold sE
    rw [ej]
    exact hD _ _ hU
  obtain ⟨ho, hd⟩ := G.hol _ ((s.s (ν.eX α)).f j)
  have hn := ho.mem_nhds hU
  have hh : DifferentiableAt ℂ h 0 := hd.differentiableAt hn
  have d0 := frG_diff G 0
  have dc : DifferentiableAt ℂ (fun z => G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z)) 0 := by
    refine DifferentiableAt.comp (g := G.frG (ν.J (ν.eA (d.ex ct)).left)) (f := fun z => ct + z) 0 ?_ (by fun_prop)
    rw [add_zero]
    exact frG_diff G ct
  have ev : (fun z => h z * G.frG (ν.J (ν.eA (d.ex ct)).left) ct * G.frG (ν.J (ν.eA (d.ex 0)).left) z) =ᶠ[nhds 0]
      fun z => φ z * G.frG (ν.J (ν.eA (d.ex 0)).left) z ^ k * G.frG (ν.J (ν.eA (d.ex ct)).left) (ct + z) *
        G.frG (ν.J (ν.eA (d.ex 0)).left) 0 := by
    filter_upwards [hn] with z hz
    have := val_fam G hs hc hf j z hz
    rwa [j0, j1, j2, j3] at this
  have := jet_congr W ev
  rw [jet_mul W (hh.mul_const _) d0, jet_mul W hh (differentiableAt_const _), jet_const,
    jet_mul W (((hφ 0).fun_mul (d0.fun_pow k)).fun_mul dc) (differentiableAt_const _), jet_const,
    jet_mul W ((hφ 0).fun_mul (d0.fun_pow k)) dc, jet_mul W (hφ 0) (d0.fun_pow k), jet_pow W d0, jet_add] at this
  rw [e1]
  exact this

end GlobalTheory.MBLow.Cl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyMember_tangentValue_eq_firstJet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  first | exact @GlobalTheory.MBLow.Cl.sE_fam_eq_jet | exact GlobalTheory.MBLow.Cl.sE_fam_eq_jet | (intros; apply GlobalTheory.MBLow.Cl.sE_fam_eq_jet <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetFam

open TrivSqZeroExt in
theorem dual_unit {a a' : ℂ} (ha : a ≠ 0) : IsUnit (inl a + inr a' : DualNumber ℂ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using ha

open TrivSqZeroExt in
theorem dual_mul {S V : DualNumber ℂ} {a a' r r' p p' e : ℂ} {k : ℕ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h1 : S * inl a * (inl r + inr r') = (inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r)
    (h2 : V * (inl a + inr a') * inl r = (1 + inr e) * inl a * (inl r + inr r')) :
    (S * V).fst / r ^ k = p ∧ (S * V).snd / r ^ k = p' + e * p + k * (r' / r) * p := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  have hu := ((ua.mul (dual_unit (a' := r') hr)).mul (dual_unit (a' := a') ha)).mul ur
  have key : S * V = (inl p + inr p') * (inl r + inr r') ^ k * (1 + inr e) := by
    apply hu.mul_right_cancel
    linear_combination (V * (inl a + inr a') * inl r) * h1 +
      ((inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r) * h2
  rw [key]
  constructor
  · simp [hr]
  · rcases k with _ | k
    · simp; ring
    · simp [TrivSqZeroExt.snd_pow]
      field_simp
      ring

open TrivSqZeroExt in
theorem dual_zero {V : DualNumber ℂ} {a r e : ℂ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h2 : V * (inl a + inr 0) * inl r = (1 + inr e) * inl a * (inl r + inr 0)) : V = 1 + inr e := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  apply (ua.mul ur).mul_right_cancel
  rw [inr_zero, add_zero, add_zero] at h2
  linear_combination h2

variable {g' r g : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r)

def join (z : Fin g' → ℂ) (t : Fin r → ℂ) : Fin g → ℂ := fun j => Sum.elim z t (σ j)

theorem leftComponent_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : zP σ (join σ z t) = z := by
  funext i; simp [zP, join]

theorem secondBlock_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : tP σ (join σ z t) = t := by
  funext i; simp [tP, join]

theorem join_zero : join σ 0 0 = 0 := by
  funext j; simp only [join]; rcases σ j with i | i <;> simp

theorem diff_join : Differentiable ℂ fun z : Fin g' → ℂ => join σ z 0 := by
  refine differentiable_pi.2 fun j => ?_
  simp only [join]
  rcases σ j with i | i
  · simp only [Sum.elim_inl]; fun_prop
  · simp

def zL : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ.symm (Sum.inl i))

def tL (c : ℂ) (v : Fin r → ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  c • ∑ l, v l • ContinuousLinearMap.proj (σ.symm (Sum.inr l))

theorem zL_apply (Y : Fin g → ℂ) : zL σ Y = zP σ Y := rfl

theorem tL_apply (c : ℂ) (v : Fin r → ℂ) (Y : Fin g → ℂ) : tL σ c v Y = c * (v ⬝ᵥ tP σ Y) := by
  simp [tL, tP, dotProduct]

theorem fderiv_eq (c : ℂ) (v : Fin r → ℂ) {F : (Fin g → ℂ) → ℂ} {φ : (Fin g' → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ Y, F Y = Complex.exp (c * (v ⬝ᵥ tP σ Y)) * φ (zP σ Y)) (Z : Fin g → ℂ) :
    fderiv ℂ F 0 Z = fderiv ℂ φ 0 (zP σ Z) + c * (v ⬝ᵥ tP σ Z) * φ 0 := by
  have e : F = fun Y => Complex.exp (tL σ c v Y) * φ (zL σ Y) := by
    funext Y; rw [h, tL_apply, zL_apply]
  have h1 : HasFDerivAt (fun Y => Complex.exp (tL σ c v Y)) _ (0 : Fin g → ℂ) := (tL σ c v).hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun Y => φ (zL σ Y)) _ (0 : Fin g → ℂ) :=
    (hφ (zL σ 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (zL σ).hasFDerivAt
  have h3 := (h1.mul h2).fderiv
  rw [e]
  refine (congrArg (fun L => L Z) h3).trans ?_
  rw [map_zero, map_zero]
  simp [tL_apply, zL_apply, mul_comm]

end GlobalTheory.MBLow.Cl.JetFam

namespace GlobalTheory.MBLow.Cl

open JetFam

theorem jet_family_deriv : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (_ : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g' → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ (Z : Fin g → ℂ) (c₀ : ℂ), zP σ Z = W ∧ (W = 0 → ∀ χ, vE (gm.s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ tP σ Z))) ∧ ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F → (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) → (jc ν s gm α).fst / ν.rg ^ k = F 0 ∧ (jc ν s gm α).snd / ν.rg ^ k = fderiv ℂ F 0 Z + k * c₀ * F 0 := by
  intro R _ _ _ _ D hE hT _ N ν g' r g bX d σ G gm W ho hW
  obtain ⟨T, hT'⟩ := GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame R D hE hT N ν g' r bX d G gm W ho hW
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.FamVal.rg_ne ν
  have hne : ∀ z, G.frG (ν.J (ν.eA (d.ex z)).left) z ≠ 0 := fun z => by
    rw [← G.fr_eq]; exact mul_ne_zero (Units.ne_zero _) hrg
  have h0 : G.frG (ν.J (ν.eA (d.ex 0)).left) 0 = ν.rg := by
    rw [← G.fr_eq, d.fr_zero]; simp
  refine ⟨join σ W T, fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / ν.rg, leftComponent_join σ W T, ?_, ?_⟩
  · intro hW0 χ
    have := hT' χ _ rfl
    subst hW0
    rw [map_zero, map_zero] at this
    rw [secondBlock_join]
    exact dual_zero (hne _) (hne _) this
  · intro k s f α F hs hF hf
    obtain ⟨o, hz, hp⟩ := ho
    have hb : redE ℂ ≫ gm.b.left = (DegPre.zeroF D ℂ).left := by
      rw [← hz.1]; exact hp.1.symm
    have hpt := fun Y => ((GlobalTheory.MBLow.Cl.exp_onto_torusExt N g' r g bX d σ).1 Y).exists
    have hφ : Differentiable ℂ fun z => F (join σ z 0) := hF.comp (diff_join σ)
    have hA : ∀ z, f α (d.ex z) * d.fr (d.t12 *ᵥ co bX α) * d.fr z =
        F (join σ z 0) * (d.fr z : ℂ) ^ k * d.fr (d.t12 *ᵥ co bX α + z) := fun z => by
      obtain ⟨h, hh⟩ := hpt (join σ z 0)
      have e1 := hf _ h hh
      have e2 := hh.2 α
      rw [hh.1] at e1
      rw [leftComponent_join] at e1 e2
      rw [secondBlock_join] at e2
      simp only [dotProduct_zero, mul_zero, Complex.exp_zero, one_mul] at e2
      linear_combination (d.fr (d.t12 *ᵥ co bX α + z) : ℂ) * e1 - f α (d.ex z) * e2
    have hB : ∀ Y, F Y = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * F (join σ (zP σ Y) 0) :=
      fun Y => by
      obtain ⟨h, hh⟩ := hpt Y
      have e1 := hf _ h hh
      have e2 := hh.2 α
      have e3 := hA (zP σ Y)
      rw [hh.1] at e1
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k (d.fr (zP σ Y)).ne_zero)
        (d.fr (d.t12 *ᵥ co bX α + zP σ Y)).ne_zero)
      linear_combination (-(d.fr (d.t12 *ᵥ co bX α + zP σ Y) : ℂ)) * e1 + f α (d.ex (zP σ Y)) * e2 +
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * e3
    have h1 := GlobalTheory.T.familyMember_tangentValue_eq_firstJet R D hE hT N ν g' d.toAB G gm.b W hb hW k s f α _ _ hs (d.c_eq α) hφ hA
    have h2 := dual_mul (hne _) (hne _) h1 (hT' α _ rfl)
    rw [h0, join_zero] at h2
    rw [fderiv_eq σ _ _ hφ hB, leftComponent_join, secondBlock_join, join_zero]
    exact h2

end GlobalTheory.MBLow.Cl

end
