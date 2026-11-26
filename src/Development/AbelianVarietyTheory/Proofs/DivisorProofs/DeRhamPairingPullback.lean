module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftDiff

private theorem thickHom_ext {R : Type} [CommRing R] {I : Ideal R}
    {powers : DividedPowers I} {X : Scheme.{0}} {s : X ⟶ Sp R}
    {T T' : Thick powers s} {f g : T ⟶ T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  change Thick.Hom T T' at f g
  cases f with
  | mk φ φ₀ comm dp pt =>
    cases g with
    | mk ψ ψ₀ comm' dp' pt' =>
      have e : φ = ψ := AlgHom.ext h
      subst ψ
      have e₀ : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
        obtain ⟨b, rfl⟩ := T.surj c
        rw [comm, comm']
      subst ψ₀
      rfl

theorem spMap_fst_surjective {B : Type} [CommRing B] (f : DualNumber B →+* B) (hf : ∀ c, f c = c.fst) :
    Function.Surjective (spMap f) := by
  intro q
  refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap B (DualNumber B) (f c) ∈ q.asIdeal ↔ c ∈ q.asIdeal
  rw [hf]
  have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem le_preimage_of_red {B : Type} [CommRing B] {X : Scheme.{0}} (f : DualNumber B →+* B)
    (hf : ∀ c, f c = c.fst) {y : Sp (DualNumber B) ⟶ X} {x : Sp B ⟶ X} (e : spMap f ≫ y = x) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := spMap_fst_surjective f hf p
  have := h (Set.mem_univ q)
  rw [← e] at this
  exact this

theorem ev_eq_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (ω : Form s)
    {T₁ T₂ T : Thick (dp0 R) s} (a : T₁ ⟶ T₂) (ψ : T₂ ⟶ T) (φ : T₁ ⟶ T) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (e : a ≫ ψ = φ) : ev ω.1 φ = ev ω.1 ψ := by
  rw [← e, ev_comp, show ev ω.1 a = 0 from ω.2 a h₁ h₂, map_zero, zero_add]

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A']
  {i : A.left ⟶ A'.left}

theorem ev_sec_sub_ev_tan (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) :
    ∃ (hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
        spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
        ((fibMor h).isMor.obj P.ext).x)
      (ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B))
      (et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x),
      ev ((fibMor h).isMor.pullForm ω).1 P.sec - ev ((fibMor h).isMor.pullForm ω).1 (P.tan hv) =
        ev ω.1 (idLift _ _ hc ec) - ev ω.1 (idLift _ _ ht et) := by
  let g : DualNumber K →+* P.B := (algebraMap K P.B).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have w : (P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ = spMap g := ((fibMor h).isMor.obj P.triv).w
  have hc : (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) := by
    rw [Category.assoc, w]
    exact (Cris.spMap_comp g (algebraMap P.B (DualNumber P.B))).symm.trans (congrArg spMap (RingHom.ext fun _ ↦ rfl))
  have ec : spMap ((fibMor h).isMor.obj P.ext).π ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i =
      ((fibMor h).isMor.obj P.ext).x := by
    let π' : DualNumber P.B →+* P.B := TrivSqZeroExt.fstHom K P.B P.B
    have e : π'.comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := RingHom.ext fun _ ↦ rfl
    show spMap π' ≫ spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i = P.x ≫ i
    rw [← Category.assoc, ← Cris.spMap_comp, e, Cris.spMap_id, Category.id_comp]
  have ht : (P.trx v ≫ i) ≫ A'.hom ≫ 𝟙 _ =
      spMap (algebraMap (DualNumber K) ((fibMor h).isMor.obj P.ext).B) :=
    ((fibMor h).isMor.obj (P.tr v).triv).w
  have et : spMap ((fibMor h).isMor.obj P.ext).π ≫ P.trx v ≫ i = ((fibMor h).isMor.obj P.ext).x :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ i) ((P.isTransl_trx v).red hv))
  refine ⟨hc, ec, ht, et, ?_⟩
  refine congrArg₂ (· - ·) (ev_eq_of_triv ω ?a (idLift _ _ hc ec) ((fibMor h).isMor.functor.map P.sec) rfl rfl ?ea)
    (ev_eq_of_triv ω ?b (idLift _ _ ht et) ((fibMor h).isMor.functor.map (P.tan hv)) rfl rfl ?eb)
  case a =>
    exact { φ := { algebraMap P.B (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := algebraMap P.B (DualNumber P.B)
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := rfl }
  case b =>
    exact { φ := { RingHom.id (DualNumber P.B) with commutes' := fun _ ↦ rfl }
            φ₀ := RingHom.id _
            comm := fun _ ↦ rfl
            dp := isDPMorphism_of_eq_bot _ rfl _ _
            pt := by
              show spMap (RingHom.id (DualNumber P.B)) ≫ P.trx v ≫ i = P.trx v ≫ i
              rw [Cris.spMap_id, Category.id_comp] }
  case ea => exact thickHom_ext fun _ ↦ rfl
  case eb => exact thickHom_ext fun _ ↦ rfl

theorem liftVal_sub_snd : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  intro K _ A _ A' _ i h hA ω U hU P hP y₁ y₂ h₁ h₂ n u c hu hdiff
  obtain ⟨m, r, t, H⟩ := GlobalTheory.T.exists_crystallineForm_lift_difference_eq_sum (DualNumber K) A'.left (A'.hom ≫ 𝟙 _) ω U hU
  have hPU : ⊤ ≤ (P.x ≫ i) ⁻¹ᵁ U := hP
  have red : ∀ c : DualNumber P.B, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) c = c.fst :=
    fun _ ↦ rfl
  have hU₁ : ⊤ ≤ y₁ ⁻¹ᵁ U := le_preimage_of_red _ red h₁.2 hPU
  have hU₂ : ⊤ ≤ y₂ ⁻¹ᵁ U := le_preimage_of_red _ red h₂.2 hPU
  have k1 := H ((liftMor (epsDP K) h).isMor.obj P.eps) (SqExt.ofModule K P.B P.B).sq rfl y₁ y₂ h₁.1 h₂.1
    h₁.2 h₂.2 hU₁ hU₂
  have e1 : liftVal h ω.1 h₁ - liftVal h ω.1 h₂ =
      -∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
    rw [← neg_sub]; exact congrArg Neg.neg k1
  have f2 : ∀ f, (valR y₂ U f).fst = valR P.x (i ⁻¹ᵁ U) ((i.app U).hom f) := fun f ↦ by
    rw [← GlobalTheory.Points.valR_comp, ← h₂.2, GlobalTheory.Points.valR_spMap_comp _ _ _ hU₂]; exact (red _).symm
  have step2 : ∀ a, ∑ k, valR P.x (i ⁻¹ᵁ U) ((i.app U).hom (r k)) *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd =
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
    intro a
    have X := ev_sec_sub_ev_tan (K := K) (A := A) (A' := A') (i := i) h ω P (hu a)
    obtain ⟨hc, ec, ht, et, E⟩ := X
    have F := GlobalTheory.T.invariantForm_abelianVariety_translate_value K A hA (u a) (hu a) ((fibMor h).isMor.pullForm ω) P
    have hUt : ⊤ ≤ (P.trx (u a) ≫ i) ⁻¹ᵁ U := fun p hp ↦ hP.tr (hu a) hp
    have hUc : ⊤ ≤ (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) ⁻¹ᵁ U :=
      fun _ _ ↦ hPU (Set.mem_univ _)
    have k2 := H ((fibMor h).isMor.obj P.ext) (SqExt.ofModule K P.B P.B).sq rfl _ _ ht hc et ec hUt hUc
    have F3 : (∑ k, valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (r k) *
        (valR (P.trx (u a) ≫ i) U (t k) - valR (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x ≫ i) U (t k))) =
        TrivSqZeroExt.inr (algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω))) := k2.symm.trans (E.symm.trans F)
    have F' := congrArg (fun z : DualNumber P.B ↦ z.snd) F3
    simp only [TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_sum] at F'
    rw [← F']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_spMap_comp _ _ _ hPU, GlobalTheory.Points.valR_comp,
      GlobalTheory.Points.valR_comp, GlobalTheory.Points.valR_comp]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have D : ∀ k, valR y₁ U (t k) - valR y₂ U (t k) = TrivSqZeroExt.inr (∑ a, c a *
      (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom (t k))).snd) := fun k ↦ hdiff (t k)
  refine (congrArg (fun z : DualNumber P.B ↦ z.snd) e1).trans ?_
  have G := Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) ↦ congrArg (valR y₂ U (r k) * ·) (D k)
  refine (congrArg (fun z : DualNumber P.B ↦ (-z).snd) G).trans ?_
  simp only [TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, f2, smul_eq_mul, MulOpposite.op_zero,
    zero_smul, add_zero, neg_inj]
  simp only [← step2, Finset.mul_sum]
  clear H k1 e1 hdiff D G step2 f2 red
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end GlobalTheory.CechKS.LiftDiff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSubStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderDeformation_form_lift_values_sub : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  first | exact @GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | exact GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | (intros; apply GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformation
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem cechPt_over (P : GPt A) : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
  (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w

@[reducible] def Pt.cst (P : GPt A) : GPt A where
  B := DualNumber P.B
  x := spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x
  w := (congrArg (_ ≫ ·) (Category.comp_id A.hom)).trans (by
    rw [Category.assoc, cechPt_over, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

theorem Pt.In.cst {P : GPt A} {U : A.left.Opens} (h : P.In U) : P.cst.In U :=
  fun _ _ ↦ h (Set.mem_univ _)

theorem cst_base (P : GPt A) :
    (dualMap (algebraMap K P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber P.B) := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_dualMap (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K (DualNumber P.B)) = algebraMap K P.B := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_inl (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem cst_red (P : GPt A) :
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x = P.x := by
  show _ ≫ spMap _ ≫ P.x = P.x
  rw [← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]

theorem cst_val (P : GPt A) {U : A.left.Opens} (hU : P.In U) (g : Γ(A.left, U)) :
    TrivSqZeroExt.fst (valR P.cst.x U g) = valR P.x U g := by
  show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hU]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem cst_trx_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : P.In U)
    (g : Γ(A.left, U)) : TrivSqZeroExt.fst (valR (P.cst.trx v) U g).snd = (valR (P.trx v) U g).snd := by
  have hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U := hU.cst.tr hv
  have hm := (P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  have e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B :=
    fst_comp_dualMap P
  rw [e1, cst_red] at hm
  rw [← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]
  simp [dualMap]

theorem eps_eq (P : GPt A) :
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps = TrivSqZeroExt.inr 1 := by
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, RingHom.algebraMap_toAlgebra]

theorem cechKS_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  intro K _ A _ A' _ i L n u θ hu h
  obtain ⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩ := h
  have hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
      P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) :=
    fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)
  refine ⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x,
    hcov, hWc, ?_, ?_, ?_⟩
  · intro k P hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    obtain ⟨h1, h2, -⟩ := hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst
    refine ⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩
    let I := Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}
    have hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0 := by
      intro a ha
      change a ∈ Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps} at ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [eps_eq P]
      simp
    change spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x =
      spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i at h2
    have hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) =
        (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) := RingHom.ext fun _ ↦ rfl
    calc spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ _
        = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x := by
          rw [← Category.assoc, ← Cris.spMap_comp, hq]
          rfl
      _ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]
      _ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]
      _ = P.x ≫ i := by rw [cst_red]
  · intro k P Q φ hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra
    let ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B :=
      { dualMap (φ.ρ : P.B →+* Q.B) with
        commutes' := fun r ↦ by
          ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }
    have h3 := (hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ
    have hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x := by
      show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
      rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
    exact h3.trans (congrArg _ hc)
  · intro k k' P U f hk hk' hU
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    have ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)))
        P.cst.x (u a) (P.cst.trx (u a)) := fun a ↦ by
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      exact P.cst.isTransl_trx (u a)
    have hd := hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst)
      hU.cst ht
    refine hd.trans ?_
    have hg : P.In (L.U (c k) ⊓ L.U (c k')) := (hk.mono (hWc k)).inf (hk'.mono (hWc k'))
    have e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd =
        (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd := fun a ↦ cst_trx_val P (hu a) hg _
    have e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd =
        (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd := fun a ↦ cst_trx_val P (hu a) hU _
    have e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val :=
      cst_val P hg _
    have e4 : ∀ r : K, TrivSqZeroExt.fst
        (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r := by
      intro r
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [eps_eq P]
    have hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst := fun S ↦ by
      ext <;> simp
    rw [hS]
    congr 1
    change (TrivSqZeroExt.fstHom K P.B P.B) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]
    simp only [e1, e2, e3, e4, dlog, Finset.sum_mul]

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformationStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_cechKodairaSpencerDeformation : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  first | exact @GlobalTheory.CechKS.cechKS_lifts | exact GlobalTheory.CechKS.cechKS_lifts | (intros; apply GlobalTheory.CechKS.cechKS_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLif
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLif
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftTriv

section General

variable {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] {I₁ : Ideal R₁} {I₂ : Ideal R₂}
  {I' : Ideal R'} {X₁ X₂ X' : Scheme.{0}} {κ₁ : DividedPowers I₁} {κ₂ : DividedPowers I₂} {κ' : DividedPowers I'}
  {s₁ : X₁ ⟶ Sp R₁} {s₂ : X₂ ⟶ Sp R₂} {s' : X' ⟶ Sp R'} {σ₁ : R₁ →+* R'} {σ₂ : R₂ →+* R'}
  {p₁ : X' ⟶ X₁} {p₂ : X' ⟶ X₂}

def pv (h : IsMor κ₁ s₁ κ' s' σ₁ p₁) (f : Z1 (O κ₁ s₁)) {T T' : Thick κ' s'} (φ : T ⟶ T') : T'.B :=
  ev f (h.functor.map φ)

theorem exists_of_pull1_eq (h₁ : IsMor κ₁ s₁ κ' s' σ₁ p₁) (h₂ : IsMor κ₂ s₂ κ' s' σ₂ p₂) (f : Z1 (O κ₁ s₁))
    (g b : Z1 (O κ₂ s₂)) (r : R')
    (e : h₁.pull1 (H1.mk _ f) = h₂.pull1 (H1.mk _ g) + r • h₂.pull1 (H1.mk _ b)) :
    ∃ G : ∀ T : Thick κ' s', T.B, ∀ (T T' : Thick κ' s') (φ : T ⟶ T'),
      G T' - φ.φ (G T) = pv h₁ f φ - (pv h₂ g φ + algebraMap R' T'.B r * pv h₂ b φ) := by
  have e' : H1.mk (O κ' s') (h₁.coef.pullbackOneCocycle f) =
      H1.mk (O κ' s') (h₂.coef.pullbackOneCocycle g + r • h₂.coef.pullbackOneCocycle b) := by
    rw [map_add (f := _), map_smul]
    exact e
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 e'
  refine ⟨G, fun T T' φ ↦ ?_⟩
  rw [← Algebra.smul_def]
  exact congrFun (congrFun (congrFun hG T) T') φ

theorem form_idLift {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Form s)
    {T T' : Thick (dp0 R) s} (Φ : T ⟶ T') (y : Sp T.B ⟶ X) (hy : y ≫ s = spMap (algebraMap R T.B))
    (ey : spMap T.π ≫ y = T.x) (y' : Sp T'.B ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R T'.B))
    (ey' : spMap T'.π ≫ y' = T'.x) (e : spMap (Φ.φ : T.B →+* T'.B) ≫ y = y') :
    ev f.1 Φ = ev f.1 (idLift T' y' hy' ey') - Φ.φ (ev f.1 (idLift T y hy ey)) := by
  let a : Thick.triv T.B y hy ⟶ Thick.triv T'.B y' hy' := Thick.trivHom Φ.φ e
  have k := Form.ev_sq f a (idLift T' y' hy' ey') (idLift T y hy ey) Φ rfl rfl fun _ ↦ rfl
  exact eq_sub_of_add_eq' k.symm

end General

section Eps

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]


omit [GrpObj A] in
def epsHom {P Q : GPt A} (φ : P.Hom Q) : P.eps ⟶ Q.eps :=
  letI := P.eps.alg
  letI := Q.eps.alg
  { φ := { dualMap (φ.ρ : P.B →+* Q.B) with
      commutes' := fun r ↦ by
        change dualMap (φ.ρ : P.B →+* Q.B) (dualMap (algebraMap K P.B) r) = dualMap (algebraMap K Q.B) r
        ext <;> simp [dualMap] }
    φ₀ := (φ.ρ : P.B →+* Q.B)
    comm := fun c ↦ by
      change φ.ρ c.fst = (dualMap (φ.ρ : P.B →+* Q.B) c).fst
      simp [dualMap]
    dp := isDPMorphism_sqDP (SqExt.ofModule K P.B P.B).sq (SqExt.ofModule K Q.B Q.B).sq _ fun a ha ↦ by
      have ha' : a.fst = 0 := ha
      change (dualMap (φ.ρ : P.B →+* Q.B) a).fst = 0
      simp [dualMap, ha']
    pt := φ.pt }

def epsSec (P : GPt A) : P.triv ⟶ (constMor A).isMor.obj P.eps :=
  letI := ((constMor A).isMor.obj P.eps).alg
  Thick.trivHom
    { (TrivSqZeroExt.inlAlgHom K P.B P.B : P.B →+* DualNumber P.B) with
      commutes' := fun r ↦ by
        change TrivSqZeroExt.inl (algebraMap K P.B r) =
          dualMap (algebraMap K P.B) (algebraMap K (DualNumber K) r)
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] }
    (by
      change spMap (RingHom.id P.B) ≫ P.x = P.x ≫ (𝟙 A : A ⟶ A).left
      simp [Cris.spMap_id])

def secVal (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (P : GPt A) : DualNumber P.B := ev f (epsSec P)

theorem pv_const (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) {P Q : GPt A} (φ : P.Hom Q) :
    (pv (constMor A).isMor f (epsHom φ) : DualNumber Q.B) =
      TrivSqZeroExt.inl (ev f φ.triv : Q.B) + secVal f Q - dualMap (φ.ρ : P.B →+* Q.B) (secVal f P) := by
  have k := Cris.ev_sq f φ.triv (epsSec Q) (epsSec P) ((constMor A).isMor.functor.map (epsHom φ)) fun c ↦ by
    change (TrivSqZeroExt.inl (φ.ρ c) : DualNumber Q.B) = dualMap (φ.ρ : P.B →+* Q.B) (TrivSqZeroExt.inl c)
    ext <;> simp [dualMap]
  exact eq_sub_of_add_eq' (G := DualNumber Q.B) k.symm

variable {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}

theorem pv_lift (h : IsGrpPullback A A' (DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    {P Q : GPt A} (φ : P.Hom Q) {y : Sp (DualNumber P.B) ⟶ A'.left} {y' : Sp (DualNumber Q.B) ⟶ A'.left}
    (hy : IsLift i P y) (hy' : IsLift i Q y') (e : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y') :
    (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) =
      liftVal h ω'.1 hy' - dualMap (φ.ρ : P.B →+* Q.B) (liftVal h ω'.1 hy) := by
  exact form_idLift ω' ((liftMor (epsDP K) h).isMor.functor.map (epsHom φ)) y hy.1 hy.2 y' hy'.1 hy'.2 e

end Eps

theorem eps_part_eq_coboundary (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hyp : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) +
      (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left)
      (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'),
      spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' →
      ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  obtain ⟨G₀, hG⟩ := exists_of_pull1_eq (liftMor (epsDP K) h).isMor (constMor A).isMor ω'.1 ω.1 b
    DualNumber.eps hyp
  let G₁ : ∀ P : GPt A, DualNumber P.B := fun P ↦ G₀ (Pt.eps P)
  refine ⟨fun P ↦ -(secVal ω.1 P).snd - (secVal b P).fst - (G₁ P).snd, fun P Q φ y y' hy hy' e ↦ ?_⟩
  have k : G₁ Q - dualMap (φ.ρ : P.B →+* Q.B) (G₁ P) =
      (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) -
        ((pv (constMor A).isMor ω.1 (epsHom φ) : DualNumber Q.B) +
          dualMap (algebraMap K Q.B) DualNumber.eps * (pv (constMor A).isMor b (epsHom φ) : DualNumber Q.B)) :=
    hG P.eps Q.eps (epsHom φ)
  rw [pv_lift h ω' φ hy hy' e, pv_const, pv_const] at k
  have k2 := congrArg TrivSqZeroExt.snd k
  simp [dualMap] at k2
  simp only [map_add (f := _), map_sub, map_neg]
  linear_combination k2

end GlobalTheory.CechKS.LiftTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLifStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))), (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) + (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b) → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left) (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'), spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' → ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  first | exact @GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | exact GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | (intros; apply GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

theorem exists_const_add_eps_const {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    (z : TensorProduct K (DualNumber K) (primDR A)) :
    ∃ a b : primDR A, liftSemi (constMor A).pull z =
      (constMor A).pull a + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  induction z with
  | add x y hx hy =>
    obtain ⟨a, b, e⟩ := hx
    obtain ⟨a', b', e'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add (f := _), e, e', map_add (f := _), map_add (f := _), smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul]
    have e1 : (TrivSqZeroExt.inl r.fst : DualNumber K) = algebraMap K (DualNumber K) r.fst := rfl
    have e2 : (TrivSqZeroExt.inr r.snd : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, mul_comm]
    have er : r = algebraMap K (DualNumber K) r.fst + DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [← e1, ← e2, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
    conv_lhs => rw [er]
    exact add_smul _ _ _

theorem liftMor_pull_eq_const_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A,
      (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) +
        (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  intro P K _ A _ A' _ i h g hA hg x
  have a₀ : IsAbelianScheme A := by
    haveI := hA.comm
    haveI : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP K) h).pull x)
  obtain ⟨a, b, e⟩ := exists_const_add_eps_const z
  rw [hz] at e
  have red : (redMor A).pull ((liftMor (epsDP K) h).pull x) = (fibMor h).pull x :=
    GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (fibMor h) (fun _ => rfl) (by simp) x
  have ra : (fibMor h).pull x = a := by
    rw [← red, e, map_add (f := _), LinearMap.map_smulₛₗ, redMor_constMor, redMor_constMor]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom (DualNumber.eps : DualNumber K) = 0 := rfl
    rw [this, zero_smul, add_zero]
  exact ⟨b, by rw [ra]; exact e⟩

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEpsStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A, (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  first | exact @GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | exact GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | (intros; apply GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
set_option autoImplicit false

noncomputable section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.CechKS


set_option maxHeartbeats 1000000 in
theorem exists_isRep_eps {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i) (hA : IsAbelianScheme A)
    (L : LB A.left) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (hu : ∀ a, IsTangent (u a))
    (H : IsCechKS A A' i L u θ) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (e : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') =
      (constMor A).isMor.pull1 (Form.cl _ ((fibMor h).isMor.pullForm ω')) +
        (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), ⨆ j, (V j).1 = ⊤ ∧ (∀ j, (V j).1 ≤ L.U (τ j)) ∧
      IsRep (fun j ↦ (V j).1) b fun j j' P ↦ -∑ a, (∑ c, algebraMap K P.B (θ a c) * dlog L (u c) (τ j) (τ j') P) *
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω')) := by
  classical
  obtain ⟨J, W, c, y, hW, hc, hl, hn, hd⟩ := GlobalTheory.T.exists_lifts_of_cechKodairaSpencerDeformation K A A' i L n u θ hu H
  obtain ⟨G, hG⟩ := GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts K A A' i h ω' _ b e
  let J' : Type := {p : J × A'.left.affineOpens × A.left.affineOpens // p.2.2.1 ≤ W p.1 ⊓ i ⁻¹ᵁ p.2.1.1}
  refine ⟨J', fun j ↦ j.1.2.2, fun j ↦ c j.1.1, ?_, fun j ↦ (j.2.trans inf_le_left).trans (hc _), ?_⟩
  · refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hW.ge (Set.mem_univ p))
    obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := A'.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i p)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ W k ⊓ i ⁻¹ᵁ U from ⟨hk, hpU⟩) (W k ⊓ i ⁻¹ᵁ U).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(k, ⟨U, hU⟩, ⟨V, hV⟩), hle⟩, hpV⟩
  · have hin : ∀ (j : J') (P : GPt A), P.In j.1.2.2.1 → P.In (W j.1.1) := fun j P hP ↦
      hP.mono (j.2.trans inf_le_left)
    refine ⟨fun j P ↦ if hP : P.In (W j.1.1) then (liftVal h ω'.1 (hl _ P hP)).snd + G P else 0,
      fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
    · simp only [dif_pos (hin j P hP), dif_pos (hin j Q (hP.map φ))]
      exact hG P Q φ _ _ _ _ (hn _ P Q φ (hin j P hP))
    · simp only [dif_pos (hin j P hj), dif_pos (hin j' P hj')]
      have hU : P.In (i ⁻¹ᵁ j.1.2.1.1) := hj.mono (j.2.trans inf_le_right)
      rw [add_sub_add_right_eq_sub, ← TrivSqZeroExt.snd_sub]
      exact GlobalTheory.T.firstOrderDeformation_form_lift_values_sub K A A' i h hA ω' _ j.1.2.1.2 P hU _ _ _ _ n u _ hu
        fun f ↦ hd _ _ P _ f (hin j P hj) (hin j' P hj') hU

theorem eval_eq_zero {K M I : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype I] {n : ℕ}
    (f k : Module.Dual K M) (b x : M) (c : I → M) (θ : Matrix (Fin n) (Fin n) K) (hb : Fin n → Module.Dual K M)
    (α p : Fin n → K) (t : Fin n → I → K) (e4 : ∀ a, hb a x = α a) (e5 : ∀ b, p b = ∑ k, f (c k) * t b k)
    (e1 : f (b + ∑ a, ∑ b, (θ a b * α a) • ∑ k, t b k • c k) = 0)
    (e2 : (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (k x) : DualNumber K) +
      (DualNumber.eps : DualNumber K) • (TrivSqZeroExt.inl (f b) + TrivSqZeroExt.inr (k b) : DualNumber K) = 0) :
    (k - ∑ a, (∑ b, θ a b * p b) • hb a) x = 0 := by
  have e3 := congrArg TrivSqZeroExt.snd e2
  have e6 : ∀ b, ∑ k, t b k * f (c k) = p b := fun b ↦
    (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (e5 b).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, e6] at e1
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, e4, Finset.sum_mul]
  simp at e3
  have e7 : ∑ a, ∑ b, θ a b * p b * α a = ∑ a, ∑ b, θ a b * α a * p b :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [e7]
  linear_combination e3 - e1


set_option maxHeartbeats 1000000 in
theorem isKSValue_of_isCechKS (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i)
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g A'.hom) (L : LB A.left) (hL : L.IsLB) (ψ : LinearMap.BilinForm K (HdR A))
    (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K)
    (hu : ∀ a, IsTangent (u a)) (H : IsCechKS A A' i L u θ) (hb : Fin n → HdR A)
    (hhb : ∀ b, DeRham.IsLieImage (hb b) (u b)) {f : HdR A} (hf : f ∈ Fil A) :
    IsKSValue h f (FlagTan.lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) u) := by
  classical
  obtain ⟨v, k, ⟨d, hd, hdk⟩, -⟩ := IsKSValue.exists_of_isAbelianScheme P h hA' hg' hf
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := GlobalTheory.T.firstChern_eq_sum_cup_invariantForms P K A g hA hg L hL ψ hψ
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have key : k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a ∈ Fil A := by
    letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
    obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA' hg' K A i h
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro x hx
    refine (Submodule.span_le (p := LinearMap.ker (k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a))).2
      (fun x hx ↦ ?_) hx
    obtain ⟨⟨x, hx'⟩, hx, rfl⟩ := hx
    have hx0 := hx
    change x ∈ F1 _ at hx
    rw [hodgeFiltration_eq_range] at hx
    obtain ⟨ω', rfl⟩ := hx
    obtain ⟨b, hbe⟩ := GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps P K A A' i h g hA' hg' ⟨_, hx'⟩
    obtain ⟨zb, hzb⟩ := H1.mk_surjective _ b.1
    let ω₀ := (fibMor h).isMor.pullForm ω'
    have hω₀ : Form.cl _ ω₀ ∈ primDR A := (fibMor h).pullback_mem_primitive hx'
    obtain ⟨J, V, τ, hV, hτ, hrep⟩ := exists_isRep_eps h hA L u θ hu H ω' zb (by
      rw [hzb]; exact congrArg Subtype.val hbe)
    have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
      simpa only [hz] using hch
    have hr := fun a ↦ GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' (u a) (hu a) J V τ hτ
    have hsum := hrep.add (IsRep.sum Finset.univ fun a _ ↦ IsRep.sum Finset.univ fun b _ ↦
      (hr b).smul (θ a b * tanVal (u a) ω₀))
    have hF1 := GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero K _ _ J _ hV _ (hsum.congr (F' := 0) fun j j' Q _ _ ↦ by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, map_mul,
        Finset.sum_mul]
      rw [neg_add_eq_zero]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_right_comm _ _ _)
    have hmem : b + ∑ a, ∑ b, (θ a b * tanVal (u a) ω₀) • ∑ k, tanVal (u b) (ω k) • c k ∈ PrimitiveSubmodule A := by
      refine Submodule.mem_comap.2 ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul, hz, hzb] at hF1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_smul]
      exact hF1
    have e1 := (Submodule.mem_dualAnnihilator _).1 hf _ hmem
    have e2 : d ((liftMor (epsDP K) h).pull ⟨_, hx'⟩) = 0 :=
      (Submodule.mem_dualAnnihilator _).1 hd _ hx0
    rw [hbe, map_add (f := _), map_smul, hdk, hdk] at e2
    have e4 : ∀ a, hb a ⟨_, hω₀⟩ = tanVal (u a) ω₀ := fun a ↦ (hhb a).2 ω₀ hω₀
    have e5 : ∀ b, ψ f (hb b) = ∑ k, f (c k) * tanVal (u b) (ω k) := fun b ↦
      (hψf f hf (hb b)).trans (Finset.sum_congr rfl fun k _ ↦ congrArg (f (c k) * ·) ((hhb b).2 (ω k) (hω k)))
    exact eval_eq_zero f k b ⟨_, hω₀⟩ c θ hb _ _ _ e4 e5 e1 e2
  refine ⟨k, ⟨d, hd, hdk⟩, ?_⟩
  have := (FlagTan.isLieImage_lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) hhb).add (isLieImage_one_iff.2 key)
  rwa [add_sub_cancel, _root_.mul_one] at this

end GlobalTheory.CechKS

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.CechKS.exists_const_isKSValue : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  intro P
  refine ⟨1, one_ne_zero, ?_⟩
  intro K _ _ A _ A' _ i h g hA hg hA' hg' L hL ψ hψ n u θ hu H hb hhb f hf w hw
  obtain ⟨u', hu', rfl⟩ := hw
  have := GlobalTheory.CechKS.isKSValue_of_isCechKS P.p5 h hA hg hA' hg' L hL ψ hψ u θ hu H hb hhb hf
  convert this using 1
  rw [GlobalTheory.FlagTan.lieComb]
  congr 2
  funext a
  refine Over.OverMorphism.ext ((hu' a).trans ?_)
  simp only [Rat.cast_one, one_mul]
  rfl

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullbackStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_pairing_pullback : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  first | exact @GlobalTheory.CechKS.exists_const_isKSValue | exact GlobalTheory.CechKS.exists_const_isKSValue | (intros; apply GlobalTheory.CechKS.exists_const_isKSValue <;> assumption)
end
