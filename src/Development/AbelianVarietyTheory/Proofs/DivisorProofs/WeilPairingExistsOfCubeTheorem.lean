module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt GlobalTheory.CartierDual WithConv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilHom

section Alg

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

section Values

variable [Algebra R A] [Algebra R B] {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]

def ev (x : A →ₐ[R] D) (z : B →ₐ[R] D) : A ⊗[R] B →ₐ[R] D :=
  Algebra.TensorProduct.lift x z fun _ _ => Commute.all _ _

theorem ev_comp_left (x : A →ₐ[R] D) (z : B →ₐ[R] D) : (ev x z).comp Algebra.TensorProduct.includeLeft = x :=
  AlgHom.ext fun a => by simp [ev]

theorem ev_comp_right (x : A →ₐ[R] D) (z : B →ₐ[R] D) : (ev x z).comp Algebra.TensorProduct.includeRight = z :=
  AlgHom.ext fun a => by simp [ev]

theorem tensorToHom_ev (f : A →ₐ[R] D) (g : B →ₐ[R] E) (u : A ⊗[R] B) (φ : CartierDual R E) :
    tensorToHom R D E (ev (Algebra.TensorProduct.includeLeft.comp f) (Algebra.TensorProduct.includeRight.comp g) u) φ =
      f (tensorToHom R A B u (transpose g.toLinearMap φ)) := by
  induction u with
  | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
  | tmul a b => simp [ev, tensorToHom_apply]

theorem tensorToHom_mul_right (u v : A ⊗[R] B) (φ ψ : CartierDual R B) :
    tensorToHom R A (B ⊗[R] B)
      (ev Algebra.TensorProduct.includeLeft
          (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft) u *
        ev Algebra.TensorProduct.includeLeft
          (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight) v : A ⊗[R] (B ⊗[R] B))
      (toConv (pair R B B (φ ⊗ₜ ψ))) = tensorToHom R A B u φ * tensorToHom R A B v ψ := by
  induction u with
  | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, add_mul, hs, ht]
  | tmul a b =>
    induction v with
    | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, mul_add, hs, ht]
    | tmul a' b' => simp [ev, tensorToHom_apply, mul_smul, smul_comm (φ.ofConv b)]

theorem tensorToHom_mul_left [Module.Finite R B] [Module.Projective R B] (u v : A ⊗[R] B) (φ : CartierDual R B) :
    tensorToHom R (A ⊗[R] A) B
      (ev (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft)
          Algebra.TensorProduct.includeRight u *
        ev (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight)
          Algebra.TensorProduct.includeRight v : (A ⊗[R] A) ⊗[R] B) φ =
      TensorProduct.map (tensorToHom R A B u) (tensorToHom R A B v) (Coalgebra.comul φ) := by
  induction u with
  | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, add_mul, hs, ht, TensorProduct.map_add_left]
  | tmul a b =>
    induction v with
    | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, mul_add, hs, ht, TensorProduct.map_add_right]
    | tmul a' b' =>
      have key : ∀ t : CartierDual R B ⊗[R] CartierDual R B,
          TensorProduct.map (tensorToHom R A B (a ⊗ₜ b)) (tensorToHom R A B (a' ⊗ₜ b')) t =
            pair R B B t (b ⊗ₜ b') • (a ⊗ₜ a') := fun t => by
        induction t with
        | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, add_smul, hs, ht]
        | tmul f g => simp [tensorToHom_apply, ← smul_tmul', smul_smul, mul_comm]
      rw [key, pair_comul_tmul]
      simp [ev, tensorToHom_apply]

end Values

variable [Bialgebra R A] [Bialgebra R B]

structure IsBimul (u : A ⊗[R] B) : Prop where

  isUnit : IsUnit u

  mul_left : ∀ (D : Type) [CommRing D] [Algebra R D] (x x' : WithConv (A →ₐ[R] D)) (z : B →ₐ[R] D),
    ev (x * x').ofConv z u = ev x.ofConv z u * ev x'.ofConv z u

  mul_right : ∀ (D : Type) [CommRing D] [Algebra R D] (x : A →ₐ[R] D) (z z' : WithConv (B →ₐ[R] D)),
    ev x (z * z').ofConv u = ev x z.ofConv u * ev x z'.ofConv u

theorem conv_incl {D : Type} [CommRing D] [Algebra R D] (j : A ⊗[R] A →ₐ[R] D) :
    (toConv (j.comp Algebra.TensorProduct.includeLeft) * toConv (j.comp Algebra.TensorProduct.includeRight)).ofConv =
      j.comp (Bialgebra.comulAlgHom R A) := AlgHom.ext fun a => by
  rw [AlgHom.convMul_apply]
  refine DFunLike.congr_fun (g := j) ?_ _
  ext <;> simp

variable [Module.Finite R B] [Module.Projective R B] {u : A ⊗[R] B} (h : IsBimul u)

def IsBimul.hom : CartierDual R B →ₐc[R] A where
  __ := tensorToHom R A B u
  counit_comp := LinearMap.ext fun φ => by
    have e := h.mul_left B 1 1 (AlgHom.id R B)
    rw [_root_.mul_one] at e
    have e' := (h.isUnit.map _).mul_eq_left.1 e.symm
    have k : ∀ v : A ⊗[R] B, Coalgebra.counit (tensorToHom R A B v φ) =
        φ (ev (1 : WithConv (A →ₐ[R] B)).ofConv (AlgHom.id R B) v) := fun v => by
      induction v with
      | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
      | tmul a b =>
        change Coalgebra.counit (φ.ofConv b • a) =
          φ.ofConv (algebraMap R B (Coalgebra.counit a) * b)
        rw [← Algebra.smul_def, map_smul, map_smul]
        exact mul_comm _ _
    exact (k u).trans (congrArg φ.ofConv e')
  map_comp_comul := LinearMap.ext fun φ => by
    have e := h.mul_left ((A ⊗[R] A) ⊗[R] B)
      (toConv (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft))
      (toConv (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight))
      Algebra.TensorProduct.includeRight
    rw [conv_incl] at e
    exact (tensorToHom_mul_left u u φ).symm.trans ((congrArg (tensorToHom R _ B · φ) e.symm).trans
      (tensorToHom_ev (Bialgebra.comulAlgHom R A) (AlgHom.id R B) u φ))
  map_one' := by
    have e := h.mul_right A (AlgHom.id R A) 1 1
    rw [_root_.mul_one] at e
    have e' := (h.isUnit.map _).mul_eq_left.1 e.symm
    have k : ∀ v : A ⊗[R] B, tensorToHom R A B v 1 =
        ev (AlgHom.id R A) (1 : WithConv (B →ₐ[R] A)).ofConv v := fun v => by
      induction v with
      | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
      | tmul a b =>
        change (Coalgebra.counit (R := R) b) • a = a * algebraMap R A (Coalgebra.counit b)
        rw [Algebra.smul_def, mul_comm]
    exact (k u).trans e'
  map_mul' φ ψ := by
    have e := h.mul_right (A ⊗[R] (B ⊗[R] B)) Algebra.TensorProduct.includeLeft
      (toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft))
      (toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight))
    rw [conv_incl] at e
    refine Eq.trans ?_ ((congrArg (tensorToHom R A _ · _) e).trans (tensorToHom_mul_right u u φ ψ))
    refine Eq.trans ?_ (tensorToHom_ev (AlgHom.id R A) (Bialgebra.comulAlgHom R B) u _).symm
    exact congrArg (tensorToHom R A B u) (ext_apply fun a => mul_apply φ ψ a)

theorem exists_hom {p : ℕ} (G H : PDivGroup p R) (u : ∀ n, G.A n ⊗[R] H.A n) (h : ∀ n, IsBimul (u n))
    (hl : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (x : G.A n →ₐ[R] D) (z : H.A (n + 1) →ₐ[R] D),
      ev (x.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) z (u (n + 1)) =
        ev x (z.comp (H.mulP n : H.A n →ₐ[R] H.A (n + 1))) (u n)) :
    ∃ w : G ⟶ H.dual, ∀ n χ, w.app n χ = tensorToHom R _ _ (u n) χ :=
  ⟨⟨fun n => (h n).hom, fun n => BialgHom.ext fun χ =>
    (tensorToHom_ev (G.res n : G.A (n + 1) →ₐ[R] G.A n) (AlgHom.id R _) (u (n + 1)) χ).symm.trans
      ((congrArg (tensorToHom R _ _ · χ) (hl n (G.A n ⊗[R] H.A (n + 1)) Algebra.TensorProduct.includeLeft
        Algebra.TensorProduct.includeRight)).trans
        (tensorToHom_ev (AlgHom.id R _) (H.mulP n : H.A n →ₐ[R] H.A (n + 1)) (u n) χ))⟩, fun _ _ => rfl⟩

end Alg

section Geo

variable {S : Scheme.{0}}

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) : ∃ t : LB.Gen (Theta A L), t.IsGen := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

theorem cubWeil_level {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : RigLB A}
    {c : CubicalStr A L} {k l : ℕ} {T : Over S} {x z : T ⟶ A} {ζ ζ' : Γ(T.left, ⊤)ˣ}
    (h : UU.CubWeil c (k * l) x z ζ) (h' : UU.CubWeil c k x (z ^ l) ζ') : ζ = ζ' := by
  have a := (UU.cubWeil_iff_weilIs globalFns_holds hA h.2.1 h.1 _).1 h.symm
  have b := (UU.cubWeil_iff_weilIs globalFns_holds hA h'.2.1 h'.1 _).1 h'.symm
  rw [Nat.cast_mul] at a
  exact inv_injective (PairingLevels.weilIs_value_eq globalFns_holds hA L.isLB c.isGen a b)

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem exists_of_cubical [IsCommMonObj (A ⊗ B)] (hAB : IsAbelianScheme (A ⊗ B)) {M : RigLB (A ⊗ B)}
    (c : CubicalStr (A ⊗ B) M) {𝒜 ℬ : PDivGroup p R} (t : 𝒜.TorsionTower A) (s : ℬ.TorsionTower B) :
    ∃ w : 𝒜 ⟶ ℬ.dual, IsWeilHom t s M.L w := by
  let X : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D], WithConv (𝒜.A n →ₐ[R] D) →* (SpAlg R D ⟶ A ⊗ B) :=
    fun n D _ _ => MonoidHom.mk' (fun x => CartesianMonoidalCategory.lift (spOver x.ofConv ≫ t.y n) 1) fun x x' => by
      ext1 <;> simp [MonObj.mul_comp, t.mul]
  let Z : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D], WithConv (ℬ.A n →ₐ[R] D) →* (SpAlg R D ⟶ A ⊗ B) :=
    fun n D _ _ => MonoidHom.mk' (fun z => CartesianMonoidalCategory.lift 1 (spOver z.ofConv ≫ s.y n)) fun x x' => by
      ext1 <;> simp [MonObj.mul_comp, s.mul]
  have ex : ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ, UU.CubWeil c (p ^ n)
      (X n _ (toConv Algebra.TensorProduct.includeLeft)) (Z n _ (toConv Algebra.TensorProduct.includeRight))
      (unitOn U) := fun n => by
    obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (N := p ^ n)
      (x := X n (𝒜.A n ⊗[R] ℬ.A n) (toConv Algebra.TensorProduct.includeLeft))
      (y := Z n _ (toConv Algebra.TensorProduct.includeRight))
      (by rw [← map_pow, 𝒜.pts_pow_self, map_one]) (by rw [← map_pow, ℬ.pts_pow_self, map_one])
    obtain ⟨U, rfl⟩ := EpsWeil.unitOn_bijective.2 ζ
    exact ⟨U, hζ⟩
  choose U hU using ex
  have at' : ∀ (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (x : WithConv (𝒜.A n →ₐ[R] D))
      (z : WithConv (ℬ.A n →ₐ[R] D)), UU.CubWeil c (p ^ n) (X n D x) (Z n D z)
        (unitOn (Units.map (ev x.ofConv z.ofConv).toRingHom.toMonoidHom (U n))) := fun n D _ _ x z => by
    have h := (hU n).comp (spOver (ev x.ofConv z.ofConv))
    have e₁ : spOver (ev x.ofConv z.ofConv) ≫ X n _ (toConv Algebra.TensorProduct.includeLeft) = X n D x := by
      simp only [X, MonoidHom.mk'_apply, comp_lift, MonObj.comp_one, ← Category.assoc, spOver_comp, ev_comp_left]
    have e₂ : spOver (ev x.ofConv z.ofConv) ≫ Z n _ (toConv Algebra.TensorProduct.includeRight) = Z n D z := by
      simp only [Z, MonoidHom.mk'_apply, comp_lift, MonObj.comp_one, ← Category.assoc, spOver_comp, ev_comp_right]
    rw [e₁, e₂] at h
    exact EpsWeil.map_unitOn (ev x.ofConv z.ofConv).toRingHom (U n) ▸ h
  have um : ∀ {D : Type} [CommRing D] {a : Dˣ} (b d : Dˣ), unitOn a = unitOn b * unitOn d → a.val = b.val * d.val := by
    intro D _ a b d h
    have e : unitOn (b * d) = unitOn b * unitOn d :=
      Units.ext (_root_.map_mul (Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom b.val d.val)
    exact congrArg Units.val ((EpsWeil.unitOn_bijective (D := D)).1 (h.trans e.symm))
  obtain ⟨w, hw⟩ := exists_hom 𝒜 ℬ (fun n => (U n).val)
    (fun n => ⟨(U n).isUnit, fun D _ _ x x' z => by
        have := (at' n D x (toConv z)).mul_left (at' n D x' (toConv z))
        rw [← map_mul] at this
        exact um _ _ ((at' n D (x * x') (toConv z)).unique this),
      fun D _ _ x z z' => by
        have := ((at' n D (toConv x) z).symm.mul_left (at' n D (toConv x) z').symm).symm
        rw [← map_mul, ← mul_inv, inv_inv] at this
        exact um _ _ ((at' n D (toConv x) (z * z')).unique this)⟩)
    fun n D _ _ x z => by
      have a := at' (n + 1) D (toConv (x.comp (𝒜.res n : 𝒜.A (n + 1) →ₐ[R] 𝒜.A n))) (toConv z)
      have b := at' n D (toConv x) (toConv (z.comp (ℬ.mulP n : ℬ.A n →ₐ[R] ℬ.A (n + 1))))
      have e₁ : X (n + 1) D (toConv (x.comp (𝒜.res n : 𝒜.A (n + 1) →ₐ[R] 𝒜.A n))) = X n D (toConv x) := by
        simp only [X, MonoidHom.mk'_apply, ← spOver_comp, Category.assoc, t.res]
      have e₂ : Z n D (toConv (z.comp (ℬ.mulP n : ℬ.A n →ₐ[R] ℬ.A (n + 1)))) = Z (n + 1) D (toConv z) ^ p := by
        ext1 <;> simp only [Z, MonoidHom.mk'_apply, ← spOver_comp, Category.assoc, s.mulP_y, MonObj.pow_comp,
          lift_fst, lift_snd, one_pow, MonObj.comp_pow]
      rw [e₁, pow_succ] at a
      rw [e₂] at b
      exact congrArg Units.val (EpsWeil.unitOn_bijective.1 (cubWeil_level hAB a b))
  exact ⟨w, fun n => ⟨U n, (UU.cubWeil_iff_weilIs globalFns_holds hAB (hU n).1 (hU n).2.1 _).1 (hU n),
    fun χ => (hw n χ).trans (tensorToHom_apply _ _)⟩⟩

end Geo

end GlobalTheory.WeilHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspForm
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowNonzero

theorem gapGe_wt_add_parWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (P : WtPar Dw) (hB : WtBig P) (j : ℕ) (w : Psi H → ℤ) :
    GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (P.wt j + GlobalTheory.FlatLine.parWt Dw w - FlagTan.kap Dw) := by
  intro τ k hk
  have hg := hB.gaps τ k hk
  have b := (P.gap_rem τ k).1
  have c : gap (GlobalTheory.FlatLine.parWt Dw w τ) k = 0 := by
    simp [gap, GlobalTheory.FlatLine.parWt]
  have hC0 : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (Dw.p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (Dw.q : ℤ) := Int.natCast_nonneg _
  push_cast at hg
  have a : (1 : ℤ) ≤ gap (P.u₁ τ) k := by
    nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]
  have e1 := mul_nonneg hD0 (le_trans zero_le_one a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans zero_le_one a)
  have gap_add : ∀ (v w : Fin (Dw.p + Dw.q) → ℤ) (k : ℕ), gap (v + w) k = gap v k + gap w k := fun v w k => by
    unfold gap; split_ifs <;> simp [Pi.add_apply] <;> ring
  have gap_sub : ∀ (v w : Fin (Dw.p + Dw.q) → ℤ) (k : ℕ), gap (v - w) k = gap v k - gap w k := fun v w k => by
    unfold gap; split_ifs <;> simp [Pi.sub_apply] <;> ring
  have gap_nsmul : ∀ (n : ℕ) (v : Fin (Dw.p + Dw.q) → ℤ) (k : ℕ), gap (n • v) k = n * gap v k := fun n v k => by
    unfold gap; split_ifs <;> simp [Pi.smul_apply, nsmul_eq_mul] <;> ring
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, gap_add, gap_sub, gap_nsmul, c]
  push_cast
  nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]


open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.Vanishing.H0 ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory in
theorem ne_zero_of_noBase {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {hB : B.IsLB}
    {W : Submodule k (H0 p B ⊤)} {U : Y.Opens} (h : NoBase hB W U) (hU : (U : Set Y).Nonempty) : ∃ f ∈ W, f ≠ 0 := by
  obtain ⟨y, hy⟩ := hU
  by_contra hne
  push Not at hne
  refine h y hy ((mem_support_baseIdeal hB W y).2 fun s hs hy' => ?_)
  obtain ⟨i, hi⟩ := exists_chart hB y
  have hu := (isUnit_ger_iff _ hi).2 hy'
  rw [ger_toSec, hne s hs, map_zero] at hu
  exact not_isUnit_zero hu

end GlobalTheory.CovTop.LowNonzero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenPtOpen

theorem top_le_preimage_of_valR_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  intro K _ P₀ F _ ψ ξ _ H O hO
  haveI : IsIntegral P₀.A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field P₀.A P₀.isAb
  by_contra hno
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have key : ∀ V : P₀.A.left.Opens, ξ p ∈ V → ⊤ ≤ ξ ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y p]; exact hV
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    P₀.A.left.isBasis_affineOpens) (show ξ p ∈ (⊤ : P₀.A.left.Opens) from trivial)
  obtain ⟨y, hyU, hyO⟩ := nonempty_preirreducible_inter U.isOpen O.isOpen ⟨_, hxU⟩ hO
  obtain ⟨f, hfO, hyf⟩ := (show IsAffineOpen U from hU).exists_basicOpen_le (V := O) ⟨y, hyO⟩ hyU
  have hUt : ⊤ ≤ ξ ⁻¹ᵁ U := key U hxU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  refine hf0 (H U f hUt ?_)
  by_contra hv
  have hu : IsUnit (valR ξ U f) := isUnit_iff_ne_zero.mpr hv
  have hb := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ U hUt f).mp hu
  exact hno (hb.trans (ξ.preimage_mono hfO))

end GlobalTheory.GenPtOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement
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
theorem _root_.GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  first | exact @GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | exact GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | (intros; apply GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.DlogCocycle

theorem resG_resG {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = resG X h u.val := rfl

theorem resG_dlog {Z : Scheme.{0}} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)} (hd : IsField W₀ d)
    {P A T : Z.Opens} (hA : A ≤ W₀) (hTA : T ≤ A) (hAP : A ≤ P) (u : Γ(Z, P)ˣ) :
    resG Z hTA (d A (resG Z hAP u.val) * resG Z hAP u⁻¹.val) =
      d T (resG Z (hTA.trans hAP) u.val) * resG Z (hTA.trans hAP) u⁻¹.val := by
  rw [map_mul, ← hd.2.2 A T hTA hA, resG_resG, resG_resG]

theorem dlog_cocycle : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  intro Z L hL W₀ d hd J W j hW hj i i' i''
  have hT0 : W i ⊓ W i' ⊓ W i'' ≤ W₀ := inf_le_left.trans (inf_le_left.trans (hW i))
  have hT : W i ⊓ W i' ⊓ W i'' ≤ L.U (j i) ⊓ L.U (j i') ⊓ L.U (j i'') :=
    inf_le_inf (inf_le_inf (hj i) (hj i')) (hj i'')
  rw [resG_dlog hd ((inf_le_left : W i ⊓ W i' ≤ W i).trans (hW i)),
    resG_dlog hd ((inf_le_left : W i' ⊓ W i'' ≤ W i').trans (hW i')),
    resG_dlog hd ((inf_le_left : W i ⊓ W i'' ≤ W i).trans (hW i))]
  have e := congrArg (fun u => resG Z hT u.val) (hL.cocycle (j i) (j i') (j i''))
  simp only [Units.val_mul, map_mul, res_val, resG_resG] at e
  have inv : ∀ {P : Z.Opens} (h : W i ⊓ W i' ⊓ W i'' ≤ P) (u : Γ(Z, P)ˣ),
      resG Z h u.val * resG Z h u⁻¹.val = 1 := fun h u => by rw [← map_mul, Units.mul_inv, map_one]
  have e1 := inv (((inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i').trans (inf_le_inf (hj i) (hj i'))))
    (L.g (j i) (j i'))
  have e2 := inv ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'').trans
    (inf_le_inf (hj i') (hj i''))) (L.g (j i') (j i''))
  have e3 := inv ((le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'').trans
    (inf_le_inf (hj i) (hj i''))) (L.g (j i) (j i''))
  generalize resG Z _ (L.g (j i) (j i')).val = x1 at e e1 ⊢
  generalize resG Z _ (L.g (j i') (j i'')).val = x2 at e e2 ⊢
  generalize resG Z _ (L.g (j i) (j i'')).val = x3 at e e3 ⊢
  generalize resG Z _ (L.g (j i) (j i'))⁻¹.val = y1 at e1 ⊢
  generalize resG Z _ (L.g (j i') (j i''))⁻¹.val = y2 at e2 ⊢
  generalize resG Z _ (L.g (j i) (j i''))⁻¹.val = y3 at e3 ⊢
  have hy3 : y3 = y1 * y2 := by
    linear_combination (-y3 * x2 * y2) * e1 - y3 * e2 + y1 * y2 * e3 + y1 * y2 * y3 * e
  rw [← e, hd.2.1 _ hT0, hy3]
  linear_combination (-(d _ x2 * y2)) * e1 - (d _ x1 * y1) * e2

end GlobalTheory.DlogCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransitionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cocycle_condition_log_derivative_transition : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (W₀ : Z.Opens) (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W₀ d → ∀ (J : Type) (W : J → Z.Opens) (j : J → L.ι), (∀ i, W i ≤ W₀) → ∀ (hj : ∀ i, W i ≤ L.U (j i)) (i i' i'' : J), resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) * resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val) + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d (W i' ⊓ W i'') (resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i'')).val) * resG Z (inf_le_inf (hj i') (hj i'')) (L.g (j i') (j i''))⁻¹.val) = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d (W i ⊓ W i'') (resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i'')).val) * resG Z (inf_le_inf (hj i) (hj i'')) (L.g (j i) (j i''))⁻¹.val) := by
  first | exact @GlobalTheory.DlogCocycle.dlog_cocycle | exact GlobalTheory.DlogCocycle.dlog_cocycle | (intros; apply GlobalTheory.DlogCocycle.dlog_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbers
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKS

theorem preimage_eq_of_agree_closedFibre : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  intro k _ X B h π₁ π₂ hyp W
  have hpt : ∀ b : B, π₁ b = π₂ b := by
    intro b
    set x := B.fromSpecResidueField b
    set φ := Spec.preimage (x ≫ h)
    have hφ : Spec.map φ = x ≫ h := Spec.map_preimage _
    have hinr : ∀ c : k, φ.hom (TrivSqZeroExt.inr c) = 0 := by
      intro c
      have : φ.hom (TrivSqZeroExt.inr c) * φ.hom (TrivSqZeroExt.inr c) = 0 := by
        rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
      exact mul_self_eq_zero.mp this
    let ψ : k →+* B.residueField b := φ.hom.comp (TrivSqZeroExt.inlHom k k)
    have hψ : ψ.comp (TrivSqZeroExt.fstHom k k k).toRingHom = φ.hom := by
      refine RingHom.ext fun z => ?_
      conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      rw [map_add (f := _), hinr, add_zero]
      rfl
    have hx : x ≫ h = Spec.map (CommRingCat.ofHom ψ) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
      rw [← hφ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      rfl
    have e := hyp _ x _ hx
    obtain ⟨s⟩ : Nonempty (Spec (B.residueField b)) := inferInstance
    have h1 : (x ≫ π₁) s = (x ≫ π₂) s := by rw [e]
    simpa [x] using h1
  apply TopologicalSpace.Opens.ext
  ext b
  change π₁ b ∈ W ↔ π₂ b ∈ W
  rw [hpt b]

end GlobalTheory.LogKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbersStatement
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
theorem _root_.GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  first | exact @GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre | exact GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre | (intros; apply GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatTermLin

theorem gs_sub_fn {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem sval_sub_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s t : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (s - c • t) r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  have hm := hJ.mem φ r
  have h1 : sval (s - c • t) r z J = sval s r z J - sval (c • t) r z J :=
    gs_sub_fn r z _ hm _ _
  have h2 : sval (c • t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  rw [h1, h2]

theorem gs_constFn {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (e : R) :
    gs r z ⊤ (constFn p ⊤ e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← gs_pull r p z ⊤ trivial]
  exact gs_res r z (U := p ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _

theorem isTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ σ' τ τ' e h h' T x y J hJ
  have a := sval_sub_smul (constFn Y.H.hom ⊤ e) τ' τ x.left y hJ
  have b := sval_sub_smul (constFn Q.P.A.hom ⊤ e) σ' σ (x ≫ Y.q).left y hJ
  rw [gs_constFn, Over.w] at a b
  refine a.trans ?_
  rw [h T x y J hJ, h' T x y J hJ]
  refine Eq.trans ?_ (congrArg (· * _) b).symm
  ring

end GlobalTheory.HeatTermLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  first | exact @GlobalTheory.HeatTermLin.isTerm_sub_smul | exact GlobalTheory.HeatTermLin.isTerm_sub_smul | (intros; apply GlobalTheory.HeatTermLin.isTerm_sub_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSPtUniq

theorem isKS_unique_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (φ : Γ(X, U.1) →+* K) (P₀ : PolAV (Sp K)) (m : P₀.A.left ⟶ t.G.left), ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V → IsGrpPullback P₀.A t.G (spMap φ ≫ chart U) m → LBIso P₀.L (t.PP.L.pull m) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → IsKS t V U v D Θ' → φ.mapMatrix Θ = φ.mapMatrix Θ' := by
  intro E _ _ _ H X t V U n v hv hb K _ _ φ P₀ m hV hpb hiso D Θ Θ' hK hK'
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  set x0 : Sp K ⟶ X := spMap φ ≫ chart U with hx0def
  have hUx : ⊤ ≤ x0 ⁻¹ᵁ U.1 := fun o _ => by
    show (chart U) ((spMap φ) o) ∈ (U.1 : Set X)
    rw [← U.2.range_fromSpec]
    exact ⟨_, rfl⟩
  have hev : GlobalTheory.FlagMod.ev x0 U.1 hUx = φ := GlobalTheory.FlagMod.ev_spMap_tau U.2 φ hUx
  have hx : spMap (GlobalTheory.FlagMod.ev x0 U.1 hUx) ≫ chart U = x0 := by rw [hev]
  have hv' := fun i => GlobalTheory.LieMet.isTan_map (GlobalTheory.FlagMod.ev x0 U.1 hUx) hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map (GlobalTheory.FlagMod.ev x0 U.1 hUx) hx hv hb
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.LiePull.lieBasis_of_tanBasis t x0 P₀.A m hpb _ hv' hb'
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φc, hφc⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd _ m t.PP.L t.PP.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hf, hl, hdiff⟩ := hK
  obtain ⟨J', W', j', d', hcov', hWj', hf', hl', hdiff'⟩ := hK'
  have hP := GlobalTheory.KSUniq.pull_diff t V U v hv Θ W j d hWj hdiff x0 hUx P₀.A m hpb u hu' dd hdd φc hφc
  have hP' := GlobalTheory.KSUniq.pull_diff t V U v hv Θ' W' j' d' hWj' hdiff' x0 hUx P₀.A m hpb u hu' dd hdd φc hφc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W i) hp
    exact this.1
  have hWU' : ∀ i, W' i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov' ▸ (le_iSup W' i) hp
    exact this.1
  have hfib : ∀ z, t.G.hom (m z) ∈ U.1 ⊓ V := fun z => by
    rw [← Scheme.Hom.comp_apply, hpb.1.w, Scheme.Hom.comp_apply]
    exact ⟨hUx (Set.mem_univ _), hV (Set.mem_univ _)⟩
  have hcv : ∀ z, ∃ i, m z ∈ W i := fun z => by
    have h2 : m z ∈ ⨆ i, W i := by rw [hcov]; exact hfib z
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hcv' : ∀ z, ∃ i, m z ∈ W' i := fun z => by
    have h2 : m z ∈ ⨆ i, W' i := by rw [hcov']; exact hfib z
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have := GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hdd t.G.hom x0 m hpb.1 U.2 t.PP.L t.PP.isLB hiso _
    (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hUx (Θ a b))
    (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hUx (Θ' a b))
    W W' j j' d d' hWU hWU' hWj hWj' hcv hcv' hf hf' hl hl' φc hφc hP hP'
  rw [hev] at this
  ext a b
  exact congrFun (congrFun this a) b

end GlobalTheory.KSPtUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPointStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (φ : Γ(X, U.1) →+* K) (P₀ : PolAV (Sp K)) (m : P₀.A.left ⟶ t.G.left), ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V → IsGrpPullback P₀.A t.G (spMap φ ≫ chart U) m → LBIso P₀.L (t.PP.L.pull m) → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → IsKS t V U v D Θ' → φ.mapMatrix Θ = φ.mapMatrix Θ' := by
  first | exact @GlobalTheory.KSPtUniq.isKS_unique_at_point | exact GlobalTheory.KSPtUniq.isKS_unique_at_point | (intros; apply GlobalTheory.KSPtUniq.isKS_unique_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg.BasisPull

theorem exists_basis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h

end GlobalTheory.LocReg.BasisPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentBasis_pullback_to_spec_of_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

theorem le_preimage_of_closedPoint {Z : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Z)
    (V : Z.Opens) (h : y.base (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro p _
  exact ((IsLocalRing.specializes_closedPoint p).map y.continuous).mem_open V.isOpen h

theorem snd_valR_epsMul {Z : Scheme.{0}} {S : Type} [CommRing S] (T : Sp (DualNumber S) ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ T ⁻¹ᵁ O) (a : S) (f : Γ(Z, O)) :
    (valR (spMap (epsMul a) ≫ T) O f).snd = a * (valR T O f).snd := by
  rw [GlobalTheory.Points.valR_spMap_comp (epsMul a) T O h f]
  simp [epsMul]

theorem epsMul_comp_algebraMap {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_epsMul {S : Type} [CommRing S] (a : S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul]

theorem epsMul_zero' {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.VertSpanZero

namespace GlobalTheory.VertSpanZero

theorem spMap_fst_algebraMap (S : Type) [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

def redOver {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) : Over.mk x ⟶ tEpsG x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ x = x
    rw [← Category.assoc, spMap_fst_algebraMap, Category.id_comp])

theorem redOver_comp_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x : Sp S ⟶ X)
    (l : List (tEpsG x ⟶ G)) (hl : ∀ u ∈ l, redOver x ≫ u = 1) : redOver x ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl u List.mem_cons_self,
      ih fun u' h => hl u' (List.mem_cons_of_mem _ h), _root_.mul_one]

theorem red_mul_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g) {n : ℕ}
    (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G))
    (hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (g' * (List.ofFn u).prod).left = g := by
  have h1 : redOver (g ≫ G.hom) ≫ (List.ofFn u).prod = 1 := by
    refine redOver_comp_prod _ _ fun w hw => ?_
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' u w).1 hw
    exact Over.OverMorphism.ext (hu a)
  change (redOver (g ≫ G.hom) ≫ (g' * (List.ofFn u).prod)).left = g
  rw [MonObj.comp_mul, h1, _root_.mul_one]
  change spMap _ ≫ g'.left = g
  rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]

end GlobalTheory.VertSpanZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitLocus

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

theorem natCast_unit_locus (S' : Scheme.{0}) (d : ℕ) : ∃ U : S'.Opens,
    (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  refine ⟨S'.basicOpen ((d : ℕ) : Γ(S', ⊤)), ?_, ?_⟩
  · intro V hV
    apply isUnit_of_basicOpen_eq_top'
    have e := Scheme.preimage_basicOpen_top V.ι ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast] at e
    rw [← e, eq_top_iff]
    intro x _
    show V.ι.base x ∈ S'.basicOpen _
    exact hV (show V.ι x ∈ (V : Set S') by rw [← Scheme.Opens.range_ι V]; exact ⟨x, rfl⟩)
  · intro T g hd
    rintro _ ⟨x, rfl⟩
    have e := Scheme.preimage_basicOpen_top g ((d : ℕ) : Γ(S', ⊤))
    rw [map_natCast, T.basicOpen_of_isUnit hd] at e
    have hx : x ∈ g ⁻¹ᵁ S'.basicOpen ((d : ℕ) : Γ(S', ⊤)) := by rw [e]; trivial
    exact hx

end GlobalTheory.UnitLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_unit_locus_open : ∀ (S' : Scheme.{0}) (d : ℕ), ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.UnitLocus.natCast_unit_locus) | (exact GlobalTheory.UnitLocus.natCast_unit_locus) | (intros; apply GlobalTheory.UnitLocus.natCast_unit_locus  <;> assumption)
end
end
