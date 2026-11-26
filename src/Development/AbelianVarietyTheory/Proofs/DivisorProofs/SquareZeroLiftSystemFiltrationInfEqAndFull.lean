module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mem_map_algebraMap_of_algHom {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) :
    e x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (e : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem K_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ →
    ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧
      (S.Full hI → S'.Full hI) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc
  have key : ∀ S S' : Sys I π s₀,
      S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ≤ S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    intro S S' c hc'
    obtain ⟨hcK, hcI⟩ := hc'
    obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
    obtain ⟨-, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S S' Φ
    obtain ⟨z, z', hz, hmk, hmk', hzz⟩ := h3 c hcI
    have h0 : H1.mk _ z = 0 := hmk.trans (LinearMap.mem_ker.1 hcK)
    obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S z hz h0
    refine ⟨LinearMap.mem_ker.2 ?_, hcI⟩
    rw [← hmk']
    refine H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
    funext U V a
    rw [h2 g hg U V a, hdg, hzz]
  refine fun S S' ↦ ⟨le_antisymm (key S S') (key S' S), fun hF z₁' hz₁' ↦ ?_⟩
  obtain ⟨Ψ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S' S
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S' S Ψ
  obtain ⟨z₁, hz₁, hz₁e⟩ := h1 z₁' hz₁'
  obtain ⟨c, hcI, hc₁⟩ := hF z₁ hz₁
  obtain ⟨y', y, hy'I, hy', hy, hyy⟩ := h3 c hcI
  have hyI : S.IsIdealValuedLiftSystemCocycle y := fun U V a ↦ by
    rw [hyy]; exact mem_map_algebraMap_of_algHom (Ψ.φ V : S'.F.obj V →ₐ[R] S.F.obj V) (hy'I U V a)
  have hd : H1.mk _ (y - z₁) = 0 := by rw [map_sub, hy, hc₁, sub_self]
  obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S (y - z₁)
    (fun U V a ↦ Ideal.sub_mem _ (hyI U V a) (hz₁ U V a)) hd
  let g' : C0 S'.F := fun W ↦ (Ψ.φ W).symm (g W)
  have hg' : S'.IsIdealValuedLiftSystemCochain g' := fun W ↦
    mem_map_algebraMap_of_algHom ((Ψ.φ W).symm : S.F.obj W →ₐ[R] S'.F.obj W) (hg W)
  have hgg : (fun W ↦ Ψ.φ W (g' W)) = g := funext fun W ↦ AlgEquiv.apply_symm_apply _ _
  refine ⟨c, hcI, hy'.symm.trans (H1.mk_eq_mk.2 ⟨g', ?_⟩)⟩
  funext U V a
  apply (Ψ.φ V).injective
  have e := h2 g' hg' U V a
  rw [hgg, hdg] at e
  rw [← e]
  show y.1 U V a - z₁.1 U V a = Ψ.φ V (y'.1 U V a - z₁'.1 U V a)
  rw [map_sub, hyy, hz₁e]
end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFullStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZeroLiftSystem_filtration_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧ (S.Full hI → S'.Full hI) := by
  first | exact @GlobalTheory.LiftSys.K_inf_eq_and_full | exact GlobalTheory.LiftSys.K_inf_eq_and_full | (intros; apply GlobalTheory.LiftSys.K_inf_eq_and_full <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOne
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  first | exact @GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | exact GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | (intros; apply GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem eq_zero_of_sum_smul_matrix {G : Type} [AddCommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∑ j, M i j • f j = 0) (k : Fin r) : f k = 0 := by
  have e1 : f k = ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) k j • f j := by
    simp [Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_mul M hM]
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem eq_one_of_prod_zpow_matrix {G : Type} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∏ j, f j ^ M i j = 1) (k : Fin r) : f k = 1 := by
  have := eq_zero_of_sum_smul_matrix M hM (fun j => Additive.ofMul (f j)) (fun i => by
    simpa [← ofMul_zpow, ← ofMul_prod] using congrArg Additive.ofMul (h i)) k
  simpa using this

theorem gtRelV_prod_tor_mul {F : Type} [Field F] {N : NumD F} {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → N.X)
    (vs : Fin r → N.Gt) (T : Fin r → (Multiplicative N.X →* Fˣ)) :
    (∏ i, ∏ j, ((N.tor (T j) * vs j).s (x i) * (N.tor (T i) * vs i).s (x j) /
        (N.θ (N.c (x j)) (N.tor (T j) * vs j).b (N.c (x i)) * N.θ (N.c (x j)) (N.tor (T j) * vs j).b
            (N.tor (T i) * vs i).b *
          N.θ (N.c (x i)) (N.tor (T i) * vs i).b (N.c (x j) * (N.tor (T j) * vs j).b))) ^ W i j : Fˣ) =
      (∏ i, ∏ j, ((vs j).s (x i) * (vs i).s (x j) /
        (N.θ (N.c (x j)) (vs j).b (N.c (x i)) * N.θ (N.c (x j)) (vs j).b (vs i).b *
          N.θ (N.c (x i)) (vs i).b (N.c (x j) * (vs j).b))) ^ W i j) *
      ∏ i, ∏ j, (T j (Multiplicative.ofAdd (x i)) * T i (Multiplicative.ofAdd (x j))) ^ W i j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_zpow]
  congr 1
  simp only [NumD.tor_mul_s_apply, NumD.Gt.mul_b, NumD.tor_b, one_mul, div_eq_mul_inv]
  ac_rfl

theorem gtRelV_prod_single {G : Type} [CommGroup G] {A : Type} [AddCommGroup A] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Fin r → (Multiplicative A →* G)) (i : Fin r) (χ : A) :
    (∏ a, ∏ b, (T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) *
        T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b))) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ (W + W.transpose) i j := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h1 : (∏ a, ∏ b, T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W i j := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro a _ ha
      simp [Pi.single_apply, ha]
    · simp
  have h2 : (∏ a, ∏ b, T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W j i := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, Matrix.transpose_apply, zpow_add]

theorem gtRelV_components_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → IsUnit (W + W.transpose).det →
      ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  intro F _ N N' r W φ e wv hT hdet v' vs us hv hu
  have hb : ∀ j, (us j).b = (vs j).b := fun j => (hu.1 j).symm.trans (hv.1 j)
  have ht : ∀ j, ∃ t, N.tor t = us j / vs j := fun j =>
    (N.exists_tor_iff _).2 (by rw [div_eq_mul_inv, NumD.Gt.mul_b, NumD.Gt.inv_b, hb, mul_inv_cancel])
  choose T hT' using ht
  have hus : us = fun j => N.tor (T j) * vs j := funext fun j => by rw [hT', div_mul_cancel]
  subst hus
  have hwv : ∀ x, wv x ≠ 0 := hT.2.2.2.2.2.1
  have key : ∀ χ', (∏ i, ∏ j, (T j (Multiplicative.ofAdd (e χ' i)) * T i (Multiplicative.ofAdd (e χ' j))) ^ W i j) = 1 := by
    intro χ'
    have a := hv.2 χ'
    have b := hu.2 χ'
    rw [a, gtRelV_prod_tor_mul W (e χ') vs T] at b
    have c := mul_right_cancel₀ (hwv _) (mul_right_cancel₀ (hwv 1) b)
    have d := Units.ext c
    exact (mul_eq_left.1 d.symm)
  have hall : ∀ χ j, T j (Multiplicative.ofAdd χ) = 1 := by
    intro χ
    refine eq_one_of_prod_zpow_matrix (W + W.transpose) hdet (fun j => T j (Multiplicative.ofAdd χ)) fun i => ?_
    obtain ⟨χ', hχ'⟩ := hT.2.2.2.1.2 (Pi.single i χ)
    have := key χ'
    rw [hχ', gtRelV_prod_single W T i χ] at this
    exact this
  funext j
  have : T j = 1 := MonoidHom.ext fun m => by simpa using hall m.toAdd j
  rw [this, NumD.tor_one, _root_.one_mul]

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_unique_components : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → IsUnit (W + W.transpose).det → ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_components_unique | exact GlobalTheory.Mum.TensTor.gtRelV_components_unique | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_components_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqDatum

theorem mem_lbPow_U {X : Scheme.{0}} {M : LB X} {n : ℕ} {x : X} {i : PUnit → M.ι} :
    x ∈ (lbPow M n).U i ↔ x ∈ M.U (i PUnit.unit) :=
  ⟨fun h => by simpa using Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => by simpa using h⟩

theorem lbPow_U_le {X : Scheme.{0}} (M : LB X) (n : ℕ) (i : PUnit → M.ι) :
    (lbPow M n).U i ≤ M.U (i PUnit.unit) := fun _ h => mem_lbPow_U.1 h

theorem chart_le {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (n : ℕ) (i j : PUnit → M.ι) :
    chart f (lbPow M n) i j ≤ chart f M (i PUnit.unit) (j PUnit.unit) :=
  inf_le_inf (Scheme.Hom.preimage_mono _ (lbPow_U_le M n i)) (Scheme.Hom.preimage_mono _ (lbPow_U_le M n j))

theorem gm_lbPow_g {X Z : Scheme.{0}} (M : LB X) (n : ℕ) (p : Z ⟶ X) (z : Z) (i i' : PUnit → M.ι)
    (hi : p z ∈ M.U (i PUnit.unit)) (hi' : p z ∈ M.U (i' PUnit.unit)) :
    gm p z _ ((lbPow M n).g i i') = gm p z _ (M.g (i PUnit.unit) (i' PUnit.unit)) ^ n := by
  show gm p z _ (∏ _k : PUnit, (res _ (pullU (𝟙 X) _ (M.g (i PUnit.unit) (i' PUnit.unit)))) ^ ((n : ℕ) : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow, zpow_natCast]
  congr 1
  refine (gm_res p z _ (show p z ∈ LB.wchart M (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart M (fun _ : PUnit => 𝟙 X) i' from
    ⟨(mem_lbPow_U (n := n)).2 hi, (mem_lbPow_U (n := n)).2 hi'⟩) _).trans ?_
  refine (gm_pull p (𝟙 X) z _ (by simpa using And.intro hi hi') _).trans ?_
  rw [Category.comp_id]

theorem gm_pullTop {X Y : Scheme.{0}} (p : X ⟶ Y) (w : X) (u : Γ(Y, ⊤)ˣ) :
    gm (𝟙 X) w ⊤ (GlobalTheory.CharKer.pullTop p u) = gm p w ⊤ u := by
  apply Units.ext
  rw [gm_val _ w ⊤ trivial, gm_val _ w ⊤ trivial]
  simp [GlobalTheory.CharKer.pullTop]
  rfl

end GlobalTheory.SqDatum

namespace GlobalTheory.SqDatum

theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (a b c d x y z : G) (h₁ : d * c = a * b) (h₂ : d ^ 2 * x * y = z) :
    (a ^ 2 * x) * (b ^ 2 * y) = c ^ 2 * z := by
  rw [← h₂]
  calc (a ^ 2 * x) * (b ^ 2 * y) = (a * b) ^ 2 * x * y := by simp only [mul_pow]; ac_rfl
    _ = (d * c) ^ 2 * x * y := by rw [h₁]
    _ = c ^ 2 * (d ^ 2 * x * y) := by simp only [mul_pow]; ac_rfl

def psi {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) : ∀ i j, Γ(pullback f f, chart f (lbPow M 2) i j)ˣ :=
  fun i j => res (chart_le f M 2 i j) (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * res le_top u

theorem gm_psi {X Y Z : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) (p : Z ⟶ pullback f f) (z : Z) (i j : PUnit → M.ι)
    (h : p z ∈ chart f (lbPow M 2) i j) :
    gm p z _ (psi f M φ u i j) = gm p z _ (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * gm p z ⊤ u := by
  dsimp only [psi]
  rw [map_mul, map_pow, gm_res p z _ h, gm_res p z _ h]

theorem pullback_fst_snd_triple_eq_snd_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem pullback_fst_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pr13 f w) = pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_fst]

theorem pullback_snd_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.snd f f (pr13 f w) = pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_snd]

theorem exists_sq_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ),
    DescCompat f M φ → Defect f M φ D → KillsSq f D u →
    ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ),
      M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  intro X Y f M hM φ D u hC hD hK
  have h₂ : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  refine ⟨lbPow M 2, psi f M φ u, h₂, GlobalTheory.lbIso_refl h₂, ?_, ?_⟩
  · intro z i i' j j' hi hi' hj hj'
    rw [gm_psi f M φ u (𝟙 _) z i' j' ⟨hi', hj'⟩, gm_psi f M φ u (𝟙 _) z i j ⟨hi, hj⟩,
      gm_lbPow_g M 2 _ z i i' (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi'),
      gm_lbPow_g M 2 _ z j' j (mem_lbPow_U.1 hj') (mem_lbPow_U.1 hj),
      hC z _ _ _ _ (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi') (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hj')]
    simp only [mul_pow]
    ac_rfl
  · intro w i j k hi hj hk
    have hj' : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ (lbPow M 2).U j := by
      rw [pullback_fst_snd_triple_eq_snd_fst]; exact hj
    have h13 : pr13 f w ∈ chart f (lbPow M 2) i k := by
      refine ⟨?_, ?_⟩
      · exact (show pullback.fst f f (pr13 f w) ∈ (lbPow M 2).U i by rw [pullback_fst_tripleFibreProductProjOneThree]; exact hi)
      · exact (show pullback.snd f f (pr13 f w) ∈ (lbPow M 2).U k by rw [pullback_snd_tripleFibreProductProjOneThree]; exact hk)
    rw [gm_psi f M φ u _ w i j ⟨hi, hj⟩, gm_psi f M φ u _ w j k ⟨hj', hk⟩, gm_psi f M φ u _ w i k h13]
    have hd := hD (Triple f) (𝟙 _) w (i PUnit.unit) (j PUnit.unit) (k PUnit.unit)
      (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hk)
    simp only [Category.id_comp] at hd
    have hk' := congrArg (gm (𝟙 _) w ⊤) hK
    simp only [map_mul, map_pow, gm_pullTop] at hk'
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _ _ _ hd hk'

end GlobalTheory.SqDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_of_defect_killed : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f M φ → Defect f M φ D → KillsSq f D u → ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ), M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  first | exact @GlobalTheory.SqDatum.exists_sq_descent | exact GlobalTheory.SqDatum.exists_sq_descent | (intros; apply GlobalTheory.SqDatum.exists_sq_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

open CartesianMonoidalCategory MonObj
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_comp_stalk {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) {W : Scheme.{0}} (f : W ⟶ (torsion G n).left) (q : W) (c : M)
    (h : ValAt G n ℓ w (f q) c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (z : Sp Ω ⟶ V)
    (hz : y ≫ W.fromSpecStalk q ≫ f ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ W.fromSpecStalk q ≫ f ≫ (torsion.ι G n).left = z ≫ w c := by
  have e := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
  have h1 := h Ω (y ≫ Spec.map (f.stalkMap q)) z (by rw [Category.assoc, reassoc_of% e]; exact hz)
  rwa [Category.assoc, reassoc_of% e] at h1

theorem comp_torsion_ι_mulN {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ torsion G n) :
    (a ≫ torsion.ι G n) ≫ mulN G n = 1 := by
  have e : torsion.ι G n ≫ mulN G n = toUnit (torsion G n) ≫ (η : 𝟙_ (Over X') ⟶ G) :=
    (pullback.condition (f := mulN G n) (g := (η : 𝟙_ (Over X') ⟶ G))).trans
      (congrArg (· ≫ (η : 𝟙_ (Over X') ⟶ G)) (toUnit_unique _ _))
  rw [Category.assoc, e, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem valAt_mul : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ hun hadd K _ _ t P Q PT QT RT hPT hQT hRT x cP cQ cR hcP hcQ hcR
  haveI : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  let h : pullback (torsion G n).hom (torsion G n).hom ⟶ X' :=
    pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  haveI : Etale h := inferInstance
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  haveI : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x)) :=
    isDomain_stalk_of_etale h (pq x)
  obtain ⟨Ω, _, _, y, hy, -⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x))
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat h (pq x) ℓ Ω y hy
  let WO : Over X' := Over.mk h
  let A' : WO ⟶ torsion G n := Over.homMk (pullback.fst (torsion G n).hom (torsion G n).hom) rfl
  let B' : WO ⟶ torsion G n :=
    Over.homMk (pullback.snd (torsion G n).hom (torsion G n).hom) pullback.condition.symm
  let A : WO ⟶ G := A' ≫ torsion.ι G n
  let B : WO ⟶ G := B' ≫ torsion.ι G n
  have hs : (A * B) ≫ mulN G n = 1 := by
    letI : CommGroup (WO ⟶ G) := Hom.commGroup
    rw [GlobalTheory.GrpTangent.comp_mulN, mul_pow, ← GlobalTheory.GrpTangent.comp_mulN, ← GlobalTheory.GrpTangent.comp_mulN,
      comp_torsion_ι_mulN, comp_torsion_ι_mulN, _root_.one_mul]
  obtain ⟨sT, hsT⟩ := exists_lift_torsion n (A * B) hs
  let g : Over.mk t ⟶ WO := Over.homMk pq (by
    show pq ≫ pullback.fst _ _ ≫ _ = t
    rw [pullback.lift_fst_assoc, hPt])
  have hgA : g ≫ A = P := by
    ext1
    simp only [A, A', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_fst_assoc, hPT]
  have hgB : g ≫ B = Q := by
    ext1
    simp only [B, B', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_snd_assoc, hQT]
  have hRT' : pq ≫ sT.left = RT := by
    haveI := mono_torsion_ι G n
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, ← Over.comp_left, hsT, hRT, ← hgA, ← hgB,
      ← MonObj.comp_mul]
    rfl
  have e1 : (pullback.fst (torsion G n).hom (torsion G n).hom) (pq x) = PT x := by
    show (pq ≫ pullback.fst _ _) x = _
    rw [pullback.lift_fst]
  have e2 : (pullback.snd (torsion G n).hom (torsion G n).hom) (pq x) = QT x := by
    show (pq ≫ pullback.snd _ _) x = _
    rw [pullback.lift_snd]
  have e3 : sT.left (pq x) = RT x := by
    show (pq ≫ sT.left) x = _
    rw [hRT']
  rw [← e1] at hcP
  rw [← e2] at hcQ
  rw [← e3] at hcR
  have hP' := valAt_comp_stalk G n ℓ w _ (pq x) cP hcP Ω y z hz
  have hQ' := valAt_comp_stalk G n ℓ w _ (pq x) cQ hcQ Ω y z (by rw [← pullback.condition]; exact hz)
  have hR' := valAt_comp_stalk G n ℓ w sT.left (pq x) cR hcR Ω y z (by rw [Over.w sT]; exact hz)
  let k : Over.mk (z ≫ ℓ) ⟶ WO :=
    Over.homMk (y ≫ (pullback (torsion G n).hom (torsion G n).hom).fromSpecStalk (pq x))
      (by simpa [WO] using hz)
  have hC := hadd Ω z cP cQ (k ≫ A) (k ≫ B) (Over.homMk (z ≫ w (cP + cQ)) (by simp [hw]))
    (by simpa [k, A, A'] using hP') (by simpa [k, B, B'] using hQ') rfl
  rw [← MonObj.comp_mul, ← hsT] at hC
  have hC' := congrArg (fun u => u.left) hC
  simp only [Over.homMk_left, Over.comp_left, k] at hC'
  refine hun Ω z cR (cP + cQ) ?_
  rw [← hR']
  simp only [Category.assoc] at hC'
  exact hC'.symm

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassMulEqAddStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_class_mul_eq_add : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  first | exact @GlobalTheory.TorsSpec.valAt_mul | exact GlobalTheory.TorsSpec.valAt_mul | (intros; apply GlobalTheory.TorsSpec.valAt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG


open GlobalTheory GlobalTheory.RootFG in
theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C], Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  first | exact @GlobalTheory.RootFG.root_fg | exact GlobalTheory.RootFG.root_fg | (intros; apply GlobalTheory.RootFG.root_fg <;> assumption)
end
end
