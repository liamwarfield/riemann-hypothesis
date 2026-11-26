module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem linearIndependent_span_of_dual_unit :
    ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ)
      (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V),
      IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) →
      LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  intro V _ L _ _ n b u f N hN hf
  classical

  let U : Matrix (Fin n) (Fin n) V := Matrix.of fun i k => b.repr (u i) k
  let F : Matrix (Fin n) (Fin n) V := Matrix.of fun k j => f j (b k)
  have hUF : U * F = N • (1 : Matrix (Fin n) (Fin n) V) := by
    ext i j
    have h1 : f j (u i) = ∑ k, b.repr (u i) k * f j (b k) := by
      calc f j (u i) = f j (∑ k, b.repr (u i) k • b k) := by rw [b.sum_repr]
        _ = ∑ k, b.repr (u i) k * f j (b k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.mul_apply, U, F, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← h1, hf]
    split_ifs <;> simp
  have hdet : IsUnit U.det := by
    have h2 : U.det * F.det = N ^ n := by
      rw [← Matrix.det_mul, hUF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact isUnit_of_mul_isUnit_left (h2 ▸ hN.pow n)
  have hb : b.toMatrix u = U.transpose := by
    ext k i
    simp [Module.Basis.toMatrix_apply, U]
  have hdet' : IsUnit (b.toMatrix u).det := by
    rw [hb, Matrix.det_transpose]; exact hdet
  have hdet2 : IsUnit (b.det u) := by
    rw [Module.Basis.det_apply]; exact hdet'
  exact (Module.Basis.is_basis_iff_det b).mpr hdet2

end GlobalTheory.CompanionTheory.CommAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasisStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_family_is_basis : ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ) (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V), IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) → LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | exact GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | (intros; apply GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntC
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntB
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem pt_zero {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ∀ N : ℕ, M.pt (N • e) = M.pt e ^ N
  | 0 => by rw [zero_smul, pt_zero, pow_zero]
  | N + 1 => by rw [succ_nsmul, M.add, pt_nsmul M e N, pow_succ]

theorem comp_pow' {X A : Over S} [GrpObj A] (x : X ⟶ A) (g : A ⟶ A) : ∀ N : ℕ, x ≫ g ^ N = (x ≫ g) ^ N
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | N + 1 => by rw [pow_succ, pow_succ, comp_mul, comp_pow' x g N]

def castM {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : LieModel G x' E := h ▸ M

theorem castM_left {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ((castM h M).pt e).left = (M.pt e).left := by
  subst h; rfl

def toAt {A : Over (Sp R)} (v : epsR R ⟶ A) : epsAt (𝟙 (Sp R)) ⟶ A :=
  Over.homMk v.left (by simp [Over.w v])

theorem toAt_left {A : Over (Sp R)} (v : epsR R ⟶ A) : (toAt v).left = v.left := rfl

theorem toAt_tan {A : Over (Sp R)} [GrpObj A] (v : epsR R ⟶ A) (hv : IsTangent v) : IsTanAt A (𝟙 (Sp R)) (toAt v) := by
  unfold IsTanAt
  rw [toAt_left]
  unfold IsTangent at hv
  rw [hv]
  first
  | (rw [Hom.one_def]; simp)
  | simp [Hom.one_def]
  | (rw [Hom.one_def, Over.comp_left]; congr 1; simp)
  | rfl

end PositivityTheory.Xgf.isogeny_decomposition_product

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

def toR {A : Over (Sp R)} (t : epsAt (𝟙 (Sp R)) ⟶ A) : epsR R ⟶ A :=
  Over.homMk t.left (by simp [Over.w t])

theorem toR_left {A : Over (Sp R)} (t : epsAt (𝟙 (Sp R)) ⟶ A) : (toR t).left = t.left := rfl

theorem toR_tan {A : Over (Sp R)} [GrpObj A] (t : epsAt (𝟙 (Sp R)) ⟶ A) (ht : IsTanAt A (𝟙 (Sp R)) t) :
    IsTangent (toR t) := by
  unfold IsTangent
  rw [toR_left]
  unfold IsTanAt at ht
  rw [ht]
  rw [Hom.one_def]; simp

theorem epsScaleR_eq (c : R) : epsScaleR c = GlobalTheory.CompanionTheory.Ar.epsMul c := rfl

theorem basis_of_lieBasis {A : Over (Sp R)} [GrpObj A] (v : epsR R ⟶ A) (hv : IsLieBasis ![v]) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel A (𝟙 (Sp R)) E) :
    ∃ b : Module.Basis (Fin 1) R E, (M.pt (b 0)).left = v.left := by
  obtain ⟨e₀, he₀⟩ := M.onto (toAt v) (toAt_tan v (hv.1 0))
  have key : ∀ e, ∃! c : Fin 1 → R, IsLieComb c ![v] (toR (M.pt e)) :=
    fun e => hv.2 _ (toR_tan _ (M.tan e))
  have hsm : ∀ (c : R) e, (M.pt (c • e)).left = spMap (epsScaleR c) ≫ (M.pt e).left := fun c e => M.smul c e
  have comb : ∀ c : R, IsLieComb ![c] ![v] (toR (M.pt (c • e₀))) := by
    intro c
    refine ⟨![toR (M.pt (c • e₀))], fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [toR_left, hsm, he₀, toAt_left]
    · simp
  have hinj : Function.Injective fun c : R => c • e₀ := by
    intro c c' h
    have h1 := (key (c • e₀)).unique (comb c) (by simpa [h] using comb c')
    simpa using congrFun h1 0
  have hsurj : Function.Surjective fun c : R => c • e₀ := by
    intro e
    obtain ⟨c, ⟨u, hu, hw⟩, -⟩ := key e
    refine ⟨c 0, M.inj (Over.OverMorphism.ext ?_)⟩
    have h0 := hu 0
    simp only [Matrix.cons_val_zero] at h0
    have hw' : (toR (M.pt e)).left = (u 0).left := by
      rw [hw]; simp [List.ofFn_succ]
    simp only
    rw [hsm, he₀, toAt_left, ← h0, ← hw', toR_left]
  let eqv : R ≃ₗ[R] E := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R E e₀) ⟨hinj, hsurj⟩
  refine ⟨(Module.Basis.singleton (Fin 1) R).map eqv, ?_⟩
  simp only [eqv, Module.Basis.map_apply, Module.Basis.singleton_apply]
  show (M.pt (LinearMap.toSpanSingleton R E e₀ 1)).left = v.left
  rw [LinearMap.toSpanSingleton_apply, one_smul, he₀, toAt_left]

end PositivityTheory.Xgf.isogeny_decomposition_product

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

theorem lc (C : Out.PolAV (Sp R)) (v : epsR R ⟶ C.A) (hv : IsLieBasis ![v]) (V : Type) [CommRing V] (f : R →+* V) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module V E) (M : LieModel C.A (spMap f ≫ 𝟙 (Sp R)) E)
      (b : Module.Basis (Fin 1) V E), (M.pt (b 0)).left = spMap (dualMap f) ≫ v.left := by
  obtain ⟨E0, i0, m0, ⟨M0⟩⟩ := lieModel_exists (Sp R) C.A R (𝟙 (Sp R))
  obtain ⟨b0, hb0⟩ := basis_of_lieBasis v hv M0
  obtain ⟨E1, i1, m1, ⟨M1⟩⟩ := lieModel_exists (Sp R) C.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) C.A R V f (𝟙 _) E0 E1 M0 M1
  letI : Algebra R V := f.toAlgebra
  letI : Module R E1 := Module.compHom E1 f
  haveI : IsScalarTower R V E1 := ⟨fun r x e => by
    show (f r * x) • e = f r • (x • e)
    rw [mul_smul]⟩
  let jR : E0 →ₗ[R] E1 :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => by
        show j (r • e) = f r • j e
        exact j.map_smulₛₗ r e }
  haveI : SmoothOfRelativeDimension C.g C.A.hom := C.smoothDim
  haveI : Smooth C.A.hom := by
    first
    | exact SmoothOfRelativeDimension.smooth C.g C.A.hom
    | exact SmoothOfRelativeDimension.smooth C.g
    | exact SmoothOfRelativeDimension.smooth (n := C.g)
  have hbc : IsBaseChange V jR := GlobalTheory.T.lie_model_isBaseChange (Sp R) C.A R V (𝟙 _) E0 E1 M0 M1 jR (fun e => hj e)
  refine ⟨E1, i1, m1, M1, hbc.basis b0, ?_⟩
  rw [IsBaseChange.basis_apply]
  have h := hj (b0 0)
  unfold LieModel.Lifts at h
  have h' := (Category.comp_id (M1.pt (j (b0 0))).left).symm.trans h
  show (M1.pt (j (b0 0))).left = _
  rw [h', hb0]

end PositivityTheory.Xgf.isogeny_decomposition_product

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

theorem tan_comp {S : Scheme.{0}} {R : Type} [CommRing R] {A B : Over S} [GrpObj A] [GrpObj B] {x : Sp R ⟶ S}
    (t : epsAt x ⟶ A) (ht : IsTanAt A x t) (g : A ⟶ B) [IsMonHom g] : IsTanAt B x (t ≫ g) := by
  unfold IsTanAt at ht ⊢
  rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]

theorem one_left {S : Scheme.{0}} {X A : Over S} [GrpObj A] : (1 : X ⟶ A).left = X.hom ≫ η[A].left := by
  rw [Hom.one_def]; simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem bc_one {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) {A : Over (Sp R)} [GrpObj A] :
    spMap (dualMap f) ≫ (1 : epsR R ⟶ A).left = (1 : epsAt (spMap f ≫ 𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, one_left, ← Category.assoc]
  congr 1
  simp only [Over.mk_hom, Category.comp_id]
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_eps {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (N : ℕ) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : V)) ≫ spMap (dualMap f) := by
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

theorem pow_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] (v : epsR R ⟶ A)
    (hv : IsLieBasis ![v]) (N : ℕ) :
    v.left ≫ (𝟙 A ^ N).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) ≫ v.left := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists (Sp R) A R (𝟙 (Sp R))
  obtain ⟨b, hb⟩ := basis_of_lieBasis v hv M
  have e1 : toAt v = M.pt (b 0) := Over.OverMorphism.ext (by rw [toAt_left, hb])
  have h := congrArg Over.Hom.left (comp_pow' (toAt v) (𝟙 A) N)
  rw [Category.comp_id, e1, ← pt_nsmul, Over.comp_left, ← e1, toAt_left, ← Nat.cast_smul_eq_nsmul R,
    M.smul, ← e1, toAt_left] at h
  exact h

end PositivityTheory.Xgf.isogeny_decomposition_product

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.isogeny_decomposition_product in
theorem isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.T.lie_model_functorial_map (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

end PositivityTheory.Xgf

end
