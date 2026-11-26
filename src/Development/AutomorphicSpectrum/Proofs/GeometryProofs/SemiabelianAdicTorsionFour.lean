module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFour
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Twfunct
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twfunct

section General

variable {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {x : Spec (CommRingCat.of R) ⟶ S}

theorem exists_lift {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T) (Γ' : QFGroup R T')
    {N N' : ℕ} {i : Γ.G.left ⟶ G.left} {i' : Γ'.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) (h' : Γ'.IsTorsionAlong G x N' i') (hN : N ∣ N')
    (u : G ⟶ G) [IsMonHom u] : ∃ a : Γ.G ⟶ Γ'.G, a.left ≫ i' = i ≫ u.left := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨k, rfl⟩ := hN
  have hg' : (g ≫ u) ^ (N * k) = 1 := by
    rw [← MonObj.pow_comp, pow_mul, hg, one_pow, MonObj.one_comp]
  obtain ⟨a, ha⟩ := (h'.kernel Γ.G (g ≫ u)).1 hg'
  exact ⟨a, by rw [ha]; simp [g]⟩

theorem left_ext {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} (v w : Y ⟶ Γ.G.left) (h1 : v ≫ Γ.G.hom = w ≫ Γ.G.hom)
    (h2 : v ≫ i = w ≫ i) : v = w := by
  have := h.inj (Over.mk (w ≫ Γ.G.hom)) (Over.homMk v h1) (Over.homMk w rfl) h2
  exact congrArg (fun z => z.left) this

omit [IsDomain R] in
theorem valAt_comp {X Y : Scheme.{0}} (v : Spec (CommRingCat.of R) ⟶ X) (a : X ⟶ Y) (s : Γ(Y, ⊤)) :
    valAt v ⊤ le_top ((a.app ⊤).hom s) = valAt (v ≫ a) ⊤ le_top s :=
  Funct.valAt_pullback v a _ rfl ⊤ le_top le_top s

omit [IsDomain R] in
theorem valAt_specMap {B : Type} [CommRing B] {Y : Scheme.{0}} (π : R →+* B) (v : Spec (CommRingCat.of R) ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (Spec.map (CommRingCat.ofHom π) ≫ v) ⊤ le_top s = π (valAt v ⊤ le_top s) := by
  have h1 : ∀ {Z : Scheme.{0}} (w : Z ⟶ Y), w.appLE ⊤ ⊤ le_top = w.appTop := fun w =>
    w.appLE_eq_app
  simp only [valAt, h1]
  rw [Scheme.Hom.comp_appTop]
  have := congrArg (fun z => z.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom π))
  exact this

omit [IsDomain R] in
theorem pt_nsmul {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) (N : ℕ) :
    M.pt (N • e) = M.pt e ^ N := by
  induction N with
  | zero =>
    have := M.add 0 0
    rw [add_zero] at this
    simpa using (left_eq_mul.1 this)
  | succ k ih => rw [succ_nsmul, M.add, ih, pow_succ]

theorem exists_tan {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) :
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  let Q := R ⧸ Ideal.span {(N : R)}
  let q : R →+* Q := Ideal.Quotient.mk _
  let c : R →+* DualNumber Q := (algebraMap Q (DualNumber Q)).comp q
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom c))
  have hc : (dualMap q).comp (algebraMap R (DualNumber R)) = c := by
    ext r <;> simp [c, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : Over.mk (Y.hom ≫ x) ⟶ epsAt x := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap q))) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hc])
  let k₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : q (N : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hc' : (dualMap q).comp (epsMul (N : R)) = c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [c, dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, -map_natCast, hN]
  have hg : (k ≫ M.pt e) ^ N = 1 := by
    rw [← MonObj.comp_pow, ← pt_nsmul, ← MonObj.comp_one k₀]
    ext1
    rw [Over.comp_left, Over.comp_left, ← Nat.cast_smul_eq_nsmul R, M.smul, ← M.tan e]
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc']
  obtain ⟨v, hv⟩ := (h.kernel Y (k ≫ M.pt e)).1 hg
  exact ⟨v.left, Over.w v, hv⟩

end General

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative
    (Submodule.mapQ _ _ φ.toIntLinearMap (by
      rintro _ ⟨a, rfl⟩
      exact ⟨φ a, (map_nsmul φ (p ^ n) a).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

theorem lev_surj {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
  exact ⟨a, by simp [lev, ha]⟩

theorem lev_zero {La : Type} [AddCommGroup La] (p n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem finite_lev {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast pow_ne_zero n hp)⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, (natCast_zsmul a (p ^ n)).symm⟩
  infer_instance

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)
  {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L)

theorem isDer_res (n : ℕ) (f : LevGrp La p (n + 1) → O) (g : LevGrp La p n → O) (w : Module.Dual O L)
    (hf : X.IsDer M (n + 1) f w) (hg : ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) : X.IsDer M n g w := by
  obtain ⟨s, hs, hw⟩ := hf
  obtain ⟨j, hj⟩ := exists_lift (X.Γ n) (X.Γ (n + 1)) (X.tors n) (X.tors (n + 1)) (pow_dvd_pow p n.le_succ) (𝟙 G)
  rw [Over.id_left, Category.comp_id] at hj
  refine ⟨(j.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · obtain ⟨a, rfl⟩ := lev_surj p n t
    have : ((X.Γ n).pt (lev p n a)).left ≫ j.left = ((X.Γ (n + 1)).pt (lev p (n + 1) (p • a))).left := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, Over.w, Over.w]
      · rw [Category.assoc, hj, X.compat]
    rw [valAt_comp, this, hs, hg]
  · obtain ⟨v, hv1, hv2, hv3⟩ := hw e
    obtain ⟨v', h1, h2⟩ := exists_tan (X.Γ n) (X.tors n) M e
    refine ⟨v', h1, h2, ?_⟩
    have hle : Ideal.span {((p ^ (n + 1) : ℕ) : O)} ≤ Ideal.span {((p ^ n : ℕ) : O)} :=
      Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (pow_dvd_pow p n.le_succ))
    let π := Ideal.Quotient.factor hle
    have : v' ≫ j.left = Spec.map (CommRingCat.ofHom (dualMap π)) ≫ v := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, Over.w, h1, hv1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Category.assoc, Category.assoc, hj, h2, hv2, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap]
    have h0 : g 1 = f 1 := by simpa [lev_zero] using hg 0
    rw [valAt_comp, this, valAt_specMap, hv3, h0]
    ext <;> simp [π, dualMap]

theorem exists_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (hu : X.Induces u φ) (n : ℕ) :
    ∃ a : (X.Γ n).G ⟶ (X.Γ n).G, a.left ≫ X.i n = X.i n ≫ u.left ∧
      ∀ t, (X.Γ n).pt t ≫ a = (X.Γ n).pt (levMap p n φ t) := by
  obtain ⟨a, ha⟩ := exists_lift (X.Γ n) (X.Γ n) (X.tors n) (X.tors n) dvd_rfl u
  refine ⟨a, ha, fun t => ?_⟩
  obtain ⟨b, rfl⟩ := lev_surj p n t
  refine (X.tors n).inj _ _ _ ?_
  rw [levMap_lev, hu, Over.comp_left, Category.assoc, ha]

theorem isDer_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L) (hu : X.Induces u φ)
    (hd : M.IsDiffOf u dφ) (n : ℕ) (f : LevGrp La p n → O) (w : Module.Dual O L) (hf : X.IsDer M n f w) :
    X.IsDer M n (fun t => f (levMap p n φ t)) (w ∘ₗ dφ) := by
  obtain ⟨a, ha, hpt⟩ := exists_endo X u φ hu n
  obtain ⟨s, hs, hw⟩ := hf
  refine ⟨(a.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · rw [valAt_comp, ← Over.comp_left, hpt, hs]
  · obtain ⟨v, hv1, hv2, -⟩ := hw e
    obtain ⟨v', h1, h2, h3⟩ := hw (dφ e)
    refine ⟨v, hv1, hv2, ?_⟩
    have : v ≫ a.left = v' := by
      refine left_ext _ (X.tors n) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, h1, hv1]
      · rw [Category.assoc, ha, h2, hd e, ← Category.assoc, hv2, Over.comp_left, Category.assoc]
    rw [valAt_comp, this, h3]
    simp only [map_one, LinearMap.comp_apply]

set_option linter.unusedVariables false in
theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  intro p hpp C _ _ _ v O _ _ _ _ _ _ S _ G _ _ _ y La _ _ _ X L _ _ M
  refine ⟨isDer_res X M, fun u _ φ dφ hu hd n f g hg => ?_⟩
  obtain rfl : g = fun t => f (levMap p n φ t) := by
    funext t
    obtain ⟨b, rfl⟩ := lev_surj p n t
    rw [hg, levMap_lev]
  refine ⟨fun hf => ?_, isDer_endo X M u φ dφ hu hd n f⟩
  obtain ⟨a, -, hpt⟩ := exists_endo X u φ hu n
  have : Finite (LevGrp La p n) := finite_lev hpp.out.ne_zero n
  exact Funct.comp_mem_btOrder O _ _ _ _ a _ hpt f hf

end PositivityTheory.HtPt.Twfunct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFour
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) :=
  @PositivityTheory.HtPt.Twfunct.tw_funct

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFourStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_adic_torsion_four : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tw_funct | exact GlobalTheory.CompanionTheory.Ar.HT.tw_funct | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tw_funct <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrder
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.Induced

theorem isHopfOrder_indOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  obtain ⟨hfin, hproj, hfull, hcomul, hinv⟩ := hA
  unfold prodSpan at hcomul
  have hmemInd : ∀ f : T → R, f ∈ indOrder ι A ↔ ∀ t : T, (fun h => f (t * ι h)) ∈ A := by
    intro f
    unfold indOrder
    exact Iff.rfl
  have hTr : ∀ g ∈ A, ∀ h0 : H, (fun h => g (h * h0)) ∈ A := by
    intro g hg h0
    obtain ⟨E, hE⟩ : ∃ E : (H × H → R) →ₗ[R] (H → R), ∀ φ h, E φ h = φ (h, h0) :=
      ⟨{ toFun := fun φ h => φ (h, h0)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Subalgebra.toSubmodule A).comap E := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hEab : E (fun z : H × H => a z.1 * b z.2) = b h0 • a := by
        funext h
        rw [hE]
        simp [mul_comm]
      show E _ ∈ Subalgebra.toSubmodule A
      rw [hEab]
      exact A.smul_mem ha _
    have h1 := hle (hcomul g hg)
    have h2 : E (fun z : H × H => g (z.1 * z.2)) = fun h => g (h * h0) := funext fun h => hE _ h
    rw [Submodule.mem_comap, h2] at h1
    simpa using h1
  have hs : Function.Surjective (QuotientGroup.mk : T → T ⧸ ι.range) := QuotientGroup.mk_surjective
  have hQfin : Finite (T ⧸ ι.range) := Finite.of_surjective _ hs
  let _ : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ : ∃ σ : T ⧸ ι.range → T, ∀ c, (σ c : T ⧸ ι.range) = c :=
    ⟨Function.surjInv hs, Function.surjInv_eq hs⟩
  have hmem : ∀ t : T, (σ (t : T ⧸ ι.range))⁻¹ * t ∈ ι.range := fun t => QuotientGroup.eq.mp (hσ _)
  choose δ hδ using fun t : T => MonoidHom.mem_range.mp (hmem t)
  have hdec : ∀ t : T, σ (t : T ⧸ ι.range) * ι (δ t) = t := fun t => by
    rw [hδ, mul_inv_cancel_left]
  have hmk : ∀ (t : T) (h : H), ((t * ι h : T) : T ⧸ ι.range) = (t : T ⧸ ι.range) := by
    intro t h
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hδmul : ∀ (t : T) (h : H), δ (t * ι h) = δ t * h := by
    intro t h
    apply hι
    rw [hδ, map_mul, hδ, hmk, mul_assoc]
  obtain ⟨e, he⟩ : ∃ e : T ⧸ ι.range → T → R,
      ∀ c t, e c t = if (t : T ⧸ ι.range) = c then 1 else 0 :=
    ⟨fun c t => if (t : T ⧸ ι.range) = c then 1 else 0, fun _ _ => rfl⟩
  have he_self : ∀ t : T, e (t : T ⧸ ι.range) t = 1 := fun t => by rw [he, if_pos rfl]
  have he_ne : ∀ (c : T ⧸ ι.range) (t : T), c ≠ (t : T ⧸ ι.range) → e c t = 0 :=
    fun c t hc => by rw [he, if_neg (fun h => hc h.symm)]
  have he_mk : ∀ (c : T ⧸ ι.range) (t : T) (h : H), e c (t * ι h) = e c t :=
    fun c t h => by rw [he, he, hmk]
  let i : (indOrder ι A) →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (σ c * ι h), (hmemInd _).mp f.2 (σ c)⟩
      map_add' := fun f g => by
        funext c
        apply Subtype.ext
        rfl
      map_smul' := fun r f => by
        funext c
        apply Subtype.ext
        rfl }
  have hp : ∀ a : T ⧸ ι.range → A,
      (fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t)) ∈ indOrder ι A := by
    intro a
    rw [hmemInd]
    intro t
    have heq : (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) =
        fun h => ((a (t : T ⧸ ι.range) : A) : H → R) (h * δ t) := by
      funext h
      rw [hmk, hδmul, mul_comm (δ t) h]
    show (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) ∈ A
    rw [heq]
    exact hTr _ (a _).2 _
  let p : (T ⧸ ι.range → A) →ₗ[R] (indOrder ι A) :=
    { toFun := fun a => ⟨fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t), hp a⟩
      map_add' := fun a b => by
        apply Subtype.ext
        rfl
      map_smul' := fun r a => by
        apply Subtype.ext
        rfl }
  have hpi' : ∀ f, p (i f) = f := by
    intro f
    apply Subtype.ext
    funext t
    show (f : T → R) (σ (t : T ⧸ ι.range) * ι (δ t)) = (f : T → R) t
    rw [hdec]
  have hpi : p.comp i = LinearMap.id := LinearMap.ext hpi'
  have := hfin
  have := hproj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective p (fun f => ⟨i f, hpi' f⟩)
  · have hQM : Module.Projective R (T ⧸ ι.range → A) := by
      obtain ⟨M, _, _, _, i0, s0, hs0⟩ := Module.Projective.iff_split.mp hproj
      refine Module.Projective.of_split
        ({ toFun := fun g c => i0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → A) →ₗ[R] (T ⧸ ι.range → M))
        ({ toFun := fun g c => s0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → M) →ₗ[R] (T ⧸ ι.range → A)) ?_
      apply LinearMap.ext
      intro g
      funext c
      show s0 (i0 (g c)) = g c
      exact LinearMap.congr_fun hs0 (g c)
    exact Module.Projective.of_split i p hpi
  · obtain ⟨d, hd0, hd⟩ := hfull
    exact ⟨d, hd0, fun f => (hmemInd _).mpr fun t => hd (fun h => f (t * ι h))⟩
  · intro f hf
    unfold prodSpan
    have hind : ∀ (c : T ⧸ ι.range), ∀ a ∈ A, (fun t => e c t * a (δ t)) ∈ indOrder ι A := by
      intro c a ha
      rw [hmemInd]
      intro t
      have heq : (fun h => e c (t * ι h) * a (δ (t * ι h))) = fun h => e c t * a (h * δ t) := by
        funext h
        rw [he_mk, hδmul, mul_comm (δ t) h]
      show (fun h => e c (t * ι h) * a (δ (t * ι h))) ∈ A
      rw [heq]
      exact A.smul_mem (hTr a ha (δ t)) (e c t)
    obtain ⟨L, hL⟩ : ∃ L : T ⧸ ι.range → T ⧸ ι.range → (H × H → R) →ₗ[R] (T × T → R),
        ∀ c1 c2 φ z, L c1 c2 φ z = e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2) :=
      ⟨fun c1 c2 =>
        { toFun := fun φ z => e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2)
          map_add' := fun φ ψ => by
            funext z
            simp only [Pi.add_apply]
            ring
          map_smul' := fun r φ => by
            funext z
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring },
        fun _ _ _ _ => rfl⟩
    have hsum : (fun z : T × T => f (z.1 * z.2)) =
        ∑ c1 : T ⧸ ι.range, ∑ c2 : T ⧸ ι.range,
          L c1 c2 (fun z : H × H => f (σ c1 * σ c2 * ι (z.1 * z.2))) := by
      funext z
      rw [Finset.sum_apply, Fintype.sum_eq_single (z.1 : T ⧸ ι.range)]
      · rw [Finset.sum_apply, Fintype.sum_eq_single (z.2 : T ⧸ ι.range)]
        · rw [hL]
          try dsimp only
          rw [he_self, he_self, one_mul, one_mul, map_mul, mul_mul_mul_comm, hdec, hdec]
        · intro c2 hc2
          rw [hL, he_ne _ _ hc2, mul_zero, zero_mul]
      · intro c1 hc1
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c2 _
        rw [hL, he_ne _ _ hc1, zero_mul, zero_mul]
    rw [hsum]
    refine sum_mem fun c1 _ => sum_mem fun c2 _ => ?_
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Submodule.span R {g | ∃ a ∈ indOrder ι A, ∃ b ∈ indOrder ι A,
          g = fun z : T × T => a z.1 * b z.2}).comap (L c1 c2) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      show L c1 c2 _ ∈ Submodule.span R _
      apply Submodule.subset_span
      refine ⟨_, hind c1 a ha, _, hind c2 b hb, ?_⟩
      funext z
      rw [hL]
      dsimp only
      ring
    exact hle (hcomul _ ((hmemInd f).mp hf (σ c1 * σ c2)))
  · intro f hf
    rw [hmemInd] at hf ⊢
    intro t
    have heq : (fun h => f ((t * ι h)⁻¹)) = fun h => f (t⁻¹ * ι h⁻¹) := by
      funext h
      rw [map_inv, mul_inv]
    show (fun h => f ((t * ι h)⁻¹)) ∈ A
    rw [heq]
    exact hinv _ (hf t⁻¹)

end GlobalTheory.CompanionTheory.Ar.BT.Induced
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjectiveStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_induction_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | exact GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [GlobalTheory.T.mem_btOrder_iff_btSet R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (GlobalTheory.T.regular_function_iff_section R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (GlobalTheory.T.regular_function_iff_section R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact GlobalTheory.T.hopf_order_induction_injective R T H H.subtype H.subtype_injective A hA
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub
end
end
