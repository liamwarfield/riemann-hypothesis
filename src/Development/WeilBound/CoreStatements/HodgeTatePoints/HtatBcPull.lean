module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace Pull

variable {B B' : Type} [CommRing B] [CommRing B'] {Y Z : Scheme.{0}}

theorem valAt_comp (y : Spec (CommRingCat.of B) ⟶ Y) (φ : Y ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ W) (f : Γ(Z, W)) :
    valAt (y ≫ φ) W h f = valAt y (φ ⁻¹ᵁ W) h ((φ.app W).hom f) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_spec (φ : B →+* B') (y : Spec (CommRingCat.of B) ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ y) ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ y) W h' f = φ (valAt y W h f) := by
  have e : (Spec.map (CommRingCat.ofHom φ) ≫ y).appLE W ⊤ h' =
      y.appLE W ⊤ h ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) y W ⊤ ⊤ h le_top
    rw [← this]
    simp [Scheme.Hom.appLE]
    rfl
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  simp only [valAt, e]
  exact congrArg (fun z => z.hom ((y.appLE W ⊤ h).hom f)) n

theorem valAt_congr {B : Type} [CommRing B] {Y : Scheme.{0}} {y y' : Spec (CommRingCat.of B) ⟶ Y} (e : y = y') (W : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y' ⁻¹ᵁ W) (f : Γ(Y, W)) : valAt y W h f = valAt y' W h' f := by
  subst e; rfl

end Pull

theorem reg_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  have h1 : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have h2 : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := e ▸ h1
  have h3 : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun z _ => by
    have hz : z = Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact h2 (by trivial)
  refine (Pull.valAt_comp _ F U h1 s).symm.trans ((Pull.valAt_congr e U h1 h2 s).trans ?_)
  rw [Pull.valAt_spec κ _ U h3, hs t h3]

end PositivityTheory.HtPt.Htat
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mh

theorem ind_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  intro R _ T _ A hA
  ext f
  refine ⟨fun h => ?_, fun h t => Twhopf.translate_mem R T A hA f h t⟩
  have := h 1
  simpa using this

theorem ext_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  intro R _ _ T _ _ R' _ _ _ A hA ⟨d, hd, hdA⟩
  classical
  cases nonempty_fintype T
  have := hA.finite
  have := hA.projective
  let c : A →ₐ[R] (T → R') :=
    AlgHom.pi fun t => (Algebra.ofId R R').comp (evalAt A t)
  let L : R' ⊗[R] A →ₐ[R'] (T → R') :=
    Algebra.TensorProduct.lift (Algebra.ofId R' (T → R')) c (fun _ _ => Commute.all _ _)
  have hL : ∀ (r : R') (a : A) (t : T), L (r ⊗ₜ a) t = r * algebraMap R R' (a.1 t) := fun r a t => rfl
  let m : T → A := fun t => ⟨_, hdA (Pi.single t 1)⟩
  let M : (T → R') →ₗ[R'] R' ⊗[R] A :=
    ∑ t, (LinearMap.proj t : (T → R') →ₗ[R'] R').smulRight ((1 : R') ⊗ₜ[R] m t)
  have hM : ∀ x, M (L x) = algebraMap R R' d • x := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
    | tmul r a =>
      have e : ∑ t, a.1 t • m t = d • a := by
        apply Subtype.ext
        funext s
        simp [m, Pi.single_apply, Finset.sum_apply, mul_comm]
      have e2 : ∀ t, (r * algebraMap R R' (a.1 t)) • ((1 : R') ⊗ₜ[R] m t) = r ⊗ₜ[R] (a.1 t • m t) := by
        intro t
        rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, Algebra.smul_def, mul_comm]
      simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, hL, e2]
      rw [← TensorProduct.tmul_sum, e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', algebraMap_smul]
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hM x
    rw [hx, map_zero] at h
    exact (smul_eq_zero_iff_right hd).1 h.symm
  have hrange : L.range = extOrder (algebraMap R R') A := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x with
      | add x y hx hy => exact (map_add L.toRingHom x y).symm ▸ add_mem hx hy
      | tmul r a =>
        exact (extOrder (algebraMap R R') A).smul_mem (OrderApi.comp_mem_extOrder (algebraMap R R') a.2) r
    · refine Algebra.adjoin_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, funext fun t => (hL _ _ t).trans (one_mul _)⟩
  let e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A :=
    (AlgEquiv.ofInjective L hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  refine ⟨⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv,
    ⟨algebraMap R R' d, hd, fun g => ?_⟩, fun g hg => ?_, fun g hg => ?_⟩,
    e, fun a t => (hL 1 a t).trans (one_mul _)⟩
  · rw [← hrange]
    refine ⟨M g, funext fun s => ?_⟩
    change L (M g) s = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, hL, m]
    simp [Pi.single_apply, apply_ite, mul_comm]
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      have key : ∀ n ∈ prodSpan A, (fun z => algebraMap R R' (n z)) ∈ prodSpan (extOrder (algebraMap R R') A) := by
        intro n hn
        induction hn using Submodule.span_induction with
        | mem n hn =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hn
          simpa using OrderApi.mul_mem_prodSpan (OrderApi.comp_mem_extOrder (algebraMap R R') ha)
            (OrderApi.comp_mem_extOrder (algebraMap R R') hb)
        | zero =>
          convert Submodule.zero_mem (prodSpan (extOrder (algebraMap R R') A)) using 1
          ext z; simp
        | add x y _ _ hx hy =>
          convert Submodule.add_mem _ hx hy using 1
          ext z; simp
        | smul r x _ hx =>
          convert Submodule.smul_mem _ (algebraMap R R' r) hx using 1
          ext z; simp
      exact key _ (hA.comul f hf)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      exact OrderApi.comp_mem_extOrder (algebraMap R R') (hA.inv f hf)
    | zero => exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | smul r x _ hx => exact Subalgebra.smul_mem _ hx r

end PositivityTheory.HtPt.Mh
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHt
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem tors_ext {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} {v v' : Y ⟶ Γ.G.left} (h1 : v ≫ Γ.G.hom = v' ≫ Γ.G.hom)
    (h2 : v ≫ i = v' ≫ i) : v = v' :=
  congrArg (·.left) (h.inj (Over.mk (v ≫ Γ.G.hom)) (Over.homMk v rfl) (Over.homMk v' h1.symm) h2)

theorem ht_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ χ' w w' ⟨s, hs, hv⟩ ⟨s', hs', hv'⟩
  have hm : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left),
      valAt y ⊤ le_top (s * s') = valAt y ⊤ le_top s * valAt y ⊤ le_top s' := fun y => by simp [valAt]
  refine ⟨s * s', fun t => ?_, fun e => ?_⟩
  · rw [hm, hs t, hs' t, ← map_mul]; rfl
  · obtain ⟨v, h1, h2, h3⟩ := hv e
    obtain ⟨v', h1', h2', h3'⟩ := hv' e
    obtain rfl : v = v' := tors_ext h (h1.trans h1'.symm) (h2.trans h2'.symm)
    refine ⟨v, h1, h2, ?_⟩
    rw [hm, h3, h3']
    ext <;> simp [add_comm]

theorem ht_olin : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M a _ α A hα hA χ w ⟨s, hs, hv⟩
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by
    have : ∀ n : ℕ, (g ≫ a) ^ n = (g ^ n) ≫ a := fun n => by
      induction n with
      | zero => simp [MonObj.one_comp]
      | succ n ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
    rw [this, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a'.left.appTop.hom s, fun t => ?_, fun e => ?_⟩
  · have : (Γ.pt t).left ≫ a'.left = (Γ.pt (α t)).left :=
      tors_ext h (by rw [Category.assoc, Over.w, Over.w, Over.w]) (by rw [Category.assoc, ha', hα])
    rw [← valAt_comp_top, this]
    exact hs (α t)
  · obtain ⟨v, ⟨h1, h2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
    obtain ⟨v', h1', h2', h3'⟩ := hv (A e)
    have : v ≫ a'.left = v' := tors_ext h (by rw [Category.assoc, Over.w, h1, h1']) (by
      rw [Category.assoc, ha', ← Category.assoc, h2, h2', hA e, Over.comp_left, Category.assoc])
    exact ⟨v, h1, h2, by rw [← valAt_comp_top, this, h3']; rfl⟩

end PositivityTheory.HtPt.Htat
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] {ρ : O → V →ₗ[K] V} {χ : O → K} {x : V} :
    x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eig, sub_eq_zero]

theorem eig_frob : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  intro K _ p _ _ d O ρ χ
  apply le_antisymm
  · classical
    intro y hy
    rw [mem_eig] at hy
    set K0 := (frobenius K p).fieldRange with hK0
    let β := Module.Basis.ofVectorSpace K0 K
    have hpow : ∀ c : K, c ^ p ∈ K0 := fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩
    have hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι := by
      intro c u ι
      have h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u := rfl
      rw [h0, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K) := by
      intro ι f
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finsupp.finsetSum_apply]
    let z : _ → Fin d → K := fun ι j => (β.repr (y j) ι : K)
    have hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r := by
      intro ι a r
      have h1 := congrFun (hy a) r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := congrArg (fun u => (β.repr u ι : K)) h1
      simp only [hsum, hrepr] at h2
      exact h2
    have hex : ∀ ι j, ∃ x : K, x ^ p = z ι j := by
      intro ι j
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (β.repr (y j) ι).2
      exact ⟨x, by rw [← frobenius_def]; exact hx⟩
    choose x hx using hex
    have hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ := by
      intro ι
      rw [mem_eig]
      intro a
      funext r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      apply frobenius_inj K p
      rw [frobenius_def, frobenius_def, sum_pow_char, mul_pow]
      simp only [mul_pow, hx]
      exact hz ι a r
    let T := Finset.univ.biUnion fun j => (β.repr (y j)).support
    have hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι) := by
      funext j
      rw [Finset.sum_apply]
      conv_lhs => rw [← β.linearCombination_repr (y j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p
      rw [hx ι j, mul_comm]
    rw [hT, frobSub]
    exact Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)
  · rw [frobSub, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eig]
    rw [SetLike.mem_coe, mem_eig] at hx
    intro a
    have hxa := hx a
    simp only [Matrix.toLin'_apply] at hxa ⊢
    funext r
    have h1 := congrFun hxa r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢
    rw [← mul_pow, ← h1, sum_pow_char]
    simp only [mul_pow]

theorem eig_dual : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s
  let ρL : O →+* Module.End K (Fin d → K) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ
  obtain ⟨e, he_hom, he_mem, he_id, -, he_comb⟩ :=
    GlobalTheory.T.eigen_projectors_split_action K C (Fin d → K) L O k S χ hχ hv ρL hL hρ
  obtain ⟨m, c, b, hc, hes⟩ := he_comb s
  set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW
  set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'
  set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE
  have hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, map_sum]
    simp only [map_smul]
  have hlinT : Matrix.toLin' E.transpose =
      ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, Matrix.transpose_sum, map_sum]
    simp only [Matrix.transpose_smul, map_smul]
  have heE : ∀ x, e s x = E.mulVec x := by
    intro x
    rw [← Matrix.toLin'_apply, hlin, hes]
    rfl
  have hEW : ∀ x, E.mulVec x ∈ W := fun x => heE x ▸ he_mem s x
  have hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i := fun i x hx => heE x ▸ he_hom s i x hx
  have hEid : ∀ x ∈ W, E.mulVec x = x := fun x hx => (heE x).symm.trans (he_id s x hx)
  have hETid : ∀ y ∈ W', E.transpose.mulVec y = y := by
    intro y hy
    simp only [hW', mem_eig, Matrix.toLin'_apply] at hy
    rw [← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul,
      ← Finset.sum_smul, ← map_sum]
    rw [hc s, if_pos rfl, map_one, one_smul]
  have hETW : ∀ z, E.transpose.mulVec z ∈ W' := by
    intro z
    rw [hW', mem_eig]
    intro a
    have hmat : ρ a * E = algebraMap k K (χ s a) • E := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec]
      have h1 := (mem_eig.1 (hEW w)) a
      simpa only [Matrix.toLin'_apply] using h1
    have h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose := by
      have hcm : E * ρ a = ρ a * E := by
        rw [hE, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]
      rw [← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]
    show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) =
      algebraMap k K (χ s a) • E.transpose.mulVec z
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul,
      LinearMap.smul_apply, Matrix.toLin'_apply]
  have hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  let B : W →ₗ[K] W' →ₗ[K] K := (dotProductBilin K K).compl₁₂ W.subtype W'.subtype
  have hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K) := fun x y => rfl
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun x hx => ?_
    have h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0 := by
      intro z
      have h1 : B x ⟨_, hETW z⟩ = 0 := by rw [hx]; rfl
      rw [hB] at h1
      change (x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1
      rwa [hadj, hEid _ x.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hinj2 : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    have h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0 := by
      intro z
      have h1 : B.flip y ⟨_, hEW z⟩ = 0 := by rw [hy]; rfl
      rw [LinearMap.flip_apply, hB] at h1
      change E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1
      rwa [← hadj, hETid _ y.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W' := Subspace.dual_finrank_eq
  have hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  have hle1 := LinearMap.finrank_le_finrank_of_injective hinj
  have hle2 := LinearMap.finrank_le_finrank_of_injective hinj2
  have hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K) := by omega
  have hbij : Function.Bijective B :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩
  obtain ⟨-, hdeg, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C W W' (sub C L W) B (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1 hbij
  have hident : dualLat C (sub C L W) B = sub C (dotDual C L) W' := by
    funext i
    ext y
    show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1
    constructor
    · intro h x hx
      have hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y := by
        rw [hB]
        show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)
        rw [← hadj, hETid _ y.2]
      rw [hxy]
      exact h _ (hEL i x hx)
    · intro h x hx
      exact h x hx
  show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)
  rw [← hident]
  exact hdeg

end PositivityTheory.HtPt.Ci
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MjBase
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mj

variable {R : Type} [CommRing R]

theorem exists_dual_family (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] :
    ∃ (n : ℕ) (l : Fin n → N →ₗ[R] R) (b : Fin n → N), ∀ a, ∑ i, l i a • b i = a := by
  classical
  obtain ⟨n, p, g, -, -, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  refine ⟨n, fun i => (LinearMap.proj i).comp g, fun i => p fun j => if i = j then 1 else 0, fun a => ?_⟩
  have hx : p (g a) = a := LinearMap.congr_fun hpg a
  rw [LinearMap.pi_apply_eq_sum_univ p (g a)] at hx
  exact hx

variable {X Y Z : Type}

def pspan (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) : Submodule R (X × Y → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ B, g = fun z => a z.1 * b z.2}

theorem mul_mem_pspan {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {a : X → R} {b : Y → R}
    (ha : a ∈ A) (hb : b ∈ B) : (fun z : X × Y => a z.1 * b z.2) ∈ pspan A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem pspan_comp {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} (N : Submodule R (Z → R))
    (σ : Z → X × Y) (h : ∀ a ∈ A, ∀ b ∈ B, (fun z => a (σ z).1 * b (σ z).2) ∈ N) {g : X × Y → R}
    (hg : g ∈ pspan A B) : (fun z => g (σ z)) ∈ N := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact h a ha b hb
  | zero => exact N.zero_mem
  | add g g' _ _ h h' => exact N.add_mem h h'
  | smul r g _ h => exact N.smul_mem r h

theorem slice_mem {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} {g : X × Y → R}
    (hg : g ∈ pspan A B) (y : Y) : (fun x => g (x, y)) ∈ A :=
  pspan_comp (Subalgebra.toSubmodule A) (fun x => (x, y)) (fun a ha b _ => by
    have := A.smul_mem ha (b y)
    rw [Subalgebra.mem_toSubmodule]
    convert this using 1
    funext x
    simp [mul_comm]) hg

theorem mem_pspan_of {A : Subalgebra R (X → R)} {B : Subalgebra R (Y → R)} [Module.Finite R A]
    [Module.Projective R A] {g : X × Y → R} (h1 : ∀ y, (fun x => g (x, y)) ∈ A)
    (h2 : ∀ l : A →ₗ[R] R, (fun y => l ⟨_, h1 y⟩) ∈ B) : g ∈ pspan A B := by
  obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
  have := Submodule.sum_mem (pspan A B) (t := Finset.univ) fun i _ => mul_mem_pspan (b i).2 (h2 (l i))
  convert this using 1
  funext z
  have e := congrFun (congrArg Subtype.val (h ⟨_, h1 z.2⟩)) z.1
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [← e]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_tensor_equiv (A : Subalgebra R (X → R)) (B : Subalgebra R (Y → R)) [Module.Finite R A]
    [Module.Projective R A] (E : X × Y ≃ Z) (C : Subalgebra R (Z → R))
    (hC : ∀ f, f ∈ C ↔ (fun z => f (E z)) ∈ pspan A B) :
    ∃ e : A ⊗[R] B ≃ₐ[R] C, ∀ (a : A) (b : B) (x : X) (y : Y), (e (a ⊗ₜ b)).1 (E (x, y)) = a.1 x * b.1 y := by
  let p : A →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : X => R) (E.symm z).1).comp A.val
  let q : B →ₐ[R] (Z → R) := (AlgHom.pi fun z => Pi.evalAlgHom R (fun _ : Y => R) (E.symm z).2).comp B.val
  let m : A ⊗[R] B →ₐ[R] (Z → R) := Algebra.TensorProduct.lift p q fun _ _ => Commute.all _ _
  have hm : ∀ (a : A) (b : B) z, m (a ⊗ₜ b) (E z) = a.1 z.1 * b.1 z.2 := fun a b z => by
    simp [m, p, q]
  have hmem : ∀ w, m w ∈ C := fun w => by
    induction w with
    | tmul a b =>
      rw [hC]
      simp only [hm]
      exact mul_mem_pspan a.2 b.2
    | add a b ha hb => rw [map_add (f := _)]; exact C.add_mem ha hb
  have hinj : Function.Injective m := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨n, l, b, h⟩ := exists_dual_family (R := R) A
    let c : (A →ₗ[R] R) → A ⊗[R] B →ₗ[R] B := fun l => (TensorProduct.lid R B).toLinearMap ∘ₗ l.rTensor B
    let s : Y → A ⊗[R] B →ₗ[R] A := fun y =>
      (TensorProduct.rid R A).toLinearMap ∘ₗ ((LinearMap.proj y).comp B.val.toLinearMap).lTensor A
    have h1 : ∀ y x w, (s y w).1 x = m w (E (x, y)) := fun y x w => by
      induction w with
      | tmul a b => rw [hm]; simp [s, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h2 : ∀ l y w, (c l w).1 y = l (s y w) := fun l y w => by
      induction w with
      | tmul a b => simp [s, c, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), AddMemClass.coe_add, Pi.add_apply, ha, hb]
    have h3 : ∀ w, ∑ i, b i ⊗ₜ c (l i) w = w := fun w => by
      induction w with
      | tmul a b' =>
        conv_rhs => rw [← h a, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb => simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib, ha, hb]
    have h4 : ∀ y, s y w = 0 := fun y => Subtype.ext (funext fun x => by rw [h1, hw]; rfl)
    have h5 : ∀ l, c l w = 0 := fun l => Subtype.ext (funext fun y => by rw [h2, h4, map_zero]; rfl)
    rw [← h3 w]
    simp [h5]
  refine ⟨AlgEquiv.ofBijective (m.codRestrict C hmem) ⟨fun u v huv => hinj (congrArg Subtype.val huv), ?_⟩,
    fun a b x y => hm a b (x, y)⟩
  rintro ⟨f, hf⟩
  have := pspan_comp (LinearMap.range m.toLinearMap) E.symm
    (fun a ha b hb => ⟨(⟨a, ha⟩ : A) ⊗ₜ (⟨b, hb⟩ : B), funext fun z => by
      have := hm ⟨a, ha⟩ ⟨b, hb⟩ (E.symm z)
      rwa [E.apply_symm_apply] at this⟩) ((hC f).1 hf)
  obtain ⟨w, hw⟩ := this
  refine ⟨w, Subtype.ext ?_⟩
  simp only [E.apply_symm_apply] at hw
  exact hw

variable {T H : Type} [CommGroup T] [CommGroup H]

theorem res_mem (ι : H →* T) {A : Subalgebra R (T → R)} {f : T → R} (hf : f ∈ A) :
    (fun h => f (ι h)) ∈ resOrder ι A := ⟨f, hf, rfl⟩

theorem mem_quotOrder {π : T →* H} {A : Subalgebra R (T → R)} {g : H → R} :
    g ∈ quotOrder π A ↔ (fun t => g (π t)) ∈ A := Iff.rfl

def resMap (ι : H →* T) (A : Subalgebra R (T → R)) : A →ₗ[R] resOrder ι A where
  toFun f := ⟨fun h => f.1 (ι h), res_mem ι f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resMap_surjective (ι : H →* T) (A : Subalgebra R (T → R)) : Function.Surjective (resMap ι A) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem res_hopf {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    (hp : Module.Projective R (resOrder ι A)) : IsHopfOrder (resOrder ι A) := by
  have := hA.finite
  refine ⟨Module.Finite.of_surjective _ (resMap_surjective ι A), hp, ?_, ?_, ?_⟩
  · obtain ⟨d, hd, h⟩ := hA.full
    refine ⟨d, hd, fun f => ⟨_, h (Function.extend ι f 0), ?_⟩⟩
    funext x
    change d * Function.extend ι f 0 (ι x) = d * f x
    rw [hι.extend_apply]
  · rintro _ ⟨f, hf, rfl⟩
    have := pspan_comp (prodSpan (resOrder ι A)) (fun z : H × H => (ι z.1, ι z.2))
      (fun a ha b hb => mul_mem_pspan (res_mem ι ha) (res_mem ι hb)) (hA.comul f hf)
    simp only [← map_mul] at this
    exact this
  · rintro _ ⟨f, hf, rfl⟩
    have := res_mem ι (hA.inv f hf)
    simp only [← map_inv] at this
    exact this

theorem res_hopf_of_section {ι : H →* T} (hι : Function.Injective ι) {A : Subalgebra R (T → R)}
    (hA : IsHopfOrder A) (s : (H → R) →ₗ[R] (T → R)) (hs : ∀ f ∈ A, s (fun h => f (ι h)) ∈ A)
    (hs' : ∀ g h, s g (ι h) = g h) : IsHopfOrder (resOrder ι A) := by
  have := hA.projective
  refine res_hopf hι hA (Module.Projective.of_split (M := A)
    (LinearMap.codRestrict (Subalgebra.toSubmodule A) (s ∘ₗ (resOrder ι A).val.toLinearMap) ?_) (resMap ι A) ?_)
  · rintro ⟨_, f, hf, rfl⟩
    exact hs f hf
  · ext g h
    exact hs' g h

end PositivityTheory.HtPt.Mj
end
