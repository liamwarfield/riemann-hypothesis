module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsReg
open GlobalTheory.Points

theorem valR_appIso_inv {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (U : X.Opens) (f : Γ(X, U))
    {C : Type} [CommRing C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
  rw [← valR_appLE y j (j.preimage_image_eq U).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res y le_rfl hy f

theorem valR_valueAt {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ) [GrpObj A] {T : Over B}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [CommRing K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) = valR x ⊤ v * valR x _ (τ.s fun _ => j).val := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  exact e

theorem range_subset {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {U : X.Opens} (p : Sp K) (h : x p ∈ U) :
    Set.range x ⊆ U := by
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y p]
  exact h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_eq_mul_unit (hne : (U₀ : Set M.Z).Nonempty) {N : M.Z.Opens} {σ : Q.SecFam N} {c : Ω}
    (hσ : Q.ThMul c N σ) {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.left} {w : W.toScheme}
    (hE : Q.ExtPt a W h) (hF : Q.FrameUnit a W h w) (hw : W.ι w ∈ N) (jL : Q.L.L.ι) (hj : h w ∈ Q.L.L.U jL) :
    ∃ (T : M.Z.Opens) (f : Γ(M.Z, T)) (e : Ω), W.ι w ∈ T ∧ e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w) ∧
      c * S.th a = valF M.pt T f * e⁻¹ ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), Set.range y = {w} →
        valF (y ≫ W.ι) T f = valF (y ≫ h) _ (σ fun _ => jL) := by
  let V : W.toScheme.Opens := h ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL)
  have hwV : w ∈ V := by
    refine ⟨?_, Set.mem_iInter.2 fun _ => hj⟩
    change (h ≫ Q.G.hom) w ∈ N
    rw [hE.1]
    exact hw
  have hT : W.ι w ∈ W.ι ''ᵁ V := ⟨w, hwV, rfl⟩
  have hval : ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), ⊤ ≤ y ⁻¹ᵁ V →
      valF (y ≫ W.ι) (W.ι ''ᵁ V) ((W.ι.appIso V).inv.hom ((h.app _).hom (σ fun _ => jL))) =
        valF (y ≫ h) _ (σ fun _ => jL) := fun K _ y hy =>
    (valR_appIso_inv W.ι V _ y hy).trans (valR_comp y h _ _).symm
  have lift : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι M.pt (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨x, hx⟩ := lift W ⟨w.1, w.2⟩
  obtain ⟨x₀, hx₀⟩ := lift U₀ hne
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  have hcond : (t₀ ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = x₀ ≫ Q.u₀ := by
    rw [Q.u₀_gen x₀ hx₀, Category.assoc, Over.w (ρ.pt a)]
    exact Category.comp_id _
  let x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := pullback.lift _ _ hcond
  have h1 : x' ≫ pullback.fst _ _ = t₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have h2 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
    rw [← Category.assoc, pullback.lift_snd, hx₀]
  have h3 : x' ≫ Q.φ ≫ Q.G.hom = M.pt := by
    rw [← h2]
    exact congrArg (x' ≫ ·) Q.cart.1.w
  have h4 : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx h3 h1
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := by
    have h5 := M.top_le_preimage_pt ⟨_, hT⟩
    rw [← hx] at h5
    exact le_preimage_mono x (W.ι.preimage_image_eq V).le h5
  have hxh : Set.range (x' ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL : Q.G.left.Opens) := by
    rw [← h4]
    exact (top_le_preimage_iff _ _).1 hxV
  obtain ⟨jP, hjP⟩ : ∃ jP, Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U jP := by
    have h5 : (t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω) ∈ ⨆ i, ρ.P.L.U i := by
      rw [ρ.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    exact ⟨i, range_subset _ _ hi⟩
  obtain ⟨he0, he1, he2⟩ := hF jP jL x' _ hj h3 h1 (h1 ▸ hjP) rfl
  refine ⟨_, _, _, hT, he0, he1, he2, ?_, fun K _ y hy => hval K y fun p _ => ?_⟩
  · have hr : (t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        x' ≫ pullback.fst _ _ := by
      rw [h1, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
    have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _
    have e := hσ Ω (RingHom.id Ω) x' _ jP jL (by rw [h2, hid, Category.id_comp]) hr (h1 ▸ hjP)
      (fun p hp => Set.mem_iInter.1 (hxh hp).2 0) (fun p hp => (hxh hp).1)
    have e2 := valR_valueAt ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ jP hjP
    have e3 : valR (X := (baseOver (Sp S.R)).left) t₀ ⊤ (fn (⟨S.th a, S.th_mem a⟩ : S.R)) = S.th a :=
      valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _
    rw [e3] at e2
    rw [Fintype.sum_unique, zpow_one, RingHom.id_apply, valF_eq_valR, e2, ← h4, ← hval Ω x hxV, hx] at e
    have hn := (div_ne_zero_iff.1 he0).1
    rw [inv_div, ← mul_div_assoc, eq_div_iff hn, _root_.mul_assoc, _root_.mul_comm (valF M.pt _ _)]
    exact e
  · have h5 : y p ∈ Set.range y := ⟨p, rfl⟩
    rw [hy] at h5
    change y p ∈ V
    rw [show y p = w from h5]
    exact hwV

end GlobalTheory.ZH.TorsReg


open GlobalTheory.Points GlobalTheory.ZH.TorsReg in
theorem GlobalTheory.ZH.mul_theta_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N σ c _ hσ a W h w hE hF hw
  constructor
  · have h5 : h w ∈ ⨆ i, Q.L.L.U i := by
      rw [Q.L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    obtain ⟨T, f, e, hT, -, -, he, hc, -⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [hc]
    exact mul_mem (RatModel.valF_mem_O hT f) he
  · intro K _ x j hx hv
    have hxw : x (IsLocalRing.closedPoint K) = w := by
      have h5 : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at h5
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    have hi : h w ∈ Q.L.L.U i := by
      by_contra hi
      refine hv (dif_neg fun hle => hi ?_)
      rw [← hxw]
      exact Set.mem_iInter.1 (hle (x := IsLocalRing.closedPoint K) trivial).2 0
    obtain ⟨T, f, e, hT, he0, he1, -, hc, hK⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [← hK K x hx] at hv
    have hxw' : (x ≫ W.ι) (IsLocalRing.closedPoint K) = W.ι w := by rw [← hxw]; rfl
    have hle : ⊤ ≤ (x ≫ W.ι) ⁻¹ᵁ T := (GlobalTheory.Points.le_preimage_iff _ _).2 (hxw' ▸ hT)
    have hb : W.ι w ∈ M.Z.basicOpen f :=
      hxw' ▸ (GlobalTheory.Points.le_preimage_iff _ _).1 ((GlobalTheory.Points.le_preimage_basicOpen_iff _ hle f).2 (isUnit_iff_ne_zero.2 hv))
    obtain ⟨hf0, hf1⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hT f).2 hb)
    rw [hc]
    refine ⟨mul_ne_zero hf0 (inv_ne_zero he0), ?_⟩
    rw [_root_.mul_inv, inv_inv]
    exact mul_mem hf1 he1

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_mul_regular_and_unit_along_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  first | exact @GlobalTheory.ZH.mul_theta_regular_and_unit | exact GlobalTheory.ZH.mul_theta_regular_and_unit | (intros; apply GlobalTheory.ZH.mul_theta_regular_and_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChartsOfUniversal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem charts_of_universal {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I K : Type} [Fintype I] [Fintype K]
    {t : I → Ω} {e : ℕ} {v : K → J → Ω} (ht : M.HasDiv t)
    (hv : ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e))
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (hd : M'.HasDiv fun k => pairing φ s (v k))
    (hu : ∀ N : RatModel o Ω', N.HasDiv (fun q : I × K => φ (t q.1) * pairing φ s (v q.2)) →
      ∃ g, M'.IsHom N (AlgHom.id o Ω') g)
    (W : M.Z.Opens) (B : J → J → Ω) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty)
    (hB : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) :
    (∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z') ∧ ∀ i, pairing φ s (B i) ≠ 0 →
      ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div (fun j => pairing φ s (B j)) i z'} ∧
        M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
          Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) := by
  have hc : ∀ (N : RatModel o Ω') (i : I) (k : K) (z : N.Z), t i ≠ 0 →
      (N.Div (fun k => pairing φ s fun j => v k j / t i ^ e) k z ↔ N.Div (fun k => pairing φ s (v k)) k z) := by
    intro N i k z hi
    simp only [pairing_div]
    exact div_mul_iff (inv_ne_zero ((map_ne_zero φ).2 (pow_ne_zero _ hi)))
  have h1 : ∀ z', f z' ∈ W → ∃ i, M'.Div (fun j => pairing φ s (B j)) i z' := fun z' hz' => by
    obtain ⟨i, hi⟩ := ht (f z')
    obtain ⟨k, hk⟩ := hd z'
    exact hf.exists_div_pairing s ((hv _ i hi).symm.trans (hB _ hz')) ((hc M' i k z' hi.1).2 hk)
  refine ⟨h1, fun i hi => ?_⟩
  set R := Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪
    Set.range fun j => pairing φ s (B j) / pairing φ s (B i)) with hR
  have hR1 : ∀ x ∈ M.ringOn W, φ x ∈ R := fun x hx => Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
  have hR2 : ∀ j, pairing φ s (B j) / pairing φ s (B i) ∈ R := fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
  have hfg : R.FG := by
    rw [hR, Algebra.adjoin_union]
    refine Subalgebra.FG.sup ?_ (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    rw [← AlgHom.map_adjoin, Algebra.adjoin_eq]
    exact (fg_ringOn hW hne).map φ
  haveI : Algebra.FiniteType o R := (Subalgebra.fg_iff_finiteType _).1 hfg
  haveI : IsFractionRing R Ω' := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    have hK : Subfield.closure (R : Set Ω') = ⊤ :=
      EE.eq_top_of_pairing_mem hs (hB _ hne.some_mem) hi
        (map_mem_of_ringOn hW hne fun x hx => Subfield.subset_closure (hR1 x hx))
        fun j => Subfield.subset_closure (hR2 j)
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 (hK ▸ Subfield.mem_top x)
    have hle : Subring.closure (R : Set Ω') ≤ R.toSubring := Subring.closure_le.2 le_rfl
    exact ⟨⟨a, hle ha⟩, ⟨b, hle hb⟩, rfl⟩
  have hN : ∀ x ∈ R, ∀ z, x ∈ (ofAffine o Ω' R).O z := fun x hx z => algebraMap_mem_O_ofAffine z (⟨x, hx⟩ : R)
  have hN1 : ∀ x ∈ M.ringOn W, φ x ∈ (ofAffine o Ω' R).ringOn (⊤ : (ofAffine o Ω' R).Z.Opens) :=
    fun x hx => mem_ringOn.2 fun z _ => hN _ (hR1 x hx) z
  obtain ⟨p, hp⟩ : ∃ p, M.IsHom (ofAffine o Ω' R) φ p :=
    exists_isHom_of_local fun z => ⟨⊤, W, trivial, hW, hne, hN1⟩
  have hpW : ∀ z, p z ∈ W := fun z => hp.map_mem_of_ringOn hW hne hN1 trivial
  have hNd : ∀ z, (ofAffine o Ω' R).Div (fun j => pairing φ s (B j)) i z := fun z => ⟨hi, fun j => hN _ (hR2 j) z⟩
  obtain ⟨g, hg⟩ := hu (ofAffine o Ω' R) fun z => by
    obtain ⟨i', hi'⟩ := ht (p z)
    obtain ⟨k, hk⟩ := hp.exists_div_pairing s ((hB _ (hpW z)).symm.trans (hv _ i' hi')) (hNd z)
    exact ⟨(i', k), div_mul_prod_iff.2 ⟨hp.div hi', (hc _ i' k z hi'.1).1 hk⟩⟩
  have hgf : g ≫ f = p := (hf.comp hg).unique hp
  let U : M'.Z.Opens := f ⁻¹ᵁ W ⊓ ⟨_, M'.isOpen_setOf_div (fun j => pairing φ s (B j)) i⟩
  have := isAffineOpen_of_isHom R (U := U) ?_ hg ?_
  · exact ⟨U, this.1, rfl, this.2⟩
  · refine Algebra.adjoin_le ?_
    rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hf.map_mem_O (mem_ringOn.1 hx _ hz.1)
    · exact mem_ringOn.2 fun z hz => hz.2.2 j
  · rintro _ ⟨z, rfl⟩
    have hz : f (g z) ∈ W := by
      have := hpW z
      rwa [← hgf] at this
    obtain ⟨j, hj⟩ := h1 _ hz
    exact ⟨hz, hg.div_of_div hj (hNd z)⟩

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem exists_projBundle_closure : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  intro o Ω _ _ _ _ M Ω' _ _ φ J _ EE s hM ⟨j₀, hj₀⟩ hs
  obtain ⟨n, t, e, m, v, ht, hv⟩ := GlobalTheory.T.exists_projective_lattice_twist_generated o Ω M hM J EE
  obtain ⟨i₀, hi₀⟩ := ht.1 (genericPoint M.Z)
  obtain ⟨k₀, hk₀⟩ : ∃ k, pairing φ s (v k) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨c, hc⟩ := EE.exists_eq_sum_pairing (φ := φ) s (hv _ i₀ hi₀) j₀
    exact hj₀ (by simp [hc, pairing_div, h])
  let τ : Fin (n + 1) × Fin m → Ω' := fun q => φ (t q.1) * pairing φ s (v q.2)
  have hφ0 : φ (t i₀) ≠ 0 := (map_ne_zero φ).2 hi₀.1
  have hτ0 : τ (i₀, k₀) ≠ 0 := mul_ne_zero hφ0 hk₀
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Fin (n + 1) × Fin m) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨(i₀, k₀)⟩).ne'
  let ε : Fin (N + 1) ≃ Fin (n + 1) × Fin m := (Fintype.equivFinOfCardEq hN).symm
  obtain ⟨M', hcl, hproj⟩ := exists_isCl_isProjOver o Ω' N (fun l => τ (ε l)) ⟨ε.symm (i₀, k₀), by simpa using hτ0⟩ (by
    set K := Subfield.closure (Set.range (algebraMap o Ω') ∪ {x | ∃ i j, x = τ (ε j) / τ (ε i)})
    have hK : ∀ q, τ q / τ (i₀, k₀) ∈ K := fun q =>
      Subfield.subset_closure (Or.inr ⟨ε.symm (i₀, k₀), ε.symm q, by simp⟩)
    obtain ⟨V, hV, hD, hR⟩ := ht.2 i₀ hi₀.1
    have h1 : ∀ x, φ x ∈ K := map_mem_of_ringOn hV ⟨genericPoint M.Z, hD ▸ hi₀⟩ fun x hx => by
      rw [hR] at hx
      induction hx using Algebra.adjoin_induction with
      | mem _ h =>
        obtain ⟨i, rfl⟩ := h
        simpa [τ, mul_div_mul_right _ _ hk₀] using hK (i, k₀)
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, (φ.commutes r).symm⟩)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    refine EE.eq_top_of_pairing_mem hs (hv _ i₀ hi₀) hk₀ h1 fun k => ?_
    rw [pairing_div, mul_div_assoc]
    exact mul_mem (inv_mem (h1 _)) (by simpa [τ, mul_div_mul_left _ _ hφ0] using hK (i₀, k)))
  have hd : ∀ z, ∃ i k, M'.Div (fun i => φ (t i)) i z ∧ M'.Div (fun k => pairing φ s (v k)) k z := fun z => by
    obtain ⟨l, hl⟩ := hcl.1 z
    exact ⟨(ε l).1, (ε l).2, div_mul_prod_iff.1 ((div_comp_iff ε.surjective).1 hl)⟩
  obtain ⟨f, hf⟩ := ht.exists_isHom (M' := M') (φ := φ) fun z => (hd z).imp fun _ h => h.choose_spec.1
  refine ⟨M', f, hf, hproj, fun W B hW hne hB => ?_⟩
  exact charts_of_universal EE hs ht.1 hv hf (fun z => (hd z).choose_spec.imp fun _ h => h.2)
    (fun N' hN' => hcl.exists_isHom fun z => by
      obtain ⟨q, hq⟩ := hN' z
      obtain ⟨l, rfl⟩ := ε.surjective q
      exact ⟨l, (div_comp_iff (t := τ) ε.surjective).2 hq⟩) W B hW hne hB

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosureStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projBundle_closure_alt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_projBundle_closure | exact GlobalTheory.ZH.RatModel.exists_projBundle_closure | (intros; apply GlobalTheory.ZH.RatModel.exists_projBundle_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitMapSnd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec

def unitMap {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    (𝟙_ (Over S') ⊗ G').left ⟶ (𝟙_ (Over S) ⊗ G).left :=
  (snd (𝟙_ (Over S')) G').left ≫ F ≫ (λ_ G).inv.left

theorem unitMap_snd {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    unitMap F ≫ (snd (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S')) G').left ≫ F := by
  rw [unitMap, Category.assoc, Category.assoc, unit_inv_snd, Category.comp_id]

theorem eq_unitMap {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left)
    {r' : Z ⟶ (𝟙_ (Over S') ⊗ G').left} {r : Z ⟶ (𝟙_ (Over S) ⊗ G).left}
    (h : r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F) : r = r' ≫ unitMap F := by
  rw [unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]

theorem fst_unit {S : Scheme.{0}} (G : Over S) :
    (fst (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S)) G).left ≫ G.hom :=
  ((Category.comp_id _).symm.trans (Over.w (fst (𝟙_ (Over S)) G))).trans (Over.w (snd (𝟙_ (Over S)) G)).symm

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

theorem famφB_comp {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by
  have push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left
    rw [Category.assoc, hc, Category.assoc])
  let ρ := pushHom pb D'.P.A (𝟙 _)
  have hρ : ρ.left = β := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α) := by
      rw [map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α := by rw [push, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)

theorem prod_fam {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (k : ℕ)
    {M : Type} [CommGroup M] (ω : (T.left ⟶ D.P.A.left) → M) (α : D.X) :
    (∏ a, ω (p.left ≫ D.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (D.Oφ p α a) ^ Oinvε a =
      ω p.left ^ k := by
  have a₀ : p.left ≫ D.famφB α 0 = p.left := Category.comp_id _
  have a₁ : p.left ≫ D.famφB α 1 = D.Oφ p α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul p (𝟙 _) (cP D _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : p.left ≫ D.famφB α 2 = D.Oφ p α 1 :=
    congrArg (fun z => z.left) (comp_cP D p α)
  have a₃ : p.left ≫ D.famφB α 3 = D.Oφ p α 3 :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p)
  have a₄ : D.Oφ p α 2 = p.left := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

omit [IsDomain R] [IsDomain V] in
theorem exists_level {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I')
    {G : Over (Spec (CommRingCat.of R))} {G' : Over (Spec (CommRingCat.of V))} {F : G'.left ⟶ G.left}
    (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (e : ℕ) :
    ∃ m : (thickObj V I' e G').left ⟶ (thickObj R I e G).left,
      m ≫ (fstG I e G).left = (fstG I' e G').left ≫ F := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)
  refine ⟨pullback.lift ((fstG I' e G').left ≫ F)
    (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩
  have e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e := pullback.condition
  rw [Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl


set_option maxHeartbeats 1600000 in
theorem expT_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
  intro R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE
  classical
  have hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left :=
    fun _ => (unitMap_snd F).symm
  have hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i := fun α i => by
    rw [famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc,
      famφB_comp C.pbB (C.c_pr α)]
  obtain ⟨σ', hσ, -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL
    C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ))
    (unitMap F) hcG σ
  choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v
    C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k)
    (unitMap C.β) (hcB α) (f (C.xe α))).exists
  have Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J' := by
    intro Z r' r hr z J J' hJ hJ'
    have := sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'
    rw [← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr] at this
    exact this
  have Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
    intro α Z r' r hr z J J' hJ hJ'
    have := sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'
    rw [← eq_unitMap C.β hr] at this
    exact this
  refine ⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩
  swap
  · have := Hf α Z r' r hr z J J' hJ hJ'
    simp only [om, Category.assoc] at this
    exact this
  obtain ⟨S, hS⟩ := hE e
  obtain ⟨m, hm⟩ := exists_level hI C.pb.1.w e
  refine ⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  have hJG : Good U.P.L.L z JG := hJG
  obtain ⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F :=
    ⟨x' ≫ m, by rw [Category.assoc, hm]⟩
  obtain ⟨hq, hlev⟩ := C.lev e Z x' x hx
  obtain ⟨hT, hW⟩ := hlev z J J' hJ hJ'
  have hW := hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)
  have rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F := by
    rw [Category.assoc, unitMap_snd]
  have rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β := by
    rw [Category.assoc, unitMap_snd]
  have rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left := by
    rw [rG₁, hx, ← Category.assoc, hG', Category.assoc]
  have rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left := by
    rw [rB₁, ← hq, ← Category.assoc, hB', Category.assoc]
  have rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left := by
    rw [fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
  obtain ⟨h0, hsum⟩ := hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ
  have hF := fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'
  have Sg := Hσ Z rG' _ rG₁ z JG JG' hJG hJG'
  rw [rG₂, hG'] at Sg
  have hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) *
      ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i =
      gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k := by
    intro α
    have := prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α
    have e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i := fun i => by
      rw [famφT_eq, ← Category.assoc, hB', Category.assoc]
    rw [← hq, ← Category.assoc x' _ C.β]
    refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun i _ => ?_)) this
    · rw [e₁]
    · rw [← Category.assoc x' _ C.β]; rfl
  refine ⟨fun α' hα => ?_, ?_⟩
  · have hi : C.xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))
  · refine (gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨α', rfl⟩ := C.xe.surjective y
    have e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α' := C.xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]
    ring

end GlobalTheory.ExpCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionSection

theorem exists_field_point {X : Scheme.{0}} (w : X) :
    ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply w _⟩

def trivSec {X : Scheme.{0}} {W : X.Opens} (f : Γ(X, W)) : LB.Sec (Inh.trivLB W.toScheme) where
  f := fun _ => (W.ι.appLE W ⊤ W.ι_preimage_self.ge).hom f
  compat := fun _ _ => (_root_.one_mul _).symm

theorem crd_trivSec {X : Scheme.{0}} {W : X.Opens} {J : Type} (f : J → Γ(X, W)) {R : Type} [CommRing R]
    (y : Sp R ⟶ W.toScheme) :
    Crd (Inh.trivLB W.toScheme) (fun j => trivSec (f j)) y (fun j => valR (y ≫ W.ι) W (f j)) :=
  ⟨PUnit.unit, 1, GlobalTheory.Points.le_preimage_top y, fun j =>
    (GlobalTheory.Points.valR_appLE y W.ι _ (GlobalTheory.Points.le_preimage_top y) (f j)).symm.trans (_root_.one_mul _).symm⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_closed (hj : JacobsonSpace M.Z) (z : M.Z) :
    ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ z ⤳ z' ∧ S.HH M z' = S.HH M z := by
  obtain ⟨z', ⟨h1, h2⟩, h3⟩ := nonempty_inter_closedPoints
    (Z := {z' | S.supI M z ⊆ S.supI M z'} ∩ closure {z}) ⟨z, fun _ h => h, subset_closure rfl⟩
    ((OpenPart.isOpen_supI_subset z).isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : z ⤳ z' := specializes_iff_mem_closure.2 h2
  refine ⟨z', h3, hs, congrArg AddSubgroup.closure (Set.Subset.antisymm (fun _ h => ?_) h1)⟩
  exact RatModel.Div.of_specializes h hs

theorem exists_functions (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (z' : M.Z) {a : S.Gam}
    (ha : a ∈ S.HH M z') :
    ∃ (W : M.Z.Opens) (l : Q.Λ) (_ : W ≤ Q.W l) (t : Ω) (i : S.J) (f : S.J → Γ(M.Z, W)), z' ∈ W ∧ t ≠ 0 ∧
      (∀ w ∈ W, S.supI M z' ⊆ S.supI M w) ∧ (∀ k, valF M.pt W (f k) = (Q.B l k ⬝ᵥ S.ev a) / t) ∧
      ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K), ⊤ ≤ y ⁻¹ᵁ W → y ≫ M.s = spMap ψ →
        ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y W (f k)) j ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hB.ov.div z'
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z' x₀ hx₀ a ha
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z'))
  set d := (fun j => algebraMap o Ω (S.proj (S.TT M z') 0 j i)) ⬝ᵥ S.ev a with hd
  let V : M.Z.Opens := ⟨(⋂ k, {w | (Q.B l k ⬝ᵥ S.ev a) / S.th x₀ ∈ M.O w}) ∩ {w | S.th x₀ / d ∈ M.O w} ∩
      {w | S.supI M z' ⊆ S.supI M w},
    ((isOpen_iInter_of_finite fun _ => M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)).inter
      (OpenPart.isOpen_supI_subset z')⟩
  have hz : z' ∈ V ⊓ Q.W l := ⟨⟨⟨Set.mem_iInter.2 fun k => h1 _ (by
    rw [Q.basis l z' hl]; exact Submodule.subset_span ⟨k, rfl⟩), h3⟩, fun _ h => h⟩, hl⟩
  have hne : ((V ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty := ⟨z', hz⟩
  choose f hf using fun k => (RatModel.mem_ringOn_iff_exists hne (x := (Q.B l k ⬝ᵥ S.ev a) / S.th x₀)).1
    (RatModel.mem_ringOn.2 fun w hw => Set.mem_iInter.1 hw.1.1.1 k)
  obtain ⟨u, hu⟩ := (RatModel.mem_ringOn_iff_exists hne (x := S.th x₀ / d)).1
    (RatModel.mem_ringOn.2 fun w hw => hw.1.1.2)
  refine ⟨V ⊓ Q.W l, l, inf_le_right, S.th x₀, i, f, hz, hx₀.1, fun w hw => hw.1.2, hf, ?_⟩
  have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K) (hy : ⊤ ≤ y ⁻¹ᵁ (V ⊓ Q.W l)),
      y ≫ M.s = spMap ψ → CrdCalc.valHom y _ hy (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
        ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y _ (f k)) j := by
    intro K _ y ψ hy hψ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_over M.s ψ y hψ _ hy]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ hy]
    rfl
  have hone : u * (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
      ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = 1 := by
    have hp := M.top_le_preimage_pt hne
    refine M.res_injective _ hne ?_
    rw [map_one, map_mul, M.res_apply, hu]
    have e := key Ω M.pt _ hp M.pt_s
    have e2 : (fun k => valR M.pt _ (f k)) = (S.th x₀)⁻¹ • (Q.B l).mulVec (S.ev a) := by
      funext k
      exact (hf k).trans (by rw [div_eq_inv_mul]; rfl)
    have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
    rw [e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e3, Matrix.one_mulVec] at e
    have e4 : ∑ j, algebraMap o Ω (S.proj (S.TT M z') 0 j i) * ((S.th x₀)⁻¹ • S.ev a) j = (S.th x₀)⁻¹ * d := by
      rw [hd, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [M.res_apply, ← valR_of_field, CrdCalc.valR_eq _ _ hp, e, e4]
    have := hx₀.1
    field_simp
  intro K _ y ψ hy hψ
  rw [← key K y ψ hy hψ]
  have := congrArg (CrdCalc.valHom y _ hy) hone
  rw [map_mul, map_one] at this
  exact right_ne_zero_of_mul_eq_one this

def torsSec (Q : Clos ρ M U₀ EE) (a : S.Gam) : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
  pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
    have h : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
    rw [Category.assoc, Category.id_comp]
    exact (congrArg (Q.u₀ ≫ ·) h).trans (Category.comp_id _))

theorem torsSec_over (Q : Clos ρ M U₀ EE) (a : S.Gam) : torsSec Q a ≫ Q.a₀ ≫ Q.P.hom = U₀.ι := by
  rw [Q.cart.w, torsSec, pullback.lift_snd_assoc, Category.id_comp]

theorem agree (Q : Clos ρ M U₀ EE) (a : S.Gam) {W : M.Z.Opens} (h : W.toScheme ⟶ Q.P.left)
    (hh : h ≫ Q.P.hom = W.ι) (e : Sp Ω ⟶ W.toScheme) (he : e ≫ W.ι = M.pt) (e₀ : Sp Ω ⟶ U₀.toScheme)
    (he₀ : e₀ ≫ U₀.ι = M.pt) (hg : e ≫ h = e₀ ≫ torsSec Q a ≫ Q.a₀) {K : Type} [Field K]
    (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
    (h1 : x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι)
    (h2 : x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left) : x ≫ h = x' ≫ Q.a₀ := by
  have lift : ∀ {F : Type} [Field F] (y : Sp F ⟶ W.toScheme) (y₀ : Sp F ⟶ U₀.toScheme), y ≫ W.ι = y₀ ≫ U₀.ι →
      ∃ v : Sp F ⟶ (W ⊓ U₀).toScheme, v ≫ M.Z.homOfLE inf_le_left = y ∧ v ≫ M.Z.homOfLE inf_le_right = y₀ := by
    intro F _ y y₀ hy
    have hr : Set.range (y ≫ W.ι) ⊆ Set.range (W ⊓ U₀).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      exact ⟨(y w).2, hy ▸ (y₀ w).2⟩
    refine ⟨IsOpenImmersion.lift (W ⊓ U₀).ι _ hr, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
    · rw [← cancel_mono U₀.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, hy]
  obtain ⟨v, hv, hv₀⟩ := lift e e₀ (he.trans he₀.symm)
  have hvι : v ≫ (W ⊓ U₀).ι = M.pt := by
    rw [← Scheme.homOfLE_ι M.Z (inf_le_left : W ⊓ U₀ ≤ W), ← Category.assoc, hv, he]
  have : IsDominant (v ≫ (W ⊓ U₀).ι) := hvι ▸ M.isDominant_pt
  have : IsDominant v := IsDominant.of_comp_of_isOpenImmersion v (W ⊓ U₀).ι
  have := Q.proper
  have E : M.Z.homOfLE (inf_le_left : W ⊓ U₀ ≤ W) ≫ h =
      M.Z.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀) ≫ torsSec Q a ≫ Q.a₀ := by
    refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ v ?_
    · simp only [Category.assoc, hh, torsSec_over, Scheme.homOfLE_ι]
    · rw [← Category.assoc, hv, ← Category.assoc, hv₀, hg]
  obtain ⟨y, hy, hy₀⟩ := lift x (x' ≫ pullback.snd _ _) (by rw [h1, Category.assoc])
  have hx' : (x' ≫ pullback.snd _ _) ≫ torsSec Q a = x' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, torsSec, pullback.lift_fst, h2, Category.assoc]
    · rw [Category.assoc, torsSec, pullback.lift_snd, Category.comp_id]
  rw [← hy, Category.assoc, E, ← Category.assoc, hy₀, ← Category.assoc, hx']

theorem crd_generic (Q : Clos ρ M U₀ EE) (a : S.Gam) (l : Q.Λ) {t : Ω} (ht : t ≠ 0)
    (x : Sp Ω ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (hx : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt)
    (hc : Crd Q.O1 Q.st (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a)) :
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x (fun k => (Q.B l k ⬝ᵥ S.ev a) / t) := by
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x
  have h1 := Q.rel l Ω x w hw
  rw [hx] at h1
  obtain ⟨c, hc⟩ := CrdCalc.crd_unique h1 hc
  have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
  have e4 := mul_eq_one_comm.1 e3
  have e5 : S.ev a = (c : Ω) • ((Q.c l).map (valR M.pt (Q.W l))).mulVec w := funext hc
  have e6 : (Q.B l).mulVec (S.ev a) = (c : Ω) • w := by
    rw [e5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec]
  have := CrdCalc.crd_smul ((Units.mk0 t ht)⁻¹ * c) hw
  convert this using 2 with k
  have e7 : Q.B l k ⬝ᵥ S.ev a = c * w k := congrFun e6 k
  rw [e7, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_inv_mul, _root_.mul_assoc]

theorem exists_section : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀ := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q z a ha
  obtain ⟨z', hcl, hs, hH⟩ := exists_closed (S := S) hB.jac z
  obtain ⟨W, l, hle, t, i, f, hz', ht, hsup, hf, hkey⟩ := exists_functions hB Q z' (hH ▸ ha)
  have liftPt : ∀ {X : Scheme.{0}} (y : Sp Ω ⟶ X) (V : X.Opens), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ e : Sp Ω ⟶ V.toScheme, e ≫ V.ι = y := fun y V hV =>
    ⟨IsOpenImmersion.lift V.ι y (by rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hV),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨e, he⟩ := liftPt M.pt W (M.top_le_preimage_pt ⟨z', hz'⟩)
  obtain ⟨e₀, he₀⟩ := liftPt M.pt U₀ (M.top_le_preimage_pt hB.ov.ne)
  have hp : (e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom = M.pt := by
    simp only [Category.assoc, torsSec_over, he₀]
  obtain ⟨e', he'⟩ := liftPt (e₀ ≫ torsSec Q a ≫ Q.a₀) (Q.P.hom ⁻¹ᵁ Q.W l) (by
    change ⊤ ≤ ((e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom) ⁻¹ᵁ Q.W l
    rw [hp]
    exact M.top_le_preimage_pt (Q.ne l))
  have hp' : e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt := by rw [← Category.assoc, he', hp]
  have hc : Crd Q.O1 Q.st (e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a) := by
    rw [he', ← Category.assoc]
    refine Q.crd Ω _ _ ?_
    rw [Category.assoc, torsSec, pullback.lift_fst, ← Category.assoc, Q.u₀_pt e₀ he₀]
    exact (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 Ω S.R.val.toRingHom a
  have hval : ∀ {K : Type} [Field K] (y : Sp K ⟶ W.toScheme), ∃ ψ : o →+* K, (y ≫ W.ι) ≫ M.s = spMap ψ ∧
      ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
        ((Q.c l).map (valR (y ≫ W.ι) (Q.W l))).mulVec (fun k => valR (y ≫ W.ι) W (f k)) j ≠ 0 := fun y =>
    ⟨(Spec.preimage ((y ≫ W.ι) ≫ M.s)).hom, (Spec.map_preimage _).symm,
      hkey _ _ _ (fun w _ => (y w).2) (Spec.map_preimage _).symm⟩
  have hcov : ⨆ j, nonzeroLocus (trivSec (f j)) = ⊤ := by
    refine top_unique fun w _ => ?_
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, -, hψ⟩ := hval y
    have : ∃ k, valR (y ≫ W.ι) W (f k) ≠ 0 := by
      by_contra hn
      push_neg at hn
      simp [hn, Matrix.mulVec, dotProduct] at hψ
    obtain ⟨k, hk⟩ := this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (CrdCalc.top_le_iff y _).1
      ((CrdCalc.crd_isUnit_iff k (crd_trivSec f y)).1 (isUnit_iff_ne_zero.2 hk))⟩
  have : IsDominant (e ≫ W.ι) := he ▸ M.isDominant_pt
  have hdom : IsDominant e := IsDominant.of_comp_of_isOpenImmersion e W.ι
  obtain ⟨g, hg, hge, hgc⟩ := GlobalTheory.T.exists_factor_closedImmersion_dense_points Γ(M.Z, Q.W l) _ W.toScheme
    ((Q.P.hom ∣_ Q.W l) ≫ (Q.aff l).isoSpec.hom) (M.Z.homOfLE hle ≫ (Q.aff l).isoSpec.hom) _ _ S.J (Q.σ l)
    (fun j => trivSec (f j)) (LB.isLB_pull Q.isLB _) (Inh.trivLB_isLB _) (Q.imm l) hcov Ω Unit (fun _ => e)
    (fun _ => e') (by rw [Set.iUnion_const]; exact hdom.denseRange) (fun _ => ⟨by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (Q.W l).ι, Category.assoc, morphismRestrict_ι, hp', Category.assoc, Scheme.homOfLE_ι, he],
      _, crd_trivSec f e, by
      have := crd_generic Q a l ht e' hp' hc
      convert this using 2 with k
      rw [he]
      exact hf k⟩)
  have hg' : g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = W.ι := by
    rw [← Category.assoc, cancel_mono] at hg
    rw [← morphismRestrict_ι, ← Category.assoc, hg, Scheme.homOfLE_ι]
  have hG : Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Set.range Q.G.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, hψ, hne⟩ := hval y
    have h1 := Q.rel l K _ _ (hgc K y _ (crd_trivSec f y))
    rw [Category.assoc y g (_ ≫ _), hg'] at h1
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    have h2 := (OpenPart.le_nonzeroLocus_iff hφ (x := (y ≫ g) ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (ψ := ψ) (by
      rw [← hψ, ← hg']; simp only [Category.assoc]) h1).2 hne
    simp only [Clos.G, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    refine ⟨z', hcl, W, hsup, i, φ, hφ, ?_, (CrdCalc.top_le_iff _ _).1 h2⟩
    change (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (y (IsLocalRing.closedPoint K)) ∈ W
    rw [hg']
    exact (y _).2
  have hfac := IsOpenImmersion.lift_fac Q.G.ι _ hG
  refine ⟨W, IsOpenImmersion.lift Q.G.ι _ hG, hs.mem_open W.isOpen hz', ?_, fun K _ x x' h1 h2 => ?_⟩
  · rw [← Category.assoc, hfac, Category.assoc, hg']
  · rw [hfac]
    refine agree Q a _ (by rw [Category.assoc, hg']) e he e₀ he₀ ?_ x x' h1 h2
    rw [← Category.assoc, hge (), he']

end GlobalTheory.ZH.TorsionSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupportStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_torsionPoints_support : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀ := by
  first | exact @GlobalTheory.ZH.TorsionSection.exists_section | exact GlobalTheory.ZH.TorsionSection.exists_section | (intros; apply GlobalTheory.ZH.TorsionSection.exists_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.exists_testFac_of_large : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → ∃ jV yV yK, Q.TestFac y u jV yV yK := by
  intro o Ω _ _ _ hA S ρ M U₀ Q hO z p _ y hy
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hat, hn, fun u hu => ?_⟩
  let j : u.V →+* OO p :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).codRestrict (OO p)
      fun x => (mem_OO_iff _).2 ((u.norm_le _).2 ⟨x, rfl⟩)
  have hj : Function.Injective j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨j, yV, IsOpenImmersion.lift U₀.ι _ hr, fun _ => rfl, hfac, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_gen
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classical_point_factor_large_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → ∃ jV yV yK, Q.TestFac y u jV yV yK := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_testFac_of_large | exact GlobalTheory.ZH.ZHPre.exists_testFac_of_large | (intros; apply GlobalTheory.ZH.ZHPre.exists_testFac_of_large <;> assumption)
end
end
