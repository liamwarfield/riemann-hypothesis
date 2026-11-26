module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.InFibChart

theorem eval_scale {K J : Type} [CommRing K] (c : K) (x : J → K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    MvPolynomial.eval (fun j => c * x j) F = c ^ d * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_subst {K J : Type} [CommRing K] [Fintype J] (g : Matrix J J K) {F : MvPolynomial J K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    ∃ F' : MvPolynomial J K, F'.IsHomogeneous d ∧
      ∀ v, MvPolynomial.eval v F' = MvPolynomial.eval (g.mulVec v) F := by
  refine ⟨MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (g i j) * MvPolynomial.X j) F, ?_, fun v => ?_⟩
  · have := hF.aeval (n := 1) (fun i => ∑ j, MvPolynomial.C (g i j) * (MvPolynomial.X j : MvPolynomial J K))
      (fun i => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using this
  · clear hF
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Matrix.mulVec, dotProduct]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

theorem hom_genericPoint (hU : (U₀ : Set M.Z).Nonempty) :
    Q.P.hom (genericPoint Q.P.left) = genericPoint M.Z := by
  have hg : genericPoint M.Z ∈ U₀ := (genericPoint_specializes hU.some).mem_open U₀.isOpen hU.some_mem
  have hw : η[ρ.P.A].left ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  let s : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ η[ρ.P.A].left) (𝟙 _) (by
      rw [Category.assoc, Category.id_comp]; exact (congrArg (Q.u₀ ≫ ·) hw).trans (Category.comp_id _))
  have hs : (s ≫ Q.a₀) ≫ Q.P.hom = U₀.ι := by
    rw [Category.assoc, Q.cart.w, pullback.lift_snd_assoc, Category.id_comp]
  have h1 : Q.P.hom ((s ≫ Q.a₀) ⟨_, hg⟩) = genericPoint M.Z :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f : U₀.toScheme ⟶ M.Z => f ⟨_, hg⟩) hs)
  have h2 := (genericPoint_specializes ((s ≫ Q.a₀) ⟨_, hg⟩)).map Q.P.hom.continuous
  rw [h1] at h2
  exact (h2.antisymm (genericPoint_specializes _)).eq

theorem exists_change (l l' : Q.Λ) {z : M.Z} (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l') :
    ∃ g : Matrix S.J S.J (M.O z), Q.B l' = g.map (↑) * Q.B l ∧
      (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑) := by
  have h : ∀ i, ∃ a : S.J → M.O z, ∑ j, a j • Q.B l j = Q.B l' i := fun i => by
    refine (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun j k => Q.B l j k)).1 ?_
    refine (Q.basis l z hl).le ((Q.basis l' z hl').ge ?_)
    exact Submodule.subset_span ⟨i, rfl⟩
  choose a ha using h
  have e : Q.B l' = (Matrix.of a).map (↑) * Q.B l := by
    ext i k
    rw [← ha i]
    simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]
  refine ⟨Matrix.of a, e, ?_⟩
  have h1 := mul_eq_one_comm.1 (Q.c_inv l)
  have h2 := Q.c_inv l'
  rw [e] at h2
  calc _ = ((Q.c l').map (valF M.pt (Q.W l')) * ((Matrix.of a).map (↑) * Q.B l)) *
        (Q.c l).map (valF M.pt (Q.W l)) := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem crd_change_loc (l l' : Q.Λ) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (y' : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp R ⟶ M.Z)
    (hy : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : y ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t) (q : Sp R) (hq : t q = genericPoint M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint R) ⤳ z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → R} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) y w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') y' w') :
    ∃ u : Rˣ, ∀ j, w' j = (u : R) * (g.map (RatModel.valLoc t z hz)).mulVec w j := by
  have ht' : y' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by
    rw [← Category.assoc, hy, Category.assoc, ht]
  have h1 := Q.rel l R y w hw
  have h2 := Q.rel l' R y' w' hw'
  rw [ht] at h1
  rw [ht', hy] at h2
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h1 h2
  refine ⟨u, ?_⟩
  let C : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl (Q.c l i j)⟩
  let C' : Matrix S.J S.J (M.O z) := Matrix.of fun i j => ⟨_, RatModel.valF_mem_O hl' (Q.c l' i j)⟩
  have hC : C = C' * g := by
    ext i j
    have := congrFun (congrFun hg i) j
    simpa [Matrix.mul_apply, C, C'] using this
  have e1 : (Q.c l).map (valR t (Q.W l)) = C.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl _).symm
  have e2 : (Q.c l').map (valR t (Q.W l')) = C'.map (RatModel.valLoc t z hz) := by
    ext i j
    exact (RatModel.valLoc_valF t hz hl' _).symm
  have hW : ⊤ ≤ t ⁻¹ᵁ Q.W l' := (CrdCalc.top_le_iff t _).2 (hz.mem_open (Q.W l').isOpen hl')
  have hdet : ((Q.c l').map (valR t (Q.W l'))).det ≠ 0 := by
    have e3 : (Q.c l').map (valR t (Q.W l')) = (CrdCalc.valHom t _ hW).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq t _ hW _
    rw [e3, ← RingHom.map_det]
    intro h0
    have hpt : ⊤ ≤ M.pt ⁻¹ᵁ Q.W l' := M.top_le_preimage_pt (Q.ne l')
    have e4 : (Q.c l').map (valF M.pt (Q.W l')) = (CrdCalc.valHom M.pt _ hpt).mapMatrix (Q.c l') := by
      ext i j
      exact CrdCalc.valR_eq M.pt _ hpt _
    have h5 : IsUnit (valR M.pt (Q.W l') (Q.c l').det) := by
      rw [CrdCalc.valR_eq M.pt _ hpt, RingHom.map_det, ← e4]
      exact Matrix.isUnit_det_of_right_inverse (Q.c_inv l')
    have h6 : genericPoint M.Z ∈ M.Z.basicOpen (Q.c l').det := by
      rw [← M.pt_apply (IsLocalRing.closedPoint Ω)]
      exact (CrdCalc.isUnit_valR_iff M.pt _ hpt _).1 h5 (Set.mem_univ _)
    have h7 : (t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det = 0 :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (h0.trans (map_zero _).symm)
    have b := Scheme.basicOpen_appLE t ⊤ (Q.W l') hW (Q.c l').det
    have h8 : q ∈ (Sp R).basicOpen ((t.appLE (Q.W l') ⊤ hW).hom (Q.c l').det) :=
      b.ge ⟨trivial, show t q ∈ _ from hq ▸ h6⟩
    rw [h7, Scheme.basicOpen_zero] at h8
    exact h8
  have h9 : ((Q.c l').map (valR t (Q.W l'))).mulVec
      (w' - (u : R) • (g.map (RatModel.valLoc t z hz)).mulVec w) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, sub_eq_zero]
    funext j
    rw [hu j, e1, e2, hC, Matrix.map_mul]
    rfl
  have h10 := sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hdet h9)
  intro j
  rw [h10]
  rfl

theorem crd_change (hU : (U₀ : Set M.Z).Nonempty) (l l' : Q.Λ) {K : Type} [Field K]
    (x : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l').toScheme) (t : Sp K ⟶ M.Z)
    (hx : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι)
    (ht : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l) (hl' : z ∈ Q.W l')
    (g : Matrix S.J S.J (M.O z))
    (hg : (Q.c l).map (valF M.pt (Q.W l)) = (Q.c l').map (valF M.pt (Q.W l')) * g.map (↑))
    {w w' : S.J → K} (hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x w)
    (hw' : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l').ι) (Q.σ l') x' w') :
    ∃ u : K, w' = fun j => u * (g.map fun a => M.val t a).mulVec w j := by
  obtain ⟨X, hX⟩ : ∃ X : Sp K ⟶ Q.P.left, X = x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι := ⟨_, rfl⟩
  have hXt : X ≫ Q.P.hom = t := by rw [hX, Category.assoc, ht]
  let p : Q.P.left := X (IsLocalRing.closedPoint K)
  have hp : Q.P.hom p = z := by
    rw [← hz, ← hXt]
    exact (Scheme.Hom.comp_apply _ _ _).symm
  let R : Type := Q.P.left.presheaf.stalk p
  let Y : Sp R ⟶ Q.P.left := Q.P.left.fromSpecStalk p
  let φ : R →+* K := (Scheme.stalkClosedPointTo (R := .of K) X).hom
  have hφ : spMap φ ≫ Y = X := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of K) X
  have hr : Set.range Y = {ξ | ξ ⤳ p} := Scheme.range_fromSpecStalk
  have hlift : ∀ k : Q.Λ, z ∈ Q.W k → ∃ y : Sp R ⟶ (Q.P.hom ⁻¹ᵁ Q.W k).toScheme,
      y ≫ (Q.P.hom ⁻¹ᵁ Q.W k).ι = Y := fun k hk =>
    ⟨IsOpenImmersion.lift _ Y (by
      rw [Scheme.Opens.range_ι, hr]
      exact fun ξ hξ => Specializes.mem_open hξ (Q.P.hom ⁻¹ᵁ Q.W k).isOpen (show Q.P.hom p ∈ Q.W k from hp ▸ hk)),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨y, hy⟩ := hlift l hl
  obtain ⟨y', hy'⟩ := hlift l' hl'
  have hxy : spMap φ ≫ y = x := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l).ι, Category.assoc, hy, hφ, hX]
  have hxy' : spMap φ ≫ y' = x' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W l').ι, Category.assoc, hy', hφ, hX, hx]
  obtain ⟨q, hq⟩ : genericPoint Q.P.left ∈ Set.range Y := hr ▸ genericPoint_specializes p
  have hq' : (Y ≫ Q.P.hom) q = genericPoint M.Z := by
    rw [Scheme.Hom.comp_apply, hq, hom_genericPoint Q hU]
  have hc : (Y ≫ Q.P.hom) (IsLocalRing.closedPoint R) ⤳ z := by
    have : Y (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
    exact specializes_of_eq ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg Q.P.hom this).trans hp))
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l) y
  obtain ⟨v', hv'⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB _) (Q.σ l') y'
  obtain ⟨u, hu⟩ := crd_change_loc Q l l' y y' (Y ≫ Q.P.hom) (hy'.trans hy.symm)
    (by rw [← Category.assoc, hy]) q hq' hc hl hl' g hg hv hv'
  have k1 := CrdCalc.crd_map φ hv
  have k2 := CrdCalc.crd_map φ hv'
  rw [hxy] at k1
  rw [hxy'] at k2
  obtain ⟨a, ha⟩ := CrdCalc.crd_unique hw k1
  obtain ⟨b, hb⟩ := CrdCalc.crd_unique k2 hw'
  refine ⟨b * φ u * a, funext fun j => ?_⟩
  have hval : ∀ c : M.O z, φ (RatModel.valLoc (Y ≫ Q.P.hom) z hc c) = M.val t c := fun c => by
    rw [← RatModel.val_spMap_comp, ← Category.assoc, hφ, hXt]
  rw [hb j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hu j, map_mul, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, hval, ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem tors_change (hB : BaseFacts S M U₀ EE) (l l' : Q.Λ) {K : Type} [Field K] (t : Sp K ⟶ M.Z)
    {z : M.Z} (hz : t (IsLocalRing.closedPoint K) = z) (hl : z ∈ Q.W l)
    (g : Matrix S.J S.J (M.O z)) (hg : Q.B l' = g.map (↑) * Q.B l) {v : S.J → K} (hv : v ∈ Q.Tors t l) :
    (g.map fun a => M.val t a).mulVec v ∈ Q.Tors t l' := by
  obtain ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, rfl⟩ := hv
  have hzz : z' = z := by rw [← hw, ← hz, Subsingleton.elim w (IsLocalRing.closedPoint K)]
  subst hzz
  refine ⟨z', ⟨w, hw⟩, x₀, hx₀, h, hh, funext fun i => ?_⟩
  have hr : Set.range t = {z'} := hw ▸ RatModel.range_eq_singleton t w
  let a : S.J → M.O z' := fun j => ⟨(Q.B l j ⬝ᵥ S.ev h) / S.th x₀,
    (hB.sec z' x₀ hx₀ h hh).1 _ ((Q.basis l z' hl).ge (Submodule.subset_span ⟨j, rfl⟩))⟩
  have e : (Q.B l' i ⬝ᵥ S.ev h) / S.th x₀ = ((∑ j, g i j * a j : M.O z') : Ω) := by
    have e1 : Q.B l' i ⬝ᵥ S.ev h = (Q.B l').mulVec (S.ev h) i := rfl
    rw [e1, hg, ← Matrix.mulVec_mulVec]
    simp [a, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← RatModel.valHom_apply t z' hr, map_sum]
  simp only [map_mul, RatModel.valHom_apply]
  rfl

theorem inFib_of_chart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (l : Q.Λ) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → (∀ (d : ℕ) (Pf : MvPolynomial S.J K), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d → (∀ v ∈ Q.Tors (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) l, MvPolynomial.eval v Pf = 0) → MvPolynomial.eval w Pf = 0) → Q.InFib (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ l x w hw H l' x' w' hx hw' d Pf hd hPf hT
  rw [Category.assoc] at hT
  obtain ⟨t, ht⟩ : ∃ t, x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t := ⟨_, rfl⟩
  have ht' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l').ι ≫ Q.P.hom = t := by rw [← Category.assoc, hx, Category.assoc, ht]
  rw [ht] at hT H
  have hl : t (IsLocalRing.closedPoint K) ∈ Q.W l := by
    rw [← ht]
    exact (x (IsLocalRing.closedPoint K)).2
  have hl' : t (IsLocalRing.closedPoint K) ∈ Q.W l' := by
    rw [← ht']
    exact (x' (IsLocalRing.closedPoint K)).2
  obtain ⟨g, hg, hc⟩ := exists_change Q l l' hl hl'
  obtain ⟨u, rfl⟩ := crd_change Q hB.ov.ne l l' x x' t hx ht rfl hl hl' g hc hw hw'
  obtain ⟨F, hF, hev⟩ := exists_subst (g.map fun a => M.val t a) hPf
  have h0 := H d F hd hF fun v hv => by
    rw [hev]
    exact hT _ (tors_change Q hB l l' t rfl hl g hg hv)
  rw [eval_scale u _ hPf, ← hev, h0, mul_zero]

end GlobalTheory.ZH.InFibChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal
open GlobalTheory.ThetaPtMove

theorem exists_good_translate : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  intro hL S P K _ _ x n hn hK th hth a
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := hth (Over.mk x) β
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 := fun e => c.ne_zero 0 ((hc 0).trans e)
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

end GlobalTheory.ThetaReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_geometricPoint : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_good_translate | exact GlobalTheory.ThetaReal.exists_good_translate | (intros; apply GlobalTheory.ThetaReal.exists_good_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) : LB X where
  «ι» := I
  U := V
  g l l' := res (show V l ⊓ V l' ≤ π ⁻¹ᵁ (A.U (idx l) ⊓ A.U (idx l')) from fun _ hy => ⟨le l hy.1, le l' hy.2⟩)
    (pullU π _ (A.g (idx l) (idx l')))

theorem gm_refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (y : X) (l l' : I) (h : y ∈ V l) (h' : y ∈ V l') :
    gm (𝟙 X) y (V l ⊓ V l') ((refinePull A π V idx le).g l l') =
      gm π y (A.U (idx l) ⊓ A.U (idx l')) (A.g (idx l) (idx l')) := by
  have hm : (𝟙 X : X ⟶ X) y ∈ V l ⊓ V l' := ⟨h, h'⟩
  refine (gm_res (𝟙 X) y _ hm _).trans ((gm_pull (𝟙 X) π y (A.U (idx l) ⊓ A.U (idx l'))
    ⟨le l h, le l' h'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem refinePull_isLB {X Y : Scheme.{0}} (A : LB Y) (hA : A.IsLB) (π : X ⟶ Y) {I : Type} (V : I → X.Opens)
    (idx : I → A.ι) (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (hV : ⨆ l, V l = ⊤) : (refinePull A π V idx le).IsLB := by
  refine ⟨hV, fun (l : I) => unit_ext (V := V l) fun y hy => ?_,
    fun (i j k : I) => unit_ext (V := V i ⊓ V j ⊓ V k) fun y hy => ?_⟩
  · refine (gm_res (𝟙 X) y _ hy _).trans ((gm_refinePull A π V idx le y l l hy hy).trans ?_)
    exact (mul_eq_left.1 (gm_cocycle hA π y (le l hy) (le l hy) (le l hy))).trans (map_one _).symm
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i j hy.1.1 hy.1.2))
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y j k hy.1.2 hy.2))).trans
      ((gm_cocycle hA π y (le i hy.1.1) (le j hy.1.2) (le k hy.2)).trans
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i k hy.1.1 hy.2)).symm))

theorem exists_mem_splitChart {S : Scheme.{0}} (E : SplitExt S) (y : E.B.left) : ∃ j, y ∈ E.chart j := by
  classical
  choose j hj using fun k : Module.Free.ChooseBasisIndex ℤ E.X => exists_chart (E.O (E.basis k)).isLB y
  refine ⟨j, ?_⟩
  show y ∈ ((⨅ k, (E.O (E.basis k)).L.U (j k) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hj

theorem exists_affine_refinement : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  intro S E Y A hA π
  have key : ∀ y : E.B.left, ∃ (V : E.B.left.Opens) (i : A.ι), y ∈ V ∧ IsAffineOpen V ∧ V ≤ π ⁻¹ᵁ A.U i ∧
      ∃ j, V ≤ E.chart j := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hA (π y)
    obtain ⟨j, hj⟩ := exists_mem_splitChart E y
    obtain ⟨V, hV, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := π ⁻¹ᵁ A.U i ⊓ E.chart j) ⟨hi, hj⟩
    exact ⟨V, i, hy, hV, fun z hz => (hle hz).1, j, fun z hz => (hle hz).2⟩
  choose V idx hy haff le hch using key
  refine ⟨refinePull A π V idx le, refinePull_isLB A hA π V idx le ?_, haff, hch,
    ⟨⟨idx, le, fun y l l' h h' => gm_refinePull A π V idx le y l l' h h'⟩⟩⟩
  exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtChartsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_refinement_splitExtCharts : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  first | exact @GlobalTheory.ZH.UFib.exists_affine_refinement | exact GlobalTheory.ZH.UFib.exists_affine_refinement | (intros; apply GlobalTheory.ZH.UFib.exists_affine_refinement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.WeightZero

theorem eq_zero_of_q_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {α : X} (h : q α ≤ 0) : α = 0 := by
  by_contra h0
  have h1 : {x | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0)
    (fun n => ?_) h1
  rw [Set.mem_setOf_eq, q.map_smul, not_lt]
  exact smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h

theorem proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t ht ht', c ⟨t, ht⟩ = c' ⟨t, ht'⟩) : S.proj T c = S.proj T' c' := by
  subst h
  rw [show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]

theorem nsmul_char {T : Type} [AddCommGroup T] (N : ℕ) (c : T →+ ZMod N) : N • c = 0 := by
  ext x
  rw [AddMonoidHom.nsmul_apply]
  simp

theorem map_add_nsmul {X T : Type} [AddCommGroup X] [AddCommGroup T] (N : ℕ) (w : X →+ (T →+ ZMod N)) (β m : X) :
    w (β + N • m) = w β := by
  rw [map_add (f := _), map_nsmul, nsmul_char, add_zero]

theorem span_eq_of_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (b : S.J → S.J → PadicAlgCl p)
    (a : S.J → τ.X) (ha : ∀ i v, τ.q (a i) ≤ τ.q (a i + S.N • v))
    (hE : τ.E = Submodule.span (OO p) (Set.range b))
    (hb : ∀ i, ((S.proj _ (τ.wt (a i))).map fun x => y₀ (algebraMap o S.R x)).mulVec (b i) = b i) :
    Submodule.span (OO p) (b '' {i | a i = 0}) =
      Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j i))) := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0 := fun α hα h => by
    have h3 := TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])
    rw [map_zero] at h3
    exact eq_zero_of_q_nonpos _ τ.pos h3
  let φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p),
    ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i := ⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩
  have hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c) := fun c => Matrix.ext fun j i => (hQd c j i).symm
  have hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0 := fun c => by
    rw [hQe, hQe, ← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero _
  obtain ⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v :=
    ⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩
  have hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i := fun c i => hL _
  have hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i := fun i => by
    rw [hQe]
    exact hb i
  simp only [hQd]
  have h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i) := by
    rw [ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩
    simp only [hQd]
    have h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i := by
      rw [← hcol, hL, hL, ← Matrix.mulVec_smul]
      rfl
    rw [h2, hQ]
    split_ifs with h
    · rw [hz α hα h, map_zero, zero_div, Real.exp_zero] at hl
      exact Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]
      exact Submodule.zero_mem _
  have h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0}) := by
    rw [hE, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases h : 0 = τ.wt (a i)
    · rw [hL, h, hb']
      exact Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩
    · rw [hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    refine h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    have := hb' i
    rw [show a i = 0 from hi, map_zero] at this
    rw [hL, this]
  · rintro _ ⟨i, rfl⟩
    refine h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩
    · rw [map_zero]
      by_contra! h
      rw [eq_zero_of_q_nonpos _ τ.pos h.le, map_zero] at h
      exact lt_irrefl _ h
    · simp
    · funext j
      rw [map_zero, _root_.one_mul, hQd]
    · rw [hcol, hQ, if_pos rfl]

theorem short_transfer {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (e : X ≃+ Y) (f : Z ≃+ Y)
    (q : QuadraticMap ℤ X ℝ) (q' : QuadraticMap ℤ Y ℝ) (hq : ∀ α, q α = q' (e α)) {N : ℕ} {y : Y}
    (h : Short (q'.comp f.toIntLinearEquiv.toLinearMap) N (f.symm y)) (v : X) :
    q (e.symm y) ≤ q (e.symm y + N • v) := by
  have h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v))) := h (f.symm (e v))
  simpa [hq] using h3

end GlobalTheory.ZH.WeightZero

namespace GlobalTheory.ZH

open WeightZero in
theorem span_rows_class_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  intro o Ω _ _ _ hA S ρ p _ y₀ t _
  obtain ⟨e, hq, hy⟩ := t.mt
  have hker : t.τ.yy.ker = t.l.yy.ker := by
    ext a
    have := hy a 0
    rw [map_zero] at this
    exact this
  have hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩ := fun α x h h' => by
    obtain ⟨a, ha⟩ := t.τ.yy_onto (QuotientAddGroup.mk α)
    rw [t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]
  have hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v := fun α h =>
    TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by
      rw [hwt α x.1 x.2 (hker ▸ x.2), h]
      rfl)
  have hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m := fun α β => by
    constructor
    · intro h
      obtain ⟨v, hv⟩ := hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])
      refine ⟨e v, ?_⟩
      rw [← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]
    · rintro ⟨m, rfl⟩
      exact map_add_nsmul _ _ _ _
  refine ⟨hker, hcl, ?_⟩
  have h1 := span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i))
    (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span
    (fun i => by
      have h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i)) :=
        proj_congr S (congrArg S.perp hker) _ _ fun x h h' =>
          (hwt _ x h h').trans (by rw [e.apply_symm_apply])
      rw [h3]
      exact t.wt i)
  have h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0} := Set.ext fun i => e.symm.map_eq_zero_iff
  have h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0 :=
    proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl
  rw [h2, h3] at h1
  exact h1

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_rows_classZero_eq_invariant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  first | exact @GlobalTheory.ZH.span_rows_class_zero | exact GlobalTheory.ZH.span_rows_class_zero | (intros; apply GlobalTheory.ZH.span_rows_class_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatLog
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
end
