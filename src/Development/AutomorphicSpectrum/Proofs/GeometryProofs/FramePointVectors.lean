module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem epsMul_eq {R : Type} [CommRing R] (a : R) :
    GlobalTheory.CompanionTheory.Ar.epsMul a = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a := by
  ext x <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul]

theorem isTanAt_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} (v : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt Xo.univ.t.G x v ↔ Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨fun h => ⟨Over.w v, h⟩, fun h => h.2⟩

theorem isEigVec_iff {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X} (τ : E →+* ℂ)
    (v : epsAt x ⟶ Xo.univ.t.G) :
    IsEigVec Xo.univ.t.act x ((algebraMap c.F R).comp (tauIn c τ)) v ↔
      Formalism.L2.Pj.IsTanAt x v.left ∧ Formalism.L2.Pj.IsEigAt c τ v.left := by
  refine and_congr (isTanAt_iff v) (forall_congr' fun a => ?_)
  rw [epsMul_eq]
  exact Iff.rfl

theorem isComb_iff {R : Type} [CommRing R] {x : Sp R ⟶ Xo.X} {n : ℕ} (a : Fin n → R)
    (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)) (w : epsAt x ⟶ Xo.univ.t.G) :
    IsComb a v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) a w.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], rfl⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, fun i => by rw [hu i, epsMul_eq], Over.OverMorphism.ext hw.symm⟩

theorem exists_frame {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) {F : Type} [Field F]
    (ψ : S →+* F) (x : Sp F ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F F := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] F := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S F ψa z τ w.left h1 h2
  exact ⟨a, (isComb_iff a v w).2 ha, fun b hb => hu b ((isComb_iff b v w).1 hb)⟩

end GlobalTheory.CompanionTheory.Ar.FrameEig


open GlobalTheory.CompanionTheory.Ar.FrameEig in
theorem GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  intro E _ _ _ H D l Xo c τ S _ _ z F _ ψ y hp hq hx hs
  obtain ⟨v, hv, fv⟩ := exists_frame z ψ (under y) hx τ D.p hp
  obtain ⟨w, hw, fw⟩ := exists_frame z ψ (under y) hx (ComplexEmbedding.conjugate τ) D.q hq
  exact ⟨v, w, hv, hw, fun U hU => ⟨hs, hU, fv, fw⟩⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectorsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S)) → ∃ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) ∧ (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) ∧ ∀ U : Set (Xo.XF c), Set.range y ⊆ U → IsFramed U τ (ψ.comp (algebraMap c.F S)) y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | exact GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem exists_cover_basicOpen {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (V : Fin n → Z.affineOpens) (hV : ∀ y : Z, ∃ j, y ∈ (V j : Z.Opens)) :
    ∃ (m : ℕ) (u c : Fin m → Γ(Z, W)), ∑ l, c l * u l = 1 ∧
      ∀ l, ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen (u l) = Z.basicOpen v := by
  classical
  let s : Set Γ(Z, W) :=
    {f | ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen f = Z.basicOpen v}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hV x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW (V j).2 x ⟨hx, hj⟩
    exact Opens.mem_iSup.2 ⟨⟨f, j, g, e⟩, hxf⟩
  have h1 : (1 : Γ(Z, W)) ∈ Ideal.span s := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : Γ(Z, W)), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x * (x : Γ(Z, W))

theorem smooth_secAlgebra {Z : Scheme.{0}} (g : Z ⟶ Sp ℚ) (e : ℕ)
    (hsm : SmoothOfRelativeDimension e g) {D : Z.Opens} (hD : IsAffineOpen D) :
    @Algebra.Smooth ℚ _ Γ(Z, D) _ (secAlgebra g D) := by
  have h0 : Smooth g := hsm.smooth
  have h1 := Smooth.smooth_appLE (f := g) (isAffineOpen_top _) hD (fun _ _ => trivial)
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv h1

theorem coords_of_formallyEtale {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] [Algebra.FormallyEtale R S] {e : ℕ} (z : Fin e → R)
    (h1 : LinearIndependent R fun i => KaehlerDifferential.D ℚ R (z i))
    (h2 : Submodule.span R (Set.range fun i => KaehlerDifferential.D ℚ R (z i)) = ⊤) :
    LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = ⊤ := by
  let b := Module.Basis.mk h1 h2.ge
  let b' := (b.baseChange S).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ R S)
  have hb : (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = b' := by
    funext i
    simp [b', b, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  rw [hb]
  exact ⟨b'.linearIndependent, b'.span_eq⟩

theorem exists_point_of_prime {Z : Scheme.{0}} {D : Z.Opens} (hD : IsAffineOpen D)
    (q : Ideal Γ(Z, D)) (hq : q.IsPrime) :
    ∃ t ∈ D, ∀ s : Γ(Z, D), s ∈ q ↔ t ∉ Z.basicOpen s := by
  refine ⟨hD.fromSpec ⟨q, hq⟩, hD.fromSpec_preimage_self.ge trivial, fun s => ?_⟩
  have h := hD.fromSpec_preimage_basicOpen s
  have h2 : (hD.fromSpec ⟨q, hq⟩ ∈ Z.basicOpen s) ↔ (⟨q, hq⟩ : PrimeSpectrum Γ(Z, D)) ∈ PrimeSpectrum.basicOpen s := by
    rw [← h]
    rfl
  rw [h2]
  simp

theorem range_valMap_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0) (D : Z.Opens)
    (hDu : D = Z.basicOpen u) :
    ∃ hD : ⊤ ≤ ζ ⁻¹ᵁ D, Set.range (valMap ζ D hD).hom =
      (Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω)) : Subalgebra ℚ Ω) := by
  subst hDu
  have hD : ⊤ ≤ ζ ⁻¹ᵁ Z.basicOpen u := (le_preimage_basicOpen_iff ζ h u).2 (isUnit_iff_ne_zero.2 hu)
  have hle : Z.basicOpen u ≤ W := Z.basicOpen_le u
  have hres : ∀ w : Γ(Z, W), (valMap ζ _ hD).hom ((Z.presheaf.map (homOfLE hle).op).hom w) = valR ζ W w :=
    fun w => by rw [← valR_eq _ _ hD, valR_res ζ hle hD]
  refine ⟨hD, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    have := hW.isLocalization_basicOpen u
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj u x
    have h1 := congrArg (valMap ζ _ hD).hom ha
    rw [map_mul, map_pow] at h1
    have h2 : ∀ t : Γ(Z, W), (valMap ζ _ hD).hom (algebraMap Γ(Z, W) Γ(Z, Z.basicOpen u) t) = valR ζ W t :=
      hres
    rw [h2, h2] at h1
    have h3 : (valMap ζ _ hD).hom x = valR ζ W a * ((valR ζ W u)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ (A : Set Ω) := fun w => by
      rw [← hA, valR_eq _ _ h]; exact ⟨w, rfl⟩
    rw [h3]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hv a)))
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
  · intro x hx
    have hAr : ∀ a ∈ A, a ∈ Set.range (valMap ζ _ hD).hom := fun a ha => by
      have : a ∈ Set.range (valMap ζ W h).hom := by rw [hA]; exact ha
      obtain ⟨w, rfl⟩ := this
      exact ⟨_, (hres w).trans (valR_eq _ _ h _)⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · have hunit : IsUnit ((Z.presheaf.map (homOfLE hle).op).hom u) :=
          RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace u
        obtain ⟨b, hb⟩ := hunit.exists_right_inv
        refine ⟨b, (inv_eq_of_mul_eq_one_right ?_).symm⟩
        rw [← hres u, ← map_mul, hb, map_one]
      · exact hAr x hx
    | algebraMap r => exact hAr _ (Subalgebra.algebraMap_mem _ r)
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

theorem snc_on_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W)
    (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0)
    {V : Z.Opens} (hV : IsAffineOpen V) (v : Γ(Z, V)) (huv : Z.basicOpen u = Z.basicOpen v)
    (z : Fin e → Γ(Z, V)) (k : ℕ) (hk : k ≤ e) (hz : IsCoords g V z)
    (hT : (V : Set Z) ∩ T = {y | y ∈ V ∧ ∃ i : Fin e, (i : ℕ) < k ∧ y ∉ Z.basicOpen (z i)})
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω))) :
    Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
      LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
      ∀ q : Ideal S, q.IsPrime →
        ((∀ s : S, (s : Ω) = valR ζ W σ → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  obtain ⟨hD, hr⟩ := range_valMap_basicOpen ζ hW h A hA u hu (Z.basicOpen v) huv.symm
  rw [← hS] at hr
  have hDaff : IsAffineOpen (Z.basicOpen v) := hV.basicOpen v
  have hDW : Z.basicOpen v ≤ W := huv ▸ Z.basicOpen_le u
  have hDV : Z.basicOpen v ≤ V := Z.basicOpen_le v
  letI iV := secAlgebra g V
  letI iD := secAlgebra g (Z.basicOpen v)
  let ψ := (valMap ζ (Z.basicOpen v) hD).hom
  have hψ : ∀ x, ψ x ∈ S := fun x => by
    have : ψ x ∈ Set.range ψ := ⟨x, rfl⟩
    rw [show Set.range ψ = (S : Set Ω) from hr] at this
    exact this
  let φ : Γ(Z, Z.basicOpen v) ≃+* S := RingEquiv.ofBijective (ψ.codRestrict S hψ) (by
    refine ⟨fun a b hab => valMap_injective ζ hD (congrArg Subtype.val hab), fun s => ?_⟩
    have hs : (s : Ω) ∈ Set.range ψ := by
      rw [show Set.range ψ = (S : Set Ω) from hr]
      exact s.2
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, Subtype.ext hx⟩)
  have hφ : ∀ x, (φ x : Ω) = ψ x := fun _ => rfl
  haveI hs0 : Algebra.Smooth ℚ Γ(Z, Z.basicOpen v) := smooth_secAlgebra g e hsm hDaff
  have hsmooth : Algebra.Smooth ℚ S := Algebra.Smooth.of_equiv φ.toRatAlgEquiv
  refine ⟨hsmooth, ?_⟩

  haveI := hV.isLocalization_basicOpen v
  haveI : Algebra.FormallyEtale Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers v)
  haveI : IsScalarTower ℚ Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨c1, c2⟩ := coords_of_formallyEtale (R := Γ(Z, V)) (S := Γ(Z, Z.basicOpen v)) z hz.1 hz.2

  letI iS : Algebra Γ(Z, Z.basicOpen v) S := φ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale Γ(Z, Z.basicOpen v) S :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  haveI : IsScalarTower ℚ Γ(Z, Z.basicOpen v) S :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨d1, d2⟩ := coords_of_formallyEtale (R := Γ(Z, Z.basicOpen v)) (S := S) _ c1 c2
  refine ⟨_, k, hk, d1, d2, fun q hq => ?_⟩
  have hq' : (q.comap φ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨t, htD, ht⟩ := exists_point_of_prime hDaff _ hq'
  have hmem : ∀ x, φ x ∈ q ↔ t ∉ Z.basicOpen x := ht
  have htV : t ∈ V := hDV htD
  have htW : t ∈ W := hDW htD
  have hzt : ∀ i, algebraMap Γ(Z, Z.basicOpen v) S (algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i)) ∈ q ↔
      t ∉ Z.basicOpen (z i) := fun i => by
    refine (hmem _).trans (not_congr ?_)
    have := Z.basicOpen_res (z i) (homOfLE hDV).op
    rw [show algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i) =
      (Z.presheaf.map (homOfLE hDV).op).hom (z i) from rfl, this]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  let sσ : Γ(Z, Z.basicOpen v) := (Z.presheaf.map (homOfLE hDW).op).hom σ
  have hsσ : (φ sσ : Ω) = valR ζ W σ := by
    rw [hφ, ← valR_res ζ hDW hD σ, valR_eq _ _ hD]
  have hσt : φ sσ ∈ q ↔ t ∈ T := by
    refine (hmem _).trans ?_
    rw [hσ t htW, not_iff_not, Z.basicOpen_res σ (homOfLE hDW).op]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  have hTt : t ∈ T ↔ ∃ i : Fin e, (i : ℕ) < k ∧ t ∉ Z.basicOpen (z i) := by
    have h1 : t ∈ (V : Set Z) ∩ T ↔ t ∈ T := ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
    rw [← h1, hT]
    exact ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
  constructor
  · intro H
    obtain ⟨i, hi, hit⟩ := hTt.1 (hσt.1 (H _ hsσ))
    exact ⟨i, hi, (hzt i).2 hit⟩
  · rintro ⟨i, hi, hit⟩ s hs
    have : s = φ sσ := Subtype.ext (hs.trans hsσ.symm)
    rw [this]
    exact hσt.2 (hTt.2 ⟨i, hi, (hzt i).1 hit⟩)

theorem sncChart_of_coords (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens)
    (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) := by
  obtain ⟨n, V, hcov, hV⟩ := hc
  obtain ⟨m, u, c, hsum, hl⟩ := exists_cover_basicOpen hW V hcov
  have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ A := fun w => by
    have : valR ζ W w ∈ Set.range (valMap ζ W h).hom := by
      rw [valR_eq _ _ h]
      exact ⟨w, rfl⟩
    rw [hA] at this
    exact this
  refine ⟨m, fun l => valR ζ W (u l), fun l => valR ζ W (c l), fun l => hv _, fun l => hv _, ?_,
    fun l hf S hS => ?_⟩
  · simp only [valR_eq _ _ h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum, hsum, map_one]
  · obtain ⟨j, v, huv⟩ := hl l
    obtain ⟨z, k, hk, hz, hT⟩ := hV j
    exact snc_on_basicOpen ζ g e T hsm hW h A hA σ hσ (u l) hf (V j).2 v huv z k hk hz hT S hS

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoordsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_of_smooth_coords : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z) (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ), SncChart A e (valR ζ W σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | exact GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange

theorem eigFrame_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  intro S R _ _ G _ _ x O _ act σ n r u V hu hV
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x E M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S R G x E M
  have hfr := (hf O act ρ σ hρ).2
  choose u' hu' using fun i => M.onto (u i) (hu.1 i).1
  choose V' hV' using fun i => M.onto (V i) (hV.1 i).1
  obtain rfl : (fun k => M.pt (u' k)) = u := funext hu'
  obtain rfl : (fun k => M.pt (V' k)) = V := funext hV'
  obtain ⟨lu, su⟩ := (hfr n u').1 hu
  obtain ⟨lV, sV⟩ := (hfr r V').1 hV
  let bu : Module.Basis (Fin n) R (eigSp ρ σ) := (Module.Basis.span lu).map (LinearEquiv.ofEq _ _ su)
  let bV : Module.Basis (Fin r) R (eigSp ρ σ) := (Module.Basis.span lV).map (LinearEquiv.ofEq _ _ sV)
  have bu_eq : ∀ i, (bu i : E) = u' i := fun i => by
    simp [bu, Module.Basis.span_apply]
  have bV_eq : ∀ i, (bV i : E) = V' i := fun i => by
    simp [bV, Module.Basis.span_apply]
  have hrn : r = n := by simpa using Fintype.card_congr (bV.indexEquiv bu)
  refine ⟨hrn, (bu.toMatrix bV).transpose, fun i => ?_, (bV.toMatrix bu).transpose, ?_, ?_⟩
  · refine (hc n _ u' _).2 ?_
    have h : V' i = ∑ k, (bu.toMatrix bV).transpose i k • u' k := by
      have h := congrArg Subtype.val (bu.sum_repr (bV i))
      rw [bV_eq] at h
      rw [← h]
      clear h hc hf hfr hu hV hu' hV' hρ
      simp only [Submodule.coe_sum, Submodule.coe_smul, bu_eq, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    exact congrArg M.pt h
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

end GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frames_invertible_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | exact GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

theorem closedPoint_germ_const {X : Scheme.{0}} {F : Type} [Field F] {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = φ o := by
  letI : Algebra O F := φ.toAlgebra
  have h := GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const z s hz ⟨genPt z, specializes_rfl⟩ o
  have e : genMap z ⟨genPt z, specializes_rfl⟩ = (Scheme.stalkClosedPointTo z).hom := by
    ext t
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    exact congrArg (fun q : X.presheaf.stalk (genPt z) ⟶ CommRingCat.of F => q.hom t)
      (Category.id_comp (Scheme.stalkClosedPointTo z))
  rw [e] at h
  exact h

theorem val_const {X : Scheme.{0}} {Ω : Type} [Field Ω] {F : Type} [Field F] {O : Type} [CommRing O]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (all : ∀ q : X, genPt ξ ⤳ q)
    (s : X ⟶ Spec (CommRingCat.of O)) (ψ : O →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom ψ))
    (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) : ValAt ξ z (ψ o) (φ o) := by
  letI : Algebra O Ω := ψ.toAlgebra
  exact ⟨all _, _, GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, all _⟩ o, closedPoint_germ_const s z φ hz o⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB OverVal

theorem isOver_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {z : Sp ℂ ⟶ 𝔐.X} {κ : c.F →+* ℂ}
    {p : Sp ℂ ⟶ Xo.X} (h : IsOver 𝔐 z κ p) :
    z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  obtain ⟨x, hx, -, hk⟩ := h
  have h1 : z ≫ 𝔐.f ≫ Y.s = x ≫ Y.j ≫ Y.s := by
    rw [← Category.assoc, ← hx, Category.assoc]
  rw [h1, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hk]
  exact (Spec.map_comp _ _).symm

theorem val_cst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p h x
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hc : ∀ o : 𝓞 c.F, ValAt 𝔐.ξ z (𝔐.cst (algebraMap (𝓞 c.F) c.F o)) (κ (algebraMap (𝓞 c.F) c.F o)) := fun o =>
    val_const 𝔐.ξ 𝔐.all (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over z
      (κ.comp (algebraMap (𝓞 c.F) c.F)) (isOver_base h) o
  obtain ⟨a, n, hn, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
  have hn0 : algebraMap (𝓞 c.F) c.F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)).2 (nonZeroDivisors.ne_zero hn)
  have hk0 : κ (algebraMap (𝓞 c.F) c.F n) ≠ 0 := (map_ne_zero κ).2 hn0
  rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  exact val_mul (hc a) (by simpa only [map_inv₀] using val_inv₀ hk0 (hc n))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_value_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem valR_mem_adjoin_of_affine {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} (ξ : Sp Ω ⟶ X)
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) {O : X.Opens} (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (t : Γ(X, O)) :
    valR ξ O t ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ IntermediateField.adjoin ℚ (A : Set Ω) := fun a => by
    apply IntermediateField.subset_adjoin
    rw [valR_eq ξ W₀ h₀, ← hA]
    exact ⟨a, rfl⟩
  let z : Sp Ω := IsLocalRing.closedPoint Ω
  obtain ⟨b, hbO, hxb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨ξ z, hO trivial⟩ (h₀ trivial)
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := fun y _ => by
    rw [Subsingleton.elim y z]
    exact hxb
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers b)
    ((X.presheaf.map (homOfLE hbO).op).hom t)
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  have hv := congrArg (valR ξ (X.basicOpen b)) h
  simp only at hv
  rw [valR_mul ξ _ hD, valR_res ξ hbO hD, hres, hres, valR_pow ξ _ h₀] at hv
  have hunit : valR ξ W₀ b ≠ 0 := ((le_preimage_basicOpen_iff ξ h₀ b).1 hD).ne_zero
  have e : valR ξ O t = valR ξ W₀ a / valR ξ W₀ b ^ n := by
    rw [eq_div_iff (pow_ne_zero n hunit)]
    exact hv
  rw [e]
  exact div_mem (hmem a) (pow_mem (hmem b) n)

theorem valR_appIso_inv {C : Type} [CommRing C] {X Y : Scheme.{0}} (r : Y ⟶ X) [IsOpenImmersion r] (y : Sp C ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) (t : Γ(Y, V)) :
    valR (y ≫ r) (r ''ᵁ V) ((r.appIso V).inv.hom t) = valR y V t := by
  rw [← valR_appLE y r (r.preimage_image_eq V).ge h, ← Scheme.Hom.appIso_hom']
  congr 1
  exact congrArg (fun φ => φ.hom t) (r.appIso V).inv_hom_id

theorem valR_mem_adjoin_of_modification : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  intro Ω _ _ X X' ξ _ _ f U _ ζ hζ hU W₀ hW₀ h₀ A hA W' h' s
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  have hV : ⊤ ≤ y ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W') := fun z hz => by
    have : z ∈ ζ ⁻¹ᵁ W' := h' hz
    rw [← hy] at this
    exact this
  have e1 : valR ζ W' s = valR y _ (((f ⁻¹ᵁ U).ι.app W').hom s) := by
    conv_lhs => rw [← hy]
    exact valR_comp y _ W' s
  rw [e1, ← valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y _ hV]
  subst hyr
  exact valR_mem_adjoin_of_affine _ hW₀ h₀ A hA (fun z hz => ((( (f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq _).ge (hV hz) : _)) _

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedFieldStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_values_in_adjoined_field : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | exact GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindex
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindex
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

theorem aeval_mul_homog {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {A : Type} [CommRing A] [Algebra ℤ A]
    (g : MRing J₀) (a : K₀ → ℕ) (hg : IsMultiHomog g a) (u : (Σ k, J₀ k) → A) (t : K₀ → A) :
    aeval (fun p => u p * t p.1) g = aeval u g * ∏ k, t k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, J₀ k), t i.1 ^ d i) = ∏ k, t k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, t k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem aeval_comp_ringHom {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (u : σ → A)
    (g : MvPolynomial σ ℤ) : aeval (fun p => φ (u p)) g = φ (aeval u g) := by
  induction g using MvPolynomial.induction_on with
  | C m => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X]

theorem pow_mul_pow_sub_eq {F : Type} [Field F] (x b : F) (hb : b ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    x ^ j * b ^ (n - j) = (x / b) ^ j * b ^ n := by
  have h : b ^ n = b ^ j * b ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [h, div_pow]
  field_simp

theorem ratio_relation_at_complex_points :
    ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)]
      [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
      (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀)
      (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 →
      (∀ j, IsMultiHomog (c j) a) →
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) →
      ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ,
        SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w →
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  intro K₀ K _ _ J₀ J _ _ Ω₀ Ω _ _ y₀ y bk bx i q r n c a hy hqr hr hc hrel z hz hzr w hw
  have hcone : ∀ g : MRing J₀, IsMultiHomog g a →
      mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        MvPolynomial.C (i (aeval y₀ g)) * ∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k := by
    intro g hg
    have h1 : mConeMap y (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) g) =
        aeval (fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1)) g := by
      simp only [mConeMap]
      rw [aeval_rename]
      have e : ((fun p : (Σ k, J k) => (MvPolynomial.C (y p) : MvPolynomial K Ω) * MvPolynomial.X p.1) ∘
          GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) =
          fun p : (Σ k, J₀ k) => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω) * MvPolynomial.X (bk p.1) := by
        funext p
        obtain ⟨k, b⟩ := p
        simp [GlobalTheory.CompanionTheory.Ar.Chg.blkV, hy]
      rw [e]
    rw [h1, aeval_mul_homog g a hg (fun p => (MvPolynomial.C (i (y₀ p)) : MvPolynomial K Ω)) (fun k => MvPolynomial.X (bk k))]
    congr 1
    exact aeval_comp_ringHom ((MvPolynomial.C : Ω →+* MvPolynomial K Ω).comp i) y₀ g
  have hXq : mConeMap y (MvPolynomial.X q) = MvPolynomial.C (y q) * MvPolynomial.X r.1 := by
    simp [mConeMap, hqr]
  have hXr : mConeMap y (MvPolynomial.X r) = MvPolynomial.C (y r) * MvPolynomial.X r.1 := by
    simp [mConeMap]
  let F : MRing J := ∑ j ∈ Finset.range (n + 1),
    rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j) * MvPolynomial.X q ^ j * MvPolynomial.X r ^ (n - j)
  have hF : F ∈ mCoordIdeal y := by
    show mConeMap y F = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, map_mul, map_pow, hcone _ (hc _), hXq, hXr]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        MvPolynomial.C (i (aeval y₀ (c j))) * (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) *
            (MvPolynomial.C (y q) * MvPolynomial.X r.1) ^ j * (MvPolynomial.C (y r) * MvPolynomial.X r.1) ^ (n - j) =
          (∏ k, (MvPolynomial.X (bk k) : MvPolynomial K Ω) ^ a k) * MvPolynomial.X r.1 ^ n *
            MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e1 : y q ^ j * y r ^ (n - j) = (y q / y r) ^ j * y r ^ n := pow_mul_pow_sub_eq _ _ hr hjn
      have e2 : (MvPolynomial.X r.1 : MvPolynomial K Ω) ^ n = MvPolynomial.X r.1 ^ j * MvPolynomial.X r.1 ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (MvPolynomial.C (y q) : MvPolynomial K Ω) ^ j * MvPolynomial.C (y r) ^ (n - j) =
          MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← e1]; simp only [map_mul, map_pow]
      rw [mul_pow, mul_pow, e2]
      have e4 : (MvPolynomial.C (y r ^ n * (i (aeval y₀ (c j)) * (y q / y r) ^ j)) : MvPolynomial K Ω) =
          MvPolynomial.C (i (aeval y₀ (c j))) * MvPolynomial.C ((y q / y r) ^ j * y r ^ n) := by
        rw [← map_mul]; congr 1; ring
      rw [e4, ← e3]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, hrel]
    simp
  obtain ⟨s, hs, he⟩ := hw
  have hev := hz.2 F hF
  have hren : ∀ j, eval z (map (Int.castRingHom ℂ) (rename (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (c j))) =
      (∏ k, s k ^ a k) * eval w (map (Int.castRingHom ℂ) (c j)) := by
    intro j
    rw [map_rename, eval_rename]
    have : z ∘ GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx = fun p => s p.1 * w p := he
    rw [this, eval_smul_homog (c j) a (hc j) s w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [F, map_sum, map_mul, map_pow, map_X, eval_X, hren] at hev
  have hP : (∏ k, s k ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)
  have hfin : (∏ k, s k ^ a k) * z r ^ n *
      ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
    rw [← hev, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [mul_assoc ((∏ k, s k ^ a k) * _), pow_mul_pow_sub_eq _ _ hzr hjn]
    ring
  exact (mul_eq_zero.1 hfin).resolve_left (mul_ne_zero hP (pow_ne_zero _ hzr))

end GlobalTheory.CompanionTheory.Ar.Rel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindexStatement
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homog_relation_ratio_reindex : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (q r : Σ k, J k) (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ), (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → q.1 = r.1 → y r ≠ 0 → (∀ j, IsMultiHomog (c j) a) → (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * (y q / y r) ^ j = 0) → ∀ z ∈ mcPts (mCoordIdeal y), z r ≠ 0 → ∀ w : (Σ k, J₀ k) → ℂ, SameOrbit (fun p => z (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx p)) w → ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * (z q / z r) ^ j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | exact GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points | (intros; apply GlobalTheory.CompanionTheory.Ar.Rel.ratio_relation_at_complex_points <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

private theorem smoothOfRelativeDimension_restrict_of_le {A S : Scheme.{0}} (f : A ⟶ S) {n : ℕ} {V W : A.Opens} (h : V ≤ W)
    (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) : SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp 0 n (A.homOfLE h) (W.ι ≫ f)
  rw [zero_add, ← Category.assoc, Scheme.homOfLE_ι] at this
  exact this

private theorem relDim_eq_of_mem_of_mem {A S : Scheme.{0}} (f : A ⟶ S) {n m : ℕ} {V W : A.Opens}
    (hV : SmoothOfRelativeDimension n (V.ι ≫ f)) (hW : SmoothOfRelativeDimension m (W.ι ≫ f))
    {x : A} (hxV : x ∈ V) (hxW : x ∈ W) : n = m :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ (smoothOfRelativeDimension_restrict_of_le f inf_le_left hV) (smoothOfRelativeDimension_restrict_of_le f inf_le_right hW)
    ⟨x, hxV, hxW⟩

theorem reldim_eq_of_two_pullbacks {P A S : Scheme.{0}} {f : A ⟶ S} {b : A ⟶ S} {p : P ⟶ A} {a₁ a₂ : P ⟶ A}
    (h₁ : IsPullback a₁ p f b) (h₂ : IsPullback a₂ p f b) {n₁ n₂ : ℕ} {W₁ W₂ : A.Opens}
    (d₁ : SmoothOfRelativeDimension n₁ (W₁.ι ≫ f)) (d₂ : SmoothOfRelativeDimension n₂ (W₂.ι ≫ f))
    (z : P) (hz₁ : a₁ z ∈ W₁) (hz₂ : a₂ z ∈ W₂) : n₁ = n₂ := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₁
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₂
  have e₁ : SmoothOfRelativeDimension n₁ ((a₁ ⁻¹ᵁ W₁).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₁)
      ((isPullback_morphismRestrict a₁ W₁).paste_vert h₁) d₁
  have e₂ : SmoothOfRelativeDimension n₂ ((a₂ ⁻¹ᵁ W₂).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₂)
      ((isPullback_morphismRestrict a₂ W₂).paste_vert h₂) d₂
  exact relDim_eq_of_mem_of_mem p e₁ e₂ hz₁ hz₂

theorem isPullback_fst_snd {X : Scheme.{0}} (G : Over X) :
    IsPullback (fst G G) (snd G G) (toUnit G) (toUnit G) := by
  exact IsPullback.of_is_product (tensorProductIsBinaryProduct G G) isTerminalTensorUnit

theorem isPullback_mul_snd {X : Scheme.{0}} (G : Over X) [GrpObj G] :
    IsPullback (fst G G * snd G G) (snd G G) (toUnit G) (toUnit G) := by
  refine IsPullback.of_is_product (c := BinaryFan.mk (fst G G * snd G G) (snd G G)) ?_ isTerminalTensorUnit
  refine BinaryFan.IsLimit.mk _ (fun u v => lift (u * v⁻¹) v) ?_ ?_ ?_
  · intro T u v
    simp [comp_mul]
  · intro T u v
    simp
  · intro T u v m h₁ h₂
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h₁ h₂
    have h₃ : m ≫ fst G G * v = u := by
      rw [← h₂]
      exact (comp_mul m (fst G G) (snd G G)).symm.trans h₁
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa using eq_mul_inv_of_mul_eq h₃
    · simpa using h₂

theorem toUnit_left {X : Scheme.{0}} (G : Over X) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem reldim_eq_unit {X : Scheme.{0}} (G : Over X) [GrpObj G] {n m : ℕ} {W V : G.left.Opens}
    (dW : SmoothOfRelativeDimension n (W.ι ≫ G.hom)) (dV : SmoothOfRelativeDimension m (V.ι ≫ G.hom))
    (g : G.left) (hg : g ∈ W) (hV : eSec G (G.hom g) ∈ V) : n = m := by
  have h₁ := (isPullback_fst_snd G).map (Over.forget X)
  have h₂ := (isPullback_mul_snd G).map (Over.forget X)
  simp only [Over.forget_map, toUnit_left] at h₁ h₂
  have p₁ : (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    simp
  have p₂ : (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = (η[G]).left (G.hom g) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mul, lift_fst, lift_snd, mul_inv_cancel,
      Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, toUnit_left]
  refine reldim_eq_of_two_pullbacks h₁ h₂ dW dV ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ?_ ?_
  · show (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ W
    rw [p₁]
    exact hg
  · show (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ V
    rw [p₂]
    unfold eSec at hV
    exact hV

private theorem smoothOfRelativeDimension_of_local {A S : Scheme.{0}} (f : A ⟶ S) (n : ℕ)
    (h : ∀ x : A, ∃ W : A.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (smoothOfRelativeDimension_iff n (W.ι ≫ f)).1 hW ⟨x, hxW⟩
  have e₁ : W.ι ''ᵁ V ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have e₂ : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := fun v hv => ⟨v, hv, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE W.ι f U (W.ι ''ᵁ V) V e₁ e₂
  have hiso : W.ι.appLE (W.ι ''ᵁ V) V e₂ = (W.ι.appIso V).hom := (Scheme.Hom.appIso_hom' W.ι V).symm
  have key : f.appLE U (W.ι ''ᵁ V) e₁ = (W.ι ≫ f).appLE U V e ≫ (W.ι.appIso V).inv := by
    rw [← hcomp, hiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨U, hU, W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxV, rfl⟩, e₁, ?_⟩
  rw [key, CommRingCat.hom_comp]
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (W.ι.appIso V).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (W.ι.appIso V).symm.commRingCatIsoToRingEquiv
  have h1 := h0.comp hstd
  rwa [zero_add] at h1

theorem smoothGrp_relDim : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X Ω _ ξ G _ _ hgen
  obtain ⟨n₀, W₀, hW₀, d₀⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (genPt ξ))
  refine ⟨n₀, smoothOfRelativeDimension_of_local G.hom n₀ fun g => ?_⟩
  obtain ⟨n, W, hgW, dW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom g
  obtain ⟨m, V, hV, dV⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (G.hom g))
  have h₁ : n = m := reldim_eq_unit G dW dV g hgW hV
  have hsp : eSec G (genPt ξ) ⤳ eSec G (G.hom g) := (hgen (G.hom g)).map (eSec G).base.hom.continuous
  have h₂ : m = n₀ := relDim_eq_of_mem_of_mem G.hom dV d₀ (hsp.mem_open V.isOpen hV) hW₀
  rw [h₁, h₂] at dW
  exact ⟨W, hgW, dW⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_group_rel_dim_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim <;> assumption)
end
end
