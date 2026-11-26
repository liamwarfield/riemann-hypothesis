module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.Mum.TensTor

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def GtRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
    (v'.s χ' : F) * wv (N'.c χ') * wv v'.b =
      ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F) *
        wv (N'.c χ' * v'.b) * wv 1

def QRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) {k : ℕ}
    (q' : N'.QT k) (qs : Fin r → N.QT k) : Prop :=
  (∀ i, e q'.1.1.toAdd i = (qs i).1.1.toAdd) ∧ GtRelV W φ e wv q'.1.2 (fun j => (qs j).1.2)

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def cmp (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (j : Fin r) : N.A :=
  ν.eA.symm (ν'.eA x ≫ T.pr j)

def chi (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ : N'.X) (i : Fin r) : N.X :=
  ν.eX.symm (T.xe (ν'.eX χ) i)

def wv (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : F :=
  valF (ν'.eA x).left _
    (T.w.s (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k), ν'.J (ν'.eA x).left)).val

def GtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  GtRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') v' vs

def PtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') {k : ℕ} (p' : QkPt D' F k)
    (ps : Fin r → QkPt D F k) : Prop :=
  ∃ (q' : N'.QT k) (qs : Fin r → N.QT k), ν'.QPt p' q' ∧ (∀ i, ν.QPt (ps i) (qs i)) ∧
    QRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') q' qs

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

section Facts

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def TensFacts (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) :
    Prop :=
  (∀ x y j, φ (x * y) j = φ x j * φ y j) ∧ Function.Bijective φ ∧
  (∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) ∧ Function.Bijective e ∧
  (∀ χ' j, φ (N'.c χ') j = N.c (e χ' j)) ∧ (∀ x, wv x ≠ 0) ∧
  (∀ x y u, (N'.θ x y u : F) * wv (x * y * u) * wv x * wv y * wv u =
    ((∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j : Fˣ) : F) *
      wv (x * y) * wv (x * u) * wv (y * u) * wv 1) ∧
  ∀ χ', (N'.ψ χ' : F) * wv 1 = wv (N'.c χ') * ((∏ i, ∏ j, N.τ (e χ' i) (e χ' j) ^ W i j : Fˣ) : F)

end Facts

end GlobalTheory.Mum.TensTor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleHermPos

open Complex Matrix
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues AnalyticHom

variable {g : ℕ}

lemma form_smul (c : ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ ((c : ℂ) • Hm).mulVec (star w) = c * (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma isHermitian_smul {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (c : ℝ) :
    ((c : ℂ) • Hm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

lemma theta_add_smul_eq (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    {v : Fin g → ℂ} (hv : Hm.mulVec (star v) = 0) (z : Fin g → ℂ) (t : ℂ) :
    θ (z + t • v) = θ z := by
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
  have hq : ∀ t : ℂ, ((z + t • v) ⬝ᵥ Hm.mulVec (star (z + t • v))) = z ⬝ᵥ Hm.mulVec (star z) := by
    intro t
    have h1 : Hm.mulVec (star (t • v)) = 0 := by rw [star_smul, mulVec_smul, hv, smul_zero]
    have h2 : v ⬝ᵥ Hm.mulVec (star z) = 0 := by
      rw [ThetaPositivity.form_conj hH z v, hv, dotProduct_zero, star_zero]
    rw [star_add, mulVec_add, h1, add_zero, add_dotProduct, smul_dotProduct, h2, smul_zero, add_zero]
  have hd : Differentiable ℂ fun t : ℂ => θ (z + t • v) :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const v))
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => θ (z + t • v)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have := hC (z + t • v)
    rwa [hq t] at this
  have := hd.apply_eq_apply_of_bounded hb t 0
  simpa using this

lemma eq_zero_of_smul_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] {v : Fin g → ℂ}
    (h : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • v, h t⟩ : Λ) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

theorem re_form_pos_of_relAmple :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    Out.RelAmple A L → ∀ (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
      (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
        u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro A _ _ hA L hL ha g u Hm χ hH hχ hfr
  haveI : Smooth A.hom := hA.smooth
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  obtain ⟨N, hN, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  choose hDa r hr hsurj using hD
  have hrg : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrg⟩
  choose s' hs' using fun i => exists_sec_pow L _ σ hσ N A.hom (s i)
  choose θ hθd hθfn _hθu hθper using fun i => ThetaBundleSec.exists_fn u hL N (s' i)
  choose ch hch using fun z => PullHermitian.exists_chart (u.ex z).left hL
  have hU : ∀ z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A L ⊤ N).U (fun _ => ch z) := fun z =>
    le_preimage_mono (u.ex z).left (chart_le L _ σ hσ N fun _ => ch z)
      ((le_preimage_lbPow _ L N fun _ => ch z).2 (hch z))
  have hval : ∀ i z, valAt' ((u.ex z).left ≫ σ) ((Out.powOver A L ⊤ N).U fun _ => ch z)
      ((s i).f fun _ => ch z) = θ i z * u.fr (ch z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L N fun _ => ch z).2 (hch z)
    (hs' i _ _ k).symm.trans (hθfn i _ z k)
  have hfr0 : ∀ z, u.fr (ch z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u.fr_ne _ _ (hch z))
  have hmem : ∀ i z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr0 z)]
  have hcov' : ∀ z, ∃ i, θ i z ≠ 0 := fun z => by
    have hz : ((u.ex z).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
      rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, (hmem i z).1 ((top_le_preimage_iff_mem _ _).2 hi)⟩

  set HN : Matrix (Fin g) (Fin g) ℂ := ((N : ℝ) : ℂ) • Hm with hHNdef
  have hHN : HN.IsHermitian := isHermitian_smul hH _
  have htr : ∀ i (l : u.Λ) z, θ i (z + l) =
      (χ l ^ N * cexp (Real.pi * (z ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))))) * θ i z := by
    intro i l z
    have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    rw [hθper i z (z + l) _ hper fun j hj => hfr l j z hj, form_smul, form_smul, mul_pow,
      ← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hχN : ∀ l, ‖χ l ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]

  obtain ⟨i0, hi0⟩ := hcov' 0
  have hne : θ i0 ≠ 0 := fun h => hi0 (by rw [h]; rfl)
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le u.Λ hHN (fun l => χ l ^ N) hχN
    (hθd i0).continuous (htr i0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w => by
    by_contra hw
    push_neg at hw
    have hw' : (w ⬝ᵥ HN.mulVec (star w)).re < 0 := by
      rw [form_smul, re_ofReal_mul]
      exact mul_neg_of_pos_of_neg hNpos hw
    exact hne (ThetaPositivity.eq_zero_of_neg hHN (hθd i0) hC hw')

  have hrval : ∀ i j w, θ i w ≠ 0 →
      valAt' ((u.ex w).left ≫ σ) (Out.nonzeroLocus (s i)) (r i j) * θ i w = θ j w := by
    intro i j w hw
    have hw' := (hmem i w).2 hw
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU w⟩
    have k₁ := congrArg (valAt' ((u.ex w).left ≫ σ) _) (hr i j fun _ => ch w)
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval,
      ← _root_.mul_assoc] at k₁
    exact (mul_right_cancel₀ (hfr0 w) k₁).symm
  have hc : ∀ w w', ((u.ex w).left ≫ σ) ≫ (A.hom ∣_ ⊤) = ((u.ex w').left ≫ σ) ≫ (A.hom ∣_ ⊤) := by
    intro w w'
    rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]

  have hker : ∀ v : Fin g → ℂ, Hm.mulVec (star v) = 0 → v = 0 := by
    intro v hv
    have hvN : HN.mulVec (star v) = 0 := by rw [hHNdef, Matrix.smul_mulVec, hv, smul_zero]
    have hinv : ∀ i (t : ℂ), θ i (t • v) = θ i 0 := fun i t => by
      simpa using theta_add_smul_eq u.Λ hHN _ hχN (hθd i) (htr i) hvN 0 t
    have hpt : ∀ t : ℂ, (u.ex (t • v)).left ≫ σ = (u.ex 0).left ≫ σ := by
      intro t
      obtain ⟨i, h0⟩ := hcov' 0
      have h0' : θ i (t • v) ≠ 0 := by rw [hinv]; exact h0
      have m0 := (hmem i 0).2 h0
      have mt := (hmem i _).2 h0'
      refine UnifTangent.eq_of_values (hDa i) mt m0 fun f => ?_
      obtain ⟨Q, rfl⟩ := hsurj i f
      induction Q using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a mt).trans
          ((congrArg (fun y => valAt' y ⊤ a) (hc _ 0)).trans (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a m0).symm)
      | add Q Q' h h' => rw [map_add (f := _), val_add _ mt, val_add _ m0, h, h']
      | mul_X Q j h =>
        rw [map_mul, val_mul _ mt, val_mul _ m0, h, MvPolynomial.eval₂Hom_X']
        congr 1
        have a1 := hrval i j _ h0'
        have a2 := hrval i j 0 h0
        rw [hinv, hinv] at a1
        exact mul_right_cancel₀ h0 (a1.trans a2.symm)
    refine eq_zero_of_smul_mem u.Λ fun t => (u.ker _).1 ?_
    have e : u.ex (t • v) = u.ex 0 := by
      ext1
      have := hpt t =≫ (A.hom ⁻¹ᵁ ⊤).ι
      rwa [Category.assoc, Category.assoc, hσ, Category.comp_id, Category.comp_id] at this
    have e0 : u.ex 0 = 1 := by
      have h00 := u.ex_add 0 0
      rw [add_zero] at h00
      exact (mul_eq_left.mp h00.symm)
    rw [e, e0]

  intro z hz
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (ThetaPositivity.form_conj hH w w)
    simp only [star_def, conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => hz (hker z ?_)
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  refine (hpsd.dotProduct_mulVec_zero_iff).mp ?_
  rw [star_star]
  exact Complex.ext h0.symm (him z)

end GlobalTheory.AmpleHermPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.VertProj

theorem isProjOver_strHom_zmod : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  intro k _ X p D hX Z i _ l _ _
  have : Module.Finite ℤ k := hX.finite
  have hfin : (Int.castRingHom k).Finite := (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact hfin
  have e : i ≫ p ≫ spMap (Int.castRingHom k) =
      strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by
    rw [← e]; infer_instance
  have hpr : IsProper (strHom (ZMod l) (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
  have hq : IsQProjOver p := by
    obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
    exact ⟨N, j, inferInstance, inferInstance, hjp⟩
  have hq₁ := isQProjOver_comp_spMap_of_finiteType hfin.finiteType hq
  have hq₂ := isQProjOver_of_isPullback_spMap (Int.castRingHom (ZMod l))
    (IsPullback.of_hasPullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) hq₁
  let u := Limits.pullback.lift (f := p ≫ spMap (Int.castRingHom k))
    (g := spMap (Int.castRingHom (ZMod l))) i (strHom (ZMod l) Z) e
  have : IsImmersion u := by
    have : IsImmersion (u ≫ Limits.pullback.fst _ _) := by
      rw [Limits.pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp u (Limits.pullback.fst _ _)
  have hu : u ≫ Limits.pullback.snd _ _ = strHom (ZMod l) Z := Limits.pullback.lift_snd _ _ _
  rw [← hu] at hpr ⊢
  exact isProjOver_of_isProper_of_isImmersion _ hq₂

end GlobalTheory.VertProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeight
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.JetsUb

open GlobalTheory.AllWt GlobalTheory.CompHS

theorem floorGaps_sub_le {N : ℕ} (a : ℕ) (m : ℤ) (v : Fin N → ℤ) (hv : Antitone v) {i j : Fin N} (hij : i ≤ j) :
    floorGaps a m v i - floorGaps a m v j ≤ v i - v j := by
  have hij' : (i : ℕ) ≤ j := hij
  have e1 : floorGaps a m v i - floorGaps a m v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k / m := by
    simp only [floorGaps, ofGaps]
    rw [← Finset.sum_range_add_sum_Ico _ hij']
    ring
  have e2 : v i - v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k := by
    have h1 := ofGaps_gap v i i
    have h2 := ofGaps_gap v i j
    simp only [ofGaps] at h1 h2
    rw [← Finset.sum_range_add_sum_Ico _ hij'] at h2
    linarith
  rw [e1, e2]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  have hN : k + 1 < N := by have := j.2; omega
  have h0 : 0 ≤ gap v k := by
    rw [gap, dite_eq_left hN]
    have := hv (show (⟨k, by omega⟩ : Fin N) ≤ ⟨k + 1, hN⟩ from Fin.mk_le_mk.2 (by omega))
    omega
  exact Int.ediv_le_self _ h0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem thA_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) (x : (E →+* ℂ) × ℕ) :
    thA Dw P.ub n x ≤ thA Dw P.u₁ n x := by
  have hd : ∀ τ (i j : Fin (Dw.p + Dw.q)), i ≤ j → P.ub τ i - P.ub τ j ≤ P.u₁ τ i - P.u₁ τ j :=
    fun τ i j h => floorGaps_sub_le _ _ _ (hu τ) h
  show (thExpZ Dw P.ub n x).toNat ≤ (thExpZ Dw P.u₁ n x).toNat
  apply Int.toNat_le_toNat
  obtain ⟨σ, i⟩ := x
  rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · by_cases hi : i < Dw.p
    · rw [thExpZ_big _ n τ i hi, thExpZ_big _ n τ i hi]
      have := hd τ ⟨i, by omega⟩ ⟨Dw.p - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_big_ge _ n τ i (by omega), thExpZ_big_ge _ n τ i (by omega)]
  · by_cases hi : i < Dw.q
    · rw [thExpZ_small _ n hp τ i hi, thExpZ_small _ n hp τ i hi]
      have := hd τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_small_ge _ n τ i (by omega), thExpZ_small_ge _ n τ i (by omega)]

theorem DF_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) :
    Formalism.L2.Pj.DF Dw (thA Dw P.ub n) ≤ Formalism.L2.Pj.DF Dw (thA Dw P.u₁ n) := by
  unfold Formalism.L2.Pj.DF
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => thA_ub_le P n hp hu (τ, i)

end GlobalTheory.RefSum.JetsUb

theorem GlobalTheory.RefSum.JetNum.of_le {D : Formalism.BasicNotions.D7} {d d' : ℕ} {c : ℝ} (h : GlobalTheory.RefSum.JetNum D d c) (hd : d' ≤ d) :
    GlobalTheory.RefSum.JetNum D d' c := fun k => by
  obtain ⟨h1, h2, h3⟩ := h k
  have hd' : (d' : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 ≤ GlobalTheory.PtTie.rr0 D := by unfold GlobalTheory.PtTie.rr0; positivity
  refine ⟨by omega, ?_, le_trans ?_ h3⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd' (by positivity)) h2
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (d' : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 2
    linarith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeDual

theorem lam_mul_left (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) {T : Over S} (a a' t : T ⟶ A) :
    lam (cls L hL) (a * a') t = lam (cls L hL) a t + lam (cls L hL) a' t := by
  have h := hC S A hA L hL T a a' t
  have hl := LB.isLB_linComb hL (fun k : Fin 8 ↦ (![a * a' * t, a * a', a * t, a' * t, a, a', t, 1] k).left)
    ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hL _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  unfold lam
  rw [← sub_eq_zero, ← e]
  abel

theorem evc_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem isAdditive_lam (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) : IsAdditive (abelian₂ A L) ∧ IsAdditive (swap (abelian₂ A L)) := by
  haveI := hA.comm
  have hs : (swap (abelian₂ A L)).IsLB := pull_isLB hP _
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (isAdditive_iff hs).2 fun Y a a' t ↦ ?_⟩
  · rw [evc_lam hL, evc_lam hL, evc_lam hL]
    exact lam_mul_left hC hA hL a a' t
  · rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_lam hL, evc_lam hL, evc_lam hL, lam_comm, lam_comm _ t a,
      lam_comm _ t a']
    exact lam_mul_left hC hA hL a a' t

theorem mono_of_isPerfect' {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) [IsMonHom x] : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem abelianDeRham_duality : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  intro hC hD hPD hF R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨haddL, haddS⟩ := isAdditive_lam hC hA hL hP
  obtain ⟨B, _, P, hB, hdim, h1, h2⟩ := hD (Sp R) A hA
  have hgB := hdim g hg
  obtain ⟨x, hx, -⟩ := h1.univ A (abelian₂ A L) hP haddL
  haveI hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying (Sp R) A A B (abelian₂ A L) P h1 h2.additive hP haddS x hx
  have perf := h1.isPerfect h2
  obtain ⟨φ, hφ⟩ := exists_isCorrForm (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg hgB))
    perf.isLB perf.zero_left perf.zero_right
  have e : LBIso (P.pull (lift (fst A A) (snd A A ≫ x)).left) (abelian₂ A L) :=
    (cls_eq_iff (pull_isLB h1.isLB _) hP).1 ((cls_eq_iff hP (pull_isLB h1.isLB _)).2 hx).symm
  obtain ⟨φ', hφ', k⟩ := hφ.pull h1.isLB (homMor (dp0 R) (𝟙 _) (𝟙 A)) (homMor (dp0 R) (𝟙 _) x)
    (h := (lift (fst A A) (snd A A ≫ x)).left)
    (by simp only [← Over.comp_left, lift_fst, Category.comp_id])
    (by simp only [← Over.comp_left, lift_snd])
    hP e
  have hψ' := isCorrForm_lam hψ
  obtain rfl := hφ'.unique (cupSquare_of_free hF (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)) hP hψ'
  have hform : ∀ a b, φ' a b = φ a (push (dp0 R) (𝟙 _) x b) := fun a b ↦ by
    have := k (push (dp0 R) (𝟙 _) (𝟙 A) a) a (push (dp0 R) (𝟙 _) x b) b (fun _ ↦ rfl) fun _ ↦ rfl
    rw [this, push_id]
    rfl
  obtain ⟨-, orth⟩ := hPD R A B g hA hB hg hgB P h1 φ hφ
  refine ⟨fun a ha b hb ↦ ?_, fun hK ↦ ?_⟩
  · rw [hform]
    exact orth a ha _ (push_mem_Fil x hb)
  · have mx : Mono x := mono_of_isPerfect' h1 (isPerfect_lam hL hK) x hx
    have ix : IsIso x := GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension (Sp R) A B hA hB g hg hgB x hmx mx
    have hd : IsDual A A (abelian₂ A L) := GlobalTheory.AbDual.transport (Sp R) A A B (abelian₂ A L) P h1 hP x ix hmx hx
    exact (hPD R A A g hA hA hg hg (abelian₂ A L) hd φ' hψ').1

end GlobalTheory.CubeDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDualStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  first | exact @GlobalTheory.CubeDual.abelianDeRham_duality | exact GlobalTheory.CubeDual.abelianDeRham_duality | (intros; apply GlobalTheory.CubeDual.abelianDeRham_duality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompGen

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, -⟩ := exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r⟩

end GlobalTheory.PullDegCompGen

namespace GlobalTheory.Mum

theorem nonempty_isPullDeg_comp_of_injective : ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (φ : R →+* R') (φ' : R' →+* R'') (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Function.Injective φ' → Nonempty (IsPullDeg φ D D') → Nonempty (IsPullDeg φ' D' D'') → Nonempty (IsPullDeg (φ'.comp φ) D D'') := by
  intro R R' R'' _ _ _ _ _ _ φ φ' D D' D'' hj ⟨p⟩ ⟨q⟩
  exact GlobalTheory.PullDegCompGen.nonempty_isPullDeg_comp hj p q

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullDegUniq

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    Nonempty (PsiOn D' (specOf φ ⁻¹ᵁ hD.W)) := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc using key
  exact ⟨⟨a, ha, hc⟩⟩

theorem exists_generic_section {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ s : (TK R').left ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme, s ≫ (specOf φ ⁻¹ᵁ hD.W).ι = jK R' :=
  ⟨(isPullback_morphismRestrict (specOf φ) hD.W).lift hD.g (jK R') hD.g_comm,
    (isPullback_morphismRestrict (specOf φ) hD.W).lift_snd _ _ _⟩

theorem nonempty_isPullDeg_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} (hα : Function.Injective α)
    (hβ : Function.Injective β) {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₁ : IsPullDeg α D₀ D₁)
    (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW⟩ := nonempty_psiOn_pull h₁
  obtain ⟨s, hs⟩ := exists_generic_section h₁
  obtain ⟨hD, -⟩ := DvrDeg.exists_isPullDeg_of_val hβ D₁ D ψW s hs gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK R₂ ≫ spMap β = genMap hβ ≫ jK R₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq hβ)
    have sα : jK R₁ ≫ spMap α = genMap hα ≫ jK R₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap hβ ≫ jK R₁ ≫ spMap α = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK R₂).left ≫ jK R₂ ≫ spMap (β.comp α) = (genMap hβ ≫ genMap hα) ≫ jK R₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap hβ ≫ D₁.xK (xe x) := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = genMap hβ ≫ jK R₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

end GlobalTheory.PullDegUniq

namespace GlobalTheory.Mum

theorem isPullDeg_unique_and_comp : (∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (D : DegPre R) (D₁ D₂ : DegPre R'), Nonempty (IsPullDeg ρ D D₁) → Nonempty (IsPullDeg ρ D D₂) → Nonempty (IsPullDeg (RingHom.id R') D₁ D₂)) ∧ ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (ρ : R →+* R') (ρ' : R' →+* R''), Function.Injective ρ → Function.Injective ρ' → ∀ (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Nonempty (IsPullDeg ρ D D') → Nonempty (IsPullDeg ρ' D' D'') → Nonempty (IsPullDeg (ρ'.comp ρ) D D'') :=
  ⟨fun _ R' _ _ _ _ ρ hρ _ _ _ ⟨p₁⟩ ⟨p₂⟩ =>
    GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel (β := RingHom.id R') hρ Function.injective_id p₁
      ((RingHom.id_comp ρ).symm ▸ p₂),
   fun _ _ _ _ _ _ _ _ _ _ _ hρ hρ' _ _ _ ⟨p⟩ ⟨q⟩ => GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ hρ' p q⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

end GlobalTheory.AmpleRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_mulEquiv_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

end GlobalTheory.GroupBplus.Aff
end
end
