module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
  (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ D χ).choose

theorem isQ_qv : QForm.IsQ D.toPre ϖ (qv D hϖ) := fun χ => (QForm.exists_QVal hϖ D χ).choose_spec

def beF : LinearMap.BilinForm ℤ D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D (isQ_qv D hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : D.toPre.X) : beF D hϖ a b = beF D hϖ b a := QForm.bOf_comm D a b

theorem beF_self (a : D.toPre.X) : beF D hϖ a a = 2 * qv D hϖ a :=
  (QForm.two_Q_eq hϖ D (isQ_qv D hϖ) a).symm

theorem beF_pos {a : D.toPre.X} (ha : a ≠ 0) : 0 < beF D hϖ a a := by
  have := QForm.Q_pos hϖ D (isQ_qv D hϖ) ha
  rw [beF_self]; omega

include oD in
theorem beF_adj (x : 𝓞 E) (a b : D.toPre.X) : beF D hϖ (x • a) b = beF D hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ D GlobalTheory.abelianSchemeLaws_all.1 oD (isQ_qv D hϖ) x a b

include oD in
theorem beF_w0 (a : D.toPre.X) : beF D hϖ a (H.w0 • a) = qv D hϖ a := by
  have h₁ := beF_adj D oD hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm D hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self D hϖ a
  omega

def tF (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b))

include oD in
theorem isScalarForm_tF : letI := H.starRing; IsScalarForm (𝓞 E) (tF D hϖ) := by
  letI := H.starRing
  refine ⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩
  · simp only [tF, map_add (f := _), neg_add, zpow_add]
  · rw [tF, tF, beF_symm]
  · rw [tF, tF, beF_adj D oD]; rfl

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist D.toPre H.w0 (tF D hϖ)

def oa0 : letI := H.starRing; (D0 (H := H) D hϖ).OAct (𝓞 E) :=
  letI := H.starRing; twistAct (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) oD


include oD in
theorem gen0 (a : D.toPre.X) : PsiUnitOn (D0 (H := H) D hϖ) a Set.univ :=
  psiUnitOn_rescale_of_qVal T D.toPre ϖ hϖ a (qv D hϖ a) (isQ_qv D hϖ a) _ (by
    show ((GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a (H.w0 • a))) : (FractionRing T.V)ˣ) : FractionRing T.V) = _
    rw [beF_w0 D oD, Units.val_zpow_eq_zpow_val]; rfl)

def rF (k : ℕ) (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b / k))

include oD in
theorem isRootForm_rF {k : ℕ} (hk : ∀ a b, (k : ℤ) ∣ beF D hϖ a b) :
    letI := H.starRing; IsRootForm (𝓞 E) k (tF D hϖ) (rF D hϖ k) := by
  letI := H.starRing
  refine ⟨⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩, fun a b => ?_⟩
  · simp only [rF, map_add (f := _)]
    rw [Int.add_ediv_of_dvd_left (hk a b), neg_add, zpow_add]
  · rw [rF, rF, beF_symm]
  · rw [rF, rF, beF_adj D oD]; rfl
  · rw [rF, tF, ← zpow_natCast, ← zpow_mul, neg_mul, Int.ediv_mul_cancel (hk a b)]
    ext; simp

theorem psiRel0 : letI := H.starRing; PsiRel D.toPre (D0 (H := H) D hϖ).psi fun y => tF D hϖ y (H.w0 • y) :=
  psiRel_rescale _ _

section ThetaShiftProofs

variable {Dm : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] (β : O →+* c.F) (b : O →+* T.V)

theorem dvd_of_dvd {k : ℕ} (hk : k ∣ l.M') (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (a a' : D.toPre.X) :
    (k : ℤ) ∣ beF D hϖ a a' :=
  (Int.natCast_dvd_natCast.2 hk).trans ((dvd_mul_left _ _).trans (hdiv a a'))

def twistedLevelPointsOfLattice (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.A :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_right l.M l.A) hdiv)) _ (pA v)

def eta0 (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.M :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_left l.M l.A) hdiv)) _ (pM v)


open scoped Classical in
variable (Dm) in
def LieCl : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = H.rt0 →
    ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oD.onB.toRingAct)
      (spMap ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V _))) τ n ∧
      n + Module.finrank (𝓞 E) D.toPre.X =
        if τ H.rt = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) then Dm.p else Dm.q


variable (Dm) in
def TateCl (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
    ∃ I : TateIsoQ Dm (D0 (H := H) D hϖ) (oa0 D oD hϖ) F,
      (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (twistedLevelPointsOfLattice D oD hϖ hdiv pA a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.A a)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dm.La), ∀ q,
        QkExt (algebraMap _ F) (eta0 D oD hϖ hdiv pM a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.M a)

def arc (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : LieCl D oD Dm β b)
    (hTate : TateCl D oD hϖ Dm β b hdiv pA pM) : ArcIn Dm l β T.V b :=
  letI := H.starRing
  { D₀ := D0 D hϖ
    oa := oa0 D oD hϖ
    nontriv := hX
    even := psiEven_twist (isScalarForm_tF D oD hϖ) H.w0 D.psi_even
    bimult := tauBimult_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) D.tau_bimult
    gen := gen0 D oD hϖ
    w0 := psi_weight_zero_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) hw
    be := beF D hϖ
    be_symm := beF_symm D hϖ
    be_pos := fun a ha => beF_pos D hϖ ha
    be_adj := beF_adj D oD hϖ
    be_dvd := hdiv
    eta := eta0 D oD hϖ hdiv pM
    etaA := twistedLevelPointsOfLattice D oD hϖ hdiv pA
    geom := fun F _ _ _ r z hr hz f hf => by
      subst hf
      obtain ⟨I, h₁, h₂, h₃⟩ := hTate F z hz
      exact ⟨hLie F r hr, I, h₁, h₂, h₃⟩ }

end ThetaShiftProofs

end GlobalTheory.TraitArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThrough
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThrough
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RootSystem

theorem exists_compatible_roots_through (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K)
    (hA : 0 < A) (hω : IsPrimitiveRoot ω A) :
    ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
      (ζ A : K) = ω := by
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) A := GlobalTheory.HostModel.isPrimitiveRoot_zeta hA
  have hint : IsIntegral ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (hz.isIntegral hA).tower_top
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A}
  haveI : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hint
  let pb := IntermediateField.adjoin.powerBasis hint
  have hroot : Polynomial.aeval ω (minpoly ℚ pb.gen) = 0 := by
    have hm : minpoly ℚ pb.gen = minpoly ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := by
      rw [IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)
    rw [hm, ← Polynomial.cyclotomic_eq_minpoly_rat hz hA, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic]
    exact (hω.isRoot_cyclotomic hA)
  let f : L →ₐ[ℚ] K := pb.lift ω hroot
  obtain ⟨ζ, h1, h2, h3⟩ := GlobalTheory.HostModel.exists_roots L K f.toRingHom
  refine ⟨ζ, h1, h2, ?_⟩
  have hg := h3 A hA (IntermediateField.AdjoinSimple.gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)) rfl
  rw [hg]
  have : f pb.gen = ω := pb.lift_gen ω hroot
  rw [IntermediateField.adjoin.powerBasis_gen] at this
  exact this

end GlobalTheory.RootSystem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimitiveRootsThroughStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_primitiveRoots_through : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K), 0 < A → IsPrimitiveRoot ω A → ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧ (ζ A : K) = ω := by
  first | exact @GlobalTheory.RootSystem.exists_compatible_roots_through | exact GlobalTheory.RootSystem.exists_compatible_roots_through | (intros; apply GlobalTheory.RootSystem.exists_compatible_roots_through <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryType
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitTate

open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  intro E _ _ _ H Dm l c O _ β hβ T b hb D _ o hP hrat
  letI := H.starRing
  haveI : CharZero (FractionRing T.V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero (AlgebraicClosure (FractionRing T.V)) :=
    charZero_of_injective_algebraMap (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).injective
  have hB : D.toPre.TauBimult := D.tau_bimult

  set g : O →+* AlgebraicClosure (FractionRing T.V) :=
    (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))).comp ((algebraMap T.V _).comp b) with hg
  have hginj : Function.Injective g :=
    (algebraMap (FractionRing T.V) _).injective.comp ((IsFractionRing.injective T.V (FractionRing T.V)).comp hb)

  obtain ⟨ζ₀, hζp, hζc, hζA⟩ : ∃ ζ₀ : ℕ → (AlgebraicClosure (FractionRing T.V))ˣ,
      (∀ n, 0 < n → IsPrimitiveRoot (ζ₀ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ₀ (n * m) ^ m = ζ₀ n) ∧
      ∀ z : O, ((β z : c.F) : ℂ) = zeta l.A → (ζ₀ l.A : AlgebraicClosure (FractionRing T.V)) = g z := by
    by_cases hz : ∃ z : O, ((β z : c.F) : ℂ) = zeta l.A
    · obtain ⟨z, hz⟩ := hz
      have h₀ : IsPrimitiveRoot (((β z : c.F) : ℂ)) l.A := by
        rw [hz]; exact Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
      have h₁ : IsPrimitiveRoot (β z) l.A :=
        IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) h₀ Subtype.val_injective
      have h₂ : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (f := β) h₁ hβ
      have h₃ : IsPrimitiveRoot (g z) l.A := h₂.map_of_injective hginj
      obtain ⟨ζ, e₁, e₂, e₃⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) l.A (g z) l.A_pos h₃
      refine ⟨ζ, e₁, e₂, fun z' hz' => ?_⟩
      have : z' = z := hβ (Subtype.val_injective (hz'.trans hz.symm))
      rw [this]; exact e₃
    · obtain ⟨ζ, e₁, e₂, -⟩ := GlobalTheory.T.exists_compatible_primitiveRoots_through (AlgebraicClosure (FractionRing T.V)) 1 1 one_pos IsPrimitiveRoot.one
      exact ⟨ζ, e₁, e₂, fun z hz' => (hz ⟨z, hz'⟩).elim⟩

  obtain ⟨-, -, -, hF⟩ := hP
  obtain ⟨-, hT⟩ := hF (AlgebraicClosure (FractionRing T.V))
  obtain ⟨I₀, hI₀⟩ := hT ζ₀ hζp hζc

  have hA : l.A ∣ l.M' := Nat.dvd_lcm_right l.M l.A
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  choose pA hpA using fun a => hrat l.A hA (I₀.ev l.A a)
  choose pM hpM using fun a => hrat l.M hM (I₀.ev l.M a)
  refine ⟨pA, pM, fun F _ _ _ z hz => ?_⟩

  let e : AlgebraicClosure (FractionRing T.V) →ₐ[FractionRing T.V] F :=
    IsAlgClosed.lift (M := F) (R := FractionRing T.V) (S := AlgebraicClosure (FractionRing T.V))
  have he : (e : AlgebraicClosure (FractionRing T.V) →+* F).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) = algebraMap (FractionRing T.V) F :=
    RingHom.ext fun x => e.commutes x
  have hK : (algebraMap (AlgebraicClosure (FractionRing T.V)) (AlgebraicClosure (FractionRing T.V))).comp
      (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) =
      algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V)) := RingHom.ext fun _ => rfl

  have base : ∀ {k : ℕ} (p₀ : QkPt D.toPre (FractionRing T.V) k) (r : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k),
      QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ r →
      ∀ p, QkExt (algebraMap _ (AlgebraicClosure (FractionRing T.V))) p₀ p →
        QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing T.V)) p r := by
    intro k p₀ r hr p hp
    have u := (existsUnique_qkExt hB (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) hK p₀).unique hp hr
    rw [u]; exact qk_equiv_refl hB r
  refine ⟨tateExt (e : AlgebraicClosure (FractionRing T.V) →+* F) he hB abelianSchemeLaws_all.1 I₀
    (ArcInputCompare.weil_ext hB (e : AlgebraicClosure (FractionRing T.V) →+* F) he), ?_, ?_, ?_⟩
  ·
    show ((Units.map (e : AlgebraicClosure (FractionRing T.V) →+* F).toMonoidHom (I₀.ζ l.A) : Fˣ) : F) = _
    rw [hI₀, Units.coe_map, hζA z hz, hg]
    exact e.commutes _
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pA a) _ (hpA a)) q hq
  · intro a q hq
    exact GlobalTheory.LiftExt.equiv_of_base hB _ he (base (pM a) _ (hpM a)) q hq

end GlobalTheory.TraitTate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryTypeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tate_pairs_unitaryType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V), Function.Injective b → ∀ (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → (∀ k : ℕ, k ∣ l.M' → ∀ q : QkPt D.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q) → ∃ (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M), ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A → ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre o F), (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧ (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧ ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a) := by
  first | exact @GlobalTheory.TraitTate.exists_tate | exact GlobalTheory.TraitTate.exists_tate | (intros; apply GlobalTheory.TraitTate.exists_tate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiser
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitArcMatch

open GlobalTheory.TraitArc GlobalTheory.TauTwist GlobalTheory.ArcBuild GlobalTheory.ArcOfPoint _root_.Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {T : CDVR}

theorem genRel_psi_twist (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : D.toPre.X) :
    GenRel (isoPullId (idIso D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 (H := H) D hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF D hϖ y y / 2 = qv D hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF D hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val D.toPre.P.isLB (DVR.pullGen_isGen _ _ _ _ (D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (TraitArc.tF D hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, TraitArc.tF, beF_w0 D oD, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv D hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (TraitArc.tF D hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

theorem exists_isPullDeg_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  intro E _ _ _ H Dm l c O _ β T b D _ oD ϖ hϖ hX hw hdiv pA pM hLie hTate Xo Y y hY
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, -, h5, h6⟩ := hY
  refine ⟨t, m, P, ?_⟩
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he0 : eSec D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec D.toPre.P.A := by
    rw [hid, Category.comp_id]; exact (Category.id_comp _).symm
  have p : IsGrpPullback D.toPre.P.A D.toPre.P.A (spMap (RingHom.id T.V)) (𝟙 _) := by
    have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
    exact (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr hid.symm rfl
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  let F := AlgebraicClosure (FractionRing T.V)
  have k6 := (h6 F (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) (fun _ => rfl) rfl).1
  have r := (maps_iff (idW D.toPre.P.L) _ (fun _ => eSec D.toPre.P.A) _ D.toPre.rig D.toPre.rig _ _
    (rigPull_le (𝟙 _) _ he0 D.toPre.P.L) (fun _ => rfl)).1 (maps_rig_id D.toPre he0)
  have r' := (maps_iff w _ (fun _ => eSec D.toPre.P.A) _ P.D.toPre.rig D.toPre.rig _ _
    (rigPull_le φ _ he D.toPre.P.L) (fun _ => rfl)).1 h3
  let xe : P.D.toPre.X ≃+ D.toPre.X := e.symm.toAddEquiv
  have hxe : ∀ y, xe (e y) = y := fun y => e.symm_apply_apply y
  obtain ⟨hD, -⟩ := GlobalTheory.ArcData.exists_isPullDeg_id D.toPre P.D.toPre (A₀ := D.toPre.P.A) (M₀ := D.toPre.P.L)
    D.toPre.P.isLB D.toPre.rig p h1 (idW D.toPre.P.L) w
    ((isGen_iff _).1 ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) rfl))) ((isGen_iff _).1 h2)
    r r' xe (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      refine (h5 y).trans ?_
      rw [hid, Category.id_comp, Category.comp_id, hxe]; rfl)
    Wo hWo ψW (jFK (R := T.V) F) (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hxe]
      exact ⟨_, _, _, genRel_psi_twist D oD hϖ F y, k6 y⟩)
  exact ⟨hD⟩

end GlobalTheory.TraitArcMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiserStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | exact GlobalTheory.TraitArcMatch.exists_isPullDeg_arc | (intros; apply GlobalTheory.TraitArcMatch.exists_isPullDeg_arc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitInputExt

theorem exists_ext_dvd_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  intro R _ _ _ D O _ V₁ _ _ _ ρ₁ b₁ hV₁ iρ₁ fρ₁ lρ₁ ib₁ N hN
  obtain ⟨D₁, ⟨h₁⟩⟩ := GlobalTheory.MumPull.exists_pull R V₁ ρ₁ iρ₁ lρ₁ D
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  let T₁ : Formalism.L2.Pj.CDVR := { V := V₁ }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₁
  obtain ⟨T', g, ϖ, e, ig, fg, hϖ, he, hass, rat⟩ :=
    GlobalTheory.QkRationalExt.exists_cdvr_ext_rational T₁ D₁.toPre D₁.tau_bimult N hN π hπ
  have lg : IsLocalHom g := fg.to_isIntegral.isLocalHom ig
  obtain ⟨D', ⟨hD⟩⟩ := GlobalTheory.MumPull.exists_pull V₁ T'.V g ig lg D₁
  have hc : Nonempty (IsPullDeg (g.comp ρ₁) D.toPre D'.toPre) :=
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V₁ T'.V ρ₁ g D.toPre D₁.toPre D'.toPre ig ⟨h₁⟩ ⟨hD⟩
  choose Q₁ hQ₁ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hπ D₁
  have hNe : (N : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  refine ⟨T', g.comp ρ₁, g.comp b₁, ϖ, D', ig.comp iρ₁, fg.comp fρ₁, ig.comp ib₁, hϖ, hc, ?_, ?_⟩
  · intro Q hQ u v
    have hq : ∀ y, Q y = e * Q₁ (hD.xe y) := fun y =>
      ReciprocityTheory.ChartRestriction.G.DVR.QForm.QVal_unique hϖ D' (hQ y)
        (GlobalTheory.QValPull.main T₁ T' g D₁.toPre D'.toPre hD π ϖ e ig hπ hϖ hass y _ (hQ₁ _))
    rw [ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf, hq, hq, hq]
    exact dvd_sub (dvd_sub (hNe.mul_right _) (hNe.mul_right _)) (hNe.mul_right _)
  · intro k hk
    exact rat D'.toPre hD D'.tau_bimult k hk

end GlobalTheory.TraitInputExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traitExtension_divisible_valuationForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  first | exact @GlobalTheory.TraitInputExt.exists_ext_dvd_rational | exact GlobalTheory.TraitInputExt.exists_ext_dvd_rational | (intros; apply GlobalTheory.TraitInputExt.exists_ext_dvd_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dm : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {T : Formalism.L2.Pj.CDVR}

theorem tateCl_of (β : O →+* c.F) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
      ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre oD F),
        (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧
        (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧
        ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a)) :
    TateCl D oD hϖ Dm β b hdiv pA pM := by
  intro F _ _ _ z hz
  letI := H.starRing
  obtain ⟨I, hζ, e₂, e₃⟩ := h F z hz
  have hw := GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)
  have ht := isScalarForm_tF D oD hϖ
  have hq := psiRel0 (H := H) D hϖ
  have hR := isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (dvd_refl l.M') hdiv)
  let s : D.toPre.X → D.toPre.X → Fˣ := fun y x =>
    Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (rF D hϖ l.M' y x)
  have hs : IsRootForm (𝓞 E) l.M' (tF D hϖ) s :=
    ⟨hR.1.map _, fun y x => by
      show (Units.map _ _) ^ _ = _
      rw [← map_pow, hR.2 y x]
      rfl⟩
  obtain ⟨s', I', s₁, -, s₃, s₄, s₅⟩ := exists_tateIsoQ_twist D.tau_bimult hw ht oD l.M' s hs I
  have lev : ∀ {k : ℕ} (hk : 0 < k) (hd : k ∣ l.M') (p : QkPt D.toPre (FractionRing T.V) k) (v : Dm.La),
      (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv D.toPre F q (I.ev k v)) → ∀ q',
      QkExt (algebraMap _ F) (qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) _ p) q' →
      QkPt.Equiv (D0 (H := H) D hϖ) F q' (I'.ev k v) := by
    intro k hk hd p v he q' hq'
    obtain ⟨q, rfl⟩ := (qkScaleEquiv hw ht hq (s₁ k hk) _).surjective q'
    have e := qkRel_qkScaleEquiv (D := D.toPre) (hψ := (D0 (H := H) D hϖ).psi_gen) hw ht hq (s₁ k hk) q
    refine e.equiv hw ht hq (s₁ k hk) (s₅ k hk v) (he q (QkRel.qkExt_of (fun y x => ?_)
      (qkRel_qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) p) e hq'))
    rw [s₃ k hk hd]
    show (Units.map _ _) ^ _ = _
    rw [← map_pow]
    congr 1
    obtain ⟨j, hj⟩ := dvd_of_dvd D hϖ (dvd_refl l.M') hdiv y x
    obtain ⟨i, hi⟩ := hd
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
    have hi0 : (i : ℤ) ≠ 0 := by
      rintro h
      have : i = 0 := by exact_mod_cast h
      rw [this, mul_zero] at hi
      omega
    simp only [rF, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hj, hi, Nat.mul_div_cancel_left _ hk]
    push_cast
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hi0), _root_.mul_assoc, Int.mul_ediv_cancel_left _ hk0]
    ring
  exact ⟨I', by rw [s₄]; exact hζ, fun v => lev l.A_pos (Nat.dvd_lcm_right l.M l.A) _ v (e₂ v),
    fun v _ q hq => lev (lt_of_lt_of_le (by decide) l.three_le) (Nat.dvd_lcm_left l.M l.A) _ v (e₃ v) q hq⟩

end GlobalTheory.TraitArc


open GlobalTheory.TraitArc in
theorem GlobalTheory.TraitArc.exists_input_recovering : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP l c O _ β hβ V₁ _ _ _ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
  obtain ⟨T, ρ, b, ϖ, D', hρ, hρf, hb, hϖ, ⟨hD⟩, hdvd, hrat⟩ :=
    GlobalTheory.T.exists_traitExtension_divisible_valuationForm R D O V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁ (2 * l.M') (by omega)
  have hBase : Base R := ⟨by haveI := hR.1; exact ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩, hR.2.2⟩
  obtain ⟨inst, o', hP'⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hBase E H Dm D o hP T.V ρ hρ D' ⟨hD⟩
  letI := inst
  have hX' : Nontrivial D'.toPre.X := hD.xe.toEquiv.nontrivial
  have hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D' hϖ a a' := fun a a' => by
    have := hdvd _ (isQ_qv D' hϖ) a a'
    exact_mod_cast this
  obtain ⟨pA, pM, hT⟩ := GlobalTheory.T.exists_rational_tate_pairs_unitaryType E H Dm l c O β hβ T b hb D' o' hP' (fun k hk => hrat k (hk.mul_left 2))
  have hLie : LieCl D' o' Dm β b := by
    intro F _ _ _ r _ τ
    obtain ⟨n, h₁, h₂⟩ := (hP'.2.2.2 F).1 τ
    refine ⟨n, h₁, ?_⟩
    split_ifs
    · exact h₂
    · exact h₂.trans hP'.1
  have hTate := tateCl_of β b D' o' hϖ hdiv pA pM hT
  refine ⟨T.V, T.cr, T.dom, inferInstance, ρ, b, ϖ, arc D' o' hϖ β b hX' hP'.2.2.1 hdiv pA pM hLie hTate,
    ⟨T.dvr, T.cpl, T.ch0⟩, hρ, hρf, hϖ, ?_⟩
  intro Xo Y y hy
  obtain ⟨t, m, P, ⟨hD₂⟩⟩ := GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser E H Dm l c O β T b D' o' ϖ hϖ hX' hP'.2.2.1 hdiv pA pM hLie hTate Xo Y y hy
  refine ⟨t, m, P, ?_⟩
  have := GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R T.V T.V ρ (RingHom.id T.V) D.toPre D'.toPre P.D.toPre
    Function.injective_id ⟨hD⟩ ⟨hD₂⟩
  rwa [RingHom.id_comp] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArc.exists_input_recovering | exact GlobalTheory.TraitArc.exists_input_recovering | (intros; apply GlobalTheory.TraitArc.exists_input_recovering <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUnifor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUnifor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UTraitHyp

theorem hypS_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  intro V _ _ I E _ _ _ H t P
  letI := P.A.isAb.comm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ t.G P.A.A (jK V) _ t.PP.L P.A.L t.PP.isLB P.A.isLB h1 h2
    ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
      by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

end GlobalTheory.UTraitHyp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUniforStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  first | exact @GlobalTheory.UTraitHyp.hypS_generic | exact GlobalTheory.UTraitHyp.hypS_generic | (intros; apply GlobalTheory.UTraitHyp.hypS_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_point_hasArcData_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  intro E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ
  obtain ⟨hdvr, hc, hcz⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨h1, h2, -, h4, h5⟩ := GlobalTheory.lawsAndExpansions.1
  have hT := GlobalTheory.twistBaseChange
  have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨χ, hχ, -⟩ := hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)
  obtain ⟨hs, -, hj, hd⟩ := (hχ χ).1 rfl
  obtain ⟨-, -, ev, hC, hX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc
  have hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x)) := by
      simp only [Scheme.Hom.comp_apply]
    rw [e]
    apply hj
    intro hx
    have hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal := hx
    have hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X))) := by
      rw [map_mul, hC, hX]
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)
  refine ⟨spMap ev ≫ χ, ?_⟩
  rw [hm]
  exact GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_arcData_at_uniformiser_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  first | exact @GlobalTheory.Mum.exists_point_hasArcData_uniformiser | exact GlobalTheory.Mum.exists_point_hasArcData_uniformiser | (intros; apply GlobalTheory.Mum.exists_point_hasArcData_uniformiser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionEmbedding
open scoped TensorProduct

namespace GlobalTheory.FiniteExtensionEmbedding

theorem exists_finite_extension_embedding (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ℚ] F)
  letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  · exact (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom

end GlobalTheory.FiniteExtensionEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitPlace

theorem exists_valuationSubring_of_injective {S K : Type} [CommRing S] [Field K] (f : S →+* K)
    (hf : Function.Injective f) (I : Ideal S) (hI : I ≠ ⊤) :
    ∃ B : ValuationSubring K, ∀ x ∈ I, f x ∈ B.nonunits := by
  have hb : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hI' : I.map f.rangeRestrict ≠ ⊤ := by
    intro h
    apply hI
    rw [← Ideal.comap_map_of_bijective f.rangeRestrict hb (I := I), h, Ideal.comap_top]
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI'
  exact ⟨B, fun x hx => hB ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩⟩

theorem mem_of_forall_prime {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F]
    (O : ValuationSubring F) (h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits) (x : F) : x ∈ O := by
  have h1 : ∀ n : ℕ, (n : F)⁻¹ ∈ O := by
    intro n
    induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime p hp =>
      have := h p hp
      rw [ValuationSubring.mem_nonunits_iff_or] at this
      push Not at this
      exact this.2
    | mul a b ha hb =>
      rw [Nat.cast_mul, mul_inv]
      exact O.mul_mem _ _ ha hb
  have h2 : ∀ q : ℚ, algebraMap ℚ F q ∈ O := by
    intro q
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact O.mul_mem _ _ (intCast_mem O _) (h1 _)
  let g : ℚ →+* O := (algebraMap ℚ F).codRestrict O h2
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hx' : IsIntegral O x := by
    obtain ⟨P, hP, hP0⟩ := hx
    refine ⟨P.map g, hP.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hP0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2

theorem exists_place (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (O : ValuationSubring F) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      ∀ x : F, (x : ℂ) ∈ W → x ∈ O := by
  by_cases h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits
  · obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (Int.castRingHom ℂ) Int.cast_injective
      (Ideal.span {(2 : ℤ)}) (by
        rw [Ne, Ideal.span_singleton_eq_top]
        decide)
    refine ⟨2, B, Nat.prime_two, ?_, fun x _ => mem_of_forall_prime O h x⟩
    simpa using hB 2 (Ideal.mem_span_singleton_self _)
  · push Not at h
    obtain ⟨p, hp, hpO⟩ := h
    obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (F.val.toRingHom.comp O.subtype)
      (fun a b h => Subtype.ext (Subtype.ext h)) (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
    have hB' : ∀ x : F, x ∈ O.nonunits → (x : ℂ) ∈ B.nonunits := fun x hx =>
      hB ⟨x, O.nonunits_subset hx⟩ (ValuationSubring.coe_mem_nonunits_iff.1 hx)
    refine ⟨p, B, hp, by simpa using hB' _ hpO, fun x hx => ?_⟩
    by_contra hxO
    have h0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have h1 : x⁻¹ ∈ O.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or]
      right
      rwa [inv_inv]
    have h2 := hB' _ h1
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    rcases h2 with h2 | h2
    · exact h0 (by simpa using h2)
    · exact h2 (by simpa using hx)

theorem exists_finite_ext (F K : Type) [Field F] [CharZero F] [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  first
  | exact @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | (apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding ..)

theorem exists_place_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (p : ℕ) (hp : p.Prime) (W₀ : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W₀.nonunits) (i : Idx H p) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : R →+* V₁) (b₁ : ↥(i.c.V W₀) →+* V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ρ₁ ∧ Function.Injective b₁ := by
  intro R _ _ _ hR E _ _ _ H
  obtain ⟨h1, h2, h3⟩ := hR
  obtain ⟨l, -, hg, hi⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨⟨l', c, hg2⟩, hl⟩ := hi 2 Nat.prime_two
  have hg' : ∀ p : ℕ, p.Prime → l'.GoodAt p := by
    subst hl
    exact hg
  haveI := c.fin
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨L, _, _, hL, ⟨jF⟩⟩ := exists_finite_ext c.F (FractionRing R)
  obtain ⟨V, _, _, hV, hVc, _, _, _, -, hfin, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) L
  have hVL := IsFractionRing.injective V L
  let O : ValuationSubring c.F := ValuationSubring.ofSubring ((algebraMap V L).range.comap jF) (fun x => by
    rcases ValuationRing.isInteger_or_isInteger V (jF x) with h | h
    · exact Or.inl h
    · right
      change jF x⁻¹ ∈ (algebraMap V L).range
      rw [map_inv₀]
      exact h)
  obtain ⟨p, W, hp, hW, hO⟩ := exists_place c.F O
  let e : V ≃+* (algebraMap V L).range := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hVL (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let g : c.V W →+* (algebraMap V L).range :=
    (jF.comp (c.V W).subtype).codRestrict _ (fun x => hO x.1 x.2)
  refine ⟨p, hp, W, hW, ⟨l', c, hg' p hp⟩, V, inferInstance, inferInstance, inferInstance, algebraMap R V,
    e.symm.toRingHom.comp g, ⟨hV, hVc, charZero_of_injective_algebraMap hinj⟩, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, ?_⟩
  intro a b h
  exact Subtype.ext (jF.injective (congrArg Subtype.val (e.symm.injective h)))

end GlobalTheory.TraitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_local_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (p : ℕ) (hp : p.Prime) (W₀ : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W₀.nonunits) (i : Idx H p) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : R →+* V₁) (b₁ : ↥(i.c.V W₀) →+* V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ρ₁ ∧ Function.Injective b₁ := by
  first | exact @GlobalTheory.TraitPlace.exists_place_finite_ext | exact GlobalTheory.TraitPlace.exists_place_finite_ext | (intros; apply GlobalTheory.TraitPlace.exists_place_finite_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumTrait.exists_unif_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  obtain ⟨p, hp, W₀, hW, i, V₁, _, _, _, ρ₁, b₁, hV₁, hρ₁, hf₁, hl₁, hb₁⟩ := GlobalTheory.T.exists_complete_dvr_local_finite_extension R hR E H
  have hpq : 1 ≤ Dm.p + Dm.q := by have := hP.2.1; omega
  let Xo : ∀ l : Level H, Moduli Dm l := fun l => (GlobalTheory.Moduli.moduli_scheme_exists E H Dm l hpq).some
  obtain ⟨Y, hY, -⟩ := (GlobalTheory.partI_of_semistableReduction GlobalTheory.SS.semistableReductionSt).2 E H Dm hpq Xo
  have hFour := ((hY p W₀ hp hW).2 i).2.2
  obtain ⟨V, _, _, _, ρ, b, ϖ, a, hV, hρi, hρf, hϖ, hmatch⟩ := GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR R hR E H Dm D o hX hP i.l i.c _ (i.c.V W₀).subtype
    Subtype.val_injective V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_arcData_at_uniformiser_completeDVR E H Dm i.l (Xo i.l) i.c _ _ (Y p W₀ hp hW i) hFour V hV b ϖ a hϖ
  obtain ⟨t, -, P, hpull⟩ := hmatch (Xo i.l) (Y p W₀ hp hW i) y hy
  exact ⟨V, _, _, _, ρ, P.D, t.G, inferInstance, inferInstance, P.A, hV, hρi, hρf, hpull, t.semi, ⟨P.U⟩,
    GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised V (maximalIdeal V) E H t P⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  first | exact @GlobalTheory.MumTrait.exists_unif_of_pelOK | exact GlobalTheory.MumTrait.exists_unif_of_pelOK | (intros; apply GlobalTheory.MumTrait.exists_unif_of_pelOK <;> assumption)
end
