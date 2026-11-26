module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesSharpReferenceSixteenTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionTransfer

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S)
    (hg : T.hom ≫ f = g) (x : T ⟶ G') (x₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  subst hg
  have e : x₀ = pushHom h T x := Over.OverMorphism.ext hx
  rw [e, ← map_pow]
  rfl

theorem torsion_transfer : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (K : Type) [Field K] (ev : V₁ →+* K)
  (Z : Over (Sp K)) [GrpObj Z] (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  ∀ (K₀ : Type) [Field K₀] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y] (φ : Z.left ⟶ Y.left),
  IsGrpPullback Z Y (spMap e) φ →
  ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ X), y ^ n = 1 →
  ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left, q ≫ pullback.fst X.hom (spMap ev) = y.left →
    q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
    ∃ y' : Over.mk (spMap e) ⟶ Y, y' ^ n = 1 ∧ y'.left = q ≫ ψ ≫ φ := by
  intro V₁ _ X _ K _ ev Z _ ψ hψ K₀ _ e Y _ φ hφ n y hy q hq hs
  let P := (Over.pullback (spMap ev)).obj X
  let T0 : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have hqP : q ≫ P.hom = T0.hom := hs
  let qq : T0 ⟶ P := Over.homMk q hqP
  have hP := isGrpPullback_pullback X (spMap ev)

  have h1 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm n
  have h0 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm 0
  rw [hy] at h1
  rw [pow_zero, pow_zero] at h0
  have hqn : (qq ^ n).left = (1 : T0 ⟶ P).left := by
    apply pullback.hom_ext
    · exact h1.symm.trans h0
    · exact (Over.w (qq ^ n)).trans (Over.w (1 : T0 ⟶ P)).symm

  have hzw : (q ≫ ψ) ≫ Z.hom = T0.hom := by
    have w := hψ.1.w
    rw [Category.assoc, w, Category.comp_id]; exact hs
  let zz : T0 ⟶ Z := Over.homMk (q ≫ ψ) hzw
  have k1 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl n
  have k0 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl 0
  rw [pow_zero, pow_zero] at k0
  have hzn : (zz ^ n).left = (1 : T0 ⟶ Z).left := by
    rw [k1, hqn]; exact k0.symm

  have hyw : (q ≫ ψ ≫ φ) ≫ Y.hom = spMap e := by
    have w := hφ.1.w
    rw [Category.assoc, Category.assoc, w, ← Category.assoc ψ, ← Category.assoc q, ← Category.assoc q, hzw]
    exact Category.id_comp _
  refine ⟨Over.homMk (q ≫ ψ ≫ φ) hyw, ?_, rfl⟩
  have m1 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) n
  have m0 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) 0
  rw [pow_zero, pow_zero] at m0
  apply Over.OverMorphism.ext
  rw [m1, hzn, m0]

end GlobalTheory.TorsionTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fibre_point_transfer_fixed_model : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (K : Type) [Field K] (ev : V₁ →+* K)
  (Z : Over (Sp K)) [GrpObj Z] (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  ∀ (K₀ : Type) [Field K₀] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y] (φ : Z.left ⟶ Y.left),
  IsGrpPullback Z Y (spMap e) φ →
  ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ X), y ^ n = 1 →
  ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left, q ≫ pullback.fst X.hom (spMap ev) = y.left →
    q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
    ∃ y' : Over.mk (spMap e) ⟶ Y, y' ^ n = 1 ∧ y'.left = q ≫ ψ ≫ φ := by
  first | exact @GlobalTheory.TorsionTransfer.torsion_transfer | exact GlobalTheory.TorsionTransfer.torsion_transfer | (intros; apply GlobalTheory.TorsionTransfer.torsion_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistFibreIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Twist

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (b : R →+* R') (a : R' →+* R'') :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem twist_fibre_iso : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (L : LB X.left), L.IsLB →
  ∀ (K : Type) [Field K]
  (ev : V₁ →+* K) (σ : K ≃+* K) (K₀ : Type) [Field K₀] (e : K₀ →+* K), σ.toRingHom.comp e = e →
  ∀ (Z : Over (Sp K)) [GrpObj Z] (LZ : LB Z.left), LZ.IsLB → ∀ (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  LBIso (L.pull (pullback.fst X.hom (spMap ev))) (LZ.pull ψ) →
  ∀ (Y : Over (Sp K₀)) [GrpObj Y] (L₀ : LB Y.left), L₀.IsLB → ∀ (φ : Z.left ⟶ Y.left), IsGrpPullback Z Y (spMap e) φ →
  LBIso LZ (L₀.pull φ) →
  ∃ f : ((Over.pullback (spMap ev)).obj X).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X).left,
    IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) (𝟙 _) f ∧
    LBIso (L.pull (pullback.fst X.hom (spMap ev))) (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) ∧
    ∀ (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left) (y₀ : Sp K₀ ⟶ Y.left), q ≫ ψ ≫ φ = spMap e ≫ y₀ →
      q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
      q ≫ f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst X.hom (spMap ev) := by
  intro V₁ _ X _ L hL K _ ev σ K₀ _ e hσe Z _ LZ hLZ ψ hψ H1 Y _ L₀ hL₀ φ hφ H2
  have hs : spMap σ.toRingHom ≫ spMap e = spMap e := by rw [spMap_comp_spMap, hσe]
  have hev : spMap σ.toRingHom ≫ spMap ev = spMap (σ.toRingHom.comp ev) := spMap_comp_spMap _ _
  have hX := isGrpPullback_pullback X (spMap ev)
  have hXσ := isGrpPullback_pullback X (spMap (σ.toRingHom.comp ev))
  have hχ := hψ.comp hφ
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : pullback X.hom (spMap (σ.toRingHom.comp ev)) ⟶ pullback X.hom (spMap ev),
      ρ ≫ pullback.fst X.hom (spMap ev) = pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) ∧
      ρ ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) ≫ spMap σ.toRingHom :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ.toRingHom)
      (by rw [pullback.condition, Category.assoc, hev]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hρ : IsGrpPullback ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) ((Over.pullback (spMap ev)).obj X)
      (spMap σ.toRingHom) ρ := hX.cancel (hXσ.congr hev.symm hρ1.symm) hρ2
  have hσχ := hρ.comp hχ
  obtain ⟨f, hf1, hf2⟩ : ∃ f : pullback X.hom (spMap ev) ⟶ pullback X.hom (spMap (σ.toRingHom.comp ev)),
      f ≫ ρ ≫ ψ ≫ φ = ψ ≫ φ ∧
      f ≫ pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd X.hom (spMap ev) :=
    ⟨hσχ.1.lift (ψ ≫ φ) (pullback.snd X.hom (spMap ev))
      (by rw [hχ.1.w]; simp only [Category.id_comp, hs]; try rfl), hσχ.1.lift_fst _ _ _, hσχ.1.lift_snd _ _ _⟩
  have hfg : IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X)
      (𝟙 _) f :=
    hσχ.cancel (hχ.congr (by simp only [Category.id_comp, hs]) hf1.symm)
      (by rw [Category.comp_id]; exact hf2)
  have hτ1 : f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = (f ≫ ρ) ≫ pullback.fst X.hom (spMap ev) := by
    rw [Category.assoc, hρ1]
  have hτχ : (f ≫ ρ) ≫ ψ ≫ φ = ψ ≫ φ := by rw [Category.assoc, hf1]
  have hτ2 : (f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap ev) ≫ spMap σ.toRingHom := by
    rw [Category.assoc, hρ2, ← Category.assoc, hf2]
  refine ⟨f, hfg, ?_, ?_⟩
  · have K1 : LBIso (LZ.pull ψ) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull LZ ψ ψ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => φ) _ ψ fun _ => rfl) H2
    have hA := pull_isLB hL (pullback.fst X.hom (spMap ev))
    have hC := pull_isLB hL₀ (ψ ≫ φ)
    have AC := LBIso.trans hA (pull_isLB hLZ ψ) hC H1 K1
    have D : LBIso (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => pullback.fst X.hom (spMap ev)) _ (f ≫ ρ) fun _ => hτ1)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => ψ ≫ φ) _ (f ≫ ρ) fun _ => hτχ.symm) AC
    exact LBIso.trans hA hC (pull_isLB hL _) AC D.symm
  · intro q y₀ hq hq'
    have hqτ : q ≫ f ≫ ρ = spMap σ.toRingHom ≫ q := by
      apply hχ.1.hom_ext
      · rw [Category.assoc, hτχ, hq, Category.assoc, hq, ← Category.assoc, hs]
      · show (q ≫ f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = (spMap σ.toRingHom ≫ q) ≫ pullback.snd X.hom (spMap ev)
        rw [Category.assoc, hτ2, ← Category.assoc, hq', Category.assoc, hq', Category.id_comp, Category.comp_id]
    rw [hτ1, ← Category.assoc, hqτ, Category.assoc]

end GlobalTheory.Poinc.Sep.Twist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesSharpReferenceSixteenTerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_iso_exists : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  intro g l hl hodd W hW
  have LL := GlobalTheory.abelianSchemeLaws_all
  choose J hJ Mat κ w w' hTf using GlobalTheory.T.fibre_eighth_power_theta_object_subfield W hW
  have hD := fun gQ : ℕ => @GlobalTheory.T.descend_to_thetaConstant_field LL.1 LL.2 (8 * gQ) (J gQ) (hJ gQ) (Mat gQ) (κ gQ) l (w gQ) (w' gQ) hl hodd
  choose j₀f hj₀f using hD
  refine ⟨(Finset.range (g + 1)).sup j₀f + 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hS C u mo hmo hTh K _ _ ev k₀ hk₀ hrat σ hσ
  have hj1 : 1 ≤ j := by omega
  obtain ⟨bT, t, v, ψ, hSh, hPr, hHT, hψ, hL, htor⟩ :=
    hTf Q.g l hl hodd j hj1 V V₁ hCN hlu Q rfl ρ hρ D e hS C u mo hmo hTh K ev k₀ hk₀ hrat
  have hle : j₀f Q.g ≤ j := by
    have := Finset.le_sup (f := j₀f) (Finset.mem_range.2 (by omega : Q.g < g + 1))
    omega
  have hs : spMap k₀.subtype = spMap k₀.subtype ≫ spMap (RingHom.id k₀) := by
    simp [spMap]
  obtain ⟨t₀, ⟨φ, hφ, hLφ, hpts, -⟩, -⟩ :=
    hj₀f Q.g j hle k₀ bT k₀ K (RingHom.id k₀) k₀.subtype (spMap k₀.subtype) t v hs hSh hPr hHT
  have hσe : σ.toRingHom.comp k₀.subtype = k₀.subtype := RingHom.ext fun r => hσ r r.2
  obtain ⟨f, hf, hfL, hfq⟩ := GlobalTheory.Poinc.Sep.Twist.twist_fibre_iso V₁ D.P.A D.P.L D.P.isLB K ev σ k₀ k₀.subtype hσe t.A t.L t.isLB ψ hψ hL t₀.A t₀.L t₀.isLB φ hφ hLφ
  refine ⟨f, hf, hfL, ?_⟩
  intro y hy q hq1 hq2
  obtain ⟨k, hk⟩ := hy
  obtain ⟨y', hy'1, hy'2⟩ := GlobalTheory.T.torsion_fibre_point_transfer_fixed_model V₁ D.P.A K ev t.A ψ hψ k₀ k₀.subtype t₀.A φ hφ (l ^ k) y hk q hq1 hq2
  haveI : IsAlgClosed k₀ := hk₀
  have hlk : IsUnit ((l ^ k : ℕ) : k₀) := by
    have h1 : IsUnit (ev (l : V₁)) := hlu.map ev
    have h2 : IsUnit ((l : k₀) : K) := by simpa using h1
    have h3 : IsUnit (l : k₀) := by
      rcases h2.exists_left_inv with ⟨x, hx⟩
      exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx
    simpa using h3.pow k
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.abelianScheme_primeToChar_torsion_rational k₀ K k₀.subtype t₀.A t₀.ab (l ^ k) hlk y' hy'1
  rw [hfq q y₀ (by rw [← hy'2, hy₀]) hq2, hq1]

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesSharpReferenceSixteenTermsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_sharp_reference_sixteen_terms : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists | exact GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerFibreConjugateEvaluationIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_conj_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  intro g l hl hlo W hW
  obtain ⟨jB, hB⟩ := GlobalTheory.T.theta_series_sharp_reference_sixteen_terms g l hl hlo W hW
  obtain ⟨jD, hD⟩ := GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates g l hl hlo W hW
  refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
  obtain ⟨f, h0, h1, h2⟩ :=
    hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
  exact ⟨f, h0, h1, h2,
    hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
      (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerFibreConjugateEvaluationIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  first
  | exact @GlobalTheory.Poinc.Sep.sharp_fibre_conj_iso
  | intro g l hl hlo W hW
    obtain ⟨jB, hB⟩ := GlobalTheory.T.theta_series_sharp_reference_sixteen_terms g l hl hlo W hW
    obtain ⟨jD, hD⟩ := GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates g l hl hlo W hW
    refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
    obtain ⟨f, h0, h1, h2⟩ :=
      hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
    exact ⟨f, h0, h1, h2,
      hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
        (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩
end
