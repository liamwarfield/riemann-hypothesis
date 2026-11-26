module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

def NoCommonZeroSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → 4 * DF w + 4 ≤ T.Q.l.M →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
      ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeF
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem eig_basis_of_full {x : Sp S ⟶ Xo.X} (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, IsTanAt x (u τ i)) (heig : ∀ τ i, IsEigAt c τ (u τ i))
    (hfull : ∀ m : TanM x Xo.univ.t.G, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S,
      m = ∑ k, a k • tvOf (hu k.1 k.2))
    (τ : E →+* ℂ) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (hwe : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w := by
  classical
  obtain ⟨a, ha, ha_uniq⟩ := hfull (tvOf hw)
  obtain ⟨α, hα, -, -⟩ := exists_sepElt c.F.val.toRingHom (fun τ => embK c τ)
    (fun τ a => rfl)
  obtain ⟨mm, hmm_def⟩ : ∃ mm : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm = fun τ' => ∑ i, a ⟨τ', i⟩ • tvOf (hu τ' i) := ⟨_, rfl⟩
  obtain ⟨mm', hmm'_def⟩ : ∃ mm' : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm' = fun τ' => if τ' = τ then tvOf hw else 0 := ⟨_, rfl⟩
  have hmm : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm τ') := by
    intro τ'
    rw [hmm_def]
    exact eig_comb τ' (fun i => tvOf (hu τ' i))
      (fun i => (eigAt_iff (c := c) (hu τ' i) τ').1 (heig τ' i)) (fun i => a ⟨τ', i⟩)
  have hmm' : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm' τ') := by
    intro τ'
    rw [hmm'_def]
    show IsEigV _ _ (if τ' = τ then tvOf hw else 0)
    by_cases h : τ' = τ
    · rw [if_pos h, h]
      exact (eigAt_iff (c := c) hw τ).1 hwe
    · rw [if_neg h]
      show ∀ b, _ = _
      intro b
      rw [map_zero, smul_zero]
  have hsum : ∑ τ', mm τ' = tvOf hw := by
    rw [hmm_def, ha, Fintype.sum_sigma]
  have hsum' : ∑ τ', mm' τ' = tvOf hw := by
    rw [hmm'_def]
    simp
  have h1 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm hmm τ
  have h2 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm' hmm' τ
  rw [hsum] at h1
  rw [hsum'] at h2
  have key : tvOf hw = mm τ := by
    rw [← h1, h2, hmm'_def]
    simp
  refine ⟨fun i => a ⟨τ, i⟩, (combAt_iff (u τ) (hu τ) _ hw).2 ?_, ?_⟩
  · rw [key, hmm_def]
  · intro b hb
    rw [combAt_iff (u τ) (hu τ) b hw] at hb
    let a' : (Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) → S := fun k =>
      if h : k.1 = τ then b (Fin.cast (congrArg Dw.mult h) k.2) else 0
    have ha' : tvOf hw = ∑ k, a' k • tvOf (hu k.1 k.2) := by
      rw [hb, Fintype.sum_sigma, Finset.sum_eq_single τ]
      · simp [a']
      · intro τ' _ hne
        simp [a', hne]
      · simp
    have hA := ha_uniq a' ha'
    funext i
    have hi := congrFun hA ⟨τ, i⟩
    simpa [a'] using hi

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X0 : Scheme.{0}} {R : Type} [CommRing R] (x0 : Sp R ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x0 Φ)

theorem epsScaleR_comp_alg (a : R) :
    (epsScaleR a).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

def scK (a : R) (p : epsR R ⟶ G') : epsR R ⟶ G' :=
  Over.homMk (spMap (epsScaleR a) ≫ p.left) (by
    rw [Category.assoc, Over.w p]
    show spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap, epsScaleR_comp_alg])

variable {x0}

theorem push_inj : Function.Injective (pushHom h (epsR R)) := by
  intro p q hpq
  have e : p.left ≫ Φ = q.left ≫ Φ := congrArg (fun V => V.left) hpq
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e ((Over.w p).trans (Over.w q).symm)

theorem push_surj (V : overAt x0 (DualNumber R) ⟶ G) : ∃ p, pushHom h (epsR R) p = V :=
  ⟨Over.homMk (h.1.lift V.left (epsR R).hom (Over.w V)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_scK (a : R) (p : epsR R ⟶ G') : pushHom h (epsR R) (scK a p) = smT x0 a (pushHom h (epsR R) p) :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem scK_zero_iff (p : epsR R ⟶ G') : IsTangent p ↔ scK 0 p = 1 := by
  have e0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsR R ⟶ G').left) = spMap (algebraMap R (DualNumber R)) ≫ η[G'].left := by
    rw [Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  constructor
  · intro hp
    apply Over.OverMorphism.ext
    show spMap (epsScaleR 0) ≫ p.left = _
    rw [e1, e0, ← spMap_comp_spMap, Category.assoc, hp]
  · intro hp
    have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ V.left) hp
    rw [e1, ← Category.assoc, e2, Category.id_comp] at this
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p.left = η[G'].left
    rw [← this]
    show _ = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (spMap (epsScaleR 0) ≫ p.left)
    rw [e0, ← spMap_comp_spMap]
    simp only [← Category.assoc, e2, Category.id_comp]

theorem isTangent_iff (p : epsR R ⟶ G') : IsTangent p ↔ smT x0 0 (pushHom h (epsR R) p) = 1 := by
  rw [scK_zero_iff, ← push_scK h, ← map_one (pushHom h (epsR R))]
  exact (push_inj h).eq_iff.symm

theorem isLieComb_iff {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G')) (w : epsR R ⟶ G') :
    IsLieComb c v w ↔ pushHom h (epsR R) w = combT x0 (fun i => pushHom h (epsR R) (v i)) c := by
  have hprod : ∀ u : Fin m → (epsR R ⟶ G'), pushHom h (epsR R) (List.ofFn u).prod =
      ∏ i, pushHom h (epsR R) (u i) := fun u => by
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show u i = scK (c i) (v i) from Over.OverMorphism.ext (hu i), push_scK]
  · intro hw
    refine ⟨fun i => scK (c i) (v i), fun i => rfl, push_inj h ?_⟩
    rw [hw, hprod]
    exact Finset.prod_congr rfl fun i _ => (push_scK h _ _).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


variable (Xo : Moduli Dw l) (c : Coeff l) in
def BcLieAnySt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber K) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → K,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo : Moduli Dw l} {c : Coeff l}

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FinExtIn
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def CDVRExtSt : Prop :=
  ∀ (T : CDVR), T.FinRes → ∀ (K : Type) [Field K] (jK : T.Fr →+* K),
    (letI := jK.toAlgebra; FiniteDimensional T.Fr K) →
    ∃ (T' : CDVR) (κ : K →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (κ (jK a)) = (e' : ℤ) * vV T.V a) ∧ T'.FinRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IntFrBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (yI : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e' : ℕ), 0 < e' →
    (∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a) →
    ∃ yI' : IntFr Xo c T' (iT.comp io),
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtRedPf
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def WtRed : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

theorem wtRed_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) (hW : WtField Xo c) (hB : FrBCFieldSt Xo c) : WtRed Xo c := by
  intro a n f hf S _ _ _ t y y' hb
  have hN := evNat_of Xo c hWD hA
  rw [← sub_eq_zero]
  set d := evR Xo c f y' - wchar (ex Dw a n) t * evR Xo c f y with hd
  have hP : ∀ P : Ideal S, P.IsPrime → d ∈ P := by
    intro P hPp
    have := hPp
    let ρ : S →+* FractionRing (S ⧸ P) := (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
    let _ : Algebra c.F (FractionRing (S ⧸ P)) := (ρ.comp (algebraMap c.F S)).toAlgebra
    let φ : S →ₐ[c.F] FractionRing (S ⧸ P) := { ρ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hB S y (FractionRing (S ⧸ P)) φ
    obtain ⟨z', hz'⟩ := hB S y' (FractionRing (S ⧸ P)) φ
    have hbz := frBorBC (Xo := Xo) (c := c) S (FractionRing (S ⧸ P)) φ t y y' z z' hb hz hz'
    have e1 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y z hz
    have e2 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y' z' hz'
    have e3 := hW a n f hf (FractionRing (S ⧸ P)) _ z z' (hA _ z) (hA _ z') hbz
    have hw : φ (wchar (ex Dw a n) t) = wchar (ex Dw a n) (fun i => Units.map (φ : S →* FractionRing (S ⧸ P)) (t i)) := by
      simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]
    have h0 : φ d = 0 := by
      rw [hd, map_sub, map_mul, ← e1, ← e2, e3, hw, sub_self]
    have h1 : algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P d) = 0 := h0
    have h2 : Ideal.Quotient.mk P d = 0 :=
      (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))) (by rw [h1, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hnil : d ∈ nilradical S := by
    rw [nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun Q hQ => hP Q hQ
  exact IsReduced.eq_zero d (mem_nilradical.mp hnil)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
