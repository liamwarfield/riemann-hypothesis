module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.ev_X {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k} (c : Chart G d)
    (n : ℕ) (i : Fin d) : c.ev n (X i) = c.x n i := by
  have hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n))) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i
  show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i
  rw [coe_substAlgHom, subst_X hs, constantCoeff_C]

theorem Chart.isMapOf_add : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k)
    (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k)
    (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ →
    c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  intro p k _ d e G H c c' ν f g φ ψ hν hf hg n j
  have hφ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' f).2 φ hf).1
  have hψ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' g).2 ψ hg).1
  let L : H.A n ⊗[k] H.A n →ₐ[k] G.A n := Algebra.TensorProduct.lift
    (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)
  have hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a) := fun a => by
    have h := congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))
    simp only [toPts_ofConv] at h
    exact h.trans (AlgHom.convMul_apply _ _ a)
  have hy : ∀ i, IsNilpotent (L (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map L
  have ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0 := fun i => by
    cases i with
    | inl i => exact hφ i
    | inr i => exact hψ i
  have hnil : ∀ t, IsNilpotent (c.ev n (X t)) := fun t => by
    rw [Chart.ev_X]; exact c.nil n t
  have h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i) := fun i => by
    cases i with
    | inl i =>
      change c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)
      rw [hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    | inr i =>
      change c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)
      rw [hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha
    (fun i => L (c'.x₂ n i)) hy h1 (ν j)
  have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n)
    (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)
  change c.ev n (subst (Sum.elim φ ψ) (ν j)) = _
  rw [e1, ← e2, hadd]
  exact congrArg L (hν n j)

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPointsStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ → c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_add | exact GlobalTheory.Katz.Chart.isMapOf_add | (intros; apply GlobalTheory.Katz.Chart.isMapOf_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem dbarCoh_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  intro M _ n A
  obtain ⟨h1, hc, hl, -, -⟩ := GlobalTheory.formCalculus M n A
  have h0 : A.IsForm 0 := by simpa using (hc 0 1 1 h1 h1).2.2.1
  have d0 : A.dbar 0 = 0 := by simpa using (hc 0 1 1 h1 h1).2.2.2.2.2.2.2.2
  have e1 : fld A 1 = 1 := rfl
  have d1 : A.dbar 1 = 0 := by
    have h := (hl 1 1 h1 h1).2
    rw [e1, mul_one, mul_one, one_mul] at h
    simpa using h
  have diag : ∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w :=
    fun w hw dw => ⟨hw, hw, dw, dw, 0, h0, by rw [d0, sub_self]⟩
  refine ⟨diag 1 h1 d1, diag, ?_⟩
  rintro c w w' z z' ⟨hw, hw', dw, dw', u, hu, eu⟩ ⟨hz, hz', dz, dz', v, hv, ev⟩
  have es (x : A.Pt → Ev n) : fld A (c • x) = c • fld A x := rfl
  have ea (x y : A.Pt → Ev n) : fld A (x + y) = fld A x + fld A y := rfl
  have em (x y : A.Pt → Ev n) : fld A (x * y) = fld A x * fld A y := rfl
  have ecomm (x y : A.Pt → Ev n) : fld A x * fld A y = fld A y * fld A x := by rw [← em, ← em, mul_comm]
  have hs (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.1
  have ds (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.2.2.2.2.2.2
  have ha (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').1
  have hm (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.1
  have da (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.2.2.2.2.2.1
  refine ⟨⟨hs _ hw, hs _ hw', ?_, ?_, c • u, hs _ hu, ?_⟩,
    ⟨ha _ _ hw hz, ha _ _ hw' hz', ?_, ?_, u + v, ha _ _ hu hv, ?_⟩,
    ⟨hm _ _ hw hz, hm _ _ hw' hz', ?_, ?_, fld A w * v + fld A z' * u, ha _ _ (hm _ _ hw hv) (hm _ _ hz' hu), ?_⟩⟩
  · rw [es, ds _ hw, dw, smul_zero]
  · rw [es, ds _ hw', dw', smul_zero]
  · rw [es, es, ds _ hu, ← eu, smul_sub]
  · rw [ea, da _ _ hw hz, dw, dz, add_zero]
  · rw [ea, da _ _ hw' hz', dw', dz', add_zero]
  · rw [ea, ea, da _ _ hu hv, ← eu, ← ev]
    abel
  · rw [em, (hl w _ hw hz).2, dw, dz, zero_mul, mul_zero, add_zero]
  · rw [em, (hl w' _ hw' hz').2, dw', dz', zero_mul, mul_zero, add_zero]
  · rw [em, em, da _ _ (hm _ _ hw hv) (hm _ _ hz' hu), (hl w _ hw hv).2, (hl z' _ hz' hu).2, dw, dz', ← eu, ← ev,
      zero_mul, zero_mul, zero_add, zero_add, mul_sub, mul_sub, ecomm z' w, ecomm z' w']
    abel

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  first | exact @GlobalTheory.ChernCalc.dbarCoh_algebra | exact GlobalTheory.ChernCalc.dbarCoh_algebra | (intros; apply GlobalTheory.ChernCalc.dbarCoh_algebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem bcMap_isPullback (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L))) (bcMap L f).hom.left f.hom.left
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
  have h1 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)) =
      pullback.snd A.X.hom (spMap (algebraMap K L)) :=
    Over.w ((Over.pullback (spMap (algebraMap K L))).map f.hom)
  have h3 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left :=
    pullback.lift_fst _ _ _
  have h2 : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hout : IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L)))
      (((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)))
      (f.hom.left ≫ B.X.hom) (spMap (algebraMap K L)) := by
    rw [h1, h2]
    exact IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))
  exact IsPullback.of_bot hout h3.symm (IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L)))

theorem isIsogeny_bcMap_iff_and_deg_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K)
    (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  intro K _ L _ _ A B f
  have := GlobalTheory.LevelMap.isFinite_descendsAlong_fpqc
  have sq := bcMap_isPullback K L f
  have hB := IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L))
  have hs : Surjective (spMap (algebraMap K L)) := GlobalTheory.LevelMap.surjective_spMap _
  have hf : Flat (spMap (algebraMap K L)) := GlobalTheory.LevelMap.flat_spMap _
  have hq : QuasiCompact (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact MorphismProperty.of_isPullback (P := @Surjective) hB.flip hs
    · exact MorphismProperty.of_isPullback (P := @Flat) hB.flip hf
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hB.flip hq
  have hiso : IsIsogeny (bcMap L f) ↔ IsIsogeny f :=
    and_congr (MorphismProperty.iff_of_isPullback (P := @IsFinite) sq.flip hQ)
      (MorphismProperty.iff_of_isPullback (P := @Surjective) sq.flip hQ)
  refine ⟨hiso, ?_⟩
  by_cases h : IsIsogeny f
  · obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f h
    have : IsFinite f.hom.left := h.1
    have e : deg (bcMap L f) = (bcMap L f).hom.left.finrank (baseChange L B).origin := if_pos (hiso.2 h)
    rw [e]
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq (baseChange L B).origin).trans (hrk _)
  · have e1 : deg (bcMap L f) = 0 := if_neg (fun h' => h (hiso.1 h'))
    have e2 : deg f = 0 := if_neg h
    rw [e1, e2]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | exact GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem isHeckeChar_mul' {c c' : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (h' : IsHeckeChar D c') :
    IsHeckeChar D (c * c') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_pow' {c : (AE D)ˣ →* Circle} (h : IsHeckeChar D c) (n : ℕ) : IsHeckeChar D (c ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEta_pow' {c : (AE D)ˣ →* Circle} (h : ResEta D c 1) (n : ℕ) : ResEta D (c ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem chi_hecke_res (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i : Fin D.R.m) :
    IsHeckeChar D (G.ch.chi (D.R.m - i)) ∧ ResEta D (G.ch.chi (D.R.m - i)) 0 := by
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hc := G.ch.chi_eq _ h1 h2
  refine ⟨⟨hc.1.1, hc.1.2⟩, ?_⟩
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  rw [pow_zero, GlobalTheory.GridWeil.triv_base hc (G.ch.triv _ h1 h2) a]

theorem rank_parity (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (i j : Fin D.R.m) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW G i j).rank % 2 ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) % 2 = (spW₁ G i j).rank % 2 := by
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [e1, e2]
  obtain ⟨a, ha⟩ := D.R.t_odd
  obtain ⟨b, hb⟩ := odd_sLen D
  simp only [rankV, ha, hb]
  constructor
  · rw [Nat.mod_mod]; ring_nf; omega
  · rw [Nat.mod_mod]

end GlobalTheory.SquareChars

namespace GlobalTheory.SquareChars

theorem square_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t →
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (beta G i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW G i j).rank ∧
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F) : D.host.F →* AF D.host.F)).range
        (alpha G t i j : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _
  obtain ⟨hχ, hχ0⟩ := chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := rank_parity G hL i j
  have hβ : ResEta D (beta G i j) (spW G i j).rank :=
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1)
  have hα : ResEta D (alpha G t i j) (spW₁ G i j).rank :=
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2)
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  exact ⟨isHeckeChar_mul' hχ hη, isHeckeChar_mul' hμ hη,
    GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hβ, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow D.host.F D.host.E h2 _ _ hα⟩

end GlobalTheory.SquareChars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegree
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

open CategoryTheory.Limits MonoidalCategory

theorem one_left_eq {k : Type} [Field k] {X : Over (Sp k)} [MonObj X] (T : Over (Sp k)) :
    (1 : T ⟶ X).left = T.hom ≫ (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ X).left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  rfl

theorem isoSpec_hom_comp_spec {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (g : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem exists_kerPow_zero_finrank_eq_deg : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f →
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  intro k _ A B f hf
  obtain ⟨-, hflat, -, hrank⟩ := isogeny_flat_finrank k A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI := hflat
  let e : Sp k ⟶ B.X.left := (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X)
  let P := pullback f.hom.left e
  let g : P ⟶ Sp k := pullback.snd f.hom.left e
  haveI : IsAffine P := isAffine_of_isAffineHom g
  let H : Type := Γ(P, ⊤)
  letI : Algebra k H := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hg : P.isoSpec.hom ≫ spMap (algebraMap k H) = g := isoSpec_hom_comp_spec g
  have hig : P.isoSpec.inv ≫ g = spMap (algebraMap k H) := by rw [← hg, Iso.inv_hom_id_assoc]
  have hw : (P.isoSpec.inv ≫ pullback.fst f.hom.left e) ≫ A.X.hom = spMap (algebraMap k H) := by
    rw [← Over.w f.hom, Category.assoc, pullback.condition_assoc, he, Category.comp_id, hig]
  let i : ptOver k H ⟶ A.X := Over.homMk (P.isoSpec.inv ≫ pullback.fst f.hom.left e) hw
  have hi : i.left = P.isoSpec.inv ≫ pullback.fst f.hom.left e := rfl
  refine ⟨H, inferInstance, inferInstance, i, ⟨⟨?_, pow_zero i⟩, ?_⟩, ?_⟩
  · ext1
    rw [Over.comp_left, one_left_eq, hi, Category.assoc, pullback.condition, ← Category.assoc, hig]
    rfl
  · intro R _ _ x hx _
    have hx' : x.left ≫ f.hom.left = spMap (algebraMap k R) ≫ e := by
      have := congrArg Over.Hom.left hx
      rw [Over.comp_left, one_left_eq] at this
      exact this
    let l : Sp R ⟶ P := pullback.lift x.left (spMap (algebraMap k R)) hx'
    obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (l ≫ P.isoSpec.hom)
    have hc : CommRingCat.ofHom (algebraMap k H) ≫ φ0 = CommRingCat.ofHom (algebraMap k R) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, Category.assoc, hg]
      exact pullback.lift_snd _ _ _
    let φ : H →ₐ[k] R :=
      { φ0.hom with commutes' := fun c => congrArg (fun u => u.hom c) hc }
    have hφ : spMap φ.toRingHom = l ≫ P.isoSpec.hom := hφ0
    refine ⟨φ, ?_, fun ψ hψ => ?_⟩
    · change spMap φ.toRingHom ≫ i.left = x.left
      rw [hφ, hi, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    · have h1 : spMap ψ.toRingHom ≫ P.isoSpec.inv = l := by
        apply pullback.hom_ext
        · rw [Category.assoc, ← hi]
          exact hψ.trans (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hig, pullback.lift_snd]
          change Spec.map _ ≫ Spec.map _ = Spec.map _
          rw [← Spec.map_comp]
          congr 1
          ext c
          exact ψ.commutes c
      have h2 : spMap ψ.toRingHom = spMap φ.toRingHom := by
        rw [hφ, ← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have h3 := Spec.map_injective h2
      exact AlgHom.ext fun a => congrArg (fun u => u.hom a) h3
  · haveI : IsFinite (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Flat (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Module.Finite k H := by
      rw [← RingHom.finite_algebraMap]
      exact (IsFinite.SpecMap_iff _).1 ‹_›
    let pt : Sp k := IsLocalRing.closedPoint k
    have h1 := Scheme.Hom.finrank_pullback_snd f.hom.left e pt
    rw [hrank] at h1
    rw [← h1]
    change _ = Scheme.Hom.finrank g pt
    rw [← hg, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl

end GlobalTheory.AV.KerPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsogenyKernelFiniteAlgebraFinrankEqDegreeStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | exact GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_zero_finrank_eq_deg; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoord
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoord
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobCoord

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem connectedPDivGroupChart_eval_nilpotent_pair (c : Chart G d) (n : ℕ) {B : Type} [CommRing B] [Algebra k B] {τ : Type} [Finite τ]
    (E : MvPowerSeries τ k →ₐ[k] B) (hE : ∀ t, IsNilpotent (E (X t)))
    (u v : Fin d → MvPowerSeries τ k) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (g : G.A n ⊗[k] G.A n →ₐ[k] B)
    (hgu : ∀ i, E (u i) = g (c.x n i ⊗ₜ 1)) (hgv : ∀ i, E (v i) = g (1 ⊗ₜ c.x n i))
    (s : MvPowerSeries (Fin d ⊕ Fin d) k) : E (at2 s u v) = g (c.ev₂ n s) := by
  have hy : ∀ j, IsNilpotent (g (c.x₂ n j)) := fun j => (c.nil₂ n j).map g
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) B).1 τ E hE (Sum.elim u v)
    (by rintro (i | i) <;> simp [hu, hv]) (fun j => g (c.x₂ n j)) hy
    (by rintro (i | i) <;> simp [Chart.x₂, hgu, hgv]) s
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 B g (c.x₂ n) (c.nil₂ n)
    (fun j => g (c.x₂ n j)) hy (fun _ => rfl) s
  unfold at2
  rw [h1, Chart.ev₂, h2]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

variable (k : Type) [CommRing k] (A : Type) [CommRing A] [Bialgebra k A]

abbrev gSumL : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A))

abbrev gSumR : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Bialgebra.comulAlgHom k A)

abbrev gFst : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Algebra.TensorProduct.includeLeft (S := k))

theorem algAssoc_apply (w : (A ⊗[k] A) ⊗[k] A) :
    Algebra.TensorProduct.assoc k k k A A A w = TensorProduct.assoc k A A A w := by
  induction w with
  | tmul x b =>
    induction x with
    | tmul a a' => simp
    | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumL_apply (t : A ⊗[k] A) :
    gSumL k A t = TensorProduct.assoc k A A A (Coalgebra.comul.rTensor A t) := by
  induction t with
  | tmul a b => simp [algAssoc_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumR_apply (t : A ⊗[k] A) : gSumR k A t = Coalgebra.comul.lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_apply (t : A ⊗[k] A) :
    gFst k A t = ((TensorProduct.mk k A A).flip 1).lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_eq_assoc (t : A ⊗[k] A) :
    gFst k A t = Algebra.TensorProduct.assoc k k k A A A (t ⊗ₜ 1) := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_tmul]

theorem cobTwo_eq (t : A ⊗[k] A) : cobTwo k A t =
    Algebra.TensorProduct.includeRight t - gSumL k A t + gSumR k A t - gFst k A t := by
  rw [cobTwo_apply, gSumL_apply, gSumR_apply, gFst_apply, Algebra.TensorProduct.includeRight_apply]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

theorem evA_cob2_eq_cobTwo_and_op_assoc : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n))
      (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)),
    (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧
      ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  intro p k _ d G c μ hμ n h
  have hX := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k _ _ _ h
  have hE : ∀ t, IsNilpotent (evA k _ h (X t)) := fun t => by rw [hX]; exact h t
  have hμ0 := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1
  have e1 : ∀ i, evA k _ h (x1 i) = c.x n i ⊗ₜ 1 := fun i => hX (Sum.inl i)
  have e2 : ∀ i, evA k _ h (x2 i) = 1 ⊗ₜ (c.x n i ⊗ₜ 1) := fun i => hX (Sum.inr (Sum.inl i))
  have e3 : ∀ i, evA k _ h (x3 i) = 1 ⊗ₜ (1 ⊗ₜ c.x n i) := fun i => hX (Sum.inr (Sum.inr i))
  have c1 : ∀ i, constantCoeff (x1 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c2 : ∀ i, constantCoeff (x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c3 : ∀ i, constantCoeff (x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have cop : ∀ u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k,
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    have hs : ∀ j, constantCoeff (Sum.elim u v j) = 0 := by rintro (j | j) <;> simp [hu, hv]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ0 i)
  have o12 : ∀ i, evA k _ h (op μ x1 x2 i) = gFst k (G.A n) (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n)) (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def])
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have o23 : ∀ i, evA k _ h (op μ x2 x3 i) =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have a2 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE (op μ x1 x2) x3 (cop _ _ c1 c2) c3 (gSumL k (G.A n))
    (fun j => by rw [o12, gFst_eq_assoc]; simp)
    (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def])
  have a3 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 (op μ x2 x3) c1 (cop _ _ c2 c3) (gSumR k (G.A n))
    (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [o23]; simp)
  refine ⟨fun s => ?_, fun i => ?_⟩
  · have a1 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]) s
    have a4 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n))
      (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) s
    rw [cob2, map_sub, map_add (f := _), map_sub, a1, a2, a3, a4, cobTwo_eq]
  · change evA k _ h (at2 (μ i) (op μ x1 x2) x3) = evA k _ h (at2 (μ i) x1 (op μ x2 x3))
    rw [a2, a3, hμ n i, gSumL_apply, gSumR_apply, Coalgebra.coassoc_apply]

end GlobalTheory.Katz.CobCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoordStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧ ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  first | exact @GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc | exact GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc | (intros; apply GlobalTheory.Katz.CobCoord.evA_cob2_eq_cobTwo_and_op_assoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvaria
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvaria
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj.FlatDep
open GlobalTheory.RootEx

variable {k : Type} [Field k]

theorem stepPt_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) :
    stepPt (x₀ + a₀) u = stepPt x₀ u + fromBlocks a₀ 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> (simp [stepPt, basePt]; try abel)

variable {G : Grid k}

theorem colVar_add (x a : ColArgs G) (u : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) :
    colVar (x + a) u j r = colVar x u j r := by
  simp [colVar, stepPt_add]

theorem rowVar_add (x a : ColArgs G) (u : Vars G) (j : ℕ) (s : Fin (topRank G j)) :
    rowVar (x + a) u j s = rowVar x u j s + if j < G.m - 1 then 0 else a j (topLast G (j + 1)) s := by
  unfold rowVar
  split_ifs with h
  · simp [stepPt_add]
  · simp

theorem ch_add {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (x₀ a₀ : Matrix n n' k) (u : StepVar n c n' → k) : ch (stepPt (x₀ + a₀) u) = ch (stepPt x₀ u) := by
  simp [ch, stepPt_add]

theorem phase_add (x a : ColArgs G) (u : Vars G) : phase (x + a) u = phase x u +
    ∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0 else
      a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0 := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, ch_add]
  by_cases hE : Even (G.m - 2 - (j : ℕ))
  · simp only [if_pos hE, rowVar_add, colVar_add, add_mul, Finset.sum_add_distrib, add_assoc]
  · simp only [if_neg hE, add_zero]

section Loc
variable [ValuativeRel k] (hs : 1 ≤ G.s)

omit [ValuativeRel k] in
theorem mem_opp_theta {j : ℕ} (hj : j < G.m) : Edge.theta G.m j ∈ oppositePath G.m := by
  simp [oppositePath]; omega

omit [ValuativeRel k] in
theorem mem_opp {b : Edge} (hb : b ∈ oppositePath G.m) :
    (∃ i, i < G.m ∧ b = .ex i G.m) ∨ ∃ j, j < G.m ∧ b = .theta G.m j := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact .inl ⟨i, hi, rfl⟩
  · exact .inr ⟨j, hj, rfl⟩

omit [ValuativeRel k] in
theorem downMap_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) {j : ℕ} (hj : j < G.m) :
    downMap hs x u j = downMap hs x' u j := by
  unfold downMap; rw [hx j hj]

omit [ValuativeRel k] in
theorem fill_congr {x x' : ColArgs G} {y y' : RowArgs G} (hx : ∀ j, j < G.m → x j = x' j)
    (hy : ∀ i, i < G.m → y i = y' i) (u : Vars G) {b : Edge} (hb : b ∈ oppositePath G.m) :
    fill hs x y u b = fill hs x' y' u b := by
  rcases mem_opp hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [fill_ex, fill_ex, hy i hi]
  · rw [fill_theta, fill_theta, downMap_congr hs hx u hj]

omit [ValuativeRel k] in
theorem phase_congr {x x' : ColArgs G} (hx : ∀ j, j < G.m → x j = x' j) (u : Vars G) :
    phase x u = phase x' u := by
  unfold phase colVar rowVar
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := hx j (by have := j.2; omega)
  have h2 := hx (j + 1) (by have := j.2; omega)
  rw [h1, h2]

theorem fromBlocks_le {n n' m m' : Type*} {A : Matrix n n' k} {t : ValueGroupWithZero k}
    (hA : ∀ r s, valuation k (A r s) ≤ t) (r : n ⊕ m) (s : n' ⊕ m') :
    valuation k (fromBlocks A 0 0 (0 : Matrix m m' k) r s) ≤ t := by
  rcases r with r | r <;> rcases s with s | s <;> simp [hA]

theorem fill_sub_le {x a : ColArgs G} {y b : RowArgs G} {t : ValueGroupWithZero k}
    (ha : ∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ t) (hb : ∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ t)
    (u : Vars G) {c : Edge} (hc : c ∈ oppositePath G.m) (r : Fin (G.rank c.tgt)) (s : Fin (G.rank c.src)) :
    valuation k ((fill hs (x + a) (y + b) u - fill hs x y u) c r s) ≤ t := by
  rcases mem_opp hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Pi.sub_apply, fill_ex, Matrix.sub_apply, transpose_apply, Pi.add_apply, Matrix.add_apply,
      add_sub_cancel_left]
    exact hb i hi s r
  · simp only [Pi.sub_apply, fill_theta, Matrix.sub_apply, transpose_apply]
    unfold downMap
    split_ifs with h h'
    · simp only [reindex_apply, submatrix_apply, Pi.add_apply, stepPt_add, Matrix.add_apply, add_sub_cancel_left]
      exact fromBlocks_le (ha j hj) _ _
    · simp only [submatrix_apply, Pi.add_apply, Matrix.add_apply, add_sub_cancel_left]
      exact ha j hj _ _
    · simp

omit [ValuativeRel k] in
theorem exists_colVar_eq (x : ColArgs G) (y : RowArgs G) (u : Vars G) (j : Fin (G.m - 1))
    (r : Fin (topRank G (j + 1))) : ∃ p q, colVar x u j r = fill hs x y u (.theta G.m j) p q := by
  refine ⟨frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega)
      (.inr ⟨(G.m - 2 - j) / 2, by omega⟩),
    frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) (.inl r), ?_⟩
  rw [fill_theta, transpose_apply, downMap, dite_eq_left j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, colVar, Fin.eta]

end Loc
end GlobalTheory.FunObj.FlatDep

open GlobalTheory.FunObj.FlatDep in
theorem GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hψ hT
  obtain ⟨n, hA, hB⟩ := GlobalTheory.T.gridMovedTensor_bounded_support_locallyConstant G ϖ e T keep g hϖ hT
  refine ⟨fun x x' y y' hx hy => ?_, n, fun x a y b ha hb => ?_⟩
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    rw [phase_congr hx u]
    have hTe : T (G.moveArgs .one g (fill hs x y u)) = T (G.moveArgs .one g (fill hs x' y' u)) :=
      hT.1 fun c hc => by simp only [Grid.moveArgs, fill_congr hs hx hy u hc]
    simp only [moved, Grid.pathAct, hTe]
  · unfold flatTensor
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [flatIntegrand]
    have hS : moved G keep g T (fill hs (x + a) (y + b) u) = moved G keep g T (fill hs x y u) := by
      have h := hB (fill hs x y u) (fill hs (x + a) (y + b) u - fill hs x y u)
        fun c hc r s => fill_sub_le hs ha hb u hc r s
      rwa [add_sub_cancel] at h
    rw [hS]
    by_cases h0 : moved G keep g T (fill hs x y u) = 0
    · simp [h0]
    have hbd := hA _ h0
    have hD : ∀ (j : Fin (G.m - 1)) r, valuation k ((if (j : ℕ) + 1 < G.m - 1 then 0 else
        a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r) ≤ 1 := by
      intro j r
      have := j.2
      split_ifs with h
      · simp
      · obtain ⟨p, q, hpq⟩ := exists_colVar_eq hs x y u j r
        rw [map_mul, hpq]
        calc _ ≤ valuation k ((ϖ ^ n : kˣ) : k) * valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) :=
              mul_le_mul' (ha _ (by omega) _ _) (hbd _ (mem_opp_theta (by omega)) _ _)
          _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hsum : valuation k (-(∑ j : Fin (G.m - 1), if Even (G.m - 2 - j) then ∑ r, (if (j : ℕ) + 1 < G.m - 1 then 0
        else a (j + 1) (topLast G (j + 1 + 1)) r) * colVar x u j r else 0)) ≤ valuation k ((1 : kˣ) : k) := by
      rw [Valuation.map_neg, Units.val_one, map_one]
      refine (valuation k).map_sum_le fun j _ => ?_
      by_cases hE : Even (G.m - 2 - (j : ℕ))
      · rw [if_pos hE]; exact (valuation k).map_sum_le fun r _ => hD j r
      · rw [if_neg hE, map_zero]; exact zero_le'
    rw [phase_add, neg_add, AddChar.map_add_eq_mul, (hψ 1).2 le_rfl _ hsum, mul_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDependsBelowAndSmallTranslationInvariaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_depends_below_and_small_translation_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → HasConductor ψ 1 → G.IsTensor ϖ e (oppositePath G.m) T → (∀ (x x' : ColArgs G) (y y' : RowArgs G), (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → flatTensor hs ψ ν (moved G keep g T) x y = flatTensor hs ψ ν (moved G keep g T) x' y') ∧ ∃ n : ℕ, ∀ (x a : ColArgs G) (y b : RowArgs G), (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → flatTensor hs ψ ν (moved G keep g T) (x + a) (y + b) = flatTensor hs ψ ν (moved G keep g T) x y := by
  first | exact @GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per | exact GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per | (intros; apply GlobalTheory.FunObj.FlatDep.flatTensor_dep_and_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrou
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrou
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((GlobalTheory.T.chart_square_coordinates_present_levels p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrouStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k'), c.IsLawOf μ → c'.IsLawOf ν → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  first | exact @GlobalTheory.Katz.isHom_map_of_semiHom_ev | exact GlobalTheory.Katz.isHom_map_of_semiHom_ev | (intros; apply GlobalTheory.Katz.isHom_map_of_semiHom_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrame
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GenericCell

theorem upM_zero_eq {ι : Type} {m : ι → ℕ} {K : Type} [Field K] : upM (0 : Cell m → K) = 1 := by
  funext τ
  ext a b
  simp only [upM, upU, Matrix.of_apply, Pi.zero_apply, Pi.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem exists_inCell_genericPoint : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  intro F _ X Y ι _ m E E' φ f hR z A hA
  have hgX : A ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA
  have hcp : (ratOf X).pt (IsLocalRing.closedPoint X.Fn) = genericPoint X.X := Scheme.fromSpecStalk_closedPoint
  obtain ⟨p, ⟨hpf, hpb⟩, -⟩ := hR.lifts X.Fn (ratOf X).pt A (hcp ▸ hgX) (upM 0) (by rw [upM_zero_eq]; exact Par.one)
  have hfp : f (p (IsLocalRing.closedPoint X.Fn)) = genericPoint X.X := by
    have h1 := congrArg (fun g : Sp X.Fn ⟶ X.X => g (IsLocalRing.closedPoint X.Fn)) hpf
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1.trans hcp
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A X.Fn p (hfp ▸ hgX) 0).1 hpb
  refine ⟨u, Fr.mem_of_specializes (hfp ▸ hgX) ((genericPoint_specializes _).map f.continuous), Fr.mem_genericPoint hu⟩

end GlobalTheory.FlagCell2.GenericCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFlagInCellOfFrameStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_flag_in_cell_of_frame : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint | exact GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint | (intros; apply GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint <;> assumption)
end
end
