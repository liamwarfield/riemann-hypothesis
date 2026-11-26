module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerComparison
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogPole.EigNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in
theorem exists_eigBasis_at (TF : TorFlag Xo c) (p : TF.Y.X) :
    ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
      (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), p ∈ U.1 ∧ IsEigBasis TF U e v := by
  classical
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  let L : Type := TF.Y.X.presheaf.stalk p
  letI : Algebra Γ(TF.Y.X, U₁) L := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
  have hloc := hU₁.isLocalization_stalk ⟨p, hp₁⟩
  let ρ₁ : Γ(TF.Y.X, U₁) →+* L := algebraMap _ _
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = TF.Y.X.fromSpecStalk p := by
    rw [← hU₁.fromSpecStalk_eq_fromSpecStalk hp₁]
    rfl
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let φ₀ : c.F →+* L := (Spec.preimage (TF.Y.X.fromSpecStalk p ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = TF.Y.X.fromSpecStalk p ≫ TF.Y.s := Spec.map_preimage _
  obtain ⟨f₀'⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y L φ₀
    (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) (by rw [Category.assoc, hs, hφ₀])
  have e0 : (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) ≫ GlobalTheory.Toroidal.genι TF.Y =
      TF.Y.X.fromSpecStalk p := by simp
  obtain ⟨f₀⟩ : Nonempty (GlobalTheory.ShFam.EigFrame TF.Y φ₀ (TF.Y.X.fromSpecStalk p)) := e0 ▸ ⟨f₀'⟩
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, hφ₀])
  have vec_bc_of_chart {S : Type} [CommRing S] {x : Sp S ⟶ TF.Y.X} {n : ℕ}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj TF.Y.t.G}
      (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart ((Over.pullback x).obj TF.Y.t.G))
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc)
      {S' : Type} [CommRing S'] (ψ : S →+* S') {x' : Sp S' ⟶ TF.Y.X} (h : x' = spMap ψ ≫ x) :
      ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶ (Over.pullback x').obj TF.Y.t.G),
        ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc' ∧
        ∀ cc : Fin n → S, vec TF.Y.t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec TF.Y.t x xc cc := by
    subst h
    letI : Algebra S S' := ψ.toAlgebra
    obtain ⟨x₁, hx₁, hcomp⟩ := LieChart.univChart_baseChange_of_chart (R := S) (R' := S') _ C n xc hx
    have h₁ := IsGrpPullback.comp
      (isGrpPullback_pullback ((Over.pullback x).obj TF.Y.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
      (isGrpPullback_pullback TF.Y.t.G x)
    obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
      (isGrpPullback_pullback TF.Y.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
    refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
    have key : (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
        (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := TF.Y.X.fromSpecStalk p)
    (by rw [hx₁, Category.comp_id, hK])
  have exists_projectors (c : Coeff l) {L : Type} [CommRing L] (φ : c.F →+* L) {x : Sp L ⟶ TF.Y.X} {n : ℕ}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj TF.Y.t.G}
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc) :
      ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) L, ∀ {k : Type} [CommRing k] (ψ : L →+* k) {x' : Sp k ⟶ TF.Y.X}
        {xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x').obj TF.Y.t.G}
        (hx' : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc'), (∀ cc : Fin n → L, vec TF.Y.t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec TF.Y.t x xc cc) → ∀ τ v, (P τ).map ψ *ᵥ v ∈ eig c (ψ.comp φ) hx' τ ∧
          (v ∈ eig c (ψ.comp φ) hx' τ → (P τ).map ψ *ᵥ v = v) := by
    classical
    have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    letI : Algebra c.F L := φ.toAlgebra
    refine ⟨fun τ => LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx) (embK c) α τ), fun {k} _ ψ {x' xc'} hx' hv τ => ?_⟩
    letI : Algebra c.F k := (ψ.comp φ).toAlgebra
    have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ m) := fun m =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m)
    have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) m → ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ m = m := fun m hm => by
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (rho hx') (embK c) α hinj (Pi.single τ m) (fun τ' => by
        by_cases h : τ' = τ
        · subst h; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
      rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
    have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (ψ ∘ cc) = ψ ∘ rho hx a cc :=
      fun a cc => vec_inj hx' (by
        show vec TF.Y.t _ xc' (ReciprocityTheory.ChartRestriction.G.Chart.tmap hx' _ _) = vec TF.Y.t _ xc' (_ ∘ ReciprocityTheory.ChartRestriction.G.Chart.tmap hx _ _)
        rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
    have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (ψ ∘ cc) = ψ ∘ (rho hx α ^ j) cc := fun j => by
      induction j with
      | zero => exact fun _ => rfl
      | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
    have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (ψ ∘ cc) =
        ψ ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
        funext j; simp
      | monomial j a =>
        rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
          Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        funext i
        exact (map_mul ψ _ _).symm
    have hP : (LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx) (embK c) α τ)).map ψ =
        LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ) := by
      ext i j
      have s : (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 := funext fun r => by
        by_cases hj : r = j <;> simp [hj, Pi.single_apply]
      rw [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, s]
      exact (congrFun (pr _ _) i).symm
    intro v
    rw [hP, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff,
      ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    exact ⟨e₁ v, e₂ v⟩

  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)
  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F L := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → L, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    have h1 : (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i) =
        (Pi.basisFun L (Fin n)).toMatrix (bK.reindex e) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, bK]
    rw [h1]
    exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  obtain ⟨g, hg, s0, B₀, -, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  have hU : IsAffineOpen (TF.Y.X.basicOpen g) := hU₁.basicOpen g
  have hU' : TF.Y.X.basicOpen g ∈ TF.Y.X.affineOpens := hU
  have hpU : p ∈ TF.Y.X.basicOpen g := by
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units L (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g)).op).hom
  have hψg : IsUnit (ψ g) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g) := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g) := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, n, e, fun j => vec TF.Y.t _ xcU (cU j), hpU, fun j => vec_tan hxU _, fun w' hw' => ?_,
    fun a τ i => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hq := hQ0 (e ⟨τ, i⟩)
    simp only [Equiv.symm_apply_apply] at hq
    have hfix : (Pr τ).map ψ *ᵥ cU (e ⟨τ, i⟩) = cU (e ⟨τ, i⟩) := by
      rw [hcUd, Matrix.mulVec_smul, hq]
    have hmem := (hPr ψ hxU hcU τ (cU (e ⟨τ, i⟩))).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) :=
      (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)) (cU (e ⟨τ, i⟩))).2 hmem a
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single (e ⟨τ, i⟩) (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a) • cU (e ⟨τ, i⟩))) := by
      rw [comb_iff hxU, Finset.sum_eq_single (e ⟨τ, i⟩) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ _) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    exact hc

end GlobalTheory.LogPole.EigNear

theorem GlobalTheory.LogPole.exists_eigBasis_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  intro E _ _ _ H Dw l Xo c TF Z _ y
  exact GlobalTheory.LogPole.EigNear.exists_eigBasis_at TF (toBase TF Z y)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  first | exact @GlobalTheory.LogPole.exists_eigBasis_near | exact GlobalTheory.LogPole.exists_eigBasis_near | (intros; apply GlobalTheory.LogPole.exists_eigBasis_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellFramedPointsTriangularFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellFramedPointsTriangularFrameChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellFrames

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Tri

variable {K : Type} [Field K] {m : ℕ}

theorem lowerTri_inv (A : Matrix (Fin m) (Fin m) K) (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, A i i ≠ 0) :
    (∀ i j, i < j → A⁻¹ i j = 0) ∧ ∀ i, A⁻¹ i i * A i i = 1 := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h), fun i => ?_⟩
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul A hdet) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at e
  · exact e
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA j i h, mul_zero]
    · rw [hB' (OrderDual.toDual_lt_toDual.2 h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem frVec_of_comb {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (e : P'.x = P.x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → S) (h3 : IsCombAt P.x (P.u σ) cf (P'.u σ i)) :
    frVec Y P' hx' σ i = ∑ j, cf j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 h3
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end GlobalTheory.LogPole.CellFrames

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cellFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC K _ _ z hz hk Q hQ
  obtain ⟨-, hWU, -, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hWU (hz hp)
  have hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := Category.assoc _ _ _
  have hQx : frX Q ≫ TF.Y.j = z ≫ toBase TF Z := hQ.over.trans hx
  have hvT : ∀ m, IsTanAtG TF.Y.t (z ≫ toBase TF Z) (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hU) (hv.1 m)
  set Lz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (L σ).map (ev z W hz) with hLzd
  set Nz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (N σ).map (ev z W hz) with hNzd
  have hLd : ∀ σ i, Lz σ i i ≠ 0 := fun σ i => ((hLu σ i).map (ev z W hz)).ne_zero
  have hLt : ∀ σ i j, i < j → Lz σ i j = 0 := fun σ i j h => by
    show ev z W hz (L σ i j) = 0
    rw [hLz σ i j h, map_zero]
  have hLinv := fun σ => CellFrames.lowerTri_inv (Lz σ) (hLt σ) (hLd σ)
  have hNdet : ∀ σ, IsUnit (Nz σ).det := fun σ => by
    rw [Matrix.det_of_upperTriangular (M := Nz σ) (fun i j h => by
      show ev z W hz (N σ i j) = 0
      rw [hNz σ i j h, map_zero])]
    refine IsUnit.prod_univ_iff.2 fun i => ?_
    show IsUnit (ev z W hz (N σ i i))
    rw [hN1, map_one]; exact isUnit_one
  have hLdet : ∀ σ, IsUnit (Lz σ).det := fun σ => by
    rw [Matrix.det_of_lowerTriangular (Lz σ) (fun i j h => hLt σ i j (OrderDual.toDual_lt_toDual.1 h))]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hLd σ i)
  have hAdet : ∀ σ, IsUnit (Lz σ * Nz σ).det := fun σ => by
    rw [Matrix.det_mul]; exact (hLdet σ).mul (hNdet σ)
  have hA : ∀ σ, Lz σ * Nz σ = (L σ * N σ).map (ev z W hz) := fun σ => Matrix.map_mul.symm
  have hvec : ∀ σ i, frVec TF.Y Q hQx σ i =
      ∑ j, (Lz σ * Nz σ) i j • GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩)) := fun σ i => by
    rw [hQ.frVec_eq hx hQx σ]
    have h1 := hcomb K z hz hU hk hx σ i
    have h2 := (GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))) _ _).1 h1
    rw [h2, hA]
    rfl
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K Q (fun σ => (Lz σ * Nz σ)⁻¹) 1
    (fun σ => (Matrix.isUnit_nonsing_inv_det_iff).2 (hAdet σ))
  obtain ⟨P, hP, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K P₀ Nz 1 hNdet
  rw [Units.val_one] at hP₀ hP
  have hQP := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).1 _ _ _ _ _ _ _ hP₀).1 hP
  have hg : (fun σ => Nz σ * (Lz σ * Nz σ)⁻¹) = fun σ => (Lz σ)⁻¹ := funext fun σ => by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hNdet σ), Matrix.one_mul]
  rw [hg, _root_.mul_one] at hQP
  let t : Ix Dw → Kˣ := fun ix => Option.elim ix 1 fun p => Units.mk0 ((Lz p.1 p.2 p.2)⁻¹) (inv_ne_zero (hLd _ _))
  have hP₀x : frX P₀ ≫ TF.Y.j = z ≫ toBase TF Z := by
    rw [eq_frX Q ((frX_fst P₀).trans hP₀.1) (frX_snd P₀)]; exact hQx
  have hU' : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1 := hP₀x ▸ hU
  refine ⟨P₀, P, t, hU', ?_, fun σ i => ?_, hP, fun σ i => ?_⟩
  · refine (GlobalTheory.Frames.frBor_iff_frChg Q P t).2 ⟨fun σ => (Lz σ)⁻¹, fun σ i j h => (hLinv σ).1 i j h,
      fun σ i => eq_inv_of_mul_eq_one_left ((hLinv σ).2 i), ?_⟩
    show GlobalTheory.Frames.FrChg _ ((1 : Kˣ) : K) Q P
    rw [Units.val_one]
    exact hQP
  · show (Lz σ i i)⁻¹ * Lz σ i i = 1
    exact inv_mul_cancel₀ (hLd σ i)
  · have h0 := CellFrames.frVec_of_comb (TF.X.F.inM hk hx) hQx hP₀x hP₀.1 σ i _ (hP₀.2.1 σ i)
    have hI := Matrix.nonsing_inv_mul _ (hAdet σ)
    have key : frVec TF.Y P₀ hP₀x σ i = GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, i⟩)) := by
      rw [h0]
      simp only [hvec, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have e2 : ∀ l, (∑ j, (Lz σ * Nz σ)⁻¹ i j * (Lz σ * Nz σ) j l) = (1 : Matrix _ _ K) i l := fun l => by
        rw [← hI, Matrix.mul_apply]
      simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : (tv (frVec TF.Y P₀ rfl σ i)).left = (tv (frVec TF.Y P₀ hP₀x σ i)).left := rfl
    rw [e1, key, GlobalTheory.LieMet.left_tanOf, ev_congr hP₀x U.1 hU' hU]

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellFramedPointsTriangularFrameChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  first | exact @GlobalTheory.LogPole.exists_cellFrames | exact GlobalTheory.LogPole.exists_cellFrames | (intros; apply GlobalTheory.LogPole.exists_cellFrames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_unit_mul {Y : Scheme.{0}} {V : Y.Opens} (y : Y) (hy : y ∈ V) [IsDomain (Y.presheaf.stalk y)]
    (t d : Γ(Y, V)) (h0 : ger y hy t ≠ 0) (h1 : ger y hy t ∣ ger y hy d) (h2 : ger y hy d ∣ ger y hy t) :
    ∃ (V' : Y.Opens) (_ : y ∈ V') (h : V' ≤ V) (b : Γ(Y, V')), (∀ z hz, IsUnit (ger z hz b)) ∧
      resG Y h t = b * resG Y h d := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hu : IsUnit b := by
    refine IsUnit.of_mul_eq_one a (mul_left_cancel₀ h0 ?_)
    calc ger y hy t * (b * a) = (ger y hy t * a) * b := by ring
      _ = ger y hy t * 1 := by rw [← ha, ← hb, mul_one]
  obtain ⟨O, hO, s, rfl⟩ := Y.presheaf.exists_germ_eq b
  have hm : y ∈ V ⊓ O := ⟨hy, hO⟩
  have e : ger y hm (resG Y inf_le_left t) = ger y hm (resG Y inf_le_right s * resG Y inf_le_left d) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG, hb, mul_comm]
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have l₁ : O' ⊓ Y.basicOpen s ≤ V ⊓ O := inf_le_left.trans i₁.le
  refine ⟨O' ⊓ Y.basicOpen s, ⟨hO', (Y.mem_basicOpen s y hO).2 hu⟩, l₁.trans inf_le_left,
    resG Y (l₁.trans inf_le_right) s, fun z hz => ?_, fun_ext_ger fun z hz => ?_⟩
  · rw [ger_resG]
    exact (Y.mem_basicOpen s z _).1 hz.2
  · have e₂ := congrArg (ger z hz.1) e'
    have a₁ := ger_resG i₁.le z hz.1 (resG Y (inf_le_left : V ⊓ O ≤ V) t)
    have a₂ := ger_resG i₂.le z hz.1 (resG Y (inf_le_right : V ⊓ O ≤ O) s * resG Y (inf_le_left : V ⊓ O ≤ V) d)
    have e₃ := a₁.symm.trans (e₂.trans a₂)
    simp only [map_mul, ger_resG] at e₃ ⊢
    exact e₃

theorem ger_ne_zero {Y : Scheme.{0}} {V O : Y.Opens} (hO : Dense (O : Set Y)) (t : Γ(Y, V))
    (h : ∀ z (hz : z ∈ V), z ∈ O → IsUnit (ger z hz t)) (y : Y) (hy : y ∈ V) : ger y hy t ≠ 0 := by
  intro h0
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y hy hy t 0 (h0.trans (map_zero _).symm)
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty O' O'.isOpen ⟨y, hO'⟩
  have e₂ := congrArg (ger z hz) e'
  have a₁ := ger_resG i₁.le z hz t
  have a₂ := ger_resG i₂.le z hz (0 : Γ(Y, V))
  have e₃ := a₁.symm.trans (e₂.trans a₂)
  rw [map_zero] at e₃
  exact (h z _ hzO).ne_zero e₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem chartFr_congr {TF : TorFlag Xo c} {K : Type} [Field K] [Algebra c.F K] {k : TF.X.F.J} {z z' : Sp K ⟶ TF.X.YY}
    (e : z = z') {hz : ⊤ ≤ z ⁻¹ᵁ TF.X.F.U k} (hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k) {Q : FrPt Xo c K}
    (h : TF.X.F.ChartFr k z hz Q) : TF.X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem det_block {K : Type} [Field K] {m : ℕ} (o : Fin m ≃ HIx Dw (psiSet H))
    (G : (Fin m ⊕ VIx Dw) → TIx Dw (psiSet H) → K) (h0 : ∀ i b, G (.inl i) (.inr b) = 0)
    (h1 : (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b)).det = 1) :
    (Matrix.of fun a b => G (((tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl _))) a) (tanOrd Dw b)).det =
      (Matrix.of fun i j => G (.inl i) (.inl (o j))).det := by
  let e := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let A : Matrix (Fin m ⊕ VIx Dw) (Fin m ⊕ VIx Dw) K := Matrix.fromBlocks
    (Matrix.of fun i j => G (.inl i) (.inl (o j))) 0 (Matrix.of fun a j => G (.inr a) (.inl (o j)))
    (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b))
  have : (Matrix.of fun a b => G (e a) (tanOrd Dw b)) = A.submatrix e e := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    have hb : tanOrd Dw b = Equiv.sumCongr o (Equiv.refl (VIx Dw)) (e b) := by
      simp only [e, Equiv.trans_apply]
      rcases tanOrd Dw b with k | k <;> simp
    rw [hb]
    rcases e a with i | i <;> rcases e b with j | j <;> simp [A, h0]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, h1, mul_one]

def diagUnit {R : Type} [CommRing R] (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R)
    (h : ∀ σ i, IsUnit (L σ i i)) : Rˣ :=
  ∏ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ), (h q.1 q.2).unit⁻¹ ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 (some q)

theorem map_diagUnit {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (h : ∀ σ i, IsUnit (L σ i i)) (t : Ix Dw → Kˣ)
    (ht : ∀ σ i, (t (some ⟨σ, i⟩) : K) * φ (L σ i i) = 1) :
    (∏ ix, t ix ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 ix).val = φ (diagUnit L h).val := by
  change _ = (Units.map (φ : R →* K) (diagUnit L h)).val
  congr 1
  rw [diagUnit, map_prod, Fintype.prod_option, FlagMod.exOf_none, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_zpow, map_inv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (Units.ext (ht q.1 q.2))


set_option maxHeartbeats 1600000 in
theorem exists_pole (hP : GlobalTheory.CovTop.Hypotheses₂) (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z)
    (V : (Y₀ TF.X Z).Opens) (hy : y ∈ V) :
    ∃ (W : (Y₀ TF.X Z).Opens) (_ : y ∈ W) (_ : W ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι)
      (k : TF.X.F.J) (δ u : Γ(Y₀ TF.X Z, W)),
      W ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧ IsUnit u ∧
      (∀ z (hz : z ∈ W), IsUnit (ger z hz δ) ↔ z ∈ U₀ TF.X Z) ∧
      (∀ (W' : (Y₀ TF.X Z).Opens) (hW' : W' ≤ W) (f : Γ(Y₀ TF.X Z, W')), (∀ z (hz : z ∈ W'), z ∉ U₀ TF.X Z →
        ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) →
        ∀ z (hz : z ∈ W'), ger z (hW' hz) δ ∣ ger z hz f) ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) ho hi,
        ev z W hz δ * H0.val (B := LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle
          ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) z
          (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k) ho hi ω₀.ω = ev z W hz u := by
  obtain ⟨i, hi⟩ := exists_chart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB y
  obtain ⟨U, n, e₀, v, hyU, hv₀⟩ := GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point E H Dw l Xo c TF Z hF y
  obtain ⟨e, W, k, L, N, hv, hyW, hWV, hc⟩ := GlobalTheory.T.exists_bigCell_chartFrame_eigenbasis E H Dw l Xo c TF Z U n e₀ v hv₀ y hyU V hy
  obtain ⟨ε, b, hb⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v _ hv.1 hv.2.1 hv.2.2
  obtain ⟨x, U', hU', hyU', hx, hbd⟩ := GlobalTheory.T.exists_coordinates_logVectorFields_determinant E H Dw l Xo c TF U b _ hyU
  have het := GlobalTheory.T.etale_bigCellCoordinates_flagSpace E H Dw l Xo c TF Z hF U n e v hv W k L N hc
  obtain ⟨s, hs, hcmp⟩ := GlobalTheory.T.kodaira_spencer_comparison hP E H Dw l Xo c TF
  let o : Fin Dw.dim ≃ HIx Dw (psiSet H) :=
    (Fintype.equivFinOfCardEq (FlagTan.card_HIx (FlagTan.isHalf_psiSet H))).symm
  obtain ⟨a, ha, hhor⟩ := GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal E H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨W', hW'a, hyW', hW'⟩ := Opens.isBasis_iff_nbhd.1 (Y₀ TF.X Z).isBasis_affineOpens
    (show y ∈ W ⊓ (toBase TF Z ⁻¹ᵁ U'.1 ⊓ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i) from ⟨hyW, hyU', hi⟩)
  have hW'W : W' ≤ W := hW'.trans inf_le_left
  have hW'U : W' ≤ toBase TF Z ⁻¹ᵁ U'.1 := hW'.trans (inf_le_right.trans inf_le_left)
  have hW'i : W' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i := hW'.trans (inf_le_right.trans inf_le_right)
  let O := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let G : Fin Dw.dim ⊕ VIx Dw → Γ(Y₀ TF.X Z, W) :=
    Sum.elim (fun i => ((toBase TF Z).appLE U.1 W hc.2.1).hom (x i)) (cellCoord N)
  let g : Fin (FlagTan.dimFlag Dw) → Γ(Y₀ TF.X Z, W') := fun a => resG _ hW'W (G (O a))
  have hfr := GlobalTheory.T.isTopFormFrame_base_coordinates_add_variables_etale c.F TF.Y.X (Y₀ TF.X Z) TF.Y.s (toBase TF Z) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) Dw.dim (FlagTan.dimFlag Dw) TF.smooth (VIx Dw) O U.1 U'.1 hU'
    U.2 W W' hW'W hc.1 hW'a hc.2.1 hW'U (cellCoord N) het x hx
  have hJ : IsUnit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g) :=
    ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isUnit_jacobian_iff i hW'a hW'i g).2 hfr
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : IsLocallyNoetherian TF.Y.X := LocallyOfFiniteType.isLocallyNoetherian TF.Y.s
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing TF.Y.X (Y₀ TF.X Z) (toBase TF Z) (VIx Dw) (LogKS.interior TF.Y) U U' hU' W hc.1 hc.2.1
    (cellCoord N) het _ hbd
  let ac : Γ(Y₀ TF.X Z, W') := algX (str₀ TF.X Z) W' (a : c.F)
  have hac : IsUnit ac := (Ne.isUnit (Rat.cast_ne_zero.2 ha)).map _
  refine ⟨W', hyW', hW'W.trans hWV, i, k,
    resG _ hW'W (((toBase TF Z).appLE U.1 W hc.2.1).hom (logDet (fun j => (b j).1) x)),
    ac * resG _ hW'W (diagUnit L hc.2.2.2.2.1).val * (show Γ(Y₀ TF.X Z, W') from
      (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g), hW'i, hW'W.trans hc.2.2.1,
    (hac.mul ((Units.isUnit _).map _)).mul hJ, fun z hz => ?_, fun W'' hW'' f hf z hz => ?_, fun K _ z hz ho hi => ?_⟩
  · rw [ger_resG]
    exact r₁ z (hW'W hz) (hW'U hz)
  · rw [ger_resG]
    exact r₂ W'' (hW''.trans hW'W) (hW''.trans hW'U) f hf z hz
  have eM : toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = inc₀ TF.X Z := Category.id_comp _
  have hzW := FlagMod.le_preimage_mono hW'W hz
  have hU₀ : ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z := fun p hp => by
    have := ho hp
    rw [Modif.off_eq] at this
    exact this
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_map _ hc.2.2.1 hzW
  obtain ⟨_, hch⟩ := exists_chartFr (z ≫ inc₀ TF.X Z) hU₀
  obtain ⟨Q, hQ⟩ := hch k hk
  obtain ⟨P₀, P, t, hU, hQP, ht, hP₀, hB⟩ := GlobalTheory.T.exists_bigCell_framedPoints_triangular_frameChange E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW hk Q hQ
  have ez : z ≫ inc₀ TF.X Z = TF.X.ptY P := FlagMod.FlagCover.eq_ptY (hQ.lies.frBor hQP)
  obtain ⟨w, hw⟩ := (hKS K P).exists_isTanFrame
  have ezM : z ≫ toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = z ≫ inc₀ TF.X Z := by rw [eM]
  choose zw hzw hzO using fun b => exists_tanLift (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) (hw.isDef b)
    (ezM.trans ez) ho
  have hzw' : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ inc₀ TF.X Z = TF.X.ptY (w b) := fun b => by
    exact (congrArg (zw b ≫ ·) eM).symm.trans (hzw b)
  have hkM := ezM ▸ hk
  have key := ω₀.isKS K P Q t w z zw i k W' hW'i g hz (fun b => hzO b W' hz) hkM ho hi (chartFr_congr ezM.symm hkM hQ)
    hQP hw hzw
  obtain ⟨v₁, v₂⟩ := GlobalTheory.T.vertical_tangentFrame_jacobian_det_one E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW P₀ P hU ez hP₀ hB (fun b => w (.inr b))
    (fun b => zw (.inr b)) (fun b => hzO _ W hzW) hw.2 (fun b => hzw' _)
  have eb : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ toBase TF Z = frX (w b) ≫ TF.Y.j := fun b => by
    rw [← Category.assoc, hzw', (TF.X.lies_ptY _).1]
  have hwU : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1 := fun b =>
    eb b ▸ FlagMod.le_preimage_map _ hc.2.1 (hzO b W hzW)
  have hdet : ∀ σ, ((N σ).map (ev z W hzW)).det = 1 := fun σ => by
    rw [Matrix.det_of_upperTriangular fun i j hij => by rw [Matrix.map_apply, hc.2.2.2.2.2.1 σ i j hij, map_zero]]
    simp [hc.2.2.2.2.2.2.1]
  have hh := hhor x K P₀ P hU _ hdet hP₀ hB (fun b => w (.inl b)) (fun b => hwU _) hw.1
  have eP : z ≫ toBase TF Z = frX P₀ ≫ TF.Y.j := by
    rw [← Category.assoc, ez, (TF.X.lies_ptY _).1,
      FlagMod.eq_frX P₀ ((FlagMod.frX_fst P).trans hP₀.1) (FlagMod.frX_snd P)]
  have hblock := det_block o (fun a b => (ev (zw b) W (hzO b W hzW) (G a)).snd) (fun i b => v₂ b _) v₁
  have e₁ : (Matrix.of fun a b => (TangentOrigin.evalPt (zw (tanOrd Dw b)) W' (hzO _ W' hz) (g a)).snd) =
      Matrix.of fun a b => (ev (zw (tanOrd Dw b)) W (hzO _ W hzW) (G (O a))).snd := by
    ext a b
    exact congrArg TrivSqZeroExt.snd (FlagMod.ev_res _ hW'W _ _ _)
  have e₂ : (Matrix.of fun i j => (ev (zw (.inl (o j))) W (hzO _ W hzW) (G (.inl i))).snd) =
      Matrix.of fun i j => (ev (frX (w (.inl (o j))) ≫ TF.Y.j) U.1 (hwU _) (x i)).snd := by
    ext i j
    exact congrArg TrivSqZeroExt.snd ((FlagMod.ev_appLE _ _ hc.2.1 _ (eb _ ▸ hwU _) _).trans
      (congrArg (· (x i)) (FlagMod.ev_congr (eb _) _ _ _)))
  rw [e₁, hblock, e₂, map_diagUnit (ev z W hzW) L hc.2.2.2.2.1 t ht] at key
  have hca : ev z W' hz ac = (a : K) := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
    exact map_ratCast ((ev z W' hz).comp (algX (str₀ TF.X Z) W')) a
  rw [FlagMod.ev_res _ hW'W hz hzW, FlagMod.ev_appLE _ _ hc.2.1 _ (eP ▸ hU), FlagMod.ev_congr eP _ _ hU, hh,
    map_mul, map_mul, hca, FlagMod.ev_res _ hW'W hz hzW, mul_assoc, mul_assoc]
  exact congrArg _ ((mul_comm _ _).trans key)

section Main

open ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


set_option maxHeartbeats 800000 in
theorem simple_pole : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ y _ V hy t ht₁ ht₂
  obtain ⟨W, hyW, hWV, i, k, δ, u, hi, hk, hu, h₁, h₂, h₃⟩ := exists_pole hP TF Z hF hKS hV ω₀ y V hy
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) :=
    haveI := (TF.X.normal (inc₀ TF.X Z y)).1
    MulEquiv.isDomain _ (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  obtain ⟨V', hyV', hV', b, hb, e⟩ := exists_unit_mul y hyW (resG _ hWV t) δ
    (by rw [ger_resG]; exact ger_ne_zero (dense_U₀ TF.X Z) t (fun z hz h => (ht₁ z hz).2 h) y _)
    (by rw [ger_resG]; exact ht₂ W hWV δ (fun z hz h hu => h ((h₁ z hz).1 hu)) y hyW)
    (h₂ W le_rfl _ (fun z hz h hu => h ((ht₁ z (hWV hz)).1 (by rwa [ger_resG] at hu))) y hyW)
  refine ⟨V', hyV', hV'.trans hWV, i, k, b * resG _ hV' u, hV'.trans hi, hV'.trans hk, fun z hz => ?_,
    fun z hz ho hc => ?_⟩
  · rw [map_mul]
    exact (hb z hz).mul ((hu.map _).map _)
  let O : (Y₀ TF.X Z).Opens := ksOpen (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) i k
  let ω : Γ(Y₀ TF.X Z, O) := ω₀.ω.loc (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k)
  have e₁ : resG _ (inf_le_left : W ⊓ O ≤ W) δ * resG _ inf_le_right ω = resG _ inf_le_left u := by
    refine FlagMod.ext_ev_field fun K _ p hp => ?_
    have a₁ := FlagMod.le_preimage_mono inf_le_left hp
    have a₂ := FlagMod.le_preimage_mono inf_le_right hp
    rw [map_mul, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₂]
    exact h₃ K p a₁ (FlagMod.le_preimage_mono inf_le_left a₂) (FlagMod.le_preimage_mono inf_le_right a₂)
  have hzO : z ∈ O := ⟨ho, hc⟩
  have hm : z ∈ W ⊓ O := ⟨hV' hz, hzO⟩
  have e₂ := congrArg (ger z hm) e₁
  have e₃ := congrArg (ger z hz) e
  simp only [map_mul, ger_resG] at e₂ e₃
  change ger (Y := Y₀ TF.X Z) z _ t * ger (Y := Y₀ TF.X Z) z hzO ω = ger (Y := Y₀ TF.X Z) z hz _
  rw [map_mul, ger_resG, e₃, mul_assoc, e₂]

end Main

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_canonical_divisor : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  first | exact @GlobalTheory.LogPole.simple_pole | exact GlobalTheory.LogPole.simple_pole | (intros; apply GlobalTheory.LogPole.simple_pole <;> assumption)
end
