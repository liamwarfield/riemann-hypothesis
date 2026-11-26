module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Keeps
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem keeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (g : p.P.Gp) :
    ∀ f ∈ CF p i, actLev p.T.Q.c (p.O i).lev2 g f ∈ CF p i := fun f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
def groupActionOnCoefficients (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (g : p.P.Gp) : CF p i →ₗ[p.T.Q.c.F] CF p i :=
  (actLev p.T.Q.c (p.O i).lev2 g).restrict (_root_.GlobalTheory.DefHalf.keeps_alt p i hp g)
end GlobalTheory.DefHalf
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadComponentsIndefinite
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RegularEmbeddingsCoverBadEmbeddingLocus
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftsOfFour
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.BadEmb
section Abstract
variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)
end Abstract
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end General
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weights
theorem lifts_of_four_quantitative_conditions {Q₁ Q₂ Q₃ Q₄ R : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop}
    (h₁ : _root_.GlobalTheory.CovTop.LiftsCondition Q₁) (h₂ : _root_.GlobalTheory.CovTop.LiftsCondition Q₂) (h₃ : _root_.GlobalTheory.CovTop.LiftsCondition Q₃) (h₄ : _root_.GlobalTheory.CovTop.LiftsCondition Q₄)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
      (PP C₁ C₂ C₃ C₄ : ℝ), Q₁ Fm x hx ι p i PP C₁ → Q₂ Fm x hx ι p i PP C₂ → Q₃ Fm x hx ι p i PP C₃ →
      Q₄ Fm x hx ι p i PP C₄ → R Fm x hx ι p i PP 0) : _root_.GlobalTheory.CovTop.LiftsCondition R := by
  refine (((h₁.and h₂).and h₃).and h₄).imp fun Fm CH _ h' => ?_
  obtain ⟨⟨⟨⟨_, -, a1⟩, _, -, a2⟩, _, -, a3⟩, _, -, a4⟩ := h'
  obtain ⟨x0, h'⟩ := ((a1.and a2).and a3).and a4
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h' x hx hle ι p hp
  exact h Fm x hx ι p i _ _ _ _ _ (b1 i) (b2 i) (b3 i) (b4 i)
end GlobalTheory.BadEmb
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.BadEmb
section Abstract
variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)
end Abstract
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end General
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weights
set_option maxHeartbeats 1000000 in
theorem regular_embeddings_cover_bad_embedding_locus_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), Pb.comap π = grpHR fr → (∀ k, (H k).comap π = grpGHR fr k) → (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) → ∀ k : Fin 2, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 3 / 2 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
  intro hX hP hGD hQ hS hT hSA _ hDG hSz hFD hDg hSh
  first
    | have h4 := _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hX hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
    | have h4 := _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
  first
    | have ua0 := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hX hP hGD hQ hS hT hSA
    | have ua0 := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGD hQ hS hT hSA
  first
    | have sg := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hX hP
    | have sg := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP
  have h3 := _root_.GlobalTheory.T.size_bounds_for_family_alt hSz
  unfold _root_.GlobalTheory.CovTop.DeepGoodness _root_.GlobalTheory.CovTop.CoversCondition at hDG
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h3 h4 ⊢
  refine _root_.GlobalTheory.BadEmb.lifts_of_four_quantitative_conditions hDG _root_.GlobalTheory.T.weight_conditions_at_index' h3 h4 ?_
  clear hDG h3 h4
  intro eps Fm x hx ι p i PP _ _ _ _ b1 b2 b3 b4 hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  have g0 := (b1 hi Y hY).1
  have gm := (b1 hi Y hY).2.1
  have hL := (b2 hi).1
  have hp1 := (b2 hi).2.1
  have hq1 := (b2 hi).2.2.1
  have hf := (b2 hi).2.2.2.1
  have hj := (b2 hi).2.2.2.2.1
  have hn := (b2 hi).2.2.2.2.2.1
  have hs := (b2 hi).2.2.2.2.2.2.2.2
  have he := (b3 hi Y hY).2.2.2.2.2.2.1
  have hg := (b3 hi Y hY).2.2.2.2.2.2.2.1
  have hrk := b4 hi Y hY 2 one_le_two le_rfl
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hs1 := hs _ (Or.inr (Or.inr rfl))
  have ec : ((2 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) =
      cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1) := by push_cast; ring
  rw [ec] at hrk
  have g2 : Y.GoodAt (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    sg _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
      (fun τ => by
        rw [add_smul, ← add_assoc]
        exact antitone_add_hodge _ _ τ (hs1.1 τ) hc0)
      (fun τ => by
        rw [add_smul, ← add_assoc, gap_add_hodge _ hp1 hq1]
        exact le_add_of_le_of_nonneg (hs1.2 τ) hc0)
  have ua := ua0 _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 he hg fr
  have hr : (Y.rk (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤
      3 / 2 * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
    refine hrk.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact (add_le_add_right (min_le_left _ _) _).trans (by norm_num)
  exact embReg_deep hL hp1 hq1 hf hj Y hY.1 _ _ hn _ g0 gm g2 (3 / 2) (by norm_num) hr _ _
    (ua _ (Or.inl hPb)) (ua _ (Or.inr ⟨k, hH k⟩)) ρ χ lamb hρ
end GlobalTheory.BadEmb
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), Pb.comap π = grpHR fr → (∀ k, (H k).comap π = grpGHR fr k) → (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) → ∀ k : Fin 2, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 3 / 2 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
  first | exact @_root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt | exact _root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt | (intros; apply _root_.GlobalTheory.BadEmb.regular_embeddings_cover_bad_embedding_locus_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoverTypeLatticeComparison
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_type_lattice_comparison_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BadIndef
set_option maxHeartbeats 1000000 in
theorem bad_components_indefinite_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  intro hX hP hGD hQ hS hT hSA hGr hG hDG hSz hFD hDg hSh
  have hB := _root_.GlobalTheory.T.cover_type_lattice_comparison_alt hP hG hDG
  have hW := _root_.GlobalTheory.T.local_share_number_bound_alt hP hGr
  have hE := _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt hX hP hGD hQ hS hT hSA hG hDG hSz hFD hDg hSh
  refine Formalism.MainNotions.Closed.imp (((hB.and hW).and hE).and hDG) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩, ⟨C4, -, x4, h4⟩⟩
  refine ⟨0, le_rfl, max (max x1 x4) (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hle
  have l4 : x4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨ψ₀, hψ₀, hsh⟩ := h2 x hx l2 ι p hp i
  obtain ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lamb, H, hsp, hwh, hlb, hhalf, hPb, hH, hρ, hrkT, hrkB⟩ :=
    h1 x hx l1 ι p hp i hi Y hY
  have hemb := fun k => h3 x hx l3 ι p hp i hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  choose n hn1 hn2 using hemb
  have hgd := (h4 x hx l4 ι p hp i hi Y hY).1
  haveI : FiniteDimensional Y.d.c₂.F (Y.V (Gk p i)) := finiteDimensional_of_lat _ hgd.2.1 hgd.2.2
  obtain ⟨S, hSg, hbd⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker (Fm.D x ι) _ _ π s hsp ρ Pb lam ψ hwh lamb hlb H hhalf n (3 / 2) hn1 hn2 ψ₀ hψ₀
  have hs := hsh S hSg
  have e0 : (0 : ℝ) ≤ Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := Nat.cast_nonneg _
  have e1 : 0 ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := (Real.exp_pos _).le
  have k1 := mul_le_mul_of_nonneg_right hs e0
  have k2 := mul_nonneg e1 e0
  have key : (Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
      3 * Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) := by
    rw [hrkT, hrkB]
    refine hbd.trans ?_
    linarith
  exact key
end GlobalTheory.BadIndef
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  first | exact @_root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | exact _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | (intros; apply _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLiftAtDefiniteBadPlaces
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentativeOfDeformationClass
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FreeHalfOfDeformationSpace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitDeformationLift
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.DefSplit
section Alg
open scoped TensorProduct
variable {K L B W : Type} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B] [AddCommGroup W] [Module K W]
end Alg
section Geo
open CategoryTheory Limits AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient (fnAt basePt)
open GlobalTheory.LevelCoverCompare (fnRule fnRule_mem fnRule_injective fnAt_comp)
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
variable {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
end Geo
section Main
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_free_action_permuting_summands_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  intro _ _
  have hw : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp hw ?_
  rintro eps Fm CH - ⟨C, hC, x0, ha⟩
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi hp' Hg _ _ φ hF => ?_⟩
  have hW := ha x hx hle ι p hp i
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hi.le⟩
  have hq : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = (Fm.D x ι).R.m - ((i : ℕ) + 1) := by rw [hW.sig.2.1]; rfl
    simpa [dat, hi] using this
  have hU := p.fw.laws.unf _ hj
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  have hL : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : Hg => (p.O i).lev2 (φ g)) :=
    ⟨fun g => h.total (φ g), fun g => h.func (φ g), fun S _ _ y => by
        have := h.one S y
        rw [← map_one φ] at this
        exact this,
      fun g g' S _ _ y y' y'' a b => by
        have := h.mul (φ g) (φ g') S y y' y'' a b
        rw [← map_mul φ] at this
        exact this,
      fun g => h.nat (φ g), fun g => h.bor (φ g)⟩
  refine split_rules hq hL hF (GlobalTheory.DefHalf.CF p i) (fun b f hf => ?_) (fun g => _root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp'.1 (φ g))
    (fun g f => rfl) _
  refine GlobalTheory.DefPt.ReadsPt.mem_cusp_of_sec hq hU hW.dom ?_
  have := sec_mul _ _ _ _ _ _ (GlobalTheory.LevelCoverCompare.fnRule_mem b) (cusp_le_sec _ _ _ _ _ hf)
  rwa [zero_add, zero_add] at this
end Main
end GlobalTheory.DefSplit
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (Hg : Type) [Group Hg] [Finite Hg] (φ : Hg →* p.P.Gp),
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun h => (p.O i).lev2 (φ h)) →
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction Hg X) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (GlobalTheory.DefHalf.sigC p) (GlobalTheory.DefHalf.CF p i))),
      (∀ (h : Hg) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : Hg) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (GlobalTheory.DefHalf.sigC p) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 (φ h)) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | exact _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace | (intros; apply _root_.GlobalTheory.DefSplit.exists_free_action_permuting_summands_thirdPlace <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsFreeHalfLiftOfNeat
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.L2.Theta Formalism.IndefR
open scoped TensorProduct
namespace GlobalTheory.NeatOne
end GlobalTheory.NeatOne
end Point
section Family
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
namespace GlobalTheory.NeatOne
theorem neat_divisor_free_half_lifts_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  intro _ _
  refine Formalism.MainNotions.Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i _ k => free_half p i (rank_add_one_lt Fm x hx ι _ C (ha x hx hle ι p hp i)) k⟩
end GlobalTheory.NeatOne
end Family
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  first | exact @_root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt | exact _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt | (intros; apply _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf
set_option maxHeartbeats 1000000 in
theorem halfH_acts_freely_on_internal_sum_decomposition : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index hP hG
  have h2 := _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace hP hG
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (h1.and h2) ?_
  rintro eps Fm CH - ⟨⟨C1, -, x1, ha1⟩, ⟨C2, -, x2, ha2⟩⟩
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi k => ?_⟩
  have a1 := ha1 x hx (le_trans (le_max_left _ _) hle) ι p hp i hi k
  have a2 := ha2 x hx (le_trans (le_max_right _ _) hle) ι p hp i hi hp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k)
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) a1
  obtain ⟨X, hX, hdX, hact, A, hfr, hint, hperm⟩ := a2
  letI := ((p.R.toRealDat.FW i)).towKs
  obtain ⟨n, b, hbW, hbK, hbsK, hbL, hbsL⟩ := p.fw.ks i
  have hK := (p.rhoGeo i).1 (fun g f hf => _root_.GlobalTheory.DefHalf.keeps_alt p i hp.1 g f hf)
  have he : ∀ g f, (((p.fw.e i) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 g f) : (p.R.FW i).WK) : Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) =
      (p.R.FW i).ρ g ((p.fw.e i) f) := by
    intro g f
    obtain ⟨hf, h⟩ := hK g f
    rw [← h]
    rfl
  obtain ⟨A', hint', hperm'⟩ := GlobalTheory.T.transport_permuted_directSum_complexification p.T.Q.c.F (Fm.D x ι).what₂.LL (Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) (CF p i)
    (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) p.P.Gp X (Fm.D x ι).what₂.embLL (p.R.FW i).WK n b hbW hbK hbsK hbL hbsL
    (p.fw.e i) (p.R.FW i).ρ (p.R.FW i).chi (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1) he
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) A hint hperm
  exact ⟨X, hX, hdX, hact, A', hfr, hint', fun h y v hv => hperm' h y v hv⟩
end GlobalTheory.DefHalf
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  first | exact @_root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | exact _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition | (intros; apply _root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointRead
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanMKEqTop
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanMKEqTop
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.CovTop.SpanMK
theorem span_MK_eq_top_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (_hR : _root_.GlobalTheory.CovTop.RowsTAlt p) (hG : GramAt p i) :
    Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) = ⊤ := by
  obtain ⟨ι, hι, -, himg⟩ := GlobalTheory.CovTop.SupImage.exists_emb_image_latW D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hspan := hG.2.2.2.2.2
  have hall : ∀ g, g ∈ Submodule.span p.T.Q.c.F
      (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i)) →
      ι g ∈ Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (himg ▸ ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨n, b, hbW, -, -, -, hbL⟩ := p.fw.ks i
  rw [eq_top_iff, ← hbL, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨f, hf⟩ := (p.fw.e i).surjective ⟨b k, hbW k⟩
  have hE : VK p.fw i = p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := GlobalTheory.AllWt.cuspW_wtZ _ _
  let g : VK p.fw i := ⟨f.1, hE.symm ▸ f.2⟩
  obtain ⟨h, hg⟩ := hι g
  have e1 : ι g = b k := by
    rw [hg]
    have : (⟨(g : p.T.R ((i : ℕ) + 1)), h⟩ : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = f := Subtype.ext rfl
    rw [this, hf]
  rw [← e1]
  exact hall g (hspan.ge Submodule.mem_top)
end GlobalTheory.CovTop.SpanMK
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanMKEqTopStatement
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_MK_spans_of_gramAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m),
    _root_.GlobalTheory.CovTop.RowsTAlt p → GramAt p i →
    Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) = ⊤ := by
  first | exact @_root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt | exact _root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt | (intros; apply _root_.GlobalTheory.CovTop.SpanMK.span_MK_eq_top_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
theorem point_read_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (hg : GramAt p i)
    (hfree : ∀ k : Fin 2, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH D k) X)
      (A : X → Submodule ℂ (VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), ∀ v ∈ A y, repAt p i (h : G0g D.nd) v ∈ A (h • y)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (π : Γ →* G0g D.nd) (s : G0g D.nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ)
      (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧
      (∀ k, IsHalf D k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X)
        (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
        ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧
      Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) := by
  classical
  obtain ⟨lam, ψ, hW, hlam, -⟩ := _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip D L hT Gi Gl Kc Y0 cX ex Csz p hp.1
  have hfin : Finite (G0g D.nd) := Finite.of_equiv _ (p.R.eG.trans p.cG).toEquiv
  let e := p.R.eG.trans p.cG
  let Pb := p.P.P0.map e.toMonoidHom
  let lamb : Pb.comap (MonoidHom.id (G0g D.nd)) →* ℂˣ :=
    lam.comp (MulEquiv.subgroupCongr (Subgroup.comap_id Pb)).toMonoidHom
  have hEig : eig (repAt p i) (Pb.comap (MonoidHom.id (G0g D.nd))) lamb =
      eig (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi) (p.F.lv2.lvl false).P
        ((Units.map D.what₂.embLL.toMonoidHom).comp (p.F.lv2.lvl false).ψ⁻¹) := by
    ext v
    rw [mem_eig, mem_eig]
    constructor
    · intro h g
      have hm : e g ∈ Pb := ⟨g, g.2, rfl⟩
      have := h ⟨e g, hm⟩
      rw [repAt_apply] at this
      simp only [e, MulEquiv.symm_apply_apply] at this
      rw [this]
      congr 2
      exact Units.ext (hlam g hm)
    · intro h γ
      obtain ⟨g, hg, hge⟩ := γ.2
      have := h ⟨g, hg⟩
      rw [repAt_apply]
      have h1 : (p.R.eG.trans p.cG).symm (γ : G0g D.nd) = g := by
        rw [MulEquiv.symm_apply_eq]; exact hge.symm
      rw [h1, this]
      congr 2
      apply Units.ext
      have h2 := hlam ⟨g, hg⟩ ⟨g, hg, rfl⟩
      have h3 : lamb γ = lam ⟨e g, ⟨g, hg, rfl⟩⟩ := by
        show lam ⟨(γ : G0g D.nd), _⟩ = _
        congr 1
        exact Subtype.ext hge.symm
      rw [h3, h2]
      rfl
  refine ⟨G0g D.nd, inferInstance, hfin, VAt p i, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    repAt p i, Pb, lam, ψ, lamb, GlobalTheory.BadCount.Inh.halfH D, ⟨fun g => rfl, fun g γ hγ => ?_⟩, hW, fun γ => rfl,
    fun k => GlobalTheory.BadCount.Inh.isHalf_halfH D k, fun k => ?_, ?_, ?_⟩
  · have : γ = 1 := hγ
    subst this; simp
  · obtain ⟨X, hX, hXd, hact, A, hf, hA, hc⟩ := hfree k
    let f : (GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd)) →* GlobalTheory.BadCount.Inh.halfH D k :=
      { toFun := fun h => ⟨h.1, h.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    letI : MulAction ((GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd))) X := MulAction.compHom X f
    refine ⟨X, hX, hXd, this, A, fun h y hy => ?_, hA, fun h y v hv => hc (f h) y v hv⟩
    have := hf (f h) y hy
    exact Subtype.ext (congrArg Subtype.val this)
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _) = _
    rw [hB.1, typeSubspace_eq_iInf_ker, hA.1, hEig]
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    obtain ⟨-, -, -, hc, -, -⟩ := p.grpRecPin
    have hsum : ∀ x : MonoidAlgebra ℂ (G0g D.nd), x = ∑ h, MonoidAlgebra.single h (x.coeff h) := fun x =>
      MonoidAlgebra.ext (by
        rw [MonoidAlgebra.coeff_sum]
        simp only [MonoidAlgebra.coeff_single]
        exact (Finsupp.univ_sum_single _).symm)
    have he0 : D.ntypes.e0 = ∑ g : p.P.Gp,
        MonoidAlgebra.single (e g) (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)) := by
      rw [hsum D.ntypes.e0, ← Equiv.sum_comp e.toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc g]
      rfl
    have hK : Representation.asAlgebraHom ((repAt p i).comp (MonoidHom.id (G0g D.nd))) D.ntypes.e0 =
        Representation.asAlgebraHom (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi)
          (∑ g, MonoidAlgebra.single g (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [he0, map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      have hee : (p.R.eG.trans p.cG).symm (e g) = g := MulEquiv.symm_apply_apply _ _
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, repAt_apply, hee]
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _ ⊓ (LinearMap.ker (eGood p.R.toRealDat i)).restrictScalars _) = _
    have hEG : eGood p.R.toRealDat i = ∑ g, ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g *
        (((p.R.toRealDat.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (p.R.toRealDat.FW i).ρ g := by
      unfold eGood Formalism.IndefR.Arith.FormsL.eOp; rfl
    rw [hB.2, typeSubspace_eq_iInf_ker, hEG, hA.2]
    rw [hEig, hK]
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead
end GlobalTheory.DefRead
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead
set_option maxHeartbeats 1000000 in
theorem exists_representative_of_deformation_class_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem hP hG
  have h2 := hG
  unfold _root_.GlobalTheory.CovTop.GramCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  exact _root_.GlobalTheory.DefRead.point_read_alt p i hp (a2 i) (a1 i hi)
end GlobalTheory.DefRead
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_class_has_representative_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  first | exact @_root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | exact _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt | (intros; apply _root_.GlobalTheory.DefRead.exists_representative_of_deformation_class_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem definite_bad_place_lift_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  intro hP hGr hG
  have h1 := _root_.GlobalTheory.T.deformation_class_has_representative_alt hP hG
  have h2 := _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt hP hGr
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  obtain ⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩ := a1 i hi
  obtain ⟨ψ₀, hψ₀, hsh⟩ := a2 i
  have hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤
      1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
    intro k
    obtain ⟨X, _, _, _, A, hf, hA, hpm⟩ := hfree k
    obtain ⟨n, hn, hn'⟩ := embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm
    have hle : Pb.comap π ≤ (H k).comap π := fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv
    have h3 := card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb
    refine ⟨n, hn, ?_⟩
    rw [one_mul]
    exact_mod_cast (hn'.trans h3.symm).le
  choose n hn hn' using hc
  obtain ⟨S, hSb, hbd⟩ := GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀
  have hs := hsh S hSb
  unfold BadAt
  rw [hT, hB]
  have hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := Nat.cast_nonneg _
  have hx := Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))
  calc _ ≤ _ := hbd
    _ ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hs hr
    _ ≤ _ := by nlinarith
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  first | exact @_root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | exact _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | (intros; apply _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem covering_bad_locus_of_descent_steps_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal →
    _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition →
    _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  intro hX hP hGD hQ hST hTF hSA hGC hGr hEx hDG hS hF hD hSh
  have h1 := _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal hP hGC hGr
  have h2 := _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree hX hP hGD hQ hST hTF hSA hGC hGr hDG hS hF hD hSh
  unfold _root_.GlobalTheory.CovTop.LiftBadSet _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1
  unfold _root_.GlobalTheory.CovTop.DeepExistence _root_.GlobalTheory.CovTop.LiftsCondition at hEx
  refine ((h1.and h2).and hEx).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, e⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := e x hx hle ι p hp
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (Fm.D x ι).R.m with hlt | hge
  · obtain ⟨Y, hY⟩ := a3 i hlt
    exact a2 i hlt Y hY
  · exact a1 i (le_antisymm (Nat.succ_le_of_lt i.isLt) hge)
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  first | exact @_root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | exact _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt <;> assumption)
end
end
