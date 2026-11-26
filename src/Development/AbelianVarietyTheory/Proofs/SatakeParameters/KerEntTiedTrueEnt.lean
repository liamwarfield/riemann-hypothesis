module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_true_ent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.ent = E ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  obtain ⟨t, ht, hO, -, hTop⟩ := GlobalTheory.T.kernelEntries_compatible_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  exact kerEntTied_withEnt I l Z O E hE hS t ht hO hTop

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Ker _root_.Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

def Part.ofBuilt {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c) : Part w Z c.O where
  pin := b.pin
  col := b.col.toColT
  errX := b.errX
  tp := b.n.tp
  xi := b.n.xi
  qp := b.div.Qp
  ker0 := b.ker0
  ker_eq := b.ker_eq
  ker := b.ker

theorem builtC_hasPart : ∀ (𝒮 : Slots), (∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c) ∧
    ∀ K X f T c, IsBuilt 𝒮 K X f T c → positionOf HasPart K X f T c := fun 𝒮 =>
  have h : ∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c := fun _ _ _ _ _ _ _ ⟨b⟩ => ⟨Part.ofBuilt b⟩
  ⟨h, fun K X f T c hc => positionOf_mono h K X f T c hc⟩

end GlobalTheory.Svd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReferenceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_level_readAsReference : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  exact @GlobalTheory.Mem.Col2.TC.LevZero.lev_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesHasReaderLevelStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChanges
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChanges
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_of_move : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  intro D cc a b SS cl N N' Ξ e e' he he' h x x' hx
  have hs : star e * e = 1 := mul_eq_one_comm.1 he
  have hs' : star e' * e' = 1 := mul_eq_one_comm.1 he'
  have hRR : ∀ y : HomE D.host.E a b, Matrix.toLin' (star e') ∘ₗ (KerMove.RR (star e) (star e') y) ∘ₗ Matrix.toLin' e = y := by
    intro y
    refine LinearMap.ext fun v => ?_
    simp only [KerMove.RR_apply, LinearMap.comp_apply, star_star]
    rw [← LinearMap.comp_apply (Matrix.toLin' (star e')) (Matrix.toLin' e'), ← Matrix.toLin'_mul, hs', Matrix.toLin'_one,
      LinearMap.id_apply, ← LinearMap.comp_apply (Matrix.toLin' (star e)) (Matrix.toLin' e), ← Matrix.toLin'_mul, hs,
      Matrix.toLin'_one, LinearMap.id_apply]
  have key := h (KerMove.RR (star e) (star e') x) (KerMove.RR (star e) (star e') x') (fun P hP => by
    have h1 := KerMove.localization_map₂ (D := D) (KerMove.RR (star e) (star e')) _ _
      (fun z hz => KerMove.perO_map (aaOf D cc) N (SDLat.smulLat e N) N' (SDLat.smulLat e' N') (KerMove.RR (star e) (star e'))
        (fun w hw => KerMove.homO_RR_inv e e' he N N' w hw) z hz) P _ (hx P hP)
    rwa [map_smul, map_sub] at h1)
  simpa only [hRR] using key

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPreservedUnitaryLatticeChangesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  first | exact @GlobalTheory.TwV.datLoc_of_move | exact GlobalTheory.TwV.datLoc_of_move | (intros; apply GlobalTheory.TwV.datLoc_of_move <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  have hi0 : i ≤ D.R.m := Nat.le_of_succ_le hi
  have hlt : i < D.R.m := hi
  have h1 : (1 : GL (Fin (D.R.N i)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi0) := one_mem _
  have h1' : (1 : GL (Fin (D.R.N (i + 1))) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) := one_mem _
  have hx : ((St i hi0).y c).1 = ratA D.host.F (1 : GL (Fin (D.R.N i)) D.host.E) * ((St i hi0).y c).1 * (1 : ((St i hi0).K ((St i hi0).chOf c)).lev.U).1 := by
    simp
  have hx' : ((St (i + 1) hi).y c').1 = ratA D.host.F (1 : GL (Fin (D.R.N (i + 1))) D.host.E) * ((St (i + 1) hi).y c').1 * (1 : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U).1 := by
    simp
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie (i + 1) hi 1 h1'
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hTie i hi0 1 h1
  have hl := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie i hi0 c ((St i hi0).y c) 1 h1 1 hx
  have hl' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hTie (i + 1) hi c' ((St (i + 1) hi).y c') 1 h1' 1 hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hTie Xi muT hL i hi c c' ((St i hi0).y c) ((St (i + 1) hi).y c') 1 h1 1 h1' 1 1 hx hx' hu'
  have hloc := hL.loc i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c')
  rw [hl, hl'] at hloc
  refine GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes D t.cc (ssRec t u μ) (t.rd u μ).lev _ _ (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x)) _ _ hu hu' ?_
  have hE : Xi i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c') = _ := funext fun z => by
    have := hd z
    simpa [(hL.mu_mul i hlt).1, -Matrix.toLin'_toMatrix'] using this
  rw [hE] at hloc
  exact hloc

end GlobalTheory.TwV

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_pair_classes_has_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  first | exact @GlobalTheory.TwV.datLoc_classes | exact GlobalTheory.TwV.datLoc_classes | (intros; apply GlobalTheory.TwV.datLoc_classes <;> assumption)
end
