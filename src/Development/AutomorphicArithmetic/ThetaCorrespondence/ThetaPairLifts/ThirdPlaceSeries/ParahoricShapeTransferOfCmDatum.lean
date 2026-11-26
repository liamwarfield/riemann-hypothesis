module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorLevelComparisonParamodularPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.ParaPlace
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ u ∈ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j), ∃ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v = u := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨hg, w', hw'u, hun⟩ := hu
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  have hxi : ¬ (T.xiTw f v).UnrAt w' := by
    intro hx
    rw [← h2] at hx
    exact hun (unr_mul hmu hx)
  unfold TwDat.xiTw at hxi
  set M := cell (D := Dof x) l.b.Bs.exp b hA j
  have fin : ∀ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) → (w' = P' ∨ IsConjPl (Dof x).host w' P') →
      ∃ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) ∧ (M.sp P').v = u := by
    intro P' hP' hc
    refine ⟨P', hP', ?_⟩
    have hw := M.sp_w P' (hP'.elim Or.inl (fun h => Or.inr (Or.inl h)))
    have hov : NG.OverPl P' u := by
      have e := (GlobalTheory.PlacePair.comap_eq_iff (Dof x) w' P').2 hc
      exact e.symm.trans hw'u
    apply HeightOneSpectrum.ext
    exact (M.sp P').w_under.symm.trans (by rw [hw]; exact hov)
  by_cases hq : w' ∈ T.Q v
  · obtain ⟨P', hP', hc⟩ := M.QP_cover w' (hQ ▸ hq)
    exact fin P' (Or.inl hP') (hc.imp Eq.symm id)
  · have hψ : (T.psi v).UnrAt w' := ((T.psi_is v).ram w').2 hq
    have hd := fun h => hxi (unr_mul h hψ)
    have hp : w' ∈ (Dof x).ntw.pD i := by
      rw [← Finset.mem_coe, (Dof x).ntw.pD_eq i, hl]
      change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde)
      split_ifs at hd ⊢
      · by_contra ho; exact hd (f.isDel'.unr w' ho)
      · by_contra ho; exact hd (f.isDel.unr w' ho)
    obtain ⟨P', hP', hc⟩ := M.DP_cover w' hp
    exact fin P' (Or.inr hP') (hc.imp Eq.symm id)
end GlobalTheory.LevCmp.ParaPlace
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ u ∈ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j), ∃ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v = u := by
  first | exact @_root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellPlacesDisjointOfSeparated
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.SepPlaces
end GlobalTheory.SepPlaces
namespace GlobalTheory.SepPlaces
end GlobalTheory.SepPlaces
namespace GlobalTheory.SepPlaces
theorem cell_places_separated_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  intro _ hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l v i b ψ hA j _ _ _ P' hP'
  exact sep_gen (Dof x) (cell (D := Dof x) l.b.Bs.exp b hA j) (fun P hP => hA.2.1 P hP) P' hP'
end GlobalTheory.SepPlaces
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_places_disjoint_of_admTw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → ¬ (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∧ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ (∀ kv, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P'').v = ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v → P'' = P') := by
  first | exact @_root_.GlobalTheory.SepPlaces.cell_places_separated_alt | exact _root_.GlobalTheory.SepPlaces.cell_places_separated_alt | (intros; apply _root_.GlobalTheory.SepPlaces.cell_places_separated_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationDeltaComparison
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.ValDelta
variable {D : D7}
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofO0 (Dof x) i (T.k v) (NX.tameVal ((Dof x).ntw.delta i) P' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  intro hP hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok e he _ P' hP' a k ha hk
  have h2 := P.q.mu.tw v
  have hp : P' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP'
  obtain ⟨hxu, hv⟩ := tameVal_delta hP.what₂.art (cfOf x) l.b.Bs.deltaRead he hp a k ha hk
  rw [l.b.Bs.exp.sgnT_one]
  refine hv.trans (congrArg Units.val ?_)
  have hp' : P' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
    rw [← (Dof x).ntw.pD_eq i]; exact hp
  obtain ⟨h1, -, h3, -, -⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe (cfOf x)) (l := (Dof x).ntw.l i)
  have hmu : ((cfOf x).mu0 j).UnrAt P' :=
    ((cfOf x).isMu0 j).unr P' fun kk => GlobalTheory.GalChar.notMem_of_ne h1 ((Dof x).host.g_prime kk) (h3 kk) hp'
  have hψ : (T.psi v).UnrAt P' := by
    change P' ∈ placesOver B.host.E (if (Dof x).ntw.l i = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde'_prime (by simp [offSet]) P' hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde_prime (by simp [offSet]) P' hp'
  have hdel : (cfOf x).delAt ((Dof x).ntw.l i) = if B.places.resChar v = B.host.pde then f.del' else f.del := by
    rw [hl]
    exact congrArg (fun c : Top.Fr B.toPre => if B.places.resChar v = B.host.pde then c.del' else c.del) w.C_eq
  have key : ∀ (u : HeightOneSpectrum (𝓞 B.host.E)) (μ δ ξ : HChar B.host.E) (y), IsUnitAt u y → μ.UnrAt u → ξ.UnrAt u →
      δ.loc u y = (μ * (δ * ξ)).loc u y := by
    intro u μ δ ξ y hy h1 h2
    have loc_mul (a b : HChar B.host.E) : (a * b).loc u y = a.loc u y * b.loc u y := rfl
    rw [loc_mul, loc_mul, h1 _ hy, h2 _ hy, one_mul, mul_one]
  rw [hdel]
  exact (key P' _ _ _ _ hxu hmu hψ).trans
    (congrArg (fun ξ : HChar B.host.E => (@HMul.hMul (HChar B.host.E) (HChar B.host.E) _ _ ((cfOf x).mu0 j) ξ).loc P' (atFin P' k)) h2.symm)
end GlobalTheory.LevCmp.ValDelta
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_valuation_delta_le_of_sideRead : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofO0 (Dof x) i (T.k v) (NX.tameVal ((Dof x).ntw.delta i) P' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  exact @_root_.GlobalTheory.LevCmp.ValDelta.locComp_of_isRc_classMapD_cenLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistCharacterTamelyRamifiedAtPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TwTameCell
theorem twist_character_tame_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j _ _ _ P' _
  have h1 := ((cfOf x).isMu0 j).tame P'
  have hx : w.I.xi ((Dof x).what₂.muTw v) ∈ T.set f := w.xi_range ▸ Set.mem_range_self _
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
  have h2 : (w.I.xi ((Dof x).what₂.muTw v)).TameAt P' := by
    rcases hx with (h | h | h) | ⟨w', h⟩
    · rw [h]; exact tameAt_one P'
    · rw [h]; exact f.isDel.tame P'
    · rw [h]; exact f.isDel'.tame P'
    · rw [← h]
      unfold TwDat.xiTw
      split_ifs
      · exact tameAt_mul (f.isDel'.tame P') ((T.psi_is w').tame P')
      · exact tameAt_mul (f.isDel.tame P') ((T.psi_is w').tame P')
  exact tameAt_mul h1 h2
end GlobalTheory.TwTameCell
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  first | exact @_root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | exact _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | (intros; apply _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationQComparison
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.ValQ
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofOk (Dof x) i (T.k v) (NX.tameVal ψ P' l.b.Bs.exp.sgnT a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  intro hP hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok e hside hR P' hP' a y ha hy
  have h2 := P.q.mu.tw v
  have hPQ : P' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP'
  have hlP := (hA.1 P' hPQ).2
  have hpD := (hA.2.1 P' hPQ).1
  have hg := (hA.2.1 P' hPQ).2
  have hmu : ((cfOf x).mu0 j).UnrAt P' := ((cfOf x).isMu0 j).unr P' fun k hk => hg k hk
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : (Dof x).host.E) : P'.adicCompletion (Dof x).host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  rw [l.b.Bs.exp.sgnT_one, tameVal_eq_locK hP.what₂.art (Dof x) i (T.k v) e ψ (T.psi v) hR hA.2.2.1 hA.2.2.2.2.1 P' hlP a y ha hy]
  have hp' : P' ∉ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde) := by
    intro h
    apply hpD
    rw [← Finset.mem_coe, (Dof x).ntw.pD_eq i, hl]
    exact h
  show _ = ((((cfOf x).mu0 j).loc P' (atFin P' y) * (w.I.xi ((Dof x).what₂.muTw v)).loc P' (atFin P' y) : ℂˣ) : ℂ)
  rw [hmu _ hxu, one_mul]
  have h3 : w.I.xi ((Dof x).what₂.muTw v) = T.xiTw f v := h2
  rw [h3]
  unfold TwDat.xiTw
  split_ifs with hc
  · rw [if_pos hc] at hp'
    have hd := f.isDel'.unr P' hp' _ hxu
    show _ = (((f.del'.loc P') ((atFin P') y) * ((T.psi v).loc P') ((atFin P') y) : ℂˣ) : ℂ)
    rw [hd, one_mul]
    rfl
  · rw [if_neg hc] at hp'
    have hd := f.isDel.unr P' hp' _ hxu
    show _ = (((f.del.loc P') ((atFin P') y) * ((T.psi v).loc P') ((atFin P') y) : ℂˣ) : ℂ)
    rw [hd, one_mul]
    rfl
end GlobalTheory.LevCmp.ValQ
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_valuation_q_le_of_sideRead : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofOk (Dof x) i (T.k v) (NX.tameVal ψ P' l.b.Bs.exp.sgnT a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameLevelValueTrivialAtWildPlace
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.TameUnitOne
open _root_.Formalism.L2.NX
end GlobalTheory.TameUnitOne
namespace GlobalTheory.LevCmp
theorem tame_value_eq_one_at_wild_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  intro _ hL
  refine StepW.of_all fun _ B _ T _ _ _ _ P x l v i b ψ hA j _ _ _ => ?_
  refine ⟨fun P'' hP'' u hu => ?_, fun P'' hP'' u hu => ?_⟩
  · have hQ : P'' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP''
    exact GlobalTheory.TameUnitOne.tameVal_eq_one ψ P'' _ ((Dof x).ntw.l i) hA.2.2.1 (hA.1 P'' hQ).2
      (fun _ _ σ _ => hA.2.2.2.2.1 σ) u hu
  · have hD : P'' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP''
    refine GlobalTheory.TameUnitOne.tameVal_eq_one ((Dof x).ntw.delta i) P'' _ 15 ((Dof x).ntw.delta_open i) ?_
      (fun A hA' σ hσ => ⟨1, ?_⟩) u hu
    · intro h
      have h1 := (Dof x).ntw.delta_tame i P'' hD
      have h2 : Ideal.absNorm P''.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 (Dof x).host.E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
        rwa [Ideal.absNorm_span_natCast] at this
      have h3 : Nat.Coprime (Ideal.absNorm P''.asIdeal) 15 := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
        rfl
      have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
      exact P''.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
    · have h1 := pow_card_eq_one' (x := (⟨(Dof x).ntw.delta i σ, σ, hσ, rfl⟩ :
        (ReciprocityTheory.Gal.Ine (F := (Dof x).host.E) A).map ((Dof x).ntw.delta i)))
      rw [(Dof x).ntw.delta_15 i P'' hD A hA'] at h1
      rw [pow_one]
      exact congrArg Subtype.val h1
end GlobalTheory.LevCmp
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' l.b.Bs.exp.sgnT u = 1) ∧ (∀ P'' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ u : 𝓞 (Dof x).host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ((Dof x).ntw.delta i) P'' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) u = 1) := by
  first | exact @_root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | exact _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt | (intros; apply _root_.GlobalTheory.LevCmp.tame_value_eq_one_at_wild_place_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.XPara
theorem parahoric_shape_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  intro hPr hL
  refine (StepW.and (_root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK hPr hL) (StepW.and (_root_.GlobalTheory.T.cell_places_disjoint_of_admTw hPr hL) (StepW.and (_root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' hPr hL)
    (StepW.and (_root_.GlobalTheory.T.conductor_valuation_q_le_of_sideRead hPr hL) (StepW.and (_root_.GlobalTheory.T.conductor_valuation_delta_le_of_sideRead hPr hL) (_root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place hPr hL)))))).trans
    (StepW.of_all fun K B f T w _ _ H P x l v i b ψ hA j htw hl hok e hS hR => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  intro u hu
  obtain ⟨P', hP', hPu⟩ := h1 P x l v i b ψ hA j htw hl hok u hu
  obtain ⟨hex, hg, hq, hd⟩ := h2 P x l v i b ψ hA j htw hl hok P' hP'
  obtain ⟨hwq, hwd⟩ := h6 P x l v i b ψ hA j htw hl hok
  have hT := h3 P x l v i b ψ hA j htw hl hok P' hP'
  have hw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').w = P' :=
    (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (hP'.elim Or.inl fun h => Or.inr (Or.inl h))
  rw [← hw] at hT
  obtain ⟨ξ, hξc, hξv⟩ := GlobalTheory.HeckeSplitComp.main _ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P') _ hT
  refine ⟨(cell (D := Dof x) l.b.Bs.exp b hA j).sp P', ξ, hPu, hξc, ?_⟩
  have hne : ∀ a : 𝓞 (Dof x).host.E, a ∉ P'.asIdeal → (a : (Dof x).host.E) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from by exact_mod_cast h0]; exact Ideal.zero_mem _)
  refine GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter _ _ _ _ _ _ _ _ _ _ _ _ e P' ξ hP' hex hg hq hd hwq hwd ?_ ?_
  · intro hq' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h4 P x l v i b ψ hA j htw hl hok e hS hR P' hq' a _ ha rfl).symm
  · intro hd' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h5 P x l v i b ψ hA j htw hl hok e hS hR P' hd' a _ ha rfl).symm
end GlobalTheory.XPara
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.paraShape_of_twisted_sideRead_readsHecke : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  first | exact @_root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | exact _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | (intros; apply _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt <;> assumption)
end
end
