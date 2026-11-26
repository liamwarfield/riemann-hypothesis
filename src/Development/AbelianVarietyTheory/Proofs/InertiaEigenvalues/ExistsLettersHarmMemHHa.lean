module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLettersHarmMemHHa
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}

def tauPsi (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) : D.what₂.Tau ≃ {τ : D.host.E →+* ℂ // InPsi H τ} :=
  Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun _ _ h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hΨ τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩

theorem tauPsi_apply (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (ρ : D.what₂.Tau) :
    ((tauPsi hΨ ρ : {τ : D.host.E →+* ℂ // InPsi H τ}) : D.host.E →+* ℂ) = tauE D ρ := rfl

def fockVarEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : FVar D m n ≃ GlobalTheory.Harm.Var {τ : D.host.E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n) :=
  (tauPsi hΨ).prodCongr (((finCongr hm).trans finSumFinEquiv.symm).prodCongr (Equiv.refl _))

def letterEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : LtN Dw n ≃ FVar D m n :=
  (GlobalTheory.Harm.thetaLetterEquiv Dw n).trans (fockVarEquiv Dw hΨ hm).symm

end GlobalTheory.FockLetters
end
end

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)




end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

theorem isLetters_letterEquiv : IsLetters Dw (letterEquiv (n := n) Dw hΨ hm) := by
  rintro ⟨τ, i, b⟩
  rcases GlobalTheory.Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate _)
    (GlobalTheory.Harm.not_mem_hostType_iff H) τ with h | ⟨τ', h, rfl⟩
  · have e : letterEquiv Dw hΨ hm ⟨τ, i, b⟩ = ((tauPsi hΨ).symm ⟨τ, h⟩,
        Fin.cast hm.symm (Fin.castAdd Dw.q (i.cast (GlobalTheory.Harm.mult_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_of_mem Dw h]
      rfl
    rw [e]
    exact ⟨rfl, Or.inl ⟨(congrArg Subtype.val ((tauPsi hΨ).apply_symm_apply ⟨τ, h⟩)).symm, rfl⟩⟩
  · have e : letterEquiv Dw hΨ hm ⟨ComplexEmbedding.conjugate τ', i, b⟩ = ((tauPsi hΨ).symm ⟨τ', h⟩,
        Fin.cast hm.symm (Fin.natAdd Dw.p (i.cast (GlobalTheory.Harm.mult_conjEmb_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_conjugate Dw h]
      rfl
    rw [e]
    refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
    change conjEmb τ' = conjEmb (tauE D ((tauPsi hΨ).symm ⟨τ', h⟩))
    rw [← tauPsi_apply hΨ, Equiv.apply_symm_apply]

end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters

end GlobalTheory.FockLetters
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenFrobenius
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigOnto


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  intro hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc
  classical
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨-, y, hy, hcy⟩ := hc

  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  have hb := Sp.B.iV_basis j w b
  obtain ⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hy
    have hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a)) := by
      rw [hjb.2]; exact Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy'
    exact hy'
  haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩
  obtain ⟨I0, hI0⟩ := Ideal.exists_maximal (heckeAlg Sp.B j w)
  obtain ⟨i0, hi0, -⟩ := Sp.mx_all j w h1 h2 hw I0 hI0

  have hinjC : Function.Injective (Sp.iotaC j w) := by
    intro a1 a2 hab
    obtain ⟨a1', rfl⟩ := (Sp.phO j w i0 hi0).surjective a1
    obtain ⟨a2', rfl⟩ := (Sp.phO j w i0 hi0).surjective a2
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    congr 1
    exact IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))
  let φ : FractionRing (Sp.B.Oc j w) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom =
      (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    exact (Sp.iotaC_coh j w i0 hi0 z).symm
  have hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x := by
    intro x
    rw [← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]
    exact congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK

  obtain ⟨Hk, -⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  obtain ⟨ej, ew⟩ := (L.X.nd.locs_mem j w i0).1 hi0
  have hμ0 : L.X.nd.mu i0 = D.what₂.muTw w := by rw [L.X.nd.mu_w i0, ew]
  have hQk : Hk.cover.B.Qc j w = C.Q w :=
    (Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))
  have lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W),
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k (z • f + f') =
          z • NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f + NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f' := by
    intro v k s ϖ hvk hc hu
    have H := GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ
      (by rw [hQk]; exact hvk) hc hu
    exact GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W),
        NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej
      (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H

  have hstd : HeckeStdTw Sp.B := heckeStdTw_of_std Sp.std
  have hLoc : LocPl D j w := Or.inl hw
  have hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k := fun v k h => by rw [← Sp.Qc_eq j w]; exact h
  have key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k := by
    intro v k hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
    obtain ⟨tC, htC1, htC2⟩ := GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk
    have ht0 : tC y = c v k • y := by
      apply (M (D.what₂.muTw w) j h1 h2).real_inj
      rw [← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]
    exact htC1 (c v k) y hy ht0
  let κF : PlE D.host → ℕ → Sp.B.Oc j w := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)

  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y hy (by
      intro v k hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
      refine ⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩
      rw [hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])
  have hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))) :=
    IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have e1 := hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have e2 := he v k hvk
    change Sp.B.hK j w v k e = _ at e1
    rw [e2] at e1
    exact (smul_left_injective _ hene e1).symm
  have hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3

  obtain ⟨i, hi, hmx⟩ := Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)
  refine ⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩
  have hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by rw [Sp.Qc_eq j w]; exact hvk
  have e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z) := by
    intro z
    unfold iotaO
    rw [RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]
    exact Sp.iotaC_coh j w i hi z
  rw [e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]
  show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k
  rw [hψv v k hvk', ← hφalg, hκF v k hvk']

end GlobalTheory.EigOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenFrobeniusStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_frobenius : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  first | exact @GlobalTheory.EigOnto.main | exact GlobalTheory.EigOnto.main | (intros; apply GlobalTheory.EigOnto.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem natCast_adicCompletion_v_le_one {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) : Valued.v ((k : Q.adicCompletion E)) ≤ 1 := by
  have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) (k : 𝓞 E)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  simpa using h

theorem exists_coprime_natCast_mul_v_le_one {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∉ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨N / p ^ N.factorization p, (Nat.coprime_ordCompl hp hN0).symm, ?_⟩
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self N p
  have hvp : Valued.v ((p : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (p : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hpQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e, mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  rw [← hsplit] at hNx
  push_cast at hNx
  rw [mul_assoc, Valuation.map_mul, map_pow, hvp, one_pow, one_mul] at hNx
  exact_mod_cast hNx

end GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem bnd_of_local {E : Type} [Field E] [NumberField E] (p : ℕ) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : S.Finite)
    (hin : ∀ Q ∈ S, ∀ i j, ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * (A i j) Q) ≤ 1)
    (hout : ∀ Q ∉ S, ∀ i j, Valued.v ((A i j) Q) ≤ 1) : Bnd p A := by
  classical
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : t.1 ∈ S then Classical.choose (hin t.1 h t.2.1 t.2.2) else 1
  have hf : ∀ t, (f t).Coprime p := by
    intro t
    by_cases h : t.1 ∈ S
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (hin t.1 h t.2.1 t.2.2)).1
    · simp only [f, dif_neg h]; exact Nat.coprime_one_left p
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hS.toFinset ×ˢ Finset.univ
  refine ⟨∏ t ∈ T, f t, Nat.Coprime.prod_left fun t _ => hf t, fun i j Q => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  by_cases hQ : Q ∈ S
  · have hmem : (Q, i, j) ∈ T := by simp [T, hQ]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hmem
    rw [hk, Nat.cast_mul, mul_comm ((f (Q, i, j) : ℕ) : Q.adicCompletion E), mul_assoc,
      Valuation.map_mul]
    refine mul_le_one' (natCast_adicCompletion_v_le_one Q k) ?_
    have := (Classical.choose_spec (hin Q hQ i j)).2
    simpa only [f, dif_pos hQ] using this
  · rw [Valuation.map_mul]
    exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) (hout Q hQ i j)

theorem one_entry_v_le_one {E : Type} [Field E] [NumberField E] (n : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · have := natCast_adicCompletion_v_le_one Q 1
    simpa using this
  · let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
    change Valued.v (ev 0) ≤ 1
    rw [map_zero, map_zero]
    exact zero_le_one

theorem inv_eq_one_off {E : Type} [Field E] [NumberField E] (n : ℕ)
    (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) :
    ∀ i j, ((G⁻¹).1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have hone : ∀ i j, ev ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by
    intro i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have h1 : ev.mapMatrix G.1 = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hev, hQ, hev, hone]
  have h2 : ev.mapMatrix G.1 * ev.mapMatrix (G⁻¹).1 = 1 := by
    rw [← map_mul]
    have : G.1 * (G⁻¹).1 = 1 := by
      have := congrArg Units.val (mul_inv_cancel G)
      simpa using this
    rw [this, map_one]
  rw [h1, one_mul] at h2
  intro i j
  rw [hev, hev, hone]
  have := congrFun (congrFun h2 i) j
  rwa [RingHom.mapMatrix_apply, Matrix.map_apply] at this

theorem bnd_and_bnd_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  intro E _ _ p hp n G S hS hpS hG
  have hGi := fun Q hQ => inv_eq_one_off n G Q (hG Q hQ)
  have key : ∀ A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
      (∀ Q ∉ S, ∀ i j, (A i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) →
      Bnd p A := by
    intro A hA
    refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
    · exact exists_coprime_natCast_mul_v_le_one p hp Q (hpS Q hQ) _
    · rw [hA Q hQ i j]; exact one_entry_v_le_one n Q i j
  exact ⟨key G.1 hG, key (G⁻¹).1 hGi⟩

end GlobalTheory.StdAtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFiniteStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.StdAtPrime

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  first | exact @GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | exact GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | (intros; apply GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupport
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SuppLatStd

theorem exists_mem_only {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ b ∈ Q.asIdeal ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → b ∈ P → P = Q.asIdeal := by
  have hQ0 : Q.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero Q.ne_bot
  have hH : Fintype.card (ClassGroup (𝓞 E)) ≠ 0 := Fintype.card_ne_zero
  have hp : (Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    refine (ClassGroup.mk0_eq_one_iff (pow_mem hQ0 _)).1 ?_
    have : (⟨Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)), pow_mem hQ0 _⟩ : nonZeroDivisors (Ideal (𝓞 E))) =
        ⟨Q.asIdeal, hQ0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨b, hb⟩ := hp.principal
  have hbm : b ∈ Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) := hb ▸ Submodule.mem_span_singleton_self b
  refine ⟨b, fun h0 => ?_, Ideal.pow_le_self hH hbm, fun P hP hbP => ?_⟩
  · rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at hb
    exact pow_ne_zero _ Q.ne_bot hb
  · have hle : Q.asIdeal ^ Fintype.card (ClassGroup (𝓞 E)) ≤ P := by
      rw [hb]; exact (Ideal.span_singleton_le_iff_mem P).2 hbP
    exact (Q.isMaximal.eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm

theorem val_mul_mulVec_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K)
    (c : K) (hz : ∀ j, Valued.v (z j) ≤ 1) (hM : ∀ i j, Valued.v c * Valued.v (M i j) ≤ 1) (i : Fin n) :
    Valued.v (c * M.mulVec z i) ≤ 1 := by
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul]
  exact mul_le_one' (hM i j) (hz j)

end GlobalTheory.SuppLatStd

namespace GlobalTheory.SuppLatStd


set_option maxHeartbeats 2000000 in
theorem lat_std_of_suppAt : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  intro D V hg hL h e Ps bad he hbad hs
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.ConjVal.components_and_conj_valuation D ι h1 h2 h4
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), AE D →+* Q.adicCompletion D.host.E,
      ∀ Q z, ev Q z = ι (finPart D z) Q :=
    ⟨fun Q => ((GlobalTheory.CharLocProd.evalAt Q).comp ι.toRingHom).comp (finPart D), fun _ _ => rfl⟩
  simp only [← hev] at hid hcj
  obtain ⟨⟨es, hes, hsum⟩, horth⟩ := he
  have e1 : ∀ Q ∈ Ps, ev Q e = 1 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_eq_single Q (fun Q' h' hne => (hid _ _ (hes Q' h')).2.2 Q hne.symm)
      (fun h' => absurd hQ h'), (hid _ _ (hes Q hQ)).2.1]
  have e2 : ∀ Q, Q ∉ Ps → ev Q e = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q' h' => (hid _ _ (hes Q' h')).2.2 Q fun hh => hQ (hh ▸ h')
  have hP : ∀ Q ∈ Ps, GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ hQ' => by
    have a := congrArg (ev (GlobalTheory.IdemSupport.cP Q)) horth
    rw [map_mul, e1 _ hQ', one_mul, map_zero] at a
    have a' := hcj e Q
    rw [a, e1 Q hQ, map_zero, map_one] at a'
    exact zero_ne_one a'

  have hA1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h) = 1 := fun Q hQ hQ' => by
    have a := hcj e (GlobalTheory.IdemSupport.cP Q)
    rw [e2 _ hQ', map_zero, GlobalTheory.ClassScalarValue.cP_cP, map_eq_zero] at a
    have hu : ev Q (e + cA D e) = 0 := by rw [map_add (f := _), e2 Q hQ, a, add_zero]
    have : (ev Q).mapMatrix (mt V h - 1) = 0 := by
      refine Matrix.ext fun i j => ?_
      change ev Q ((mt V h - 1) i j) = 0
      rw [← hs i j, map_mul, hu, zero_mul]
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  have hinv : ∀ Q, (ev Q).mapMatrix (mt V h) * (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q => by
    rw [← map_mul, show mt V h * mt V h⁻¹ = 1 by unfold Formalism.L2.Theta.mt; rw [map_inv]; exact Units.mul_inv _, map_one]
  have hB1 : ∀ Q, Q ∉ Ps → GlobalTheory.IdemSupport.cP Q ∉ Ps → (ev Q).mapMatrix (mt V h⁻¹) = 1 := fun Q hQ hQ' => by
    have := hinv Q
    rwa [hA1 Q hQ hQ', one_mul] at this

  have hlog : ∀ x : WithZero (Multiplicative ℤ), ∃ n : ℕ, x ≤ WithZero.exp (n : ℤ) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, hx ▸ zero_le'⟩
    · exact ⟨(WithZero.log x).toNat, by
        rw [← WithZero.exp_log hx]; exact WithZero.exp_le_exp.2 (by rw [WithZero.log_exp]; exact Int.self_le_toNat _)⟩
  choose fn hfn using hlog
  set S := Ps ∪ Ps.image GlobalTheory.IdemSupport.cP with hS
  set f : HeightOneSpectrum (𝓞 D.host.E) × Fin V.rank × Fin V.rank → ℕ := fun p =>
    fn (Valued.v (ev p.1 (mt V h p.2.1 p.2.2))) ⊔ fn (Valued.v (ev p.1 (mt V h⁻¹ p.2.1 p.2.2))) with hf
  set N : ℕ := (S ×ˢ (Finset.univ ×ˢ Finset.univ : Finset (Fin V.rank × Fin V.rank))).sup f with hN'
  have hN : ∀ Q ∈ S, ∀ i j, Valued.v (ev Q (mt V h i j)) ≤ WithZero.exp (N : ℤ) ∧
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ WithZero.exp (N : ℤ) := by
    intro Q hQ i j
    have hle : f (Q, i, j) ≤ N := Finset.le_sup (Finset.mem_product.2 ⟨hQ, Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ j⟩⟩)
    constructor
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_left.trans hle))
    · exact (hfn _).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_sup_right.trans hle))
  have hout : ∀ Q, Q ∉ S → Q ∉ Ps ∧ GlobalTheory.IdemSupport.cP Q ∉ Ps := fun Q hQ =>
    ⟨fun h' => hQ (Finset.mem_union_left _ h'), fun h' => hQ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨_, h', GlobalTheory.ClassScalarValue.cP_cP Q⟩))⟩

  choose b hb0 hbQ hbP using fun Q : HeightOneSpectrum (𝓞 D.host.E) => exists_mem_only Q
  set m : 𝓞 D.host.E := (∏ Q ∈ S, b Q) ^ N with hm
  have hm1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ 1 :=
    fun Q => (GlobalTheory.CharLocProd.val_algebraMap Q _).trans_le (Q.valuation_le_one m)
  have hmN : ∀ Q ∈ S, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E)
      (algebraMap (𝓞 D.host.E) D.host.E m)) ≤ WithZero.exp (-(N : ℤ)) := fun Q hQ => by
    rw [GlobalTheory.CharLocProd.val_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (Ideal.pow_mem_pow ?_ N)
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hQ
    rw [hc]; exact Ideal.mul_mem_right _ _ (hbQ Q)
  have hone : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (i j : Fin V.rank),
      Valued.v ((1 : Matrix (Fin V.rank) (Fin V.rank) K) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hcond : ∀ Q i j, Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h i j)) ≤ 1 ∧
      Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m)) *
      Valued.v (ev Q (mt V h⁻¹ i j)) ≤ 1 := fun Q i j => by
    by_cases hQ : Q ∈ S
    · have k : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
        rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      exact ⟨(mul_le_mul' (hmN Q hQ) (hN Q hQ i j).1).trans k.le, (mul_le_mul' (hmN Q hQ) (hN Q hQ i j).2).trans k.le⟩
    · obtain ⟨o1, o2⟩ := hout Q hQ
      have a1 : ev Q (mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hA1 Q o1 o2) i) j
      have a2 : ev Q (mt V h⁻¹ i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Q.adicCompletion D.host.E)) i j :=
        congrFun (congrFun (hB1 Q o1 o2) i) j
      rw [a1, a2]
      exact ⟨mul_le_one' (hm1 Q) (hone i j), mul_le_one' (hm1 Q) (hone i j)⟩

  have hmat : ∀ Q, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1.map (GlobalTheory.CharLocProd.evalAt Q) =
      (ev Q).mapMatrix (mt V h⁻¹) := fun Q => by
    rw [← map_inv, ← Subgroup.coe_inv, ← map_inv]
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, hev]
    rfl
  have memG : ∀ x, x ∈ Bridge.hLat V (finPt V h) ↔ ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((((ev Q).mapMatrix (mt V h⁻¹)).mulVec
      (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i) ≤ 1 := fun x => by
    rw [GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL (finPt V h) x]
    refine forall_congr' fun i => forall_congr' fun Q => ?_
    rw [← hmat Q]
    have := RingHom.map_mulVec (GlobalTheory.CharLocProd.evalAt Q) ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V h).1)⁻¹).1
      (fun j => algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (x j)) i
    exact iff_of_eq (congrArg (fun w => Valued.v w ≤ 1) this)
  have memS : ∀ x, x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank ↔
      ∀ i (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (x i)) ≤ 1 := fun x => by
    rw [← hL, GlobalTheory.ClassScalarValue.mem_hLat ι h1 h2 V hL 1 x]
    simp only [OneMemClass.coe_one, map_one, inv_one, Units.val_one, Matrix.one_mulVec]
    rfl
  have hsm : ∀ (x : Fin V.rank → D.host.E) i, (m • x) i = algebraMap (𝓞 D.host.E) D.host.E m * x i := fun x i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  refine ⟨m, pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q), ?_, ?_, ?_⟩
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memS _).2 fun i Q => ?_)
    have hx' := (memG x).1 hx
    have e3 : algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) i) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) *
          ((ev Q).mapMatrix (mt V h)).mulVec (((ev Q).mapMatrix (mt V h⁻¹)).mulVec
            (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j))) i := by
      rw [Matrix.mulVec_mulVec, hinv Q, Matrix.one_mulVec, hsm, map_mul]
    rw [e3]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).1) i
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    refine Submodule.smul_mem _ a ((memG _).2 fun i Q => ?_)
    have hx' := (memS x).1 hx
    have e3 : (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) ((m • x) j)) =
        algebraMap D.host.E (Q.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E m) •
          (fun j => algebraMap D.host.E (Q.adicCompletion D.host.E) (x j)) := funext fun j => by
      rw [hsm, map_mul]; rfl
    rw [e3, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SuppLatStd.val_mul_mulVec_le _ _ _ (fun j => hx' j Q) (fun i j => (hcond Q i j).2) i
  · have hmap : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ Q.asIdeal := fun Q hne heq => by
      refine hne (HeightOneSpectrum.ext ?_)
      rw [← heq]
      ext x
      rw [GlobalTheory.IdemSupport.mem_cP]
      have hle : Q.asIdeal.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤
          Q.asIdeal.comap (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
        Ideal.map_le_iff_le_comap.2 fun y hy => by
          rw [Ideal.mem_comap, Ideal.mem_comap]; simpa [GlobalTheory.IdemSupport.cO_cO] using hy
      constructor
      · intro hx
        simpa [GlobalTheory.IdemSupport.cO_cO] using
          Ideal.mem_map_of_mem (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) hx
      · intro hx
        simpa using hle hx
    intro P hPp hmP
    obtain ⟨Q, hQS, hbQP⟩ := (hPp.prod_mem_iff).1 (hPp.mem_of_pow_mem _ hmP)
    obtain rfl := hbP Q P hPp hbQP
    rcases Finset.mem_union.1 hQS with hQ | hQ
    · exact ⟨hmap Q fun hc => hP Q hQ (by rw [hc]; exact hQ), hbad Q hQ⟩
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
      refine ⟨hmap _ fun hc => hP Q' hQ' ?_, fun hm' => hbad Q' hQ' ?_⟩
      · rw [GlobalTheory.ClassScalarValue.cP_cP] at hc
        rw [← hc]; exact hQ'
      · rwa [GlobalTheory.IdemSupport.mem_cP, map_natCast] at hm'

end GlobalTheory.SuppLatStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupportStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (bad : ℕ), IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e V h → ∃ m : 𝓞 D.host.E, m ≠ 0 ∧ Ideal.span {m} • Bridge.hLat V (finPt V h) ≤ Formalism.L2.Pj.stdLat D.host.E V.rank ∧ Ideal.span {m} • Formalism.L2.Pj.stdLat D.host.E V.rank ≤ Bridge.hLat V (finPt V h) ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → m ∈ P → P.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ P ∧ ((bad : ℕ) : 𝓞 D.host.E) ∉ P := by
  first | exact @GlobalTheory.SuppLatStd.lat_std_of_suppAt | exact GlobalTheory.SuppLatStd.lat_std_of_suppAt | (intros; apply GlobalTheory.SuppLatStd.lat_std_of_suppAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFibreIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnits
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.ExportSeries

namespace GlobalTheory.OnePlaceCong

def locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) : Rˣ where
  val := 1 - g + g * x
  inv := 1 - g + g * (x⁻¹ : Rˣ)
  val_inv := by
    have h := x.mul_inv
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h
  inv_val := by
    have h := x.inv_mul
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h

theorem coe_locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    ((locU g hg x : Rˣ) : R) = 1 - g + g * x := rfl

theorem locU_inv {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    (locU g hg x)⁻¹ = locU g hg x⁻¹ := rfl

variable {D : D7}

theorem finPart_locU_mem {g : AE D} (hg : g * g = g) {z : (AE D)ˣ} (hz : finPart D (z : AE D) ∈ intAE D) :
    finPart D ((locU g hg z : (AE D)ˣ) : AE D) ∈ intAE D := by
  have h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)
  have hfg : finPart D g ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])
  rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul]
  exact add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)

theorem res_locU_eq_one {A : Type} [CommGroup A] {PP : Pl D.host.E} {χ : (AE D)ˣ →* A} {c : (kP PP)ˣ →* A}
    (hχ : IsResAt χ PP c) (hI : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (N : ℕ)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (x : (AE D)ˣ) (hx : finPart D (x : AE D) ∈ intAE D)
    (y : Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ intAE D) (hxy : finPart D (x : AE D) - 1 = N • y) :
    χ (locU (idemAt PP) hI.1.1 x) = 1 := by
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have hfa := finPart_locU_mem he hx
  have hxa := GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa
  obtain ⟨hE, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI
  obtain ⟨w, rfl⟩ := GlobalTheory.SplitDualLat.finPart_surjective (D := D) y
  have hX := GlobalTheory.IdemRes.toEAf_mem_of_finPart hx
  have hW := GlobalTheory.IdemRes.toEAf_mem_of_finPart hy
  have key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0 := by
    change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]
  have key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul] at key0
    linear_combination key0
  have ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩) := by
    apply Subtype.ext
    change Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) =
      1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) *
        (1 + N • Formalism.IndefR.Datum.toEAf D w)
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]
  have hN0 : ((N : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hN
  refine (hχ _ ?_ hxa 1 ?_).trans (map_one c)
  · change (1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP
    linear_combination (-((x : AE D) - 1)) * he
  · rw [ha, map_add (f := _), map_sub, map_one, map_mul, hres, map_add (f := _), map_one, map_nsmul, nsmul_eq_mul, hN0]
    simp

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  intro D A _ PP χ κ ht N hN x hx hxy
  obtain ⟨y, hy, hxy⟩ := hxy
  have hPP : PP ∈ ({PP} : Finset (Pl D.host.E)) := Finset.mem_singleton_self PP
  have hsp : SplitSet ({PP} : Finset (Pl D.host.E)) := ht.split
  have hI := hsp.isIdemAt hPP
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have h0 : idemAt PP * cA D (idemAt PP) = 0 := hsp.mul_conj hPP hPP
  have hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, he]
  have hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) =
      1 - idemAt PP - cA D (idemAt PP) := by
    linear_combination he + hc + 2 * h0
  have hres := ht.res PP hPP

  have hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x *
      locU (1 - idemAt PP - cA D (idemAt PP)) hg x := by
    apply Units.ext
    simp only [Units.val_mul, coe_locU]
    linear_combination ((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc +
      (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0

  have hA : χ (locU (idemAt PP) he x) = 1 := res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy

  have hB : χ (locU (cA D (idemAt PP)) hc x) = 1 := by
    have hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) =
        locU (idemAt PP) he (Units.map (cA D).toMonoidHom x) := by
      apply Units.ext
      change cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)
      rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    have h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1 := by
      refine res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y)
        (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_
      · change finPart D (cA D (x : AE D)) ∈ intAE D
        rw [GlobalTheory.SplitDualLat.finPart_cA]
        exact GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1
      · change finPart D (cA D (x : AE D)) - 1 = _
        rw [GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy,
          map_nsmul]
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    set b := locU (cA D (idemAt PP)) hc x with hb
    have hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) =
        ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) := by
      change cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)
      rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]
    obtain ⟨a, ha⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz
    have hr : χ (idF D a) = 1 := ht.real a
    have ha' : idF D a = b * Units.map (cA D).toMonoidHom b := ha
    rw [ha', map_mul, hcb, h1, mul_one] at hr
    exact hr

  have hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1 := by
    have hi0 : infPart D (idemAt PP) = 0 := SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI
    have hi1 : infPart D (cA D (idemAt PP)) = 0 := by
      rw [GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]
    have hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP := Finset.sum_singleton _ _
    refine ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_
    · rw [coe_locU, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub,
        RingHom.map_one, hi0, hi1, hx.1]
      ring
    · rw [locU_inv]
      exact finPart_locU_mem hg hx.2.2
    · change (idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) *
        (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _
      rw [hidem]
      linear_combination (-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0
  rw [hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]

end GlobalTheory.OnePlaceCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnitsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  first | exact @GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | exact GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | (intros; apply GlobalTheory.OnePlaceCong.chi_eq_one_of_cong <;> assumption)
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem chi_eq_one_of_finPart : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units

theorem char_root_eq_one' (V : HSp D) {A : Type} [CommGroup A] (c : (AE D)ˣ →* A) (N : ℕ) (hN : Odd N)
    (hF : ∀ a, c (idF D a) = 1) (hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1)
    (hcong : ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1)
    (g : GA D V) (x : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hg : ∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) : c x = 1 := by
  obtain ⟨w, hw, hwe⟩ := hg
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← GlobalTheory.DetRootCong.finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹))
    (GlobalTheory.DetRootCong.quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := GlobalTheory.DetRootCong.exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.FibreIdem

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

end GlobalTheory.FibreIdem
end
