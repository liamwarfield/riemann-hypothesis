module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobenius
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.FrobSame

open Polynomial

theorem multiset_eq_of_esymm {s t : Multiset ℂ} {r : ℕ} (hs : Multiset.card s = r) (ht : Multiset.card t = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → s.esymm k = t.esymm k) : s = t := by
  have hall : ∀ k, s.esymm k = t.esymm k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · by_cases hkr : k ≤ r
      · exact h k hk hkr
      · rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega),
          Multiset.powersetCard_eq_empty _ (by omega)]
  have hp : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    simp only [hall]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, ← Polynomial.roots_multiset_prod_X_sub_C t, hp]

end GlobalTheory.FrobSame

namespace GlobalTheory.FrobSame

theorem frobEig_eq_of_eig_eq : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  intro D cf Rw Sb eig hE hC j hj1 hjm σ σ' hσ hgσ hσ' hgσ' P hP hPS heq
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  obtain ⟨hu, he⟩ := hE ⟨i, hi⟩ σ hσ hgσ P hP hPS
  obtain ⟨hu', he'⟩ := hE ⟨i, hi⟩ σ' hσ' hgσ' P hP hPS
  obtain ⟨π, hπ⟩ := hC (i + 1) hj1 hjm σ hσ hgσ
  obtain ⟨π', hπ'⟩ := hC (i + 1) hj1 hjm σ' hσ' hgσ'
  have hcard : (D.naut.frobEig (Rw.locR σ P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu, ← hπ.2.2.1 P hP, D.naut.locG_dim]
  have hcard' : (D.naut.frobEig (Rw.locR σ' P)).card = D.R.r := by
    rw [D.naut.frobEig_card _ hu', ← hπ'.2.2.1 P hP, D.naut.locG_dim]
  have hq0 : ((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ≠ 0 := by
    have e : Formalism.ConjugateSelfDual.normV P = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    rw [e]; exact_mod_cast GlobalTheory.GalChar.absNorm_ne_zero P
  let f : ℂ → ℂ := fun a => a⁻¹ * (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹
  have hfi : Function.Injective f := by
    intro a b hab
    have hc : (((cf.mu0 ⟨i, hi⟩).val P : ℂˣ) : ℂ)⁻¹ * (((Formalism.ConjugateSelfDual.normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero (Units.ne_zero _)) (inv_ne_zero (pow_ne_zero _ hq0))
    simp only [f, mul_assoc] at hab
    exact inv_injective (mul_right_cancel₀ hc hab)
  have hmap : (D.naut.frobEig (Rw.locR σ' P)).map f = (D.naut.frobEig (Rw.locR σ P)).map f := by
    refine multiset_eq_of_esymm (r := D.R.r) (by rw [Multiset.card_map, hcard'])
      (by rw [Multiset.card_map, hcard]) fun k hk1 hkr => ?_
    have e1 := he k hk1 hkr
    have e2 := he' k hk1 hkr
    rw [heq k hk1 hkr, e1] at e2
    exact (mul_left_cancel₀ (pow_ne_zero (k * (D.R.r - k) / 2) hq0) e2).symm
  exact Multiset.map_injective hfi hmap

end GlobalTheory.FrobSame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobeniusStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  first | exact @GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | exact GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | (intros; apply GlobalTheory.FrobSame.frobEig_eq_of_eig_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvalues
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.TripRho

open GlobalTheory.TwistedSelmerCompare GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions _root_.Formalism.L2.NR


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isRhoOfRow_of_frobEig : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  intro D Rw rowS hRho hGP a σ s hRT hs hj hg hloc hfe
  obtain ⟨hiso, hgood, hspec⟩ := hRho (D.ntw.twOf a) s
  have hjr := D.nd.j_range a
  have hσs : D.what₂.isot (D.nd.j a) (rowS _ s) ≠ ⊥ := by rw [← hj]; exact hiso
  obtain ⟨π', hc', hr', hl', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 (rowS _ s) hσs hgood
  obtain ⟨π'', -, -, hl'', -, -, -⟩ := hGP (D.nd.j a) hjr.1 hjr.2 σ hg.1 hg.2
  obtain ⟨φ, ι, h1, h2, h3⟩ := hRT
  have h2' : ∀ x : ↥D.LL0, ι (φ ((if D.ntw.side (D.ntw.twOf a) s then D.ntw.emb0 (D.ntw.twOf a)
      else D.ntw.emb0b (D.ntw.twOf a)) x)) = embLL0 D x := by
    intro x; rw [hs]; exact h2 x
  obtain ⟨-, hss, hev⟩ := hspec π' hc' hr' hl' φ ι h1 h2'
  refine ⟨?_, ?_⟩
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    have e1 : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    have e2 : mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
        (D.ntw.rhoS _ s) = mapRep φ (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      rfl
    rw [e1, isSSRep_map_iff]
    rw [e2, isSSRep_map_iff] at hss
    exact hss
  · filter_upwards [hev, D.naut.locG_unr_ae π', D.naut.locG_unr_ae π'', hfe] with w hw hu' hu'' hf hsp
    intro B g hB hg'
    have hR : Rw.locR (rowS _ s) w = Rw.locR σ w := by
      have u1 : D.naut.unr (Rw.locR (rowS _ s) w) := by rw [← hl' w hsp]; exact hu'
      have u2 : D.naut.unr (Rw.locR σ w) := by rw [← hl'' w hsp]; exact hu''
      rw [D.naut.unr_eq_lpUnr _ u1, D.naut.unr_eq_lpUnr _ u2, hf hsp]
    have hpar : D.naut.locG (D.naut.tw π' D.naut.etaTinv) w =
        D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [D.naut.locG_tw, hl' w hsp, hR, hloc w hsp]
    have hcp := hw B g hB hg'
    rw [hpar] at hcp
    refine Eq.trans ?_ hcp
    have hcomp : (iotaO D.nd D.naut a).comp (D.ntw.twist₂ a) =
        ι.toRingHom.comp (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := by
      ext y
      exact (h3 y).symm
    have e1 : ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map (D.ntw.twist₂ a) := rfl
    have e2 : ((mapRep (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))))
          (D.ntw.rhoS (D.ntw.twOf a) s) g : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((D.ntw.rhoS (D.ntw.twOf a) s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).map
            (φ.comp (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))) := rfl
    rw [e1, Matrix.charpoly_map, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, ← e2]

end GlobalTheory.TripRho

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvaluesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRhoOfRow_of_frobenius_eigenvalues : ∀ (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT), GlobalTheory.HeightCounting.RhoSpec D Rw rowS → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (s : D.ntw.Sig (D.ntw.twOf a)), GlobalTheory.RowTriple.ReadTw D a → D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsGoodRow D a σ → (∀ w, IsSplitPl D.host w → D.naut.locW a σ w = Rw.locR σ w) → (∀ᶠ P in Filter.cofinite, IsSplitPl D.host P → D.naut.frobEig (Rw.locR (rowS _ s) P) = D.naut.frobEig (Rw.locR σ P)) → GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.IsRhoOfRow D a σ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.rhoTrip D a s) := by
  first | exact @GlobalTheory.TripRho.isRhoOfRow_of_frobEig | exact GlobalTheory.TripRho.isRhoOfRow_of_frobEig | (intros; apply GlobalTheory.TripRho.isRhoOfRow_of_frobEig <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem exists_sig_of_row (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hOcc : EigOcc D S θ hL Sb eig) (hall : D.nexp.sig_all) (i : D.ntw.Tw) (b : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (hiso : D.what₂.isot j σ ≠ ⊥) (hgood : D.nd.goodRow σ) :
    ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P →
      P ∉ D.ntw.S0 i → eig j (Bs.rowS i s) k P = eig j σ k P := by
  classical
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc j h1 h2 σ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i b x hx0
  set e := Bs.eF i j b h1 h2 with he
  have hfix : MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))
      (G0g D.nd) (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b)
      (e.symm (Φ x)) = e.symm (Φ x) := by
    letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A j).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  have hhk : ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      D.nexp.hkF i j b k P (e.symm (Φ x)) =
        (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
          (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P))) • e.symm (Φ x) := by
    intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply]
    have h3 := hΦT (hL j k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm
  obtain ⟨s, hj, hb, hs⟩ := hall i j b (e.symm (Φ x))
    (fun k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
      (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P)))
    (by simpa using hΦ0) hfix hhk
  refine ⟨s, hj, hb, fun k P hk1 hk2 hsp hP => ?_⟩
  have h3 := hs k P hk1 hk2 hsp hP
  rw [Bs.rowS_eig i s k P hk1 hk2 hsp hP] at h3
  subst hj hb
  have hu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i (D.ntw.side i s) P : D.ntw.O i) ^ k ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact (Bs.cHk i (D.ntw.side i s) P).ne_zero
  exact (readLL0 S i (D.ntw.side i s)).injective (mul_left_cancel₀ (M₀ := FractionRing (D.ntw.O i)) hu h3)

end GlobalTheory.RowTriple

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem tripAll_of_sideB (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hT : EigTrue D cf Rw Sb eig) (hOcc : EigOcc D S θ hL Sb eig) (hP : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw)
    (hall : D.nexp.sig_all) (hloc : ∀ a σ v, IsSplitPl D.host v → D.naut.locW a σ v = Rw.locR σ v)
    (hR : ∀ a, ReadTw D a) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.TripAll D := by
  classical
  intro a σ hσ
  obtain ⟨hiso, hgood⟩ := hσ
  obtain ⟨h1, h2⟩ := D.nd.j_range a
  obtain ⟨s, hj, hb, he⟩ := exists_sig_of_row D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc hall (D.ntw.twOf a)
    (D.ntw.twSide a) (D.nd.j a) h1 h2 σ hiso hgood
  obtain ⟨hiso', hgood', -⟩ := Bs.rhoS _ s
  rw [hj] at hiso'
  refine ⟨s, hj, hb, GlobalTheory.T.isRhoOfRow_of_frobenius_eigenvalues D Rw Bs.rowS Bs.rhoS hP a σ s (hR a) hb hj ⟨hiso, hgood⟩ (hloc a σ) ?_⟩
  have hfin : ((Sb ∪ D.ntw.S0 (D.ntw.twOf a) : Finset (PlE D.host)) : Set (PlE D.host)).Finite := Finset.finite_toSet _
  filter_upwards [hfin.compl_mem_cofinite] with P hP' hsp
  have hP1 : P ∉ Sb := fun h => hP' (by simp [h])
  have hP2 : P ∉ D.ntw.S0 (D.ntw.twOf a) := fun h => hP' (by simp [h])
  exact GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius D cf Rw Sb eig hT hP (D.nd.j a) h1 h2 σ (Bs.rowS _ s) hiso hgood hiso' hgood' P hsp hP1
    fun k hk1 hk2 => he k P hk1 hk2 hsp hP2

end GlobalTheory.RowTriple

end
