module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwist

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityBoundTransferOfCmDatum
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityPosOfRestrictedEigenformCopy
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideEigenformCopyTransfer
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepTransportOfCopyAll
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
private theorem multiset_eq_of_esymm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r)
    (h : ∀ k, 1 ≤ k → k ≤ r → M.esymm k = M'.esymm k) : M = M' := by
  have hp : (M.map fun a => Polynomial.X - Polynomial.C a).prod = (M'.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, h1, h2]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [Multiset.esymm]
    · rw [h k hk0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, hp, Polynomial.roots_multiset_prod_X_sub_C]
private theorem multiset_eq_of_norm_pz (M M' : Multiset ℂ) (r : ℕ) (h1 : M.card = r) (h2 : M'.card = r) (q u : ℂ) (n : ℕ)
    (hq : q ≠ 0) (hu : u ≠ 0)
    (h : ∀ k, 1 ≤ k → k ≤ r → q ^ (k * (r - k) / 2) * (M.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k =
      q ^ (k * (r - k) / 2) * (M'.map fun a => a⁻¹ * u⁻¹ * (q ^ n)⁻¹).esymm k) : M = M' := by
  have hinj : Function.Injective fun a : ℂ => a⁻¹ * u⁻¹ * (q ^ n)⁻¹ := fun a b hab =>
    inv_injective (mul_right_cancel₀ (inv_ne_zero hu) (mul_right_cancel₀ (inv_ne_zero (pow_ne_zero _ hq)) hab))
  refine Multiset.map_injective hinj (multiset_eq_of_esymm_pz _ _ r (by rw [Multiset.card_map, h1])
    (by rw [Multiset.card_map, h2]) fun k a b => mul_left_cancel₀ (pow_ne_zero _ hq) (h k a b))
private theorem isRepOf_of_split_pz (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₂ : IsRepOf D l ι π s ρ₂)
    (c₁ : Continuous (fun g => ((ρ₁ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))) (s₁ : IsSSRep ρ₁)
    (f₁ : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((ρ₁ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)) : IsRepOf D l ι π s ρ₁ := by
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, hs, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 hs B g hB hg, hw.2 B g hB hg])
  refine ⟨c₁, s₁, f₂.mono fun w hw B σ hB hσ => ?_⟩
  rw [hcp σ]
  exact hw B σ hB hσ
private theorem side_data_pz (D : D7) (cf : CharFrame D) (hCS : CharSide D cf) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (hE : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (S : RatDat D.ntw)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT)
    (hR : RowEig D S eig c rowS) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hi : D.what₂.isot (D.ntw.jS i s) (rowS i s) ≠ ⊥) (hg : D.nd.goodRow (rowS i s)) (π : D.naut.CG D.R.r)
    (hπ : ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR (rowS i s) w) (j : Fin D.R.m) (hj : j.1 + 1 = D.ntw.jS i s)
    (t : ℝ) (P : PlE D.host) (hP : IsSplitPl D.host P) (h1 : P ∉ Sb) (h2 : P ∉ D.ntw.S0 i) :
    ∃ M : Multiset ℂ, M.card = D.R.r ∧
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) P) t) =
        (((M.map (· * ((cf.eta.val P : ℂˣ) : ℂ))).map (· * ((normV P : ℕ) : ℂ) ^ ((t : ℝ) : ℂ))).map
          fun α => Polynomial.X - Polynomial.C α).prod ∧
      ∀ k, 1 ≤ k → k ≤ D.R.r → ∃ x : ↥D.LL0, embLL0 D x = ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * (M.map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k ∧
        algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) =
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i (D.ntw.side i s) P) ^ k *
            IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
              (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
              ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x) := by
  obtain ⟨hu, he⟩ := hE j (rowS i s) (by rw [hj]; exact hi) hg P hP h1
  rw [← hπ P hP] at hu he
  refine ⟨D.naut.frobEig (D.naut.locG π P), by rw [D.naut.frobEig_card _ hu, D.naut.locG_dim], ?_, fun k a b => ?_⟩
  · have hue : D.naut.unr (D.naut.locG D.naut.etaTinv P) := (D.naut.etaTinv_def P).1
    have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv P) = {((cf.eta.val P : ℂˣ) : ℂ)} := by
      rw [hCS.frob _ P ((hCS.unr_iff _ P).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
    have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv P) = 1 := D.naut.locG_dim _ P
    rw [galPol, D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue),
      D.naut.frobEig_char _ _ _ hu hue hd hfe]
  · refine ⟨eig (D.ntw.jS i s) (rowS i s) k P, ?_, hR i s k P a b hP h2⟩
    have := he k a b
    rw [hj] at this
    exact this
private theorem read_cancel_pz (D : D7) (i : D.ntw.Tw) (b : Bool) (u : (D.ntw.O i)ˣ) (k : ℕ) (x y : ↥D.LL0)
    (h : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u ^ k *
        IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
          (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) ((if b then D.ntw.emb0 i else D.ntw.emb0b i) y)) : x = y :=
  RingHom.injective _ (RingHom.injective _ (mul_left_cancel₀ (pow_ne_zero _ (u.isUnit.map _).ne_zero) h))
theorem UpperTheory.galoisRep_transport_of_copyAll_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → ∀ (Rw : RowSide D) (jE' : D'.host.E →+* Qb) (A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D' cf' jE'), RowCusp D Rw → GalEx D' → GlobalTheory.RowTie.ChebSplit D'.nd → ∀ (Sb : Finset (PlE D.host)) (Sb' : Finset (PlE D'.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (eig' : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' eig' → ∀ (S : RatDat D.ntw) (S' : RatDat D'.ntw) (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) (c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ), SameUnits c c' → ∀ (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) (rowS' : ∀ i, D'.ntw.Sig i → D'.what₂.FT), RowEig D S eig c rowS → RowEig D' S' eig' c' rowS' → RhoSpec D Rw rowS → (∀ i s, D'.what₂.isot (D'.ntw.jS i s) (rowS' i s) ≠ ⊥ ∧ D'.nd.goodRow (rowS' i s)) → RhoSpec D' A'.row rowS' := by
  intro hGA D D' ι e h cf cf' hF hCS Rw jE' A' hRC hGal hCh Sb Sb' eig eig' hE hE' S S' c c' hU rowS rowS' hR hR' hρ hgood
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i s
  refine ⟨(hgood i s).1, (hgood i s).2, fun π' hc hr hloc φ ιq hφ hι => ?_⟩
  obtain ⟨hi, hg, hspec⟩ := hρ i s
  have hjr := D.ntw.jS_range i s
  obtain ⟨π, pc, pr, ploc, -⟩ := hRC _ hjr.1 hjr.2 _ hi hg
  have hemb : ∀ x, (if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) (e x) =
      (if (overD D r).ntw.side i s then (overD D r).ntw.emb0 i else (overD D r).ntw.emb0b i) x := by
    intro x
    have e1 := eq_of_heq (h.cp.emb0 i i HEq.rfl x)
    have e2 := eq_of_heq (h.cp.emb0b i i HEq.rfl x)
    have e3 : (overD D r).ntw.side i s = D.ntw.side i s := rfl
    rw [e3]
    cases D.ntw.side i s
    · exact e2
    · exact e1
  have hι0 : ∀ x : ↥D.LL0, ιq (φ ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hemb y, h.cp.embLL0_eq]
    exact hι y
  obtain ⟨c1, s1, f1⟩ := hspec π pc pr ploc φ ιq hφ hι0
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt hGA _ cf' jE' A' hGal _ ιq π' hc hr
  refine isRepOf_of_split_pz _ ιq _ _ hCh _ ρ' hρ' c1 s1 ?_
  have hmu : cf.mu0 = cf'.mu0 := eq_of_heq hF.mu0
  have heta : cf.eta = cf'.eta := eq_of_heq hF.eta
  have hcc : ∀ b P, c' i b P = c i b P := fun b P => eq_of_heq (hU i i b P P HEq.rfl HEq.rfl)
  have hj : (⟨D.ntw.jS i s - 1, by omega⟩ : Fin D.R.m).1 + 1 = D.ntw.jS i s := Nat.sub_add_cancel hjr.1
  filter_upwards [f1, Sb.eventually_cofinite_notMem, Sb'.eventually_cofinite_notMem,
    (D.ntw.S0 i).eventually_cofinite_notMem] with P hP n1 n2 n3 hs B σ hB hσ
  obtain ⟨M, m1, m2, m3⟩ := side_data_pz D cf hCS Rw Sb eig hE S c rowS hR i s hi hg π ploc _ hj
    ((1 - (D.R.nV : ℝ)) / 2) P hs n1 n3
  obtain ⟨M', m1', m2', m3'⟩ := side_data_pz _ cf' A'.chr A'.row Sb' eig' hE' S' c' rowS' hR' i s (hgood i s).1 (hgood i s).2
    π' hloc _ hj ((1 - (D.R.nV : ℝ)) / 2) P hs n2 n3
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 := by
    have hn : normV P = Ideal.absNorm P.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    exact Nat.cast_ne_zero.mpr fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp (hn ▸ h0))
  have hM : M = M' := by
    refine multiset_eq_of_norm_pz M M' D.R.r m1 m1' _ _ (D.R.nV / 2) hq
      ((cf.mu0 ⟨D.ntw.jS i s - 1, by omega⟩).val P).ne_zero fun k a b => ?_
    obtain ⟨x, x1, x2⟩ := m3 k a b
    obtain ⟨y, y1, y2⟩ := m3' k a b
    rw [← hmu] at y1
    rw [← hemb y, hcc] at y2
    have hxy : x = e y := read_cancel_pz D i _ _ k _ _ (x2.symm.trans y2)
    refine x1.symm.trans (Eq.trans ?_ y1)
    rw [hxy, h.cp.embLL0_eq]
  subst hM
  rw [← heta] at m2'
  exact (hP B σ hB hσ).trans (m2.trans m2'.symm)
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.HeightCounting.SideCopy.Restage
set_option maxHeartbeats 1000000
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
private theorem eigen_zero_one_transfer (h : CopyAll D D' ι e)
    (hs : ∀ i (s : D.ntw.Sig i) P, D.ntw.hEig i s 0 P = 1) : ∀ i (s : D'.ntw.Sig i) P, D'.ntw.hEig i s 0 P = 1 := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact hs
private theorem lowAll_eq (h : CopyAll D D' ι e) : lowAll D' = lowAll D := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact ((Eq.refl (lowAll D)) :))
private theorem over_S0_transfer (h : CopyAll D D' ι e) (low : Finset ℕ) (hs : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) low)) :
    ∀ i, OverSet D' (D'.ntw.S0 i) (insert (D'.ntw.l i) low) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem hecke_map_transfer (h : CopyAll D D' ι e) (hs : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i →
      IsSplitPl D.host P → k ≤ D.R.r →
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)) :
    ∀ i j b k P (x : D'.ntw.B i j b), 1 ≤ j → j ≤ D'.R.m → P ∉ D'.ntw.S0 i → IsSplitPl D'.host P → k ≤ D'.R.r →
      D'.nexp.embB i j b (D'.ntw.hk i j b k P x) = D'.nexp.hkF i j b k P (D'.nexp.embB i j b x) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem eigen_system_transfer (h : CopyAll D D' ι e)
    (hs : ∀ i (s : D.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (GlobalTheory.EigTie.sigEv s)) :
    ∀ i (s : D'.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D'.nexp i (D'.ntw.jS i s) (D'.ntw.side i s) (GlobalTheory.EigTie.sigEv s) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  exact (by with_unfolding_all exact (hs :))
private theorem emb_eq_of_equiv {r : Rest D} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) (i : D.ntw.Tw) (x : ↥(overD D r).LL0) :
    D.ntw.emb0 i (e x) = (overD D r).ntw.emb0 i x ∧ D.ntw.emb0b i (e x) = (overD D r).ntw.emb0b i x :=
  ⟨eq_of_heq (h.emb0 i i HEq.rfl x), eq_of_heq (h.emb0b i i HEq.rfl x)⟩
private theorem hecke_coeff_transfer (h : CopyAll D D' ι e) {c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ}
    {c' : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ} (hc : SameUnits c c')
    (hs : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
      c i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)) :
    ∀ i b P, P ∉ D'.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D'.host.E D'.nd.Om, IsFrob (F := D'.host.E) (D'.nd.plOm.1 P) (normV P) σ →
      c' i b P = Units.map (algebraMap (D'.ntw.O0 i) (D'.ntw.O i)).toMonoidHom
        (if b then D'.ntw.delta i σ else (D'.ntw.delta i σ)⁻¹) := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  intro i b P hP σ hσ
  have h1 := eq_of_heq (hc i i b P P HEq.rfl HEq.rfl)
  have h2 := hs i b P hP σ hσ
  exact (by with_unfolding_all exact ((h1.trans h2) :))
private theorem psi_law_transfer (h : CopyAll D D' ι e) {S : RatDat D.ntw} {S' : RatDat D'.ntw} {θ θ'} (h1 : PsiStd D θ) (h2 : PsiStd D' θ')
    (h3 : PsiLaw D S θ) : PsiLaw D' S' θ' := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hpl : D.naut.plGw = (overD D r).naut.plGw := eq_of_heq h.pl
  have hxi : ∀ kv, NX.xiRed (overD D r) kv = NX.xiRed D kv := fun kv => by
    unfold NX.xiRed NX.pG
    rw [← hpl]
    rfl
  intro i b u hu hu'
  have a1 := h1 ⟨u, hu'⟩
  have a2 := h2 ⟨u, hu'⟩
  simp only [hxi] at a2
  have a3 : e ((psiUOf (overD D r).nd (NX.xiRed (overD D r)) θ' ⟨u, hu'⟩ : (↥(overD D r).LL0)ˣ) : ↥(overD D r).LL0) =
      ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0) := by
    apply (embLL0 D).injective
    rw [h.cp.embLL0_eq, a1]
    simp only [hxi]
    exact (by with_unfolding_all exact (a2 :))
  have a4 := h3 i b u hu hu'
  rw [← a3] at a4
  have a5 : ∀ (i : D.ntw.Tw) x, readLL0 S i b (e x) = readLL0 S' i b x := fun i x => by
    obtain ⟨b1, b2⟩ := emb_eq_of_equiv h.cp i x
    cases b
    · exact (by with_unfolding_all exact ((congrArg (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) b2) :))
    · exact (by with_unfolding_all exact ((congrArg (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) b1) :))
  exact (by with_unfolding_all exact ((a4.trans (a5 i _)) :))
open _root_.Formalism.L2.DIV GlobalTheory.HeightCounting.ThetaSt in
private theorem psi_standard_of_units {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) {θ}
    (hl : ∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd)
    (hp : ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) : PsiStd D θ := by
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  rintro ⟨v, hv⟩
  obtain ⟨g, rfl⟩ := eG.surjective v
  let u : P0 := ⟨g, (hl g).2 hv⟩
  have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
  have h1 := hp u hv
  rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum] at h1
  have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), D.what₂.embLL (ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) =
      Complex.exp (2 * Real.pi * Complex.I / (D.host.g kv.1 : ℂ)) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
        (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
    intro kv
    have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
        (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
      rw [map_mul, _root_.GlobalTheory.HeightCounting.ThetaSt.res_xiBar_alt kv (hT.place kv), hT.comp u kv, ThetaSt.supSum_map]
      rfl
    rw [← hres]
    have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
        (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
      apply (res kv).injective
      rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hW kv _ _ hb, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine (congrArg D.what₂.embLL h1).trans ?_
  rw [← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
    map_inv₀, map_prod, Finset.prod_inv_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun kv _ => hfac kv)
private theorem lambda_datum_transfer (h : CopyAll D D' ι e) {cf : CharFrame D} {cf' : CharFrame D'} (hf : SameFrame cf cf')
    (hs : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) :
    ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  obtain ⟨Z, hO, hT, rfl, hq, hF⟩ := hs
  have hmu : Z.C.mu0 = cf'.mu0 := eq_of_heq hf.mu0
  have hd : Z.C.del = cf'.del := eq_of_heq hf.del
  have hd' : Z.C.del' = cf'.del' := eq_of_heq hf.del'
  have hj : D.ntw.jL = (overD D r).ntw.jL := eq_of_heq h.jL
  have hs2 : D.ntw.s2 = (overD D r).ntw.s2 := eq_of_heq h.s2
  have hX : D.ntw.Xv = (overD D r).ntw.Xv := eq_of_heq h.Xv
  let Z' : GlobalTheory.LamTie.LamDat (overD D r) := ⟨cf', Z.q0, Z.w0, Z.c, Z.chi⟩
  have hl : ∀ l a c, Z'.lam0 l a c = Z.lam0 l a c := fun l a c => by
    change cf'.mu0 a * (if l = D.host.pde then cf'.del' else cf'.del) * _ = _
    rw [← hmu, ← hd, ← hd']
    rfl
  refine ⟨Z', ⟨(by with_unfolding_all exact (hO.places :)), (by with_unfolding_all exact (hO.aux :)), (by with_unfolding_all exact (hO.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((h.cp.inW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), j, fun x => ?_, ?_⟩
  · exact (by with_unfolding_all exact (((congrArg j (h.cp.embLL0_eq x).symm).trans ((t1 (e x)).trans
      (congrArg (GlobalTheory.ToricDenom.toBar D.ntw i) (emb_eq_of_equiv h.cp i x).1))) :))
  · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, ← hj, ← hs2, ← hX]
    simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk] at t2
    exact (by with_unfolding_all exact (t2 :))
open GlobalTheory.EigTie GlobalTheory.TwInputs Formalism.MainNotions.IntegralHeckeForms in
private theorem is_eig_sys_sig_ev_of_eig_occ {cf : CharFrame D} {Rw low Pq S hL eig θ} (Bs : SideB D cf Rw low Pq S hL eig θ) {Sb : Finset (PlE D.host)} (hSb : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) (hOcc : EigOcc D S θ hL Sb eig) (i : D.ntw.Tw) (s : D.ntw.Sig i) :
    IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (sigEv s) := by
  classical
  obtain ⟨h1, h2⟩ := D.ntw.jS_range i s
  obtain ⟨hiso, hgood, -⟩ := Bs.rhoS i s
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc _ h1 h2 _ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i (D.ntw.side i s) x hx0
  set e := Bs.eF i (D.ntw.jS i s) (D.ntw.side i s) h1 h2 with he
  have hact : ∀ g : G0g D.nd, e (D.nexp.actG i _ _ g (e.symm (Φ x))) = Φ (actL D S (D.ntw.jS i s) g x) := fun g => by
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    have hc : ((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A (D.ntw.jS i s)).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  have hE : eG D.nexp i _ _ (e.symm (Φ x)) = e.symm (Φ x) := by
    letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [hact]
    rfl
  have hU : e.symm (Φ x) ∈ Fm0 D.nexp i (D.ntw.jS i s) (D.ntw.side i s) := by
    simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    rintro ⟨u, hu⟩
    have hu' : u ∈ Formalism.IndefR.NX.U D.nd := by
      have := hu
      rw [Bs.exp.U_eq] at this
      exact this
    have hx2 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hxg).2 ⟨u, hu'⟩)
    apply e.injective
    rw [map_smul, e.apply_symm_apply, Bs.psiU i _ u hu hu']
    refine (hact u).trans ?_
    rw [hx2, hΦs]
    rfl
  refine ⟨e.symm (Φ x), ⟨_, hU, hE⟩, by simpa using hΦ0, ?_⟩
  rintro k P ⟨hk1, hk2, hsp, hP⟩
  apply e.injective
  rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply, sigEv,
    Bs.rowS_eig i s k P hk1 hk2 hsp hP]
  have h3 := hΦT (hL (D.ntw.jS i s) k P) (Bs.hs _ h1 h2 k P) x
  rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
  rw [mul_smul]
  congr 1
  exact h3.symm
theorem side_data_transferred_alt (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (h : CopyAll D D' ι e) {cf : CharFrame D} {cf' : CharFrame D'}
    (hf : SameFrame cf cf') (hCS : CharSide D cf) {Rw Pq S hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ)
    {jE'} (A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D' cf' jE') (hRC : RowCusp D Rw) (hG : GalEx D') (hCh : GlobalTheory.RowTie.ChebSplit D'.nd)
    {S' : RatDat D'.ntw} (In : RatIn D' S') (hSb : OverSet D' In.Sb (lowAll D')) {Sb Sb'}
    (hT : GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig) (hT' : GlobalTheory.TwInputs.EigTrue D' cf' A'.row Sb' In.eig)
    (hE : ∀ i (s : D.ntw.Sig i), GlobalTheory.EigTie.IsEigSys D.nexp i (D.ntw.jS i s) (D.ntw.side i s) (GlobalTheory.EigTie.sigEv s))
    (hψ : PsiStd D θ) (hψ' : PsiStd D' In.θ) {Pq'}
    (c : ∀ (i : D'.ntw.Tw) (_b : Bool) (_P : PlE D'.host), (D'.ntw.O i)ˣ) (hc : SameUnits B.cHk c) (X : NExpTied D')
    (pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (hadm : NX.AdmTw D' i k Q ψ),
      (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D' Pq' Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D' Pq' (D'.ntw.pD i))
    (eF : ∀ i j b, 1 ≤ j → j ≤ D'.R.m → D'.nexp.Fm i j b ≃ₗ[FractionRing (D'.ntw.O i)] Fm S' i j b)
    (bsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i j b),
      x ∈ D'.nexp.Bsup i j b ↔ eF i j b h1 h2 x ∈ Bsup S' i j b)
    (act : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i j b),
      eF i j b h1 h2 (D'.nexp.actG i j b g x) = actG S' i j b (In.rho j h1 h2) (In.chi j h1 h2) g (eF i j b h1 h2 x))
    (hkEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (k : ℕ) (P : PlE D'.host) (x : D'.nexp.Fm i j b), P ∉ D'.ntw.S0 i →
      IsSplitPl D'.host P → k ≤ D'.R.r → eF i j b h1 h2 (D'.nexp.hkF i j b k P x) =
        algebraMap (D'.ntw.O i) (FractionRing (D'.ntw.O i)) (c i b P) ^ k •
          hkF D' S' i j b (In.hL j) (In.hs j h1 h2) k P (eF i j b h1 h2 x)) :
    ∃ B' : SideB D' cf' A'.row (lowAll D') Pq' S' In.hL In.eig In.θ, B'.exp = X ∧ B'.eF = eF ∧ ∀ i, In.Sb ⊆ D'.ntw.S0 i := by
  obtain ⟨Rp⟩ : Nonempty (RingPart D' cf' (lowAll D')) := by
    rw [lowAll_eq h]
    exact UpperTheory.nonempty_coefficientRingData_of_isomorphic_CMDatum h hf A'.bare _ (RingPart.of B)
  have hS : ∀ i, In.Sb ⊆ D'.ntw.S0 i := hSb.subset_twistExceptionalPlaces subset_rfl Rp.tw
  have hP : PsiLaw D' S' In.θ := psi_law_transfer h hψ hψ' B.psiU
  have hrow := fun i (s : D'.ntw.Sig i) => UpperTheory.heckeEigenspace_descent_of_equivariant_equiv D' S' In X.U_eq hP hS c eF act hkEq i _ _ (D'.ntw.jS_range i s).1
    (D'.ntw.jS_range i s).2 _ (eigen_system_transfer h hE i s)
  choose rowS r1 r2 r3 using hrow
  have hρ : RhoSpec D' A'.row rowS := _root_.UpperTheory.galoisRep_transport_of_copyAll_alt hArt h hf hCS Rw jE' A' hRC hG hCh Sb Sb' eig In.eig hT hT' S S' B.cHk c hc
    B.rowS rowS B.rowS_eig r3 B.rhoS fun i s => ⟨r1 i s, r2 i s⟩
  exact ⟨{ twF := Rp.twF, tw := Rp.tw, cover := UpperTheory.sidePlace_exists_of_copyAll h B.cover, chiD := Rp.chiD, chi := Rp.chi, eta_eq := Rp.eta_eq
           ringSpec_normalisedCharacter_eq := Rp.ringSpec_normalisedCharacter_eq, del_eq := Rp.del_eq, iCq_embO := Rp.iCq_embO, embO_star := Rp.embO_star
           deltaRead := Rp.deltaRead, exp := X, pq := pq, psiU := hP, rho := In.rho, chiL := In.chi, hs := In.hs, eF := eF
           bsup := bsup, act := act, cHk := c, hkEq := hkEq, cHk_del := hecke_coeff_transfer h hc B.cHk_del, hk_emb := hecke_map_transfer h B.hk_emb
           sigSpan := sigSpan_copy h B.sigSpan, rowS := rowS, rowS_eig := r3, hEig_zero := eigen_zero_one_transfer h B.hEig_zero, rhoS := hρ },
    rfl, rfl, hS⟩
private theorem exists_full_equiv {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : GlobalTheory.HeightCounting.Up.CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩
end GlobalTheory.HeightCounting.SideCopy.Restage
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.SideCopy.Restage
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
private theorem frame_components_heq_alt {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
section State
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
private theorem same_frame_of_eq {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {P' : Pre2 K w'}
    (hB : B'.toPre = B.toPre) (hf : HEq f' f) (x : St P) (x' : St P') : SameFrame (cfOf x) (cfOf x') := by
  have h : HEq w'.I.C w.I.C := (heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm)
  obtain ⟨h1, h2, h3, h4⟩ := frame_components_heq_alt hB h
  exact ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩
theorem psi_std_of_level_i {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) : PsiStd (Dof x) l.rat.In.θ :=
  psi_standard_of_units x.m.z.pins.keep.psi l.rat.rat.lvl l.rat.rat.psi
theorem eig_true_and_eig_occ_of_low {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) {Sb : Finset (PlE (Dof x).host)} (h1 : l.rat.In.Sb ⊆ Sb)
    (h2 : GlobalTheory.TwInputs.Eig.Low (Dof x) Sb) : GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb l.rat.In.eig ∧
      GlobalTheory.TwInputs.EigOcc (Dof x) l.rat.S l.rat.In.θ l.rat.In.hL Sb l.rat.In.eig := by
  have h := _root_.GlobalTheory.TwInputs.Eig.eig_of_rational_adjoint hL x.r.Y x.m.z.pins.char.base.lev x.m.intersectionNumber_baseChange.prim.unif x.m.z.pins.char.base.models.HW
    x.m.z.good.2 l.rat.rat l.a.A.wdT l.a.A.row l.a.row h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨(congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb l.rat.In.eig) hC).mp h.1, h.2⟩
end State
private theorem eig_low_s0 (D : D7) {F : TwFrameC D} (T : TwistFrameLowIndexCompatibility D F (lowAll D)) (i : D.ntw.Tw) :
    GlobalTheory.TwInputs.Eig.Low D (D.ntw.S0 i) := by
  refine (GlobalTheory.TwInputs.Eig.low_SbD D).mono (OverSet.subset_twistExceptionalPlaces (fun P hP => ?_) subset_rfl T i)
  obtain ⟨p, h1, -, h3⟩ := (RatSide.lowSet_finite D).mem_toFinset.1 hP
  exact ⟨p, h1, h3⟩
end GlobalTheory.HeightCounting.SideCopy.Restage
open GlobalTheory.HeightCounting.SideCopy GlobalTheory.HeightCounting.SideCopy.Restage in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.side_eigenform_copy_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∀ X : NExpTied (Dof x''), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) → ∀ eF : (∀ i j b, 1 ≤ j → j ≤ (Dof x'').R.m → (Dof x'').nexp.Fm i j b ≃ₗ[FractionRing ((Dof x'').ntw.O i)] Fm l''.rat.S i j b), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (y : (Dof x'').nexp.Fm i j b), y ∈ (Dof x'').nexp.Bsup i j b ↔ eF i j b h1 h2 y ∈ Bsup l''.rat.S i j b) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (g : G0g (Dof x'').nd) (y : (Dof x'').nexp.Fm i j b), eF i j b h1 h2 ((Dof x'').nexp.actG i j b g y) = actG l''.rat.S i j b (l''.rat.In.rho j h1 h2) (l''.rat.In.chi j h1 h2) g (eF i j b h1 h2 y)) → (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (eF i j b h1 h2 y)) → ∃ b0 : _root_.GlobalTheory.HeightCounting.SettingsFormsData l''.a l''.rat l''.Pq, b0.Bs.exp = X ∧ b0.Bs.eF = eF := by
  intro hPr _ hL K B' f' T' w' _ _ _ B f T w hE hf _ _ _ _ _ P x lb P' _ x' _ hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _
    cHk hc X hpq eF hsup hact hecke_map_transfer
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := exists_full_equiv hN hG.pl hD
  have hF : SameFrame (cfOf x) (cfOf x'') := same_frame_of_eq hE.1 hf x x''
  obtain ⟨Sb, a1, a2, a3⟩ := GlobalTheory.TwInputs.Eig.exists_low lb.rat.In.Sb (Dof x).ntw.S0 lb.b.Sb_le (eig_low_s0 _ lb.b.Bs.tw)
  obtain ⟨Sb', b1, b2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) l''.rat.In.Sb (fun i => i.elim) (fun i => i.elim)
    fun i => i.elim
  obtain ⟨hT, hO⟩ := _root_.GlobalTheory.HeightCounting.SideCopy.Restage.eig_true_and_eig_occ_of_low lb.toLI a1 a2
  obtain ⟨B2, h1, h2, h3⟩ := _root_.GlobalTheory.HeightCounting.SideCopy.Restage.side_data_transferred_alt hPr.what₂.art h hF lb.a.A.chr lb.b.Bs l''.a.A lb.cusp
    (_root_.GlobalTheory.HeightCounting.galEx_of_cgTrue_alt hL hPr.what₂.fin hPr.what₂.gal _ l''.a.A.wdT ⟨l''.a.cg⟩) (GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb _)
    l''.rat.In l''.rat.rat.Sb_le hT (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.eig_true_and_eig_occ_of_low l'' b1 b2).1 (is_eig_sys_sig_ev_of_eig_occ lb.b.Bs a3 lb.rat.In.ks hO)
    (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.psi_std_of_level_i lb.toLI) (_root_.GlobalTheory.HeightCounting.SideCopy.Restage.psi_std_of_level_i l'') cHk hc X hpq eF hsup hact hecke_map_transfer
  refine ⟨⟨B2, h3, ?_, lambda_datum_transfer h hF lb.b.lam⟩, h1, h2⟩
  rw [lowAll_eq h]
  exact over_S0_transfer h _ lb.b.rootsOfUnityRing_le_wittIntegers
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesRestageOfCarry
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StFacts
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem st_facts_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) :
    HkAd (sideAt x g hg a) l.rat.In.Sb ((l.rat.In.hL)) ∧ KeepsMat (D := Dof x) fun i => (l.mt.ad.PV i).ψ :=
  ⟨(l.rat.rat.hecke), x.r.Y.hF, l.mt.ad.id⟩
end GlobalTheory.HeightCounting.SerCarry
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMove
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.SerGlue
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}
theorem exists_move_alt (hKP : KPx B' f') (hF : Forced K B' T') (hS' : Start K B' f' T' w') (hO : K.Over B'.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (hE : Enl B B') (hf : HEq f' f) (hSt : Start K B f T w) (hpx : HEq w'.px w.px) (hsel : HEq w'.I.sel w.I.sel)
    (hJ : HEq w'.I.J w.I.J) (hδ : HEq w'.δ w.δ) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (hExt : Ext P.z P'.z) (x' : St P')
    (hG : SameGal (Dof x) (Dof x')) (N : TwNew (Dof x')) {ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL}
    {e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0} (hN : CopyN (Dof x) N ι e) (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x'') (ho : x''.o = oTw x' N) :
    ∃ (ι' : (Dof x).what₂.LL →+* (Dof x'').what₂.LL) (e' : ↥(Dof x'').LL0 ≃+* ↥(Dof x).LL0), CopyAll (Dof x) (Dof x'') ι' e' ∧
      SameFrame (cfOf x) (cfOf x'') ∧ HEq l.Pq l''.Pq ∧
      ∃ (g : Geo x) (g'' : Geo x'') (hg : GlobalTheory.RealGeo.InGeo g) (hg'' : GlobalTheory.RealGeo.InGeo g'') (a : BigHost (Dof x))
        (a'' : BigHost (Dof x'')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x'' g'' hg'' a'') ι') := by
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := copyAll_ex hN hG.pl hD
  obtain ⟨h1, h2, h3, h4⟩ := fr_same hE.1 ((heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm))
  obtain ⟨g, g'', hg, hg'', hX⟩ := GlobalTheory.HeightCounting.SerMove.exists_geo_extN hExt x x''
  have hO' : K.Over B.toPre := hE.1 ▸ hO
  exact ⟨ι', e', h, ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩,
    (by with_unfolding_all exact ((choice_heq hE.1 (p := (l.Pq)) (p' := (l''.Pq)) ((l.Pq_over)) ((l''.Pq_over)) (s := (w.I.sel)) (s' := (w'.I.sel)) ((hsel)) ((l.sel)) ((l''.sel))) : _)),
    g, g'', hg, hg'', bigHost_st hO' hB x, bigHost_st hO hB x'',
    GlobalTheory.HeightCounting.SerMove.realMove_of_link x x'' ι' e' g g'' ⟨hO, hKP, hF, hS', hE, hf, hSt, hpx, hsel, hJ, hδ, hExt, h.cp, ⟨h.cp.gal, h.pl⟩, hX⟩ hg hg'' _ _⟩
end GlobalTheory.HeightCounting.SerGlue
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem series_restage_of_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _ cHk hc
  obtain ⟨ι', e', h, hcf, hPq, g, g'', hg, hg'', a, a'', ⟨m⟩⟩ := _root_.GlobalTheory.HeightCounting.SerGlue.exists_move_alt hKP hF hS' hO hB hE hf hSt hpx hsel hJ hδ
    x lb.toLI.toLA hExt x' hG N hN x'' l''.toLA ho
  obtain ⟨H, hp⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt lb.toLI g hg a
  obtain ⟨H', hp'⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt l'' g'' hg'' a''
  obtain ⟨L, hl, hq⟩ := sideB_facts lb.b.Bs lb.b.eF
  exact (by with_unfolding_all exact ((series_move h m ((x.m.z.geo)) ((x''.m.z.geo)) (kKs := (lb.rat.kKs)) (hk := (lb.rat.hk)) ((l''.rat.kKs))
    ((l''.rat.hk)) ((lb.b.YS)) ((lb.b.fi)) hl lb.rat.rat.Sb_le l''.rat.rat.Sb_le H H' (hs := (lb.b.Bs.hs)) (c := lb.b.Bs.cHk)
    ((l''.rat.In.hs)) (c' := cHk) hc ((L)) hcf lb.a.A.chr l''.a.A.chr hp hp' hPq hq lb.b.tau ((lb.b.ser))) : _))
end GlobalTheory.HeightCounting.SerCarry
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_series_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  first | exact @_root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | exact _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | (intros; apply _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeEigenformCopyTransferUpper
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.HkCopy
end GlobalTheory.HeightCounting.Up.HkCopy
theorem GlobalTheory.HeightCounting.Up.hecke_eigenform_copy_of_restriction_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∃ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) := by
  intro _ _ hL K B' f' T' w' _ _ _ B f T w _ _ _ _ _ _ _ P x lb P' _ x' l' _ N ι e hN x'' l'' ho _ _ _ _ _ _ _ _
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  have hS : GlobalTheory.TwistChoice.SameExport (Dof x) (Dof x'') := hD ▸ hN.cp.toSameExport
  exact GlobalTheory.HeightCounting.Up.HkCopy.exists_cHk_copy hS lb.b.Bs.cHk
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigenform_copy_transfer_upper_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∃ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.hecke_eigenform_copy_of_restriction_alt | exact _root_.GlobalTheory.HeightCounting.Up.hecke_eigenform_copy_of_restriction_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.hecke_eigenform_copy_of_restriction_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
theorem multiplicity_lower_bound_of_restricted_copy_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ
  obtain ⟨cHk, hc⟩ := _root_.GlobalTheory.T.hecke_eigenform_copy_transfer_upper_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ
  obtain ⟨YS, X, hpq, hhk, hfi, ⟨ser⟩, htau⟩ := _root_.GlobalTheory.T.mem_of_series_carry_alt hPr hSer hL hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ cHk hc
  obtain ⟨b0, hX, heF⟩ := _root_.GlobalTheory.T.side_eigenform_copy_transfer_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ cHk hc X hpq YS.eF ser.sup YS.act hhk
  exact ⟨{ toLI := l'', b := { toSettingsFormsState := b0, YS := YS, eF := heF.symm, fi := hfi, ser := hX ▸ ser, tau := hX ▸ htau } }⟩
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_pos_of_restricted_eigenform_copy_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt | exact _root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.multiplicity_lower_bound_of_restricted_copy_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsEigenformCopyOfEigensystem
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.CopyEx
section Gen
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Rows Formalism.MainNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TwInputs.Move
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
end Gen
section Types
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem.Top
end Types
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder plUnder_surjective)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
variable {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'}
theorem exists_eigenform_copy_upper_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∃ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hf _ _ _ _ _ _ x _ _ hx x' l' hg => exists_copy_st h hf x hx x' l'.a.A.bare hg
end GlobalTheory.HeightCounting.Up.CopyEx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenform_copy_of_eigensystem_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∃ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.CopyEx.exists_eigenform_copy_upper_alt | exact _root_.GlobalTheory.HeightCounting.Up.CopyEx.exists_eigenform_copy_upper_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.CopyEx.exists_eigenform_copy_upper_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeEigenvalueListTransferUpper
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ListCarry
open GlobalTheory.Mem.R3.Tr GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.TwInputs.Move
theorem hecke_eigenvalue_list_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  intro _ _ hL K B' f' T' w' _ _ _ B f T w hE hf _ _ _ _ _ P x _ P' _ x' _ _ N ι e hc x'' _ ho _ _ _ _ _ _ _ _ cDep hp
  have hD : Dof x'' = N.toD7 := by
    unfold Dof
    rw [ho]
    exact dof_oTw x' N
  obtain ⟨a1, a2, a3⟩ := lev_fr x
  obtain ⟨b1, b2, b3⟩ := lev_fr x''
  obtain ⟨c1, c2, c3⟩ := fr_heq hE.1 hf
  exact listPin_copyN hc hD x''.m.z.lev.is (b1.trans (c1.trans a1.symm)) (b2.trans (c2.trans a2.symm))
    (b3.trans (c3.trans a3.symm))
    (fun h3 => (GlobalTheory.HeightCounting.Up.ListModel.nonempty_grid w' x''.o.Z x''.m.z ⟨1, cDep, K.s.b⟩ h3).map fun G => G.pl)
    (twistPlaces_not_over_leastSplitAuxiliaryPrime w' x''.o.Z x''.m.z) hp
end GlobalTheory.HeightCounting.Up.ListCarry
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigenvalue_list_transfer_upper_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ListCarry.hecke_eigenvalue_list_transfer_alt | exact _root_.GlobalTheory.HeightCounting.Up.ListCarry.hecke_eigenvalue_list_transfer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ListCarry.hecke_eigenvalue_list_transfer_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
theorem exists_levelB1_carried_of_levelI_same_gal : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  intro hPr hSer hL
  refine Step.of_evG (((evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)).imp
    fun K _ _ _ _ H B' f' T' hO hKP hF _ w' hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG => ?_)
  have hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV :=
    fun X hX => ⟨(H.1 X hX).1, (H.2 X hX).2⟩
  obtain ⟨N, ι, e, hN⟩ := _root_.GlobalTheory.T.exists_eigenform_copy_of_eigensystem_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG
  obtain ⟨x'', l'', ho, hlev, hrow, hPq, hRS, hSb, hhL, heig, hθ⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq' hL x' l' N
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]
    rfl
  refine ⟨x'', _root_.GlobalTheory.T.multiplicity_pos_of_restricted_eigenform_copy_alt hPr hSer hL hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho hlev
    hrow hPq hRS hSb hhL heig hθ, ?_, _root_.GlobalTheory.T.hecke_eigenvalue_list_transfer_upper_alt hPr hSer hL hKP hF hS' B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e
    hN x'' l'' ho hlev hrow hPq hRS hSb hhL heig hθ⟩
  rw [hD]
  exact hN.carried
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelI_same_gal_transfer_to_levelB1_list : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (_root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal | exact _root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal | (intros; apply _root_.GlobalTheory.HeightCounting.Up.exists_levelB1_carried_of_levelI_same_gal <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsPreservedUnderLevelTransferOfCmDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem points_preserved_under_level_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x →
    Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  intro hPr hSer hL
  refine StepW.trans (_root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN hPr hSer hL) ?_
  refine StepW.of_all ?_
  intro K B f T w _ _ hq P x D0 l hC
  have hlaw := hq P x l
  obtain ⟨x', hl', ho, hLc⟩ := _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie hL x l (GlobalTheory.GeoTie.geoNTh hlaw) (GlobalTheory.GeoTie.geoTie hlaw)
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  refine ⟨⟨oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw)), fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, hl',
    carried_thTw D0 (Dof x) _ hC, fun cDep hLs => ?_⟩
  have hgen (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp)
      (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.IsLamTieFull D.ntw Z →
        GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw (lamTw (thTw D th) Z) := fun h => h
  have htrans (y : St P) (N : TwNew (Dof y))
      (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof y), GlobalTheory.LamTie.IsLamTieFull (Dof y).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
      (c b : ℝ) {I : Type} (Lc : Formalism.IndefR.Links.LevCh (Dof y) I)
      (h : ListPin (Dof y) Lc c b) :
      ListPin (w.st (oTw y N).Z).toD7 (levCh (a := y.o.Z) (oTw y N).Z Lc) c b := by
    obtain ⟨G, h1, h2⟩ := h
    exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := y.o.Z) (oTw y N).Z G) :)),
      ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩,
      (by with_unfolding_all exact ((hN _ h2) :))⟩
  have eL : m'.z.R.toRealDat.toLevCh =
      (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw))).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
  rw [eL]
  exact htrans x _ (fun Z h => hgen _ _ Z h) _ _ _ hLs
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelB2_carried_of_levelB1 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | exact _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
theorem multiplicity_bound_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MoveToBase hL := by
  intro hP hS hL
  refine StepW.trans (StepW.and (_root_.GlobalTheory.T.levelI_same_gal_transfer_to_levelB1_list hP hS hL) (_root_.GlobalTheory.T.exists_levelB2_carried_of_levelB1 hP hS hL)) (StepW.of_all fun K B' f' T' w' _ _ h => ?_)
  obtain ⟨h, h'⟩ := h
  intro B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₁, ⟨l₁⟩, hC₁, hL₁⟩ := h B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₂, hl₂, hC₂, hL₂⟩ := h' P' x₁ (Dof x) l₁ hC₁
  exact ⟨x₂, hl₂, hC₂, fun c hc => hL₂ c (hL₁ c hc)⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveToBase_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MoveToBase hL := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt | exact _root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.multiplicity_bound_of_local_components_alt <;> assumption)
end
end
