module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SemilinearFactorsThroughReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeight
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.PDivLat.latt_free_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, _lie, hal, _⟩ := hG
  obtain ⟨L, -⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  haveI : Nontrivial (PreTilt O p) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  refine ⟨Module.Free.of_equiv L, Module.Finite.equiv L, ?_⟩
  rw [← L.finrank_eq, Module.finrank_fin_fun]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  first | exact @GlobalTheory.PDivLat.latt_free_finrank | exact GlobalTheory.PDivLat.latt_free_finrank | (intros; apply GlobalTheory.PDivLat.latt_free_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOne
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.MuLattice

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}

def muMap (hε : IsPrimitiveSystem ε) (a : Ainf p O) : TDual (PDivGroup.mu p O) where
  toFun t := ofPadic p O ((epsEquiv hε).symm t) * a
  map_add' s t := by rw [map_add (f := _), map_add (f := _), add_mul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl

theorem muMap_apply (hε : IsPrimitiveSystem ε) (a : Ainf p O) (t) :
    muMap hε a t = ofPadic p O ((epsEquiv hε).symm t) * a := rfl

theorem epsEquiv_symm_eps (hε : IsPrimitiveSystem ε) : (epsEquiv hε).symm (epsTate hε) = 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℤ_[p] (epsTate hε)).symm

theorem muMap_mem (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : muMap hε (Sandwich.mu ε * a) ∈ latt (PDivGroup.mu p O) := fun n =>
  ⟨0, fun t => by
    rw [muMap_apply, ghost_mul, ghost_mul, hμ, zero_mul, mul_zero, LinearMap.zero_apply]⟩

def toLatt (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0) :
    Ainf p O →ₗ[Ainf p O] latt (PDivGroup.mu p O) where
  toFun a := ⟨muMap hε (Sandwich.mu ε * a), muMap_mem hε hμ a⟩
  map_add' a b := by
    ext t
    simp only [muMap_apply, Submodule.coe_add, LinearMap.add_apply]
    ring_nf
  map_smul' c a := by
    ext t
    simp only [muMap_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem toLatt_eps (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : (toLatt hε hμ a).1 (epsTate hε) = Sandwich.mu ε * a := by
  change ofPadic p O ((epsEquiv hε).symm (epsTate hε)) * _ = _
  rw [epsEquiv_symm_eps, map_one, one_mul]

theorem latt_mu_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  have hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0 :=
    (GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε).2.2.1
  have hdom := GlobalTheory.ainf_isDomain_and_mu_ne_zero p C v O hv ε (by simpa [zeta] using hε 1)
  haveI := hdom.1
  have hbij : Function.Bijective (toLatt hε hμ) := by
    constructor
    · intro a b hab
      have h := congrArg (fun y : latt (PDivGroup.mu p O) => y.1 (epsTate hε)) hab
      simp only [toLatt_eps] at h
      exact mul_left_cancel₀ hdom.2 h
    · intro y
      have hg : ∀ n, ghost p O n (y.1 (epsTate hε)) = 0 := fun n => by
        obtain ⟨x, hx⟩ := y.2 n
        rw [hx, Subsingleton.elim (hodgeTate (PDivGroup.mu p O) (epsTate hε)) 0, map_zero]
      obtain ⟨a, ha⟩ := GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ hg
      refine ⟨a, Subtype.ext (LinearMap.ext fun t => ?_)⟩
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change ofPadic p O ((epsEquiv hε).symm (epsEquiv hε c)) * (Sandwich.mu ε * a) = y.1 (epsEquiv hε c)
      rw [LinearEquiv.symm_apply_apply, ← ha]
      have hc : epsEquiv hε c = c • epsTate hε := rfl
      rw [hc, LinearMap.map_smulₛₗ, smul_eq_mul]
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm, fun y => ?_⟩
  have h := toLatt_eps hε hμ ((LinearEquiv.ofBijective _ hbij).symm y)
  rw [← h]
  congr 2
  exact (LinearEquiv.ofBijective _ hbij).apply_symm_apply y

end GlobalTheory.MuLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOneStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  first | exact @GlobalTheory.MuLattice.latt_mu_equiv | exact GlobalTheory.MuLattice.latt_mu_equiv | (intros; apply GlobalTheory.MuLattice.latt_mu_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlog
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlog
set_option autoImplicit false

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem lie_eq_zero_of_dlog {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
    {ε : PreTilt O p} {hε : IsPrimitiveSystem ε} {G : PDivGroup p O} (hD : HasDatum hε G)
    (x : G.Lie) (hx : ∀ χ, x (dlog G χ) = 0) : x = 0 := by
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  obtain ⟨D, e, fil, lie, -, hb⟩ := hD
  have hG : Function.Surjective (G.pairing O).flip := (G.pairing_flip_bijective C).2
  have h0 : bQuot D (lie.symm x) = 0 :=
    GlobalTheory.DetInv.HTKer.pairingO_inj (hε := hε) hG e _ _ fun χ => by
      rw [hb, hx]; simp [pairingO]
  obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
  have h1 : D.bb m = 0 := by
    rw [← hm] at h0; exact h0
  have h2 : lie.symm x = 0 := by
    rw [← hm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h1
  simpa using congrArg lie h2

theorem exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hD
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O G.omega := (GlobalTheory.PDiv.omega_finite_projective p C v O hv G).1
  set S := Submodule.span O (Set.range (dlog G)) with hS
  let T := Submodule.torsion O (G.omega ⧸ S)
  let π : G.omega →ₗ[O] (G.omega ⧸ S) ⧸ T := T.mkQ ∘ₗ S.mkQ
  have hπ : Function.Surjective π := T.mkQ_surjective.comp S.mkQ_surjective
  haveI : Module.Flat O ((G.omega ⧸ S) ⧸ T) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.QuotientTorsion.torsion_eq_bot
  haveI : Module.Free O ((G.omega ⧸ S) ⧸ T) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O ((G.omega ⧸ S) ⧸ T)
  have hcoord : ∀ i, b.coord i ∘ₗ π = 0 := fun i =>
    lie_eq_zero_of_dlog C hv hD _ fun χ => by
      change b.coord i (T.mkQ (S.mkQ (dlog G χ))) = 0
      have hs : S.mkQ (dlog G χ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact Submodule.subset_span ⟨χ, rfl⟩
      rw [hs, map_zero, map_zero]
  have hzero : ∀ q : (G.omega ⧸ S) ⧸ T, q = 0 := fun q => by
    obtain ⟨w, rfl⟩ := hπ q
    refine b.ext_elem fun i => ?_
    change b.coord i (π w) = b.coord i 0
    rw [(b.coord i).map_zero]
    exact LinearMap.congr_fun (hcoord i) w
  have htor : Module.IsTorsion O (G.omega ⧸ S) := fun q => by
    have := hzero (T.mkQ q)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff] at this
    exact this
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨c, nonZeroDivisors.ne_zero hc0, fun w => ?_⟩
  have := Submodule.mem_annihilator.1 hc (S.mkQ w) Submodule.mem_top
  rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end GlobalTheory.PDivLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupExistsSmulMemSpanDlogStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → ∃ c : O, c ≠ 0 ∧ ∀ w : G.omega, c • w ∈ Submodule.span O (Set.range (dlog G)) := by
  first | exact @GlobalTheory.PDivLat.exists_smul_mem_span_dlog | exact GlobalTheory.PDivLat.exists_smul_mem_span_dlog | (intros; apply GlobalTheory.PDivLat.exists_smul_mem_span_dlog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.HodgeNat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem theta_xi_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (xi ε) = 0 := by
  have h1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
  have h2 := h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [xi, map_sum]
  simpa [map_pow, WittVector.fontaineTheta_teichmuller, zeta] using h2

theorem ghost_mu_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (n : ℕ) :
    ghost p O n (Sandwich.mu ε) = 0 := by
  induction n with
  | zero =>
    show WittVector.fontaineTheta O p (Sandwich.mu ε) = 0
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  | succ n ih =>
    rw [← ghost_frobenius, Dieudonne.frobenius_mu, ghost_mul, ih, mul_zero]

noncomputable def muPair [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : TDual G where
  toFun t := Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)
  map_add' s t := by
    simp only [epsPairing, map_add (f := _), LinearMap.add_apply, mul_add]
  map_smul' a t := by
    simp only [epsPairing, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring

theorem muPair_mem [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : muPair hε G χ ∈ latt G := fun n =>
  ⟨0, fun t => by
    show ghost p O n (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) = 0
    rw [ghost_mul, ghost_mu_eq_zero hε, zero_mul]⟩

end GlobalTheory.PDivLat.HodgeNat


open GlobalTheory.PDivLat.HodgeNat in
theorem GlobalTheory.PDivLat.iota_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H f hG hH M _ _ r M' _ _ r' u ι ι' hrs hrk hu hι hι' w
  obtain ⟨hfree, hfin, -⟩ := GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G hG
  haveI : Nontrivial (Ainf p O) := (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv).nontrivial
  obtain ⟨hMfree, -, -⟩ := Dieudonne.free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (theta_xi_eq_zero hε) r hrs fun m hm => (hrk m).1 hm
  haveI := hMfree

  have key : ∀ χ : H.dual.Tate, u (ι' (dlog H χ)) = ι (omegaMap G H f (dlog H χ)) := by
    intro χ
    let Y : latt H := ⟨muPair hε H χ, muPair_mem hε H χ⟩
    have h1 : ι' (dlog H χ) = r' Y := hι' χ Y fun t => rfl
    have h2 : ι (dlog G (tateMap H.dual G.dual O (dualHom G H f) χ)) = r (lattMap f Y) := by
      refine hι _ _ fun t => ?_
      show Sandwich.mu ε * ofPadic p O (epsPairing hε H (tateMap G H O f t) χ) = _
      rw [epsPairing, epsPairing, pairing_tateMap]
    rw [h1, hu, ← h2, dlog_tateMap]
  obtain ⟨c, hc, hcw⟩ := GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog p C v O hv ε hε H hH
  have hspan : ∀ x ∈ Submodule.span O (Set.range (dlog H)),
      u (ι' x) = ι (omegaMap G H f x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact key χ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h := hspan _ (hcw w)
  simp only [map_smul] at h
  have h' : c • (u (ι' w) - ι (omegaMap G H f w)) = 0 := by rw [smul_sub, h, sub_self]
  have tf : ∀ x : M, c • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis O M
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
    simpa using (mul_eq_zero.1 h3).resolve_left hc
  exact sub_eq_zero.1 (tf _ h')
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNaturalStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  first | exact @GlobalTheory.PDivLat.iota_natural | exact GlobalTheory.PDivLat.iota_natural | (intros; apply GlobalTheory.PDivLat.iota_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponent
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.LieHodgeTate

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, lie, hal, -⟩ := hG
  have hprim : IsPrimitiveRoot (root ε).untilt p := by
    have := hε 1
    simpa [zeta] using this
  obtain ⟨-, hle, -, hfil, -, -⟩ := HodgeTateBound.bound p C v O hv ε hprim ℤ_[p] G.height D
  obtain ⟨-, -, -, hsurj, hν, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hprim
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i
    funext j
    simp only [toO, LinearEquiv.apply_symm_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · let φ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ (LinearMap.codRestrict D.Fil D.al fun u => hle ⟨u, rfl⟩)
    have hφ : φ = 0 := by
      apply (Pi.basisFun O (Fin G.height)).ext
      intro i
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← hsingle i]
      have h1 : (⟨D.al (toO e (e.symm (Pi.single i 1))), hle ⟨_, rfl⟩⟩ : D.Fil) =
          fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
      change x (fil.symm ⟨D.al _, _⟩) = 0
      rw [h1, LinearEquiv.symm_apply_apply]
      exact hx _
    ext w
    obtain ⟨u, hu⟩ := hfil _ (fil w).2
    have h1 : WittVector.fontaineTheta O p (nu ε) • fil w = ⟨D.al u, hle ⟨u, rfl⟩⟩ :=
      Subtype.ext hu.symm
    have h2 : WittVector.fontaineTheta O p (nu ε) * x w = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← fil.symm_apply_apply (WittVector.fontaineTheta O p (nu ε) • w),
        map_smul fil, h1]
      exact LinearMap.congr_fun hφ u
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hν
    · simpa using h
  · haveI : ValuationRing O := ValuationRing.of_integers v hv
    haveI : Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb) := by
      haveI : Module.Free O (LinearMap.range D.bb) :=
        GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing O _
      exact Module.Free.of_equiv (D.bb.quotKerEquivRange).symm
    haveI : Module.Free O ((Fin G.height → O) ⧸ D.Fil) := by
      change Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb); infer_instance
    obtain ⟨N', hN'⟩ := GlobalTheory.exists_isCompl_of_projective_quotient D.Fil
    let ρ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ D.Fil.projectionOnto N' hN'
    choose r hr using fun i => hsurj (ρ (Pi.single i 1))
    obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
    refine ⟨L r, fun t => ?_⟩
    rw [hL]
    have hρ : ∀ w, ρ w = ∑ i, WittVector.fontaineTheta O p (r i) * w i := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ ρ w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr, smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hθ : WittVector.fontaineTheta O p (r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i))) =
        ρ (D.al (toO e t)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hρ, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, RingHom.map_mulVec]
      rfl
    rw [hθ]
    have h3 : D.Fil.projectionOnto N' hN' (D.al (toO e t)) = fil (hodgeTate G t) := by
      rw [show D.al (toO e t) = ((fil (hodgeTate G t) : D.Fil) : Fin _ → O) from hal t,
        Submodule.projectionOnto_apply_left]
    change x (fil.symm (D.Fil.projectionOnto N' hN' (D.al (toO e t)))) = _
    rw [h3, LinearEquiv.symm_apply_apply]

end GlobalTheory.LieHodgeTate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponentStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  first | exact @GlobalTheory.LieHodgeTate.main | exact GlobalTheory.LieHodgeTate.main | (intros; apply GlobalTheory.LieHodgeTate.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLattice
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LattIota

variable {A O M : Type} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M] {ι : Type}
  (θ : A →+* O) (hs : Function.Surjective θ) (R : (ι → A) →ₛₗ[θ] M)
  (hR : ∀ s : ι → A, (∀ i, θ (s i) = 0) → R s = 0)

include hR in
theorem eq_of_theta_eq {s s' : ι → A} (h : ∀ i, θ (s i) = θ (s' i)) : R s = R s' := by
  rw [← sub_eq_zero, ← map_sub]
  exact hR _ fun i => by rw [Pi.sub_apply, map_sub, h, sub_self]

def descend : (ι → O) →ₗ[O] M where
  toFun ρ := R (fun i => Function.surjInv hs (ρ i))
  map_add' ρ ρ' := by
    rw [← map_add (f := _)]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]
  map_smul' c ρ := by
    have h1 : (c • R (fun i => Function.surjInv hs (ρ i)) : M) =
        θ (Function.surjInv hs c) • R (fun i => Function.surjInv hs (ρ i)) := by
      rw [Function.surjInv_eq hs]
    rw [RingHom.id_apply, h1, ← LinearMap.map_smulₛₗ]
    exact eq_of_theta_eq θ R hR fun i => by
      simp [Function.surjInv_eq hs]

theorem descend_comp (s : ι → A) : descend θ hs R hR (fun i => θ (s i)) = R s :=
  eq_of_theta_eq θ R hR fun i => Function.surjInv_eq hs _

variable [Fintype ι]

def dotL (ρ : ι → O) : (ι → O) →ₗ[O] O where
  toFun w := ρ ⬝ᵥ w
  map_add' := dotProduct_add ρ
  map_smul' c w := by rw [dotProduct_smul, RingHom.id_apply]

end GlobalTheory.LattIota

namespace GlobalTheory.LattIota

theorem iota_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG M _ _ r π hrs hker hπ
  obtain ⟨D, e, fil, lie, hal, hb⟩ := hG
  obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by
    simpa [zeta] using hε 1
  obtain ⟨hdom, -, hkerθ, hsθ, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε1
  obtain ⟨hFG, hrangeFil, -, hνFil, -, -⟩ :=
    GlobalTheory.Sandwich.HodgeTateBound.bound p C v O hv ε hε1 ℤ_[p] G.height D
  obtain ⟨hFin, hProj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hkerθ]; exact Ideal.mem_span_singleton_self _
  let R : (Fin G.height → Ainf p O) →ₛₗ[WittVector.fontaineTheta O p] M :=
    r.comp (L : (Fin G.height → Ainf p O) →ₗ[Ainf p O] latt G)
  have hR : ∀ s : Fin G.height → Ainf p O, (∀ i, WittVector.fontaineTheta O p (s i) = 0) →
      R s = 0 := by
    intro s hs0
    have hu : ∀ i, ∃ u, u * xi ε = s i := fun i => by
      rw [← Ideal.mem_span_singleton', ← hkerθ]; exact hs0 i
    choose u hu using hu
    have hsu : s = xi ε • u := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hu]
    change r (L s) = 0
    rw [hker, hsu, map_smul]
    exact ⟨_, rfl⟩
  let Φ := descend _ hsθ R hR
  have hΦ : ∀ s, Φ (fun i => WittVector.fontaineTheta O p (s i)) = r (L s) := fun s =>
    descend_comp _ hsθ R hR s
  have hlift : ∀ ρ : Fin G.height → O, ∃ s : Fin G.height → Ainf p O,
      (fun i => WittVector.fontaineTheta O p (s i)) = ρ := fun ρ =>
    ⟨fun i => Function.surjInv hsθ (ρ i), funext fun i => Function.surjInv_eq hsθ _⟩
  have hΦs : Function.Surjective Φ := by
    intro m
    obtain ⟨y, rfl⟩ := hrs m
    obtain ⟨s, rfl⟩ := L.surjective y
    exact ⟨_, hΦ s⟩
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ρ hρ
    obtain ⟨s, rfl⟩ := hlift ρ
    rw [hΦ, hker] at hρ
    obtain ⟨n, hn⟩ := hρ
    have hs : s = xi ε • L.symm n := by
      apply L.injective; rw [map_smul, L.apply_symm_apply, hn]
    funext i
    rw [hs, Pi.smul_apply, smul_eq_mul, map_mul, hθξ, zero_mul, Pi.zero_apply]
  have hπHT : ∀ s t, π (r (L s)) (hodgeTate G t) =
      (fun i => WittVector.fontaineTheta O p (s i)) ⬝ᵥ (fil (hodgeTate G t) : Fin G.height → O) := by
    intro s t
    rw [hπ, hL, ← hal, RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    rfl
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i; funext j
    by_cases hij : j = i
    · subst hij; simp [toO]
    · simp [toO, Pi.single_apply, hij]
  have hext : ∀ f₁ f₂ : G.dual.omega →ₗ[O] O,
      (∀ t, f₁ (hodgeTate G t) = f₂ (hodgeTate G t)) → f₁ = f₂ := by
    intro f₁ f₂ hf
    let g : (G.dual.omega →ₗ[O] O) → (Fin G.height → O) →ₗ[O] O := fun f =>
      f ∘ₗ fil.symm.toLinearMap ∘ₗ (D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩))
    have key : ∀ f t, g f (toO e t) = f (hodgeTate G t) := by
      intro f t
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) (toO e t) =
          fil (hodgeTate G t) := Subtype.ext (hal t)
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, LinearEquiv.symm_apply_apply]
    have hg : g f₁ = g f₂ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      change g f₁ (Pi.single i 1) = g f₂ (Pi.single i 1)
      rw [← hsingle, key, key, hf]
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, hw⟩ := hνFil _ (fil x).2
    have hgx : ∀ f, g f w = WittVector.fontaineTheta O p (nu ε) * f x := by
      intro f
      have h1 : D.al.codRestrict D.Fil (fun w => hrangeFil ⟨w, rfl⟩) w =
          WittVector.fontaineTheta O p (nu ε) • fil x := Subtype.ext hw
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, map_smul,
        LinearEquiv.symm_apply_apply, smul_eq_mul]
    exact mul_left_cancel₀ hν (by rw [← hgx, ← hgx, hg])
  have hπΦ : ∀ ρ x, π (Φ ρ) x = ρ ⬝ᵥ (fil x : Fin G.height → O) := by
    intro ρ
    obtain ⟨s, rfl⟩ := hlift ρ
    have := hext (π (Φ (fun i => WittVector.fontaineTheta O p (s i))))
      (dotL (fun i => WittVector.fontaineTheta O p (s i)) ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap)
      (fun t => by rw [hΦ, hπHT]; rfl)
    intro x
    exact LinearMap.congr_fun this x
  let κ : G.omega →ₗ[O] (Fin G.height → O) :=
    LinearMap.pi fun i => lie (D.Fil.mkQ (Pi.single i 1))
  have hκ : ∀ w i, κ w i = lie (D.Fil.mkQ (Pi.single i 1)) w := fun w i => rfl
  have hk : ∀ w m, κ w ⬝ᵥ m = lie (D.Fil.mkQ m) w := by
    intro w
    have : dotL (κ w) = (LinearMap.applyₗ w : Module.Dual O G.omega →ₗ[O] O) ∘ₗ
        lie.toLinearMap ∘ₗ D.Fil.mkQ := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      simp [dotL, hκ]
    intro m
    exact LinearMap.congr_fun this m
  have hκi : Function.Injective κ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine (Module.forall_dual_apply_eq_zero_iff O w).1 fun φ => ?_
    obtain ⟨q, rfl⟩ := lie.surjective φ
    obtain ⟨m, rfl⟩ := D.Fil.mkQ_surjective q
    rw [← hk, hw, zero_dotProduct]
  refine ⟨Φ ∘ₗ κ, hΦi.comp hκi, fun m => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨ρ, rfl⟩ := hΦs m
    have hρ : D.Fil ≤ LinearMap.ker (dotL ρ) := fun f hf => by
      obtain ⟨x, hx⟩ := fil.surjective ⟨f, hf⟩
      have := LinearMap.congr_fun h0 x
      rw [hπΦ, hx] at this
      exact this
    let ψ : ((Fin G.height → O) ⧸ D.Fil) →ₗ[O] O := D.Fil.liftQ (dotL ρ) hρ
    let w := (Module.evalEquiv O G.omega).symm (ψ ∘ₗ lie.symm.toLinearMap)
    have hw : ∀ φ : G.Lie, φ w = ψ (lie.symm φ) := fun φ => by
      change (Module.evalEquiv O G.omega w) φ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨w, ?_⟩
    change Φ (κ w) = Φ ρ
    congr 1
    funext i
    rw [hκ, hw, LinearEquiv.symm_apply_apply]
    simp [ψ, dotL]
  · rintro ⟨w, rfl⟩
    refine LinearMap.ext fun x => ?_
    change π (Φ (κ w)) x = 0
    rw [hπΦ, hk, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (fil x).2, map_zero]
    rfl
  · intro χ y hy
    let sχ : Fin G.height → Ainf p O := fun i =>
      ofPadic p O (epsPairing hε G (e.symm (Pi.single i 1)) χ)
    have hpair : ∀ t, sχ ⬝ᵥ (fun i => ofPadic p O (e t i)) = ofPadic p O (epsPairing hε G t χ) := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hlin : epsPairing hε G t χ =
          ∑ i, e t i * epsPairing hε G (e.symm (Pi.single i 1)) χ := by
        conv_lhs => rw [ht]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [epsPairing, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hlin, map_sum]
      simp only [dotProduct, sχ, map_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hyL : y = L (sχ ᵥ* D.G) := by
      apply Subtype.ext
      refine LinearMap.ext fun t => ?_
      rw [hL, hy, ← dotProduct_mulVec, mulVec_mulVec, D.G_mul_F, smul_mulVec, one_mulVec,
        dotProduct_smul, hpair, smul_eq_mul]
    rw [hyL, ← hΦ]
    change Φ (κ (dlog G χ)) = _
    congr 1
    funext i
    rw [hκ, ← hb, LinearEquiv.symm_apply_apply, RingHom.map_vecMul]
    simp [bQuot, pairingO, Datum.bb, Matrix.toLin'_apply, vecMul, dotProduct, padicToO, sχ,
      mul_comm]

end GlobalTheory.LattIota
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeSequenceFirstMapLatticeStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeSequence_first_map_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O), HasDatum hε G → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (π : M →ₗ[O] G.dual.Lie), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ (y : latt G) t, π (r y) (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t)) → ∃ ι : G.omega →ₗ[O] M, Function.Injective ι ∧ Function.Exact ι π ∧ (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) := by
  first | exact @GlobalTheory.LattIota.iota_exists | exact GlobalTheory.LattIota.iota_exists | (intros; apply GlobalTheory.LattIota.iota_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMap
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.ConstMu

theorem frobenius_ofPadic {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem frobenius_phiInv' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem frobenius_mu' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv']

theorem existsUnique_lattMap : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε g hg
  obtain ⟨ec, hec⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
  obtain ⟨em, hem⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
  have eig := GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf p C v O hv ε hε
  set l : latt (PDivGroup.mu p O) := em.symm 1 with hl_def
  have hl : l.1 (epsTate hε) = Sandwich.mu ε := by
    rw [← hem l, hl_def, LinearEquiv.apply_symm_apply, mul_one]
  have htate : ∀ t : (PDivGroup.mu p O).Tate, ∃ a : ℤ_[p], t = a • epsTate hε := by
    intro t
    obtain ⟨a, rfl⟩ := (epsEquiv hε).surjective t
    exact ⟨a, rfl⟩
  have hlval : ∀ a : ℤ_[p], l.1 (a • epsTate hε) = ofPadic p O a * Sandwich.mu ε := by
    intro a
    rw [map_smulₛₗ, hl, smul_eq_mul]
  have hgen : ∀ y : latt (PDivGroup.mu p O), y = em y • l := by
    intro y
    apply em.injective
    rw [map_smul, hl_def, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hpull : ∀ (f : const p O ⟶ PDivGroup.mu p O) (y : latt (PDivGroup.mu p O)),
      ec (lattMap f y) = y.1 (tateMap _ _ O f (constGen p O)) := by
    intro f y
    rw [hec]
    rfl

  set b : Ainf p O := ((g l).1 (constGen p O)) with hb_def
  have hbeig : WittVector.frobenius b = WittVector.frobenius (xi ε) * b := by
    have h1 := hg l (WittVector.frobenius (xi ε) • l) (by
      intro t
      obtain ⟨a, rfl⟩ := htate t
      rw [Submodule.coe_smul, LinearMap.smul_apply, hlval, smul_eq_mul, map_mul,
        frobenius_ofPadic, frobenius_mu']
      ring) (constGen p O)
    rw [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hb_def, ← h1]
  obtain ⟨c, hc, hcu⟩ := eig b hbeig
  have hfix : ∀ f : const p O ⟶ PDivGroup.mu p O, lattMap f = g ↔
      ec (lattMap f l) = ec (g l) := by
    intro f
    constructor
    · intro h; rw [h]
    · intro h
      apply LinearMap.ext
      intro y
      rw [hgen y, map_smul, map_smul, ec.injective h]
  refine ⟨constHom (PDivGroup.mu p O) (c • epsTate hε), ?_, ?_⟩
  · show lattMap _ = g
    rw [hfix, hpull, tateMap_constHom, hlval, hec, hc]
  · intro f hf
    rw [hfix, hpull, hec] at hf
    obtain ⟨a, ha⟩ := htate (tateMap _ _ O f (constGen p O))
    rw [ha, hlval] at hf
    have hac : a = c := hcu a hf
    rw [← (constHom (PDivGroup.mu p O)).apply_symm_apply f, constHom_symm_apply, ha, hac]

end GlobalTheory.PDivLat.ConstMu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMapStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  first | exact @GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | exact GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | (intros; apply GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinf
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_ofPadic' (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  ext n
  simp only [phiInv, ofPadic, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem frob_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  conv_lhs => rw [← phiInv_ofPadic' c]
  exact frob_phiInv _

def frobT (G : PDivGroup p O) (y : TDual G) : TDual G where
  toFun t := WittVector.frobenius (y t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _)]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, frob_ofPadic, smul_eq_mul]

def xiPhiInvT (ε : PreTilt O p) (G : PDivGroup p O) (m : TDual G) : TDual G where
  toFun t := xi ε * phiInv p O (m t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _), mul_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, phiInv_ofPadic', smul_eq_mul, mul_left_comm]

def frobLatt (G : PDivGroup p O) :
    latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G where
  toFun y := ⟨frobT G y.1, fun n => by
    obtain ⟨x, hx⟩ := y.2 (n + 1)
    exact ⟨x, fun t => by rw [← hx]; rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((y.1 + z.1) t) = _
    rw [LinearMap.add_apply, map_add (f := _)]; rfl
  map_smul' a y := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((a • y.1) t) = _
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]; rfl

end GlobalTheory.PDivLat.Frob


open GlobalTheory.PDivLat.Frob in
theorem GlobalTheory.PDivLat.exists_frobenius_latt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  obtain ⟨-, -, -, h0, hs, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  refine ⟨fun G => frobLatt G, fun G y t => rfl, fun G m => ?_⟩
  refine ⟨⟨xiPhiInvT ε G m.1, fun n => ?_⟩, ?_⟩
  · cases n with
    | zero => exact ⟨0, fun t => by
        show ghost p O 0 (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, h0, zero_mul, LinearMap.zero_apply]⟩
    | succ k =>
      obtain ⟨x, hx⟩ := m.2 k
      exact ⟨(p : O) • x, fun t => by
        show ghost p O (k + 1) (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, hs, hphi, hx, LinearMap.smul_apply, smul_eq_mul]⟩
  · apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius (xi ε * phiInv p O (m.1 t)) = _
    rw [map_mul, frob_phiInv]; rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinfStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  first | exact @GlobalTheory.PDivLat.exists_frobenius_latt | exact GlobalTheory.PDivLat.exists_frobenius_latt | (intros; apply GlobalTheory.PDivLat.exists_frobenius_latt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatum
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat


set_option maxHeartbeats 2000000 in
theorem prismaticDieudonneHodgeAt_of_hasDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hD
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, hker, hθ, -, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hθξ : WittVector.fontaineTheta O p (xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
  have hμ : Sandwich.mu ε ≠ 0 := fun h => GlobalTheory.Dieudonne.not_dvd_mu hε1 (h ▸ dvd_zero _)

  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf p C v O hv ε hε

  have hsep : ∀ (G : PDivGroup p O) (x x' : G.dual.Lie),
      (∀ t, x (hodgeTate G t) = x' (hodgeTate G t)) → x = x' := fun G x x' h =>
    sub_eq_zero.1 ((GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)).1 (x - x') fun t => by
      rw [LinearMap.sub_apply, h, sub_self])
  have hqex : ∀ G : PDivGroup p O, ∃ q : latt G →ₛₗ[WittVector.fontaineTheta O p] G.dual.Lie,
      ∀ y t, q y (hodgeTate G t) = WittVector.fontaineTheta O p (y.1 t) := fun G => by
    choose x hx using fun y : latt G => y.2 0
    refine ⟨{ toFun := x
              map_add' := fun a b => hsep G _ _ (fun t => ?_)
              map_smul' := fun c a => hsep G _ _ (fun t => ?_) }, fun y t => (hx y t).symm⟩
    · rw [LinearMap.add_apply, ← hx, ← hx, ← hx]; exact ghost_add 0 (a.1 t) (b.1 t)
    · rw [LinearMap.smul_apply, ← hx, ← hx, smul_eq_mul]; exact ghost_mul 0 c (a.1 t)
  choose q hq using hqex

  haveI hadd : (lattFunctor p O).Additive :=
    { map_add := fun {X Y f g} => ModuleCat.hom_ext (LinearMap.ext fun y =>
        Subtype.ext (LinearMap.ext fun t => by
          change y.1 (tateMap _ _ O (f + g).unop t) =
            y.1 (tateMap _ _ O f.unop t) + y.1 (tateMap _ _ O g.unop t)
          rw [unop_add, map_add (f := _), LinearMap.add_apply, map_add (f := _)])) }

  obtain ⟨D, r, hr, nr⟩ := GlobalTheory.CompanionTheory.ModuleReduction.exists_reduction (Ainf p O) O
    (WittVector.fontaineTheta O p) hθ (xi ε) hker (PDivGroup p O)ᵒᵖ (lattFunctor p O)

  have hπex : ∀ G : PDivGroup p O, ∃ π : D.obj (op G) →ₗ[O] G.dual.Lie,
      ∀ m, π (r (op G) m) = q G m := fun G =>
    GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction (Ainf p O) O (WittVector.fontaineTheta O p) hθ
      (xi ε) hθξ _ (D.obj (op G)) G.dual.Lie (r (op G)) (q G) (hr (op G)).1 (hr (op G)).2
  choose π hπ using hπex

  have hιex := fun G : PDivGroup p O => GlobalTheory.T.exists_hodgeSequence_first_map_lattice p C v O hv ε hε G (hD G) (D.obj (op G))
    (r (op G)) (π G) (hr (op G)).1 (hr (op G)).2 (fun y t => (LinearMap.congr_fun (hπ G y) _).trans (hq G y t))
  choose ι hι using hιex
  have nr' : ∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : latt H),
      (D.map f.op).hom (r (op H) m) = r (op G) (lattMap f m) := fun G H f m => nr _ _ f.op m
  refine ⟨lattFunctor p O, D, φ, fun G => r (op G), ι, π, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hadd
  · exact fun G => GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G (hD G)
  · intro G m
    obtain ⟨n, hn⟩ := hφ2 G m
    exact ⟨n, hn⟩
  · intro G H f m
    refine Subtype.ext (LinearMap.ext fun t => ?_)
    exact (hφ1 H m _).trans (hφ1 G (lattMap f m) t).symm
  · exact fun G => hr (op G)
  · exact fun G H f m => nr' G H f m
  · intro G
    refine ⟨(hι G).1, (hι G).2.1, fun x => ?_⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent p C v O hv ε hε G (hD G)).2 x
    exact ⟨r (op G) y, (hπ G y).trans (hsep G _ _ fun t => (hq G y t).trans (hy t))⟩
  · intro G H f w
    exact GlobalTheory.T.pDivGroup_hodgeTateFirstMap_natural p C v O hv ε hε G H f (hD G) (hD H) (D.obj (op G)) (r (op G)) (D.obj (op H))
      (r (op H)) (D.map f.op).hom (ι G) (ι H) (hr (op G)).1 (hr (op G)).2 (nr' G H f)
      (hι G).2.2 (hι H).2.2 w
  · intro G H f x
    obtain ⟨m, rfl⟩ := (hr (op H)).1 x
    refine ((congrArg (π G) (nr' G H f m)).trans (hπ G _)).trans ?_
    refine (hsep G _ _ fun t => ?_).trans (congrArg _ (hπ H m).symm)
    exact (hq G _ t).trans ((hq H m _).symm.trans (congrArg (q H m) (hodgeTate_tateMap f t)))
  · obtain ⟨e, he⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
    exact ⟨e, fun m => (he _).trans ((hφ1 _ _ _).trans (congrArg _ (he m).symm))⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
    refine ⟨e, fun m => mul_left_cancel₀ hμ ?_⟩
    have h1 : Sandwich.mu ε * e (φ _ m) = WittVector.frobenius (Sandwich.mu ε * e m) :=
      (he _).trans ((hφ1 _ _ _).trans (congrArg _ (he m).symm))
    have h2 : WittVector.frobenius (Sandwich.mu ε * e m) =
        Sandwich.mu ε * (WittVector.frobenius (xi ε) * WittVector.frobenius (e m)) := by
      rw [map_mul, GlobalTheory.Dieudonne.frobenius_mu]
      ring
    exact h1.trans h2
  · intro g hg
    obtain ⟨f, hf, hu⟩ := GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map p C v O hv ε hε g fun m m' hm t => by
      have e : m' = φ _ m := Subtype.ext (LinearMap.ext fun t => by rw [hm, hφ1])
      subst e
      exact (congrArg (fun z => z.1 t) (hg m)).trans (hφ1 _ _ t)
    exact ⟨f, hf, fun f' hf' => hu f' hf'⟩

end GlobalTheory.PDivLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatumStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticDieudonneHodge_of_hodgeTateDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  first | exact @GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | exact GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | (intros; apply GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum <;> assumption)
end
