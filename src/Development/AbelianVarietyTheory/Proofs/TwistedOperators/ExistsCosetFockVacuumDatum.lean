module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainAdjointLatticeExchange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRepresentativesHalfQuotientPairingTrivialD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CoreOnto.Reps

private theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

private theorem nsmul_inj {D : D7} {m n : ℕ} {K : ℕ} (hK : 0 < K) {x y : Mx D m n} (h : K • x = K • y) : x = y := by
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have h' := congrArg (fun z : Mx D m n => incA D (K : D.host.E)⁻¹ • z) h
  rwa [← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, mul_comm, inv,
    one_smul, one_smul] at h'

private theorem isHalf_add {D : D7} {m n : ℕ} {c : AE D} {x y : Mx D m n} (hx : IsHalf c x) (hy : IsHalf c y) :
    IsHalf c (x + y) := fun a b => by simp only [Matrix.add_apply, mul_add, hx a b, hy a b]

private theorem isHalf_neg {D : D7} {m n : ℕ} {c : AE D} {x : Mx D m n} (hx : IsHalf c x) : IsHalf c (-x) := fun a b => by
  simp only [Matrix.neg_apply, mul_neg, hx a b]

private theorem isHalf_zero {D : D7} {m n : ℕ} (c : AE D) : IsHalf c (0 : Mx D m n) := fun a b => by simp

private theorem symplO_zero_right {D : D7} (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x 0 0
  simp only [add_zero] at this
  exact (add_eq_left.1 this.symm)

private theorem symplO_neg_right {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

private theorem psi_ne_zero {F : Type*} [AddGroup F] (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

private theorem finLat_of_nsmul {D : D7} {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : GlobalTheory.AscFin.FinLat Λ)
    (hle : A ≤ Λ) {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : GlobalTheory.AscFin.FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a :=
    continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

end GlobalTheory.CoreOnto.Reps

open GlobalTheory.CoreOnto.Reps in
theorem _root_.GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∃ R : Finset (WO (G.pS (.core i)) (G.pT (.core i))), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) ∧ (∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) ∧ (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) → y = y') ∧ (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf e u ∧ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) ≠ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y')) := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set Λ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := latO (G.pS (.core i)) (G.pT (.core i))
    (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) with hΛ
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hinf : infPart D e = 0 := Formalism.IndefR.Fin.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hdual : ∀ u, IsHalf (cA D e) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf e l →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l u) = 1) :=
    GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D W.ψ _ _ _ _ W.ψ_std hS hT e hee hec hinf hfin
  obtain ⟨K, hK, hKΛ⟩ : ∃ K : ℕ, 0 < K ∧ ∀ u ∈ Λ, K • u ∈ depLat G (.core i) := by
    obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT (.core i)) (ΛT := G.latT (.core i)) hS
      (G.pl.modul_ne_bot sc)
    refine ⟨K, hK, fun u hu => ⟨nsmul_mem hu K, fun e' he' => ?_⟩⟩
    rw [smul_comm]
    exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e'
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he'])) _ hu)

  have hKy : ∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i),
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → K • y ∈ Λ := by
    intro y hy hyt
    refine (hdual _ (GlobalTheory.StdHalfLat.half_nsmul hy K)).2 fun l hl _ => ?_
    rw [← GlobalTheory.DownLift.SplitSep.symplO_nsmul_swap]
    exact hyt _ (hKΛ l hl)
  let A : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) :=
    { carrier := {y | IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i),
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1}
      add_mem' := fun {a b} ha hb => ⟨isHalf_add ha.1 hb.1, fun u hu => by
        rw [GlobalTheory.ConjHalfDual.symplO_add_right', AddChar.map_add_eq_mul, ha.2 u hu, hb.2 u hu, one_mul]⟩
      zero_mem' := ⟨isHalf_zero _, fun u _ => by rw [symplO_zero_right, AddChar.map_zero_eq_one]⟩
      neg_mem' := fun {a} ha => ⟨isHalf_neg ha.1, fun u hu => by
        rw [symplO_neg_right, AddChar.map_neg_eq_inv, ha.2 u hu, inv_one]⟩ }
  let KΛ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := Λ.map (nsmulAddMonoidHom K)
  have hKΛle : KΛ ≤ Λ := by
    rintro _ ⟨w, hw, rfl⟩
    exact nsmul_mem hw K
  have finΛ : GlobalTheory.AscFin.FinLat Λ := GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)
  have finKΛ : GlobalTheory.AscFin.FinLat KΛ :=
    finLat_of_nsmul finΛ hKΛle hK (fun u hu => ⟨u, hu, rfl⟩)
  let N : AddSubgroup ↥Λ := KΛ.addSubgroupOf Λ
  haveI : CompactSpace ↥Λ := isCompact_iff_compactSpace.mp finΛ.cpt
  have hNopen : IsOpen (N : Set ↥Λ) := by
    obtain ⟨U, hU, h0, hUK⟩ := finKΛ.opn
    refine AddSubgroup.isOpen_of_mem_nhds N (g := 0) ?_
    refine Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds (by simpa using h0)) ?_
    intro a ha
    exact AddSubgroup.mem_addSubgroupOf.2 (hUK _ ha (finΛ.fin _ a.2))
  haveI : Finite (↥Λ ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNopen
  let f : ↥A →+ ↥Λ :=
    { toFun := fun y => ⟨K • (y : WO (G.pS (.core i)) (G.pT (.core i))), hKy _ y.2.1 y.2.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp [nsmul_add] }
  let g : ↥A →+ ↥Λ ⧸ N := (QuotientAddGroup.mk' N).comp f
  have hker : ∀ y : ↥A, y ∈ g.ker ↔ (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ Λ := by
    intro y
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (f y) : ↥Λ ⧸ N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change K • (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ KΛ ↔ _
    constructor
    · rintro ⟨w, hw, hwe⟩
      have : w = (y : WO (G.pS (.core i)) (G.pT (.core i))) := nsmul_inj hK (by simpa using hwe)
      exact this ▸ hw
    · intro hy
      exact ⟨_, hy, by simp⟩
  haveI : Finite (↥A ⧸ g.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective g)
  haveI : Fintype (↥A ⧸ g.ker) := Fintype.ofFinite _
  let sec : ↥A ⧸ g.ker → ↥A := Function.surjInv QuotientAddGroup.mk_surjective
  have hsec : ∀ q, (QuotientAddGroup.mk (sec q) : ↥A ⧸ g.ker) = q := Function.surjInv_eq _
  have hsame : ∀ a b : ↥A, ((a : WO (G.pS (.core i)) (G.pT (.core i))) - b ∈ Λ) ↔
      (QuotientAddGroup.mk a : ↥A ⧸ g.ker) = QuotientAddGroup.mk b := by
    intro a b
    rw [QuotientAddGroup.eq, hker]
    push_cast
    rw [show -(a : WO (G.pS (.core i)) (G.pT (.core i))) + (b : WO (G.pS (.core i)) (G.pT (.core i))) =
      -((a : WO (G.pS (.core i)) (G.pT (.core i))) - (b : WO (G.pS (.core i)) (G.pT (.core i)))) by abel, neg_mem_iff]
  let R : Finset (WO (G.pS (.core i)) (G.pT (.core i))) :=
    Finset.univ.image (fun q => (sec q : WO (G.pS (.core i)) (G.pT (.core i))))
  have hR : ∀ y ∈ R, y ∈ A := by
    intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (sec q).2
  have hsep : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ Λ → y = y' := by
    intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have := (hsame _ _).1 hyy
    rw [hsec, hsec] at this
    rw [this]
  refine ⟨R, fun y hy => hR y hy, ?_, hsep, ?_⟩
  · intro y hy hyt
    let a : ↥A := ⟨y, hy, hyt⟩
    refine ⟨sec (QuotientAddGroup.mk a), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hsame a _).2 (hsec _).symm
  · intro y hy y' hy' hne
    have hnot : y - y' ∉ Λ := fun h => hne (hsep y hy y' hy' h)
    have hhalf : IsHalf (cA D e) (y - y') := by
      rw [sub_eq_add_neg]
      exact isHalf_add (hR y hy).1 (isHalf_neg (hR y' hy').1)
    obtain ⟨l, hl, hle, hne1⟩ : ∃ l ∈ Λ, IsHalf e l ∧
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y')) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hnot ((hdual _ hhalf).2 hc)
    refine ⟨l, hl, hle, fun h => hne1 ?_⟩
    have hsplit : symplO (G.pS (.core i)) (G.pT (.core i)) l y =
        symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y') + symplO (G.pS (.core i)) (G.pT (.core i)) l y' := by
      rw [← GlobalTheory.ConjHalfDual.symplO_add_right', sub_add_cancel]
    rw [hsplit, AddChar.map_add_eq_mul] at h
    exact (mul_eq_right₀ (psi_ne_zero _ _)).1 h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OrthOff

theorem orthOff : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  intro D _ T L μ0 _ sc G W M _ e he S T' LS LT u hu y hy
  classical
  have hx : FinPl.MxAt (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) (y.map (cA D)) :=
    GlobalTheory.PlaceModelComb.mxAt_of_idemSum he (Or.inr fun i j => by
      rw [Matrix.map_apply, ← map_mul, hy i j])
  have hu' := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hoff : ∀ i j, u i j ∈ FinPl.idOff D (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    intro i j
    rw [FinPl.idOff, Ideal.mem_iInf]
    rintro ⟨w, PP, hPP, rfl⟩
    have hin : HeightOneSpectrum.under (𝓞 D.host.F) PP ∈ G.pl.S0 := by
      unfold Places.W0 at hPP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
      rw [G.pl.under_w hv]
      exact hv
    have h := hu' i j
    rw [FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at h
    exact h.2 ⟨_, fun h' => h' hin⟩
  have hh : hO S T' u y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * u d a = 0 :=
      GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hx c b) (hoff d a)
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T'.gram c d) * u d a
        = incA D (S.gram⁻¹ a b) * incA D (T'.gram c d) * (cA D (y c b) * u d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

end GlobalTheory.OrthOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_vector_symplectic_orthogonal : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  first | exact @GlobalTheory.OrthOff.orthOff | exact GlobalTheory.OrthOff.orthOff | (intros; apply GlobalTheory.OrthOff.orthOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreVacRe

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem reLat_sigOK (G : GridData L sc) (i : ℕ) (h : i ≤ D.R.m) (r : ReLat (G.V (.core i))) : r.sp.SigOK :=
  (G.isV (X := .core i) (by simpa [Node.InRange] using h) (by simp)).sigOK

theorem frameLat_selfDual (V : HSp D) : IsSelfDualC V (GlobalTheory.AdelicU.frameLat V) := by
  have e : GlobalTheory.AdelicU.frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [GlobalTheory.AdelicU.mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [e]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem vacExists_reLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i)))
    (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'),
    ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _)
      (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  intro D _ _ _ _ _ _ G W _ _ i hi r r' S S' M M'
  exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is r.sp r'.sp (cart M) (cart M')
    (reLat_sigOK G i hi.le r) (reLat_sigOK G (i + 1) hi r')
    (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ) (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M' τ)
    _ _ (frameLat_selfDual r.sp) (frameLat_selfDual r'.sp)

end GlobalTheory.CoreVacRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i))) (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  first | exact @GlobalTheory.CoreVacRe.vacExists_reLat | exact GlobalTheory.CoreVacRe.vacExists_reLat | (intros; apply GlobalTheory.CoreVacRe.vacExists_reLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemHalf

theorem infPart_eq_zero_of_isSplitIdem {D : D7} {e : AE D} (h : IsSplitIdem D e) :
    infPart D e = 0 ∧ infPart D (cA D e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := h
  have hz : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  have hs : infPart D e + infPart D (cA D e) = 0 := by rw [← (infPart D).map_add, hε, hz]
  have hm : infPart D e * infPart D (cA D e) = 0 := by rw [← (infPart D).map_mul, h2, (infPart D).map_zero]
  have hi : infPart D e * infPart D e = infPart D e := by rw [← (infPart D).map_mul, h1]
  have hb : infPart D (cA D e) = - infPart D e := eq_neg_of_add_eq_zero_right hs
  rw [hb, mul_neg, hi] at hm
  have ha : infPart D e = 0 := neg_eq_zero.mp hm
  exact ⟨ha, by rw [hb, ha, neg_zero]⟩

theorem halfFin : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  intro D P e he m n y hy
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have h0 : infPart D (∑ PP ∈ P, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).1
  have h1 : infPart D (cA D (∑ PP ∈ P, es PP)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (cA D), map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).2
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rcases hy with hy | hy
  · rw [← hy i j, (infPart D).map_mul, h0, zero_mul]
  · rw [← hy i j, (infPart D).map_mul, h1, zero_mul]

end GlobalTheory.IdemHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  first | exact @GlobalTheory.IdemHalf.halfFin | exact GlobalTheory.IdemHalf.halfFin | (intros; apply GlobalTheory.IdemHalf.halfFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetEigen

theorem heisO_lincomb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) :
    heisO ψ S T y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • heisO ψ S T y (f i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cosetSum_eigen : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  intro D ψ S T ΛS ΛT P e he Λd R x hR h2 h3 h4 g hg y hy hyd
  classical
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm]; exact he.2
  have half_add : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a + b) :=
    fun ha hb i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  have half_neg : ∀ {a : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) (-a) :=
    fun ha i j => by rw [Matrix.neg_apply, mul_neg, ha i j]
  have half_sub : ∀ {a b : WO S T}, IsHalf (cA D e) a → IsHalf (cA D e) b → IsHalf (cA D e) (a - b) :=
    fun ha hb => by rw [sub_eq_add_neg]; exact half_add ha (half_neg hb)
  have ann_add : ∀ {a b : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → (∀ u ∈ Λd, ψ (symplO S T u b) = 1) →
      ∀ u ∈ Λd, ψ (symplO S T u (a + b)) = 1 :=
    fun ha hb u hu => by rw [Formalism.IndefR.Fin.symplO_add_right, AddChar.map_add_eq_mul, ha u hu, hb u hu, one_mul]
  have ann_neg : ∀ {a : WO S T}, (∀ u ∈ Λd, ψ (symplO S T u a) = 1) → ∀ u ∈ Λd, ψ (symplO S T u (-a)) = 1 :=
    fun ha u hu => by rw [Formalism.IndefR.Fin.symplO_neg_right, AddChar.map_neg_eq_inv, ha u hu, inv_one]
  choose! f hfR hfΛ using h2
  have hyz : ∀ z ∈ R, IsHalf (cA D e) (y + z) ∧ ∀ u ∈ Λd, ψ (symplO S T u (y + z)) = 1 := fun z hz =>
    ⟨half_add hy (hR z hz).1, ann_add hyd (hR z hz).2⟩
  have hzy : ∀ z ∈ R, IsHalf (cA D e) (z + -y) ∧ ∀ u ∈ Λd, ψ (symplO S T u (z + -y)) = 1 := fun z hz =>
    ⟨half_add (hR z hz).1 (half_neg hy), ann_add (hR z hz).2 (ann_neg hyd)⟩
  have hfix : ∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a →
      heisO ψ S T a g = g := fun a ha hh =>
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he a ha (Or.inr hh)
  have key : ∀ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T y (heisO ψ S T z g) =
      ψ (symplO S T x y) • (ψ (-symplO S T x (f (y + z))) • heisO ψ S T (f (y + z)) g) := by
    intro z hz
    obtain ⟨hh, ha⟩ := hyz z hz
    have hσR := hfR _ hh ha
    have ha0 := hfΛ _ hh ha
    generalize f (y + z) = s at hσR ha0 ⊢
    have hσh := (hR _ hσR).1
    have ha0h : IsHalf (cA D e) (y + z - s) := half_sub hh hσh
    have e1 : heisO ψ S T y (heisO ψ S T z g) = heisO ψ S T s g := by
      rw [← Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hy (hR z hz).1)]
      have hsplit : y + z = s + (y + z - s) := by abel
      rw [hsplit, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_add_of_iso ψ
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.symplOH_half_zero hec hσh ha0h), hfix _ ha0 ha0h]
    have hlin : symplO S T x y + symplO S T x z = symplO S T x s + symplO S T x (y + z - s) := by
      rw [← Formalism.IndefR.Fin.symplO_add_right, ← Formalism.IndefR.Fin.symplO_add_right]
      congr 1; abel
    have hph : -symplO S T x z = symplO S T x y + -symplO S T x s + -symplO S T x (y + z - s) := by
      linear_combination (-1 : AF D.host.F) * hlin
    rw [e1, hph, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv ψ (symplO S T x (y + z - s)),
      h4 _ ha0 ha0h, inv_one, mul_one, smul_smul]
  rw [heisO_lincomb, Finset.sum_congr rfl key, ← Finset.smul_sum]
  congr 1
  refine Finset.sum_nbij' (fun z => f (y + z)) (fun z => f (z + -y)) (fun z hz => hfR _ (hyz z hz).1 (hyz z hz).2)
    (fun z hz => hfR _ (hzy z hz).1 (hzy z hz).2) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => rfl)
  · have hs := hfR _ (hyz z hz).1 (hyz z hz).2
    have h1 := hfΛ _ (hyz z hz).1 (hyz z hz).2
    have h2' := hfΛ _ (hzy _ hs).1 (hzy _ hs).2
    have ht := hfR _ (hzy _ hs).1 (hzy _ hs).2
    have hsum := add_mem h1 h2'
    have heq : y + z - f (y + z) + (f (y + z) + -y - f (f (y + z) + -y)) = z - f (f (y + z) + -y) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ ht hsum).symm
  · have ht := hfR _ (hzy z hz).1 (hzy z hz).2
    have h1 := hfΛ _ (hzy z hz).1 (hzy z hz).2
    have h2' := hfΛ _ (hyz _ ht).1 (hyz _ ht).2
    have hs := hfR _ (hyz _ ht).1 (hyz _ ht).2
    have hsum := add_mem h1 h2'
    have heq : z + -y - f (z + -y) + (y + f (z + -y) - f (y + f (z + -y))) = z - f (y + f (z + -y)) := by abel
    rw [heq] at hsum
    exact (h3 z hz _ hs hsum).symm

end GlobalTheory.CosetEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_heisenberg_isEigenvector : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  first | exact @GlobalTheory.CosetEigen.cosetSum_eigen | exact GlobalTheory.CosetEigen.cosetSum_eigen | (intros; apply GlobalTheory.CosetEigen.cosetSum_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.PairLift (adjO)
noncomputable section
namespace GlobalTheory.ExchLatPf

theorem exchLat : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  intro D hOff T L μ0 hLi sc G W M hM hEx hLat i hi r r' hr hr' g hg
  have hAdj := GlobalTheory.AdjLawPf.adjLaw D W.ψ W.ψ_std (G.V (.core i)) (G.V (.core (i+1)))
  have hE := (hEx W.ψ (G.V (.core i)) (G.V (.core (i+1))) W.ψ_std).2.1
  have hL := hLat D hOff T L μ0 hLi sc G W M hM i hi r r' hr hr' (fun _ => True)
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · refine (hE _ _).trans (congrArg _ ?_)
    have h2 : adjO (G.V (.core i)) (G.V (.core (i+1))) (2 • u) = 2 • adjO (G.V (.core i)) (G.V (.core (i+1))) u := by
      rw [two_smul, two_smul, hAdj.add]
    rw [h2]
    exact hg.1 _ ((hL u).1 hu)
  · refine (hE _ _).trans (congrArg _ ?_)
    exact hg.2 (cA D e) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isSplitIdem_cA he) _ ((hL u).1 hu) (hAdj.half e u hue)

end GlobalTheory.ExchLatPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeIsLatticeVacuumCoreChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain : All fun {D} _ _ _ {G} W _ => ExchLaw D → LatExch → ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ g : WO r.sp r'.sp → ℂ, IsLatVac (heisO W.ψ r.sp r'.sp) (latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) fun _ => True) g → IsLatVac (heisO W.ψ (G.pS (.core i)) (G.pT (.core i))) (latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
  first | exact @GlobalTheory.ExchLatPf.exchLat | exact GlobalTheory.ExchLatPf.exchLat | (intros; apply GlobalTheory.ExchLatPf.exchLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombination
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CombTheta

theorem comb_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  classical
  intro D ψ θ S T hψ hθ g hg ι R c t ht
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ g hg
  have hth : ∀ z ∈ R, IsThetaFunO ψ S T (heisO ψ S T (t z) g) := fun z hz => (ft.2 (t z) (ht z hz)).1
  have key : ∀ s ⊆ R, IsThetaFunO ψ S T (∑ z ∈ s, c z • heisO ψ S T (t z) g) ∧
      ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
        (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ),
        pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ s, c z • heisO ψ S T (t z) g) φ =
          ∑ z ∈ s, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨GlobalTheory.OrientedHeis.theta_zero, fun sS BS sT BT φ =>
        GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      intro hs
      have hiR : i ∈ R := hs (Finset.mem_insert_self i s)
      have ih' := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      simp only [Finset.sum_insert hi]
      refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hth i hiR)) ih'.1, fun sS BS sT BT φ => ?_⟩
      rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (c i) (hth i hiR) ih'.1 φ, ih'.2,
        (ft.2 (t i) (ht i hiR)).2 sS BS sT BT φ]
  exact ⟨(key R subset_rfl).1, fun sS BS sT BT φ => (key R subset_rfl).2 sS BS sT BT φ⟩

end GlobalTheory.CombTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFiniteHeisenbergCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (g : WO S T → ℂ), IsThetaFunO ψ S T g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsThetaFunO ψ S T (∑ z ∈ R, c z • heisO ψ S T (t z) g) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (∑ z ∈ R, c z • heisO ψ S T (t z) g) φ = ∑ z ∈ R, c z • heisO ψ S T (t z) (pureTensorO ψ θ S T sS sT BS BT g φ) := by
  first | exact @GlobalTheory.CombTheta.comb_theta | exact GlobalTheory.CombTheta.comb_theta | (intros; apply GlobalTheory.CombTheta.comb_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisJointEigen

theorem coeff_zero_of_separated {ι V : Type*} [AddCommGroup V] [Module ℂ V] [DecidableEq ι] (v : ι → V) :
    ∀ R : Finset ι, (∀ z ∈ R, v z ≠ 0) →
      (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ R, A (v z) = χ z • v z) ∧ χ y ≠ χ y') →
      ∀ c : ι → ℂ, ∑ z ∈ R, c z • v z = 0 → ∀ z ∈ R, c z = 0 := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ _ c _ z hz; simp at hz
  | insert a s ha ih =>
    intro hv hsep c hsum
    have hv' : ∀ z ∈ s, v z ≠ 0 := fun z hz => hv z (Finset.mem_insert_of_mem hz)
    have hsep' : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' →
        ∃ (A : V →ₗ[ℂ] V) (χ : ι → ℂ), (∀ z ∈ s, A (v z) = χ z • v z) ∧ χ y ≠ χ y' := by
      intro y hy y' hy' hne
      obtain ⟨A, χ, hA, hχ⟩ := hsep y (Finset.mem_insert_of_mem hy) y' (Finset.mem_insert_of_mem hy') hne
      exact ⟨A, χ, fun z hz => hA z (Finset.mem_insert_of_mem hz), hχ⟩
    rw [Finset.sum_insert ha] at hsum
    have hs0 : ∀ b ∈ s, c b = 0 := by
      intro b hb
      have hab : b ≠ a := fun h => ha (h ▸ hb)
      obtain ⟨A, χ, hA, hχ⟩ := hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a s) hab
      have key : ∑ z ∈ s, (c z * (χ z - χ a)) • v z =
          A (c a • v a + ∑ z ∈ s, c z • v z) - χ a • (c a • v a + ∑ z ∈ s, c z • v z) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_smul, hA a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum,
          add_sub_add_comm, smul_comm (χ a) (c a), sub_self, zero_add, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [map_smul, hA z (Finset.mem_insert_of_mem hz), smul_smul, smul_smul, ← sub_smul]
        congr 1
        ring
      rw [hsum, map_zero, smul_zero, sub_zero] at key
      have h := ih hv' hsep' (fun z => c z * (χ z - χ a)) key b hb
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hχ
    have hsum0 : ∑ z ∈ s, c z • v z = 0 := Finset.sum_eq_zero fun z hz => by rw [hs0 z hz, zero_smul]
    rw [hsum0, add_zero] at hsum
    have hca : c a = 0 := (smul_eq_zero.1 hsum).resolve_right (hv a (Finset.mem_insert_self a s))
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hca
    · exact hs0 z hz

theorem sum_heisO_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  intro D ψ S T ΛS ΛT P e he R hsep g hg hg0 c hc hsum
  obtain ⟨z0, hz0, hcz⟩ := hc
  apply hcz
  classical
  refine coeff_zero_of_separated (fun z => heisO ψ S T z g) R ?_ ?_ c hsum z0 hz0
  · intro z _ h
    apply hg0
    funext w
    have h1 := congrFun h (w - z)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (Formalism.IndefR.Fin.psi_ne_zero ψ _)
    · exact h2
  · intro y hy y' hy' hne
    obtain ⟨u, hu, hhalf, hψ⟩ := hsep y hy y' hy' hne
    have hfix : heisO ψ S T u g = g :=
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac ψ hg he u hu (Or.inl hhalf)
    refine ⟨Formalism.IndefR.Fin.heisL ψ S T u, fun z => ψ (symplO S T u z), fun z _ => ?_, hψ⟩
    have h1 := congrArg (fun L => L g) (Formalism.IndefR.Fin.heisL_comm ψ S T u z)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Formalism.IndefR.Fin.heisL_apply] at h1
    rw [hfix] at h1
    rw [Formalism.IndefR.Fin.heisL_apply]
    exact h1

end GlobalTheory.HeisJointEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  first | exact @GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | exact GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | (intros; apply GlobalTheory.HeisJointEigen.sum_heisO_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacComb

theorem isLatVac_sum_heisO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, ∀ u ∈ Λ, ψ (symplO S T u (t z)) = 1) → IsLatVac (heisO ψ S T) Λ (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  intro D ψ S T Λ g hg ι R c t ht
  have key : ∀ w : WO S T, heisO ψ S T w g = g → (∀ z ∈ R, ψ (symplO S T w (t z)) = 1) →
      heisO ψ S T w (∑ z ∈ R, c z • heisO ψ S T (t z) g) = ∑ z ∈ R, c z • heisO ψ S T (t z) g := by
    intro w hw hwt
    rw [GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hw, hwt z hz, one_smul]
  refine ⟨fun u hu => key (2 • u) (hg.1 u hu) fun z hz => ht z hz _ (AddSubgroup.nsmul_mem Λ hu 2),
    fun e he u hu hue => key u (hg.2 e he u hu hue) fun z hz => ht z hz u hu⟩

end GlobalTheory.LatVacComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, ∀ u ∈ Λ, ψ (symplO S T u (t z)) = 1) → IsLatVac (heisO ψ S T) Λ (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.LatVacComb.isLatVac_sum_heisO | exact GlobalTheory.LatVacComb.isLatVac_sum_heisO | (intros; apply GlobalTheory.LatVacComb.isLatVac_sum_heisO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombination
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombFockTranslate

theorem isFockVacAt_comb : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  intro D ψ θ S T hψ hθ J τ g hg hv ι R c t ht
  exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ g hg τ J hv ι R t c ht

end GlobalTheory.CombFockTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtFiniteHeisenbergCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ : D.what₂.Tau) (g : WO S T → ℂ), IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ J g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, (t z).map (infPart D) = 0) → IsFockVacAt (heisO ψ S T) θ τ J (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  first | exact @GlobalTheory.CombFockTranslate.isFockVacAt_comb | exact GlobalTheory.CombFockTranslate.isFockVacAt_comb | (intros; apply GlobalTheory.CombFockTranslate.isFockVacAt_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CosDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cA_cA₀ {D : D7} (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => show a ⊗ₜ[D.host.F] star (star x) = _; rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem latO_le_true {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩

theorem isLatVac_mono {D : D7} {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ' ≤ Λ) {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ f) : IsLatVac hs Λ' f :=
  ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end GlobalTheory.CosDatum

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CosDatum in
theorem datumEx : DatumEx := by
  intro D hq T L μ0 hL sc G W M hM i hi r r' hr hr' S S' MM MM' x₀ hx₀
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hθ : IsInfFam W.θ := W.θ_is
  have hEx : ExchLaw D := GlobalTheory.T.adjointExchange_laws_thetaHeisenberg D
  have hLE : LatExch := GlobalTheory.T.coreChain_adjoint_latticeExchange
  have hadj := GlobalTheory.AdjLawPf.adjLaw D W.ψ hψ (G.V (.core i)) (G.V (.core (i + 1)))
  obtain ⟨e, he, -⟩ := W.cosVec_is
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.thetaChain_unitVacuum_otherLattices_exists D hq T L μ0 hL sc G W M hM i hi r r' S S' MM MM'
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ := GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice D hq T L μ0 hL sc G W M hM i hi e he
  have hxi := GlobalTheory.T.corePair_integralPoint_pairs_trivially_half D hq T L μ0 hL sc G W M hM i hi e he x₀ hx₀
  have hhalf : ∀ z ∈ R, IsHalf e (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) := fun z hz => by
    have := hadj.half _ z (hR1 z hz).1
    rwa [cA_cA₀] at this
  have hfin : ∀ z ∈ R, (adjO (G.V (.core i)) (G.V (.core (i + 1))) z).map (infPart D) = 0 := fun z hz =>
    GlobalTheory.T.infinitePart_eq_zero_of_isHalf_idempotentSum _ e he _ (Or.inl (hhalf z hz))
  let c : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ :=
    fun z => W.ψ (-symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) z)
  let f : WO r.sp r'.sp → ℂ :=
    ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) f₀
  have hexs : ∀ g : WO r.sp r'.sp → ℂ,
      exch (G.V (.core i)) (G.V (.core (i + 1)))
        (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g) =
      ∑ z ∈ R, c z • heisO W.ψ (G.pS (.core i)) (G.pT (.core i)) z (exch (G.V (.core i)) (G.V (.core (i + 1))) g) := by
    intro g
    funext x
    have h2 := fun z : WO (G.pS (.core i)) (G.pT (.core i)) =>
      congrFun ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).2.1 z g) x
    show (∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) g)
      (adjO (G.V (.core i)) (G.V (.core (i + 1))) x) = _
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, h2 z]
    rfl
  have hf₀th : IsThetaFunO W.ψ r.sp r'.sp f₀ := hf₀.2.theta
  have hcomb := GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ f₀ hf₀th R c _ hfin
  have hex0 : exch (G.V (.core i)) (G.V (.core (i + 1))) f₀ ≠ 0 := by
    intro h0
    apply GlobalTheory.SeeSaw.Inh.vac_ne_zero hf₀
    funext y
    obtain ⟨x, rfl⟩ := (hEx W.ψ _ _ hψ).2.2.2.1.2 y
    exact congrFun h0 x
  have hRne : ∃ z ∈ R, c z ≠ 0 := by
    obtain ⟨y', hy', -⟩ := hR2 0 (fun _ _ => mul_zero _) (fun u _ => by
      have h00 : symplO (G.pS (.core i)) (G.pT (.core i)) u 0 = 0 := by unfold symplO hO; simp
      rw [h00, AddChar.map_zero_eq_one])
    exact ⟨y', hy', addChar_ne_zero _ _⟩
  refine ⟨f, ⟨hcomb.1, ?_, fun τ => GlobalTheory.T.isFockVacuumAt_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ τ f₀ hf₀th (hf₀.2.fock τ) R c _ hfin⟩,
    ?_, fun φ => ?_⟩
  · intro h0
    have h2 : exch (G.V (.core i)) (G.V (.core (i + 1))) f = 0 := by rw [h0]; rfl
    refine GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero W.ψ (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he R hR4
      _ (GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' f₀ hf₀.2.lat) hex0 c hRne ?_
    rw [← hexs f₀]
    exact h2
  · show IsLatVac _ _ _
    refine GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ r.sp r'.sp _ f₀ (isLatVac_mono (latO_le_true _ _ _ _ _) hf₀.2.lat) R c _ ?_
    intro z hz u hu
    rw [GlobalTheory.T.half_vector_symplectic_orthogonal D hq T L μ0 hL sc G W M hM e he r.sp r'.sp _ _ u hu _ (hhalf z hz), AddChar.map_zero_eq_one]
  · have hpt : ptOf W.ψ W.θ MM MM' f φ = ∑ z ∈ R, c z • heisO W.ψ r.sp r'.sp
        (adjO (G.V (.core i)) (G.V (.core (i + 1))) z) (ptOf W.ψ W.θ MM MM' f₀ φ) :=
      hcomb.2 (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hfl := GlobalTheory.T.isTheta_isLatticeVacuum_fockPureTensor W.ψ W.θ r.sp r'.sp hψ hθ _ _ _ f₀ hf₀th hf₀.2.lat (cart MM) (onb MM) (cart MM') (onb MM') φ
    have hgl := GlobalTheory.T.adjointExchange_isLatticeVacuum_coreChain D hq T L μ0 hL sc G W M hM hEx hLE i hi r r' hr hr' _ hfl.2
    have hth : IsThetaFunO W.ψ r.sp r'.sp (ptOf W.ψ W.θ MM MM' f φ) := by
      rw [hpt]; exact (GlobalTheory.T.isThetaFunction_finiteHeisenbergCombination W.ψ W.θ r.sp r'.sp hψ hθ _ hfl.1 R c _ hfin).1
    have hth' := (((GlobalTheory.T.selfDualLattice_changeOfLattice_laws D).2.2 W.ψ (G.V (.core i)) (G.V (.core (i + 1))) r r').1 _).1 hth
    have hΦth := ((hEx W.ψ (G.V (.core i)) (G.V (.core (i + 1))) hψ).1 _).1 hth'
    have hΦ := hexs (ptOf W.ψ W.θ MM MM' f₀ φ)
    rw [← hpt] at hΦ
    rw [hΦ] at hΦth ⊢
    refine ⟨⟨hΦth, GlobalTheory.T.isLatticeVacuum_sum_heisenbergTranslates W.ψ _ _ _ _ (isLatVac_mono (Λ' := depLat G (.core i)) (fun u hu => hu.1) hgl) R c (fun z => z)
      (fun z hz => (hR1 z hz).2)⟩, ?_⟩
    intro e' he' y hy hyd
    obtain rfl := GlobalTheory.T.idempotentSum_over_finite_places_unique _ _ _ he he'
    exact GlobalTheory.T.cosetSum_heisenberg_isEigenvector W.ψ _ _ (G.latS (.core i)) (G.latT (.core i)) G.pl.W0 e he (depLat G (.core i)) R _ hR1 hR2 hR3 hxi
      _ hgl y hy hyd

end GlobalTheory.CoreOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cosetFockVacuumDatum : DatumEx := by
  first | exact @GlobalTheory.CoreOnto.datumEx | exact GlobalTheory.CoreOnto.datumEx | (intros; apply GlobalTheory.CoreOnto.datumEx <;> assumption)
end
