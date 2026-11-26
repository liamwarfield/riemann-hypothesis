module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)
open scoped ComplexOrder

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn)

theorem exists_stdRig (n : ℕ) : ∃ (V : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), V.rank = n ∧ V.SigOK ∧ r.IsStd ∧ r.Is := by
  let V : HSp D := Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hg : V.gram = 1 := by
    change (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0).gram = (1 : Matrix (Fin n) (Fin n) D.host.E)
    ext i j
    change Fin n at i j
    change (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0).gram i j = (if i = j then 1 else 0)
    simpa [Formalism.BasicNotions.Examples₂.sgn] using
      (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j)
  let Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, IsIntegral ℤ (y i) := fun y => by
    simp only [Λ, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨y i, h⟩, rfl⟩⟩
  have hsingle : ∀ i, (Pi.single i 1 : Fin V.rank → D.host.E) ∈ Λ := fun i => (hmem _).2 fun k => by
    by_cases h : k = i
    · subst h; simpa using isIntegral_one
    · simpa [h] using isIntegral_zero
  have hsd : IsSelfDualC V Λ := by
    refine ⟨Submodule.IsLattice.of_fg D.host.E (Submodule.fg_pi fun _ => ?_), fun y => ⟨fun hy x hx => ?_, fun h => (hmem y).2 fun i => ?_⟩⟩
    · rw [Submodule.one_eq_span]
      exact Submodule.fg_span (Set.finite_singleton _)
    · have hs : IsIntegral ℤ (∑ a, ∑ b, star (x a) * V.gram a b * y b) := by
        rw [hg]
        refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
        by_cases hab : a = b
        · subst hab
          simpa using (Formalism.BasicNotions.Examples₂.star_isIntegral _ ((hmem x).1 hx a)).mul ((hmem y).1 hy a)
        · simpa [Matrix.one_apply, hab] using isIntegral_zero
      exact ⟨⟨_, hs⟩, rfl⟩
    · obtain ⟨b, hb⟩ := h _ (hsingle i)
      have e : ∑ a, ∑ c, star ((Pi.single i 1 : Fin V.rank → D.host.E) a) * V.gram a c * y c = y i := by
        rw [hg, Finset.sum_eq_single i]
        · simp [Matrix.one_apply]
        · intro a _ ha
          simp [ha]
        · simp
      rw [e] at hb
      exact hb ▸ b.isIntegral_coe
  obtain ⟨r, hr, hri⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D V Λ (Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n) hsd
  have hgt : ∀ τ, gramAt D V τ = 1 := fun τ => by rw [gramAt, hg]; simp
  refine ⟨V, ⟨Λ, r.β, fun _ => 1, fun _ => 1⟩, rfl, Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n,
    ⟨hg, fun y => (hmem y).trans (forall_congr' fun i => ⟨fun h => ⟨⟨y i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩),
      fun _ => ⟨rfl, rfl⟩⟩, hsd, hr ▸ hri.2.1, fun τ => ⟨?_, V.rank, ?_⟩⟩
  · rw [hgt]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  · rw [hgt]
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩ <;> simp

theorem bottom_chars {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) ∧
      IsHeckeChar D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) ∧
      ResEta D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) (SqNum.botSmall D i j) ∧
      ResEta D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (SqNum.botBig D i j) := by
  have hmul : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ * η) := fun h1 h2 =>
    ⟨h1.1.mul h2.1, fun x => by rw [MonoidHom.mul_apply, h1.2, h2.2, mul_one]⟩
  have heta : IsHeckeChar D L.eta := hL.eta.1
  have hpow : ∀ n, IsHeckeChar D (L.eta ^ n) := fun n =>
    ⟨heta.1.pow n, fun x => by rw [MonoidHom.pow_apply, heta.2, one_pow]⟩
  have hi := i.2
  have hchiE := G.ch.chi_eq (D.R.m - i) (by omega) (by omega)
  have rpow : ∀ n, ResEta D (L.eta ^ n) n := fun n => by
    induction n with
    | zero => exact ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by simp⟩
    | succ n ih => rw [pow_succ]; exact resEta_mul ih (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
  have rchi : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by
    rw [pow_zero]; exact GlobalTheory.GridWeil.triv_base hchiE (G.ch.triv _ (by omega) (by omega)) a⟩
  obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
  refine ⟨hmul (GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j) (hpow _), hmul hchiE.1 (hpow _),
    resEta_parity (resEta_mul (GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j) (rpow _)) ?_,
    resEta_parity (resEta_mul rchi (rpow _)) ?_⟩ <;> omega

theorem isSelfDualC_neg' {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (h : IsSelfDualC A Λ) :
    IsSelfDualC (neg A) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [neg_gram, hc]
  · simp [neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

theorem exists_bottomTri {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X := by
  obtain ⟨A, rA, hA1, hA2, hA3, hA4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j)
  obtain ⟨A', rA', hB1, hB2, hB3, hB4⟩ := exists_stdRig (D := D) (SqNum.botSmall D i j)
  obtain ⟨WW, rW, hW1, hW2, hW3, hW4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j + SqNum.botSmall D i j)
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hc := fun t => bottom_chars hL G i j t
  have hd : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ / η) := fun h1 h2 =>
    ⟨h1.1.div' h2.1, fun x => by rw [MonoidHom.div_apply, h1.2, h2.2, div_one]⟩
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (hc t).2.1 (hd (hc t).2.1 (hc t).1)
    (hA1 ▸ (hc t).2.2.2) (by rw [hW1, div_eq_mul_inv]; exact resEta_mul (hc t).2.2.2 (resEta_inv (hc t).2.2.1))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (hc t).1 (hd (hc t).1 (hc t).2.1)
    (hB1 ▸ (hc t).2.2.1) (by rw [hW1, div_eq_mul_inv, Nat.add_comm (SqNum.botBig D i j)]; exact resEta_mul (hc t).2.2.1 (resEta_inv (hc t).2.2.2))
  have s1 : (neg A).SigOK := sigOK_sgn true hA2
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg A) WW (fun τ => -rA.s τ) rW.s
    s1 hW2 (fun τ => isCartanInv_sgn true _ τ (hA4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA.Λ rW.Λ (isSelfDualC_neg' hA4.1) hW4.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ A' WW rA'.s rW.s
    hB2 hW2 (fun τ => (hB4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA'.Λ rW.Λ hB4.1 hW4.1
  choose e he using GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G
  choose c hc' using fun t w => GlobalTheory.ConstRatio.exists_expAt (SqNum.nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW rA rW _ _ _ _ _ hA4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ A' WW rA' rW _ _ _ _ A.rank _ hB4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨A, A', WW, ⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩, hA1, hB1, hA3, hB3, hW3,
    ⟨by rw [hA1, hB1, hW1], hA4, hB4, hW4, hω, hω', hv, hv', he, fun t w _ => hc' t w, hf, hf', hm, hm'⟩⟩

theorem IsBottomTri.integrable {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) :
    (∀ P g, IntegrableOn (X.ker W.ψ W.θ t P g) X.fd X.m) ∧ ∀ P g, IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := by
  have h := hX.is
  have hA := GlobalTheory.ConstRatio.posDef_of_std hX.std
  have hA' := GlobalTheory.ConstRatio.posDef_of_std hX.std'
  refine ⟨fun P g => ?_, fun P g => ?_⟩
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).1 P)).1 g
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac'.1 h.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).2 P)).1 g

end GlobalTheory.RowTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFunB

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree.LineDerFunB


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem frameMat_isom (d : HermitianOrthogonalExtensionData A B c ε) : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram :=
  GlobalTheory.ChiGrid.SumDual.gram_isom A B d.ι d.isom

theorem perp_sub (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (frameMat B A d.ι)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun d.perp i) (f j)

theorem gram_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k l : ℕ} (f : Fin k → Fin c) (g : Fin l → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * d.a.submatrix id g = (antiDiagonalSignGramMatrix c ε).submatrix f g :=
  d.gram_sub f g

def jacDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ) : HypDec B A σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := frameMat B A d.ι
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := frameMat_isom d
  i₀e := perp_sub d _
  i₀e' := perp_sub d _
  rank_add := by have := d.rank; omega

def midCol {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) : Matrix (Fin B.rank) (Fin 1) D.host.E :=
  d.a.submatrix id fun _ : Fin 1 => (⟨σ, by omega⟩ : Fin c)

def coreMat {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) :
    Matrix (Fin B.rank) (Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank) D.host.E :=
  (Matrix.fromCols (frameMat B A d.ι) (midCol d h)).submatrix id finSumFinEquiv.symm

theorem nLine_gram (i j : Fin 1) : (GlobalTheory.SeeSaw.Model.nLine D).gram i j = -1 := by
  show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
  rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Examples₂.sgn]

theorem perp_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * frameMat B A d.ι = 0 := by
  have h := congrArg conjTranspose (perp_sub d f)
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at h

theorem coreMat_gram {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (coreMat d h)ᴴ * B.gram * coreMat d h = (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).gram := by
  have hNN : (midCol d h)ᴴ * B.gram * midCol d h = (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => (?_ : _ = (-1 : D.host.E)).trans (nLine_gram i j).symm)
    simp only [submatrix_apply, antiDiagonalSignGramMatrix]
    rw [if_pos (by omega), if_true]
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * Matrix.fromCols (frameMat B A d.ι) (midCol d h) =
      Matrix.fromBlocks A.gram 0 0 (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, frameMat_isom,
      hNN]
    rw [show (frameMat B A d.ι)ᴴ * B.gram * midCol d h = 0 from perp_sub d _,
      show (midCol d h)ᴴ * B.gram * frameMat B A d.ι = 0 from perp_sub' d _]
    rfl
  refine Matrix.ext fun i j => ?_
  rw [GlobalTheory.Doubling.gram_hsum]
  exact congrFun (congrFun key _) _

theorem coreMat_perp {σ k : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) (f : Fin k → Fin c) (hf : ∀ i, (f i).1 + σ + 1 ≠ c) :
    (coreMat d h)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * d.a.submatrix id f = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul, perp_sub]
    rw [show (midCol d h)ᴴ * B.gram * d.a.submatrix id f = 0 from (gram_sub' d _ _).trans (Matrix.ext fun i j => by
      simp only [submatrix_apply, antiDiagonalSignGramMatrix, Matrix.zero_apply]
      rw [if_neg (by have := hf j; omega)])]
    exact fromRows_zero
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun key _) j

def besDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) : HypDec B (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)) σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := coreMat d h
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := coreMat_gram d h
  i₀e := coreMat_perp d h _ fun i => by have := i.2; simp only [Fin.val_castLE]; omega
  i₀e' := coreMat_perp d h (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev) fun i => by
    have := i.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  rank_add := by have := d.rank; show A.rank + 1 + 2 * σ = B.rank; omega

section Grid

open GlobalTheory.FunObj

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem cocpt_top {j : ℕ} (hj : j ≤ D.R.m) : CoCpt (G.V (.top j)) := by
  have h := G.isV (X := .top j) hj fun i e => by cases e
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def rowBes (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ + 1) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  besDec (G.rowDec j hj) h

def rowJac (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ) : HypDec (G.V (.grid D.R.m j)) (G.V (.top j)) σ :=
  jacDec (G.rowDec j hj) h

def topVolN (M : Vol G) (hM : M.IsRow) (hj : 0 < D.R.m) (h : D.R.m - 1 - 0 = 2 * ((D.R.m - 2) / 2) + 1) :
    VolN (rowBes G 0 hj ((D.R.m - 2) / 2) h) :=
  ⟨M.νN, M.fdN, hM.unip⟩

end Grid

end GlobalTheory.RowUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthShift

open GlobalTheory.StdFrames (cpt mem_OA_iff comp_toAd toAd toAd_spec)
open scoped Pointwise

variable {D : D7}

theorem modul_mem_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {r : 𝓞 D.host.E}
    (hr : r ∈ G.modul) : (r : D.host.E) ∈ shiftId G := by
  have h0 : G.pl.modulBar sc ≠ ⊥ := by
    intro h
    apply G.pl.modul_ne_bot sc
    unfold Places.modulBar at h
    have := congrArg (fun J => D.host.conj⁻¹ • J) h
    simpa using this
  have h1 := FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) h0
  have h2 : (r : D.host.E) ∈ ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hr
  simpa [shiftId] using FractionalIdeal.mul_mem_mul h2 h1

theorem smul_mem_idLat {n : ℕ} {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {r : 𝓞 D.host.E} (hr : (r : D.host.E) ∈ J)
    {t : Fin n → D.host.E} (ht : t ∈ idLat I Λ) : r • t ∈ idLat (I * J) Λ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨s * r, FractionalIdeal.mul_mem_mul hs hr, y, hy, ?_⟩
    rw [mul_comm, mul_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

variable {S B : HSp D} {LS : Lat S} {LT LT' : Lat B}

theorem inc_smul_mem {r : 𝓞 D.host.E} (hr : ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) :
    incA D (r : D.host.E) • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, r • t, hr t ht, ?_⟩
    ext i j
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * ((r : D.host.E) * t i) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_eq_of_toEAf {b b' x : AE D} (h : toEAf D b = toEAf D b') (h0 : infPart D x = 0) : b * x = b' * x := by
  have h1 : infPart D ((b - b') * x) = 0 := ((infPart D).map_mul _ _).trans (by rw [h0, mul_zero])
  have h2 : toEAf D (b - b') = 0 := ((toEAf D).map_sub _ _).trans (sub_eq_zero.2 h)
  have h3 : toEAf D ((b - b') * x) = 0 := ((toEAf D).map_mul _ _).trans (by rw [h2, zero_mul])
  have h4 := (comp_toAd D).ext _ h1 ((congrArg (toAd D) h3).trans (toAd D).map_zero)
  exact sub_eq_zero.1 ((sub_mul b b' x).symm.trans h4)

theorem exists_lift_int (c : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ c' : AE D, toEAf D c' = c.1 ∧ finPart D c' ∈ intAE D := by
  obtain ⟨c', -, hc'⟩ := (comp_toAd D).surj (toAd D c.1)
  refine ⟨c', GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) hc', ((comp_toAd D).int c').2 fun Q => ?_⟩
  rw [hc']
  exact (mem_OA_iff _).1 c.2 Q


set_option maxHeartbeats 800000 in
theorem smul_mem_of_idS {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : ∀ r ∈ 𝔪, ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F 𝔪) {b : AE D} (hb : toEAf D b = s.1) :
    b • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  have key : ∃ b' : AE D, toEAf D b' = s.1 ∧ b' • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
    clear hb
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨incA D (r : D.host.E), rfl, inc_smul_mem (h𝔪 r hr) hu⟩
    | zero => exact ⟨0, RingHom.map_zero _, by rw [zero_smul]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c, hc, hc'⟩ := hy
      exact ⟨a + c, by rw [RingHom.map_add (f := _), ha, hc, Subring.coe_add], by rw [add_smul]; exact add_mem ha' hc'⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c', hc, hc'⟩ := exists_lift_int c
      refine ⟨c' * a, ((toEAf D).map_mul c' a).trans (congrArg₂ (· * ·) hc ha), ?_⟩
      rw [mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D S B _ _ _ _ hc' _ ha'
  obtain ⟨b', hb', hm⟩ := key
  have e : b • u = b' • u := Matrix.ext fun i j =>
    mul_eq_of_toEAf (hb.trans hb'.symm) (GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)).1
  rw [e]
  exact hm

theorem mem_latO_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  intro D hOff T L μ0 hL sc G S B LS I Λ₀ hS _ _ z hz ⟨e, he, hez⟩
  have h𝔪 : ∀ r ∈ G.modul, ∀ t ∈ idLat I Λ₀, r • t ∈ idLat (I * shiftId G) Λ₀ :=
    fun r hr t ht => smul_mem_idLat (modul_mem_shiftId G hr) ht
  have hle : G.modul • homLat LS (idLat I Λ₀) ≤ homLat LS (idLat (I * shiftId G) Λ₀) :=
    Submodule.smul_le.2 fun r hr x hx y hy => by
      rw [smul_mulVec]
      exact h𝔪 r hr _ (hx y hy)
  have h1 : e • z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) fun _ => True := by
    refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hOff hL G) (fun i j => ?_) ?_
    · change e * (e * z i j) = e * z i j
      rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
    · refine AddSubgroup.closure_mono ?_ hez
      rintro _ ⟨α, hα, x, hx, rfl⟩
      exact ⟨α, hα, x, hle hx, rfl⟩
  obtain ⟨-, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
    by_cases hQ : Q ∈ G.pl.W0
    · rw [e1 Q hQ, sub_self]; exact zero_mem _
    · rw [e2 Q hQ, sub_zero]; exact one_mem _
  have hid : (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F G.modul := by
    refine (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
    change Valued.v (cpt (D := D) w (toEAf D (1 - e))) ≤ _
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
    exact zero_le
  have h2 := smul_mem_of_idS (LS := LS) h𝔪 hz hid rfl
  have h3 := add_mem h1 h2
  rwa [← add_smul, add_sub_cancel, one_smul] at h3

end GlobalTheory.DepthShift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.DepthShift.mem_latO_shift | exact GlobalTheory.DepthShift.mem_latO_shift | (intros; apply GlobalTheory.DepthShift.mem_latO_shift <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownFock

theorem isThetaFunO_fock_down : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  intro D T L sc G W ρ t i j hi hj e _he φ f hf Q
  have hv : IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.mu t i j)) (G.onT W.cart (.mu t i j))
      (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) (ρ.vT i j) := ρ.vT_is t i j hi hj
  have hf' : IsThetaFunO W.ψ _ _ f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 hv.2.theta
  exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf' Q

end GlobalTheory.DownFock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  first | exact @GlobalTheory.DownFock.isThetaFunO_fock_down | exact GlobalTheory.DownFock.isThetaFunO_fock_down | (intros; apply GlobalTheory.DownFock.isThetaFunO_fock_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridExistenceOfFunctoriality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.RowEx.GridExPf

open _root_.Formalism.L2.Col GlobalTheory.GridPlaces

variable {D : D7}

theorem under_conjugatePrime_ne_of_class {p : ℕ} (hp : p.Prime) (hcl : D.host.cls p = .splitK) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (conjPrime₂ P).under (𝓞 D.host.K) ≠ P.under (𝓞 D.host.K) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h2, hd, hj⟩ : p ≠ 2 ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
    obtain ⟨h1, -, h3, h4⟩ := (primeClass_eq_splitK_iff D.host.toHostRaw).1 hcl
    exact ⟨UpperTheory.Small.ne_two D.host h1, h3, h4⟩
  obtain ⟨s, hs⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ s * s + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hs ⊢
    rw [← hs]; ring
  have hsq := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hsq]
    have := (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ))).neg
    simpa using this
  let b : 𝓞 D.host.K := ⟨⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.K D.host.E) Subtype.val_injective).1 hint⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) b := ⟨_, rfl⟩
  have hβ1 : (β : D.host.E) = D.host.sqrtMinusD := by rw [hβ]; rfl
  have hβ2 : β * β = -(D.host.d : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [hβ1, sq] using hsq)
  have hβ3 : cO D.host.E β = -β := RingOfIntegers.ext (by
    show star (β : D.host.E) = ((-β : 𝓞 D.host.E) : D.host.E)
    rw [bridge_star_holds D.R D.host, hβ1, D.host.conj_sqrtMinusD, ← hβ1]
    simp)
  have key : ∀ t : ℤ, (t : 𝓞 D.host.E) + β ∈ P.asIdeal ↔ (t : 𝓞 D.host.E) - β ∈ P.asIdeal := by
    intro t
    have h1 : (t : 𝓞 D.host.K) + b ∈ ((conjPrime₂ P).under (𝓞 D.host.K)).asIdeal ↔
        (t : 𝓞 D.host.K) + b ∈ (P.under (𝓞 D.host.K)).asIdeal := by rw [h]
    have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) = t + β := by
      rw [map_add (f := _), map_intCast, hβ]
    have h4 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ (conjPrime₂ P).asIdeal ↔
      algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((t : 𝓞 D.host.K) + b) ∈ P.asIdeal := h1
    rw [h3, mem_conjP, map_add (f := _), map_intCast, hβ3, ← sub_eq_add_neg] at h4
    exact h4.symm
  have hprod : ((s : 𝓞 D.host.E) + β) * (s - β) ∈ P.asIdeal := by
    have e : ((s : 𝓞 D.host.E) + β) * (s - β) = (p : 𝓞 D.host.E) * m := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hm
      push_cast at this
      linear_combination this - hβ2
    rw [e]
    exact Ideal.mul_mem_right _ _ hP
  have ha : (s : 𝓞 D.host.E) + β ∈ P.asIdeal := (P.isPrime.mem_or_mem hprod).elim id (key s).2
  have hb := (key s).1 ha
  have h5 : (2 : 𝓞 D.host.E) * β ∈ P.asIdeal := by
    have := sub_mem ha hb
    rwa [show (s : 𝓞 D.host.E) + β - (s - β) = 2 * β by ring] at this
  rcases P.isPrime.mem_or_mem h5 with h6 | h6
  · exact h2 (prime_eq_of_mem P hp Nat.prime_two hP (by exact_mod_cast h6))
  · have h7 := neg_mem (Ideal.mul_mem_left _ β h6)
    rw [hβ2, neg_neg] at h7
    exact hd (prime_eq_of_mem P hp D.host.hyp.2.1 hP h7)

theorem exists_places_of_cls (T : Type) (L : LevCh D T) (μ0 : T) (hL : L.Is μ0)
    (hg : ∀ k, D.host.cls (D.host.g k) = .splitK) (hde : D.host.cls D.host.pde = .splitK)
    (hde' : D.host.cls D.host.pde' = .splitK) (hq : ∀ k, q0 D ≠ D.host.g k)
    (hQ : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : ∃ P : Places L, P.v0 ∉ S1 D := by
  classical
  choose 𝔭 h𝔭 using exists_primes L hL
  obtain ⟨hq0, hq1, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hq2 : q0 D % LevelStarExponents.condE D = 1 := by
    have h1 : 1 < LevelStarExponents.condE D := by
      have := D.host.qd_big
      have hA : 0 < D.host.QS := D.host.QS_pos
      have hq' : 2 ≤ D.host.q := by omega
      have hd' : 1 ≤ D.host.d := by omega
      show 1 < D.host.QS * D.host.q * D.host.d
      calc 1 < 1 * 2 * 1 := by norm_num
        _ ≤ D.host.QS * D.host.q * D.host.d := Nat.mul_le_mul (Nat.mul_le_mul hA hq') hd'
    rw [← Nat.mod_mod_of_dvd _ (dvd_mul_left _ (Formalism.MainNotions.rPrAv D)), hq1, Nat.mod_eq_of_lt h1]
  have hq3 : D.host.cls (q0 D) = .splitK := GlobalTheory.Mem.cls_eq_splitK_of_cond D.host hq2
  obtain ⟨v0, hv0⟩ := exists_place D.host.F hq0
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ w : HeightOneSpectrum (𝓞 D.host.E), ∀ p : ℕ, p.Prime →
      (p : 𝓞 D.host.F) ∈ v.asIdeal → w.under (𝓞 D.host.F) = v ∧ w.under (𝓞 D.host.K) = 𝔭 p := by
    intro v
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal
    · obtain ⟨p, hp, hv⟩ := h
      obtain ⟨w, hw⟩ := exists_over_both hp v hv (𝔭 p) (h𝔭 p hp).1
      exact ⟨w, fun p' hp' hv' => prime_eq_of_mem v hp hp' hv hv' ▸ hw⟩
    · obtain ⟨w, -⟩ := exists_place D.host.E hq0
      exact ⟨w, fun p hp hv => absurd ⟨p, hp, hv⟩ h⟩
  choose w hw using hw
  have hS : ∀ v ∈ insert v0 (S1 D), ∃ p : ℕ, p.Prime ∧ D.host.cls p = .splitK ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact ⟨_, hq0, hq3, hv0⟩
    · rcases (S1_mem_OmF D).1 hv with h | h | h | h
      · exact ⟨_, D.host.g_prime 0, hg 0, h⟩
      · exact ⟨_, D.host.g_prime 1, hg 1, h⟩
      · exact ⟨_, D.host.pde_prime, hde, h⟩
      · exact ⟨_, D.host.pde'_prime, hde', h⟩
  have hde2 : ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → p.Prime ∧ D.host.cls p = .splitK := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, hde⟩
    · exact ⟨D.host.pde'_prime, hde'⟩
  refine ⟨⟨v0, hv0, w, fun v hv => ?_, fun v hv => ?_, fun v k hv => ?_, fun p hp => ⟨𝔭 p, fun v hv => ?_⟩,
    fun t P hP hS1 => ?_, fun t P hP h => ?_⟩, fun h => ?_⟩
  · obtain ⟨p, hp, -, h⟩ := hS v (by convert hv)
    exact (hw v p hp h).1
  · obtain ⟨p, hp, hc, h⟩ := hS v (by convert hv)
    refine GlobalTheory.MovedIdem.exists_isIdemAt (w v) fun e => under_conjugatePrime_ne_of_class hp hc (w v)
      ((natCast_mem_under (M := D.host.F) (w v) p).1 (by rw [(hw v p hp h).1]; exact h)) ?_
    rw [show conjPrime₂ (w v) = w v from HeightOneSpectrum.ext ((conjIdeal_asIdeal (w v)).symm.trans e)]
  · exact (hL.Pg _).2 ⟨k, (hw v _ (D.host.g_prime k) hv).2.trans ((h𝔭 _ (D.host.g_prime k)).2.1 k rfl)⟩
  · exact (hw v p (hde2 p hp).1 hv).2
  · obtain ⟨q, hq', hqP, hne⟩ := exists_prime_mem (hL.Q_pl t) hP
    have hqv := (natCast_mem_under (M := D.host.F) P q).2 hqP
    have h1 : q = D.host.pde ∨ q = D.host.pde' := by
      rcases (S1_mem_OmF D).1 hS1 with h | h | h | h
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 0) hqv h) (hne 0)
      · exact absurd (prime_eq_of_mem _ hq' (D.host.g_prime 1) hqv h) (hne 1)
      · exact Or.inl (prime_eq_of_mem _ hq' D.host.pde_prime hqv h)
      · exact Or.inr (prime_eq_of_mem _ hq' D.host.pde'_prime hqv h)
    obtain ⟨h2, h3⟩ := hw _ q hq' hqv
    rcases eq_or_eq_conjP h2 with h | h
    · exact h.symm
    · exfalso
      apply under_conjugatePrime_ne_of_class hq' (hde2 q h1).2 P hqP
      rw [← h, h3, (h𝔭 q hq').2.2 h1 t P hP hqP]
  · exact hQ t P hP ((natCast_mem_under (M := D.host.F) P _).1 (h ▸ hv0))
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact hq 0 (prime_eq_of_mem _ hq0 (D.host.g_prime 0) hv0 h)
    · exact hq 1 (prime_eq_of_mem _ hq0 (D.host.g_prime 1) hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).1 (prime_eq_of_mem _ hq0 D.host.pde_prime hv0 h)
    · exact (leastSplitAuxiliaryPrime_ne_typePrimes D).2 (prime_eq_of_mem _ hq0 D.host.pde'_prime hv0 h)

theorem leastSplitAuxiliaryPrime_ne_typePrime_of_sizes {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := hs.2.2.2.2.2.2.2.2.1
  have h2 := (hs.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k k).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  rw [← e] at h2
  nlinarith

end GlobalTheory.RowEx.GridExPf

namespace GlobalTheory.RowEx

open GlobalTheory.RowEx.GridExPf

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThThGAct
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LiftGroupEquiv.th_thG_act : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ t (g : G) (x : (A.fam.R t).S.Forms), R.Th t (R.jX t ((A.fam.R t).r g x)) = R.gE g (R.Th t (R.jX t x))) ∧ ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), R.thG i t (R.jV i t ((A.fam.L i t).r g x)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t x)) := by
  intro hP D G _ _ Pl0 T0 A Ks _ _ _ R F hC
  have hRr : R.grp_red_R := hC.grp.red_R
  have hRl : R.grp_red_L := hC.grp.red_L
  have hMx : R.models_jX := hC.models.jX
  have hMv : R.models_jV := hC.models.jV
  refine ⟨fun t g x => ?_, fun i t g x => ?_⟩
  · have H1 := @GlobalTheory.FormAction.act_eq_translate D G _ _ Pl0 T0 A Ks _ _ _ R hRr hMx t g x
    exact H1.elim fun κ hh =>
      @GlobalTheory.T.chainCompositeLift_intertwines_finiteGroupActions D G _ _ Pl0 T0 A Ks _ _ _ R F hC.lev hC.grp hC.fam hC.models hC.chain
        (fun t j _ => GlobalTheory.MultFinite.schurMult hP _ _) t g κ hh.1 _ _ hh.2
  · have H2 := @GlobalTheory.RationalFormsAction.act_eq_translate_lift_V D G _ _ Pl0 T0 A Ks _ _ _ R hRl hMv i t g x
    exact H2.elim fun κ hh => @GlobalTheory.T.thetaProjection_intertwines_levelLifts D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t g κ hh.1 _ _ hh.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowFock

theorem isThetaFunO_fock_right : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W _ ρ _ t i j hi hj e _ φ f hf Q
  have h₀ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (vacOf ρ (.right i j)) :=
    (ρ.vX_is i j hi hj).2.theta
  have hfθ : IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) f :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf.2 h₀
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hfθ Q

end GlobalTheory.RowFock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_fock_vector_rightward_arrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} {W : G'.Weil}, W.Over R → ∀ (ρ : RealMatch W), RealMatch.Over R ρ → ∀ (t : T) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f → ∀ Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank, IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) (W.fock (.chi i j) f Q) := by
  first | exact @GlobalTheory.RowFock.isThetaFunO_fock_right | exact GlobalTheory.RowFock.isThetaFunO_fock_right | (intros; apply GlobalTheory.RowFock.isThetaFunO_fock_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem movedVec_theta_fockVac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  intro D T L sc G W U S t p hp d hd
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  exact GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2

end GlobalTheory.RowReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVector_definitePair_theta_fockVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  first | exact @GlobalTheory.RowReal.movedVec_theta_fockVac | exact GlobalTheory.RowReal.movedVec_theta_fockVac | (intros; apply GlobalTheory.RowReal.movedVec_theta_fockVac <;> assumption)
end
end
