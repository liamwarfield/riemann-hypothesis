module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem galois_relation_away_from_l (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      UpperTheory.GalS.RelW N A (A.wdOf i r w) (A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, -⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w hw => ?_⟩
    rw [(htw a ρ2 χB c2 cB).2.1 w (Or.inl hw) (Or.inl hw), (htw a ρ1 χA c1 cA).2.1 w (Or.inl hw) (Or.inl hw),
      awayA w hw, awayB w hw]
    have k1 := ((away1 w hw).char hLP (A.lpTw (A.locG A.etaT w) (1 / 2)) (by rw [A.lpDim_tw, A.locG_dim])
      ((A.unr_tw _ _).2 (A.etaT_unr w))).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) - 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_int N A hLP] at k1
    convert k1 using 2
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w hw => ?_⟩
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), awayχ w hw]
    have k1 := (away1 w hw).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) + 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_twist N A hLP] at k1
    convert k1 using 2
    push_cast
    ring

end GlobalTheory.BCGal
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def DistinctAbsIrredConstituents (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂

def G3a (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ((N.l i ≠ H.g 0 ∧ N.l i ≠ H.g 1) ∨ GlobalTheory.CoefDuty.Live N i) → DistinctAbsIrredConstituents N i r

def ResidualCharpolyIndependent (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ (x y : N.X i) (g : G H.E N.Om),
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly

def G3 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop := G3a N i r ∧ ResidualCharpolyIndependent N i r

variable {N}
theorem g3 {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : At.G3 N i r) : G3 N i r := ⟨fun _ => h.1, h.2⟩
theorem g3' {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : G3 N i r) : G3 N i r := h
end

def DeRhamJumpsDistinctCondition (D : D7) : Prop :=
  (∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x,
      D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀) ∧
  ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r

end UpperTheory.GalS
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleThreePrime Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TypeLeaf (labSig FullLab)

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LabTameS : Prop :=
  (∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree = A.lpDim a →
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), σ ∈ wildSet N (N.plOm.1 (A.plGw k v)) →
      A.inePol a σ = (X - 1) ^ A.lpDim a) ∧
  ∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree = A.lpDim a →
    Squarefree (A.items₂ k (A.plGw k v) a) → 16 * A.lpDim a ^ 2 < H.g k → Nc N A a
end

def FullBase (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree = D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def FullLabS (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  FullBase D Sig ∧ ∀ (k : Fin 2) (v : D.nd.PlG k), Nc D.nd D.naut (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

theorem fl0' {D : D7} {Sig : List (Formalism.BasicNotions.Part D.naut.CG)} (h : FullLabS D Sig) : FullBase D Sig := h.1
theorem fullLabS_of_fullLabS_trivial {D : D7} {Sig : List (Formalism.BasicNotions.Part D.naut.CG)} (h : FullLabS D Sig) : FullLabS D Sig := h

def ResidualTameEigenvalueCondition (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
        (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
          (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
        Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
              (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
            fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
        ∃ φ : G D.host.E D.nd.Om,
          redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k) ∧
      (∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
          (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
          (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
            (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
          Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
            ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
                (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
              fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
          D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
            ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂)

def AdmissibleResidualTameEigenvalues (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullBase D Sig →
    (∀ k v, Squarefree (labSig D Sig k v)) → IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ → ResidualTameEigenvalueCondition D i Sig ρ

theorem g3p {D : D7} (h : LabelDegreeHypotheses D) : AdmissibleResidualTameEigenvalues D := fun i Sig hx hf _ => h i Sig hx hf
theorem g3p' {D : D7} (h : AdmissibleResidualTameEigenvalues D) : AdmissibleResidualTameEigenvalues D := h

end UpperTheory.GalS
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.GalS

section
open Formalism.MainNotions.SumRepresentations Polynomial GlobalTheory.BaseChangeConj

theorem rep_conj : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, mapRep (iotaOQ D.nd D.naut i) (r x) g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i r hr x P Pa hP hB ρ hρc hρs hwd
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin

  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    have hS := hwS
    rw [D.nd.S_def] at hS
    have hS' := fun h => hS ⟨h, hwl⟩
    have hu : D.naut.unr (D.naut.locV i P w) := D.naut.locV_unr i P w hsp hwQ
      (Fin.forall_fin_two.2 ⟨fun h => hS' (Or.inl h), fun h => hS' (Or.inr (Or.inl h))⟩)
      fun h => hS' (Or.inr (Or.inr h))
    have hloc := hB.2.2.2.1 w hsp
    have hwd' := hwd w hwl
    rw [hloc] at hwd'
    replace hwd' := hwd'.eq_of_unr ((D.naut.unr_tw _ _).2 hu)
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by rw [hwd']; exact (D.naut.unr_tw _ _).2 hu
    have e1 := D.naut.wdOf_frob i ρ w hwl hρc hun B σ hB' hσ
    rw [hwd', ← D.naut.pt_loc i P x hP w hso] at e1
    have e2 := (hr x).2.2 w hso B σ hB' hσ
    apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) (r x) σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e1, e3, Matrix.charpoly_map, e2, Polynomial.map_map]
    rfl
  have hc2 : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    contQ_of_continuous D.nd D.naut i (r x) (hr x).1
  have hall := charpoly_eq_of_dense' ρ (mapRep (iotaOQ D.nd D.naut i) (r x)) hρc hc2 _ hdense hfrob
  have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) := by
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ (hr x).2.1
    have e : mapRep (iotaOQ D.nd D.naut i) (r x) =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) := by
      ext g a b
      rfl
    rw [e]
    exact h
  exact hBN _ _ ρ _ hρs hss hall

end

section
open Polynomial

theorem heckeQ : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) →
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  intro D i x P Pa hP hBC ρ hc hss hwd
  refine ⟨hc, hss, fun w hw B σ hB hσ => ?_⟩
  have hS := (D.nd.S_def i w).not.1 hw.2.2.1
  have hunr : D.naut.unr (D.naut.locV i P w) := by
    refine D.naut.locV_unr i P w hw.1 hw.2.2.2 (fun k hk => hS ⟨?_, hw.2.1⟩)
      (fun hk => hS ⟨Or.inr (Or.inr hk), hw.2.1⟩)
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hloc := hBC.2.2.2.1 w hw.1
  have hw' := (hwd w hw.2.1).eq_of_unr ((D.naut.unr_tw _ _).2 (by rw [hloc]; exact hunr))
  have hu : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hw', hloc]
    exact (D.naut.unr_tw _ _).2 hunr
  have e := D.naut.wdOf_frob i ρ w hw.2.1 hc hu B σ hB hσ
  rw [hw', hloc, ← D.naut.pt_loc i P x hP w hw] at e
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  rw [e, Polynomial.map_map]
  rfl

theorem splitBC_of_galIso : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GalIsoN N A i → GlobalTheory.RowTie.ChebSplit N → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A →
    GlobalTheory.RowTie.SplitBC N A i := by
  intro R H what₂ N A i hG hC hAN P P' hag Pa Pa' hB hB'
  obtain ⟨r, hrc, -, hr0⟩ := hG P Pa hB
  obtain ⟨r', hrc', -, hr0'⟩ := hG P' Pa' hB'
  have hr := fun w h1 (h2 : A.unr (isoLoc N A Pa w)) => (hr0 w h1).eq_of_unr ((A.unr_tw _ _).2 h2)
  have hr' := fun w h1 (h2 : A.unr (isoLoc N A Pa' w)) => (hr0' w h1).eq_of_unr ((A.unr_tw _ _).2 h2)
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (Fact.out : (N.l i).Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have hinj : Function.Injective (Polynomial.map (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have hgood : ∀ᶠ w in Filter.cofinite, (w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
      A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w) := by
    filter_upwards [hfin.eventually_cofinite_notMem, GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa,
      GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa', hag] with w h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  have hS := Filter.eventually_cofinite.1 hgood
  have hd := hC hS.toFinset
  have hu : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa w) → A.unr (A.wdOf i r w) := fun w h1 h2 => by
    rw [hr w h1 h2]; exact (A.unr_tw _ _).2 h2
  have hu' : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa' w) → A.unr (A.wdOf i r' w) := fun w h1 h2 => by
    rw [hr' w h1 h2]; exact (A.unr_tw _ _).2 h2
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G H.E N.Om) (Qbar (N.l i)) R.nV
    (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    (fun g => ((r' g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    _ hd hrc hrc' (by
      rintro g ⟨w, hw, hsp, B, hBw, hg⟩
      have hw' : ¬ ¬ ((w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
          A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w)) := by
        simpa using hw
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := not_not.1 hw'
      apply hinj
      have e : A.wdOf i r w = A.wdOf i r' w := by
        rw [hr w h1 h2, hr' w h1 h3, hB.2.2.2.1 w hsp, hB'.2.2.2.1 w hsp, h4 hsp]
      rw [A.wdOf_frob i r w h1 hrc (hu w h1 h2) B g hBw hg,
        A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) B g hBw hg, e])
  refine hAN Pa Pa' hB.1 hB'.1 ?_
  filter_upwards [hgood] with w hw
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := hw
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  have e1 := A.wdOf_frob i r w h1 hrc (hu w h1 h2) _ σ (N.plOm.2 w) hσ
  have e2 := A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) _ σ (N.plOm.2 w) hσ
  have hm : A.frobEig (A.wdOf i r w) = A.frobEig (A.wdOf i r' w) := by
    have e3 := congrArg Polynomial.roots (e1.symm.trans ((congrArg _ (key σ)).trans e2))
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
  have e4 : A.wdOf i r w = A.wdOf i r' w := by
    rw [A.unr_eq_lpUnr _ (hu w h1 h2), hm, ← A.unr_eq_lpUnr _ (hu' w h1 h3)]
  rw [hr w h1 h2, hr' w h1 h3] at e4
  have e5 := congrArg (fun a => A.lpTw a (-((1 - (R.nV : ℝ)) / 2))) e4
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using e5

end

end UpperTheory.GalS
end
