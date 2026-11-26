module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
namespace At
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section RepOps
variable {Γ : Type} [Group Γ] {k : Type} [CommRing k]
end RepOps
def provisionFortyOne (i : N.Loc) : Prop :=
  ((∃ rq : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, IsHeckeGaloisQ N A i x (rq x)) ∧
    ∃ r, GoodR N i r) ∧
  (∀ P P' : A.AV i, A.ptV i P ≠ none → A.ptV i P = A.ptV i P' →
    (∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ N.S i → w ∉ N.Q i →
      (IsSplitPl H w → A.locV i P w = A.locV i P' w) ∧
      (¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w))) ∧
  ∀ r, GoodR N i r → G1 N i r ∧ _root_.UpperTheory.GalS.G2a N A i r ∧ _root_.UpperTheory.GalS.G3 N i r ∧ G4 N i r
end At
open Formalism.BasicNotions
def adm2_alt (D : D7) : Prop := _root_.UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut
def adm7_alt (D : D7) : Prop := _root_.UpperTheory.GalN.AllCuspidalOpenBound D.nd D.naut
def provisionFortyOne (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne D.nd D.naut i
def CuspidalGaloisUnramified' (D : D7) : Prop := ∀ i, _root_.UpperTheory.GalS.UnusedSlot55 D.nd D.naut i
def provisionFirst (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D ∧ _root_.Formalism.MainNotions.SumRepresentations.CuspidalGaloisUnramified' D ∧ Conclusion42 D
def AdmAAlt (D : D7) : Prop := tie0 D ∧ hypO D ∧ adm1 D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D
def AdmAtAlt (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D ∧ _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
def AdmissibleDatum (D : D7) : Prop := _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D ∧ adm6 D ∧ adm8 D
end Formalism.MainNotions.SumRepresentations
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleParameterJ
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain
variable {D : D7}
section Sets
variable (D)
end Sets
section Emb
variable (D)
variable {D}
end Emb
section Stmt
variable (D)
variable {D} (L : SizeData₂ D)
end Stmt
section admitted
variable (D)
def DeRhamFamilyAwayAlt : Prop := ∀ i r, GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r
variable {D} (L : SizeData₂ D)
def AdmJAlt : Prop :=
  _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ CrysIffWD D.nd D.naut ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D ∧ AdmDict D ∧ AdmRead D ∧ AdmPar L
def JumpClosed : Prop := ∀ L : SizeData₂ D, _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → JumpConditions L
end admitted
end Formalism.MainNotions.AdmissibleParameterJ
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeStatement
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
def Adm3PVariant (D : D7) : Prop := SumRepresentations.tieLab D ∧ _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
def ThreePrimeTheoremStatement (D : D7) : Prop := _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D → TheoremThreePrime D
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeHolds
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem theorem_three_prime_holds_alt_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleThreePrime.ThreePrimeTheoremStatement D := by
  rintro ⟨hT, hG⟩ hBB i Sig ⟨x, hx⟩ hdz hgood
  have hcusp := cusp_of D hT i x Sig hx hgood
  refine ⟨hcusp, fun ρ hρ => ?_⟩
  have hG' := _root_.UpperTheory.GalS.g3p' hG i Sig ⟨x, hx⟩ hdz (fun k v => (hgood k).1.2.1 v) hcusp ρ hρ
  have hfact : ∀ j : Fin 2, Fact (D.host.g j).Prime := fun j => ⟨D.host.g_prime j⟩
  have hBB' : Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hBB
  have hne : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → D.nd.l i ≠ D.host.g k :=
    fun k hk h => hk (Or.inl h)
  have key : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn (redF D i ρ) ⊤ ∧
      (∀ (H : Subgroup (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) [H.Normal], Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) →
        Group.IsSolvable (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) → (∀ v, D.ntypes.tg k v ∈ H) →
        Formalism.CyclotomicNorms.IrredOn (redF D i ρ) H) := by
    intro k hk
    have hA := (hG' k (hne k hk)).1
    choose ι hι using hA
    choose φ hφ using fun v => (hι v).2.2
    have T := Formalism.CyclotomicNorms.irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
      (fun j v => D.naut.items₂ j (D.naut.plGw j v) (isoLoc D.nd D.naut Sig (D.naut.plGw j v)))
      D.nd.chiT hBB' (fun j => (hgood j).1) (D.nd.l i) k hk (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (redF D i ρ)
      (fun v => D.ntypes.tg k v) φ ι hφ (fun v => (hι v).1) (fun v => (hι v).2.1)
    exact ⟨T.1, T.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)
    · have h1 : D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := fun h1 => by
        have hm : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := ⟨h0, h1⟩
        rw [hBB'] at hm
        exact hm
      exact (key 1 h1).1
    · exact (key 0 h0).1
  · intro k hk Hs _ hopen hsolv hIne
    have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ Hs) := Subgroup.quotient_finite_of_isOpen Hs hopen
    exact (key k hk).2 Hs inferInstance hsolv
      (fun v => hIne _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))
  · intro k hk w hw hTG
    obtain ⟨v, j, ι, e₁, e₂, he₁, he₂, hinj, hcp, hchi⟩ := (hG' k hk).2 w hw hTG
    show ¬ (Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)))).IsRoot _
    rw [hcp, hchi]
    exact not_root_of hk (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
      (D.nd.chiT k) (hgood k).1 (hgood k).2 v j ι hinj e₁ e₂ he₁ he₂
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem residual_irreducible_of_theorem_three_prime_alt (D : D7) (h : _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D) (hAN : SumRepresentations.adm5 D) (hBN : LitBNIrr (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))
    (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) : ResidualIrreducibleRankR D :=
  residual_irreducible_of_theorem D (_root_.Formalism.MainNotions.AdmissibleThreePrime.theorem_three_prime_holds_alt_alt D h) hAN hBN hrho hdz
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end
