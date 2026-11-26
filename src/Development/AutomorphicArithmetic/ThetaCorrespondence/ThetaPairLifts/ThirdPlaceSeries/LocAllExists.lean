module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAutSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExists
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExists
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
noncomputable section
namespace GlobalTheory.HeckeLocN
set_option synthInstance.maxHeartbeats 400000
section Psi
variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)
end Psi
set_option maxHeartbeats 2000000 in
theorem ndSpec_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  intro hArt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI _ _ hpd hCheb hOS hVal big
  obtain ⟨hO, hc⟩ := GlobalTheory.T.twistConductors_over_real_places_and_conj_stable D cf C tp hCS.off
  have hG := GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable D cf M C tp hMI hO
  have hX := GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer D
  have hR := GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators D M C tp.tup hStd hG hMI
  have hCm := GlobalTheory.T.liftedHeckeOperators_at_generators_commute D M C hR hStd hG hX
  choose F1 hF1 using GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues D M C hR (plEmb A.pl) hCm
  choose F2 hF2 hF2' using GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers D A.pl big
  choose F3 hF3 using GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff D
  choose F4 hF4 using GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings D C Bs.twF low (plEmb A.pl) Bs.tw hCS.choice
  obtain ⟨X, hXE, h1, h2, h3, h4⟩ : ∃ X : CoefIn D.what₂, X.E = plEmb A.pl ∧ (∀ j w, (F1 j w).1 ≤ (X.Kx j w).1) ∧
      (∀ j w, (F2 w).1 ≤ (X.Kx j w).1) ∧ (∀ j w, (F3 w).1 ≤ (X.Kx j w).1) ∧ ∀ j w, (F4 w).1 ≤ (X.Kx j w).1 :=
    ⟨coefIn A.pl (fun j w => feSup (feSup (F1 j w) (F2 w)) (feSup (F3 w) (F4 w)))
      (fun j w x => (le_sup_of_le_left le_sup_right : (F2 w).1 ≤ ((F1 j w).1 ⊔ (F2 w).1) ⊔ ((F3 w).1 ⊔ (F4 w).1)) (hF2 w x)), rfl,
      fun _ _ => le_sup_of_le_left le_sup_left, fun _ _ => le_sup_of_le_left le_sup_right,
      fun _ _ => le_sup_of_le_right le_sup_left, fun _ _ => le_sup_of_le_right le_sup_right⟩
  have hS : SplitK (mt0 M) C.Q hR X := fun j w => hF1 j w X hXE (h1 j w)
  choose twC hTwA hTwR hTwE using fun j w => hF4 w X j hXE (h4 j w)
  obtain ⟨ψ0, -, hψ0, -⟩ := hCS.nct.psi_eq
  have hP := GlobalTheory.T.twistCharacterValues_integral_units_at_place D C X ψ0 hψ0
  have hs := GlobalTheory.T.heckeStandardFacts_on_localisation_base D M C hR X hS hStd hG hX hCm
  have hd := GlobalTheory.T.finiteDimensional_localisation_space_all (base M C hR X hS)
  have hML := LatticeFinitenessFree.mtLoc_holds (partCompl_of hs hd)
  have hAct := GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice _ hs hd hML (GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places D M C hR X hS tp.tup hMI hX)
    (GlobalTheory.T.heckeOperators_on_localisation_space_semisimple D M C hR X hS hStd GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace hG hX)
  have hAHK := GlobalTheory.T.heckeRing_acts_on_lattice_as_operators _ hs hd hML hAct
  have hI := osInt D (base M C hR X hS)
  have hGal := fun w (hw : TwistedAt D w) => GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l D cf C tp w hArt hCheb hCS.psi hw (hVal w hw) (hCS.adm w hw)
  have htw : ∀ w v, v ∈ C.Q w → TwistedAt D w := fun w v hv => by
    by_contra hw
    rw [hCS.off w hw] at hv
    exact absurd hv (Finset.notMem_empty v)
  have hQl : ∀ w v, v ∈ C.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun w v hv =>
    C.twI_l w ▸ ((hCS.adm w (htw w v hv)).1 v hv).2
  have hQS : ∀ w v, v ∈ C.Q w → v ∉ exceptionalPlaces D.host (D.what₂.places.resChar w) := fun w v hv h => by
    have ha := (hCS.adm w (htw w v hv)).2.1 v hv
    rcases h.1 with h | h | h
    · exact ha.2 0 h
    · exact ha.2 1 h
    · refine ha.1 (Finset.mem_coe.1 ?_)
      rw [D.ntw.pD_eq, C.twI_l]
      exact h
  have hSs : ∀ l v, v ∈ exceptionalPlaces D.host l → IsSplitPl D.host v := fun l v h => by
    rcases h.1 with h | h | h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 0 v h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 1 v h
    · split_ifs at h
      · exact hpd v (Or.inr h)
      · exact hpd v (Or.inl h)
  have hRP := fun j w (hw : TwistedAt D w) => psN_ram hψ0 hP j w (hGal w hw).1
  refine ⟨_, _, nonempty_spec (base M C hR X hS) C hs hd hML (LatticeFinitenessFree.mtSub_free _) (LatticeFinitenessFree.mtSub_finite _) (GlobalTheory.T.localisation_heckeRing_isLocalRing _ hs hd) hAct
    (GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point _ hs hd hML hAct hAHK) (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i))
    (GlobalTheory.T.localisation_galoisCharacter_continuous D M C hR X hS twC ψ0 hP hTwA (psN_open hψ0 hP))
    (fun i v hv => hv.elim (fun h => hSs _ v ((Set.Finite.mem_toFinset _).1 h))
      (fun h => ((hCS.adm _ (htw _ v h)).1 v h).1))
    (fun i => Finset.disjoint_left.2 fun v h h' => hQS _ v h' ((Set.Finite.mem_toFinset _).1 h)) hQl ?_ hI
    (GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing D _ hI hOS) (fun a => hTwE _ _ a.2.2.2.2.2) (fun a => psN_ord hψ0 hP _ _) (fun a => psN_open hψ0 hP _ _)
    (fun a => psN_anti hψ0 hP _ _) (fun a => hRP _ _ a.2.2.2.2.2)
    (fun a v hv B hB σ hσ => (psN_eq_one hψ0 hP _ _ σ).2 ((hGal _ a.2.2.2.2.2).2 v hv B hB σ hσ))
    A.pl M big (fun j w h1 h2 v k s ϖ hg hcj hu x => hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x) hO hc
    (fun _ => rfl) (iqC X) (fun j w z => (iqC_alg X j w _).trans rfl) ?_ ?_ hAHK (plGwDisj D) ?_ (fun a => hTwA _ _)
    (fun a => hTwR _ _) (fun j w => hF3 w X j (h3 j w))⟩
  · intro i v hv
    have hw : TwistedAt D (wOf _ i) := i.2.2.2.2.2
    obtain ⟨σ, hσ, hne⟩ := (hRP (jOf _ i) _ hw v _ (D.nd.plOm.2 v)).2 hv
    have ha := hCS.adm _ hw
    have h1 := D.ntw.twistCharacterFamily_unramified (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) v (ha.1 v hv).2 (ha.2.1 v hv).2 (ha.2.1 v hv).1 _
      (D.nd.plOm.2 v) σ hσ
    refine ⟨σ, hσ, fun e => hne ?_⟩
    have e' : Units.map (twC (jOf _ i) (wOf _ i)).toMonoidHom (D.ntw.chi1 (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) σ) *
        psN X ψ0 hP (jOf _ i) (wOf _ i) σ = 1 := e
    rwa [h1, map_one, one_mul] at e'
  · intro j w x
    change A.pl.ι w (iqC X j w (ecC X j w x)) = _
    rw [iqC_ec, hXE]
    exact (A.pl.ι w).apply_symm_apply _
  · intro j w z hz
    obtain ⟨x, hx⟩ := iqC_surj X j w _ (h2 j w (hF2' w z hz))
    exact ⟨x, (congrArg (A.pl.ι w) hx).trans ((A.pl.ι w).apply_symm_apply z)⟩
  · intro a g y hy
    obtain rfl := (C.embW _).injective (hy.trans (hψ0 _ g).symm)
    exact (psN_spec hP _ _ g).symm
end GlobalTheory.HeckeLocN
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExistsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_eigen_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  first | exact @_root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | exact _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt | (intros; apply _root_.GlobalTheory.HeckeLocN.ndSpec_exists_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGen
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Chi1LocIsGal
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiLocGal
section General
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end General
section Values
variable {E : Type} [Field E] [NumberField E]
end Values
theorem chi1_loc_isGal_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), IsGlobalArtin art → ∀ (i : X.nd.Loc) (j' : Fin D.R.m), j'.1 + 1 = X.nd.j i → ∃ n, GlobalTheory.GalChar.IsGal art (Sp.iq i) (Y.naut.iotaQC i) (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ he _ _ big X T Sp Y Cb hAu art ha i j' hj
  letI := D.ntw.crO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDomain (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDVR (T.twOf i)
  letI := D.ntw.topO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_topologicalRing (T.twOf i)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' he j'
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 (GlobalTheory.GalChar.del_alg C' (X.nd.l i))⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n := hn
  have hj1 := X.nd.j_range i
  obtain ⟨B1, hB1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) hj1.1 hj1.2
  have hχ : ∀ x, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ x = (cf.mu0 j' * cf.delAt (X.nd.l i) * cf.eta⁻¹).1 x := by
    intro x
    have h1 := Bs.ringSpec_normalisedCharacter_eq j' x
    have h2 := Bs.del_eq (T.twOf i) x
    have h3 := Bs.eta_eq x
    rw [hj] at h1
    have h4 : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
    rw [h4] at h2
    change (Bs.chiD.mu0 (X.nd.j i)).χ x * (Bs.chiD.del (T.twOf i)).χ x *
      (Bs.chiD.etaT.χ x)⁻¹ = (cf.mu0 j').1 x * (cf.delAt (X.nd.l i)).1 x * (cf.eta.1 x)⁻¹
    rw [h1, h2, h3]
  set χb := GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r with hχb
  have key : ∀ P ∉ B1, ∃ x : ↥D.LL0, Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ((χb.val P : ℂˣ) : ℂ)⁻¹ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        X.nd.embK i (x : D.what₂.LL) = algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
          (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ))) := by
    intro P hP
    obtain ⟨α, hα, x, hx, hσ⟩ := hB1 P hP
    refine ⟨x, ?_, fun σ hσ' => T.twO_emb i x _ (hσ σ hσ')⟩
    rw [val_block (val_of_at hχ hα) hx, inv_inv]
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hAlm : GlobalTheory.GalChar.AlmostIn (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) χb := by
    filter_upwards [hev] with P hP
    obtain ⟨x, hx, -⟩ := key P hP
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩
  have hf : ∀ x : ↥D.LL0, Y.naut.iotaQC i (Sp.iq i (((X.nd.embK i).comp D.LL0.val.toRingHom) x)) =
      Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x := by
    intro x
    rw [← hAu.iotaQ i]
    exact Y.iota_LL i x
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  obtain ⟨r0, hr0⟩ := GlobalTheory.GalChar.exists_isGal hO hκ ha hn' hf hAlm
  haveI : T2Space (X.nd.O i) := (GlobalTheory.GalChar.isEmbedding_toQ hO hκ).t2Space
  have hlO := (GlobalTheory.CoefEmbed.embedding_closed_integral (X.nd.l i) (X.nd.O i) hO (Sp.iq i) hκ).2.2.2
  have hl0 : ((X.nd.l i : ℕ) : D.ntw.O0 (T.twOf i)) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap (D.ntw.O0 (T.twOf i)) (FractionRing (D.ntw.O0 (T.twOf i)))) h
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 (T.twOf i))] at h'
    have h'' := (D.ntw.emb0 (T.twOf i)).injective (h'.trans (map_zero _).symm)
    exact (Fact.out : (X.nd.l i).Prime).ne_zero (by exact_mod_cast h'')
  have hc1 : Continuous ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.continuous_ringHom (D.ntw.twistBaseCoefficientRing_isAdic (T.twOf i)) hO hl0 hlO (T.twist₂ i)).comp
      (D.ntw.twistCharacterFamily_continuous (T.twOf i) (X.nd.j i) (T.twSide i)))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero
  have heq : r0 = (Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i)) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (GlobalTheory.GalChar.continuous_units r0 hr0.2.1) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne]
      with v hv hu hl A' hA' σ hσ
    refine frob_any (D.nd.plOm.2 v) hA' (fun σ' hσ' => ?_) hσ
    obtain ⟨x, hx1, hx2⟩ := key v hv
    apply Units.ext
    apply GlobalTheory.GalChar.toQ_injective (Sp.iq i)
    apply (Y.naut.iotaQC i).injective
    rw [hr0.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ', ← hx1]
    show _ = Y.naut.iotaQC i (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ')))))
    rw [← hx2 σ' hσ']
    exact (hf x).symm
  exact ⟨n, heq ▸ hr0⟩
end GlobalTheory.ChiLocGal
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGen
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiTame
section General
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end General
theorem chi_one_tameGen_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  intro hP D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb hAu i k v hl
  obtain ⟨art, ha⟩ := hP D.host.E D.nd.Om
  have hj := X.nd.j_range i
  let j' : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  obtain ⟨n, hG⟩ := _root_.GlobalTheory.ChiLocGal.chi1_loc_isGal_alt D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb
    hAu art ha i j' (by simp only [j']; omega)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlp : (X.nd.l i).Prime := Fact.out
  have hgp := D.host.g_prime k
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  obtain ⟨hN, hg2, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ hgp (D.nd.g_split k) _ hwg
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
    GlobalTheory.GalChar.notMem_of_ne hgp hlp hl.symm hwg
  have hA := D.nd.plOm.2 (D.naut.plGw k v)
  obtain ⟨hp, -, hpg, -, hD⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec C' (l := X.nd.l i)
  have hdel : (cf.delAt (X.nd.l i)).UnrAt (D.naut.plGw k v) :=
    hD.unr _ (GlobalTheory.GalChar.notMem_of_ne hgp hp (hpg k).symm hwg)
  have hloc : ∀ x, IsUnitAt (D.naut.plGw k v) x →
      (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r).loc (D.naut.plGw k v) x =
        (cf.mu0 j').loc (D.naut.plGw k v) x := fun x hx => by
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hx]
    change (cf.mu0 j').loc _ x * (cf.delAt (X.nd.l i)).loc _ x = _
    rw [hdel x hx, mul_one]
  have hI := (hG.ine_pow_iff ha (Or.inl hwl) hA (D.host.g k - 1)).2 fun x hx => by
    rw [hloc x hx, ← hN]
    exact (GlobalTheory.Mem.WildChar.orders_on_units _ _ _).1 ((cf.isMu0 j').tame _) x hx
  haveI := D.host.isCMField_hostE
  obtain ⟨u, hu, hrep, hunit, σ, eσ, hσ⟩ := exists_tameRep hP ha hA hgp
    ((GlobalTheory.ChiLocGal.normV_eq_absNorm _).trans hN) hwg hg2 (fun a ha' x hx => isUnitAt_nat hwg ha' hx)
    (D.ntypes.tg_gen k v) _ (hG.cont (X.nd.O_adic i) (Sp.iq_alg i)) fun σ hσ => by
      rw [← map_pow, GlobalTheory.GalChar.inQ_eq_one, map_pow, hI σ hσ]
  obtain ⟨c, hc, hcv⟩ := A.chiT k v j' u hu hrep
  refine ⟨c, hc, ?_⟩
  have hvS : D.naut.plGw k v ∈ X.nd.S i := by
    rw [X.nd.S_def i]
    refine ⟨?_, hwl⟩
    fin_cases k
    · exact Or.inl hwg
    · exact Or.inr (Or.inl hwg)
  have hvQ : D.naut.plGw k v ∉ X.nd.Q i := fun h => (Finset.disjoint_left.mp (X.nd.SQ_disj i) hvS) h
  have hψ : T.psiL i (D.ntypes.tg k v) = 1 := by
    by_contra hne
    exact hvQ ((T.psiL_ram i _ _ hA).mp ⟨_, D.ntypes.tg_mem k v, hne⟩)
  have e1 := hG.loc (Or.inl hwl) eσ
  rw [GlobalTheory.GalChar.inQ_inj _ hσ, hloc _ hunit] at e1
  have e2 : X.nd.chi i 1 (D.ntypes.tg k v) = ((Units.map (T.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) (D.ntypes.tg k v) := by
    refine (DFunLike.congr_fun (T.chi_tw i) _).trans ?_
    exact (congrArg (_ * ·) hψ).trans (mul_one _)
  rw [← hcv, e2]
  refine Eq.trans ?_ e1
  unfold iotaO
  rw [hAu.iotaQ i]
  rfl
end GlobalTheory.ChiTame
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneTameGenStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_character_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  first | exact @_root_.GlobalTheory.ChiTame.chi_one_tameGen_alt | exact _root_.GlobalTheory.ChiTame.chi_one_tameGen_alt | (intros; apply _root_.GlobalTheory.ChiTame.chi_one_tameGen_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVISupIndep
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.MtIndep
section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end rep
section loc
variable {D : D7}
def phiSubmodule {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D)
    (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  ⨆ (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W)) (h : NG.IsIrrRep (M μ j h1 h2).wt.ρ S')
    (_ : Good X Y σ' c j (A.au.cls j h1 h2 { (M μ j h1 h2).wt with S := S', irrS := h })),
    (NG.isoTyp (M μ j h1 h2).wt.ρ S').comap (M μ j h1 h2).real
theorem phi_submodule_heq {cf : CharFrame D} {jE : D.host.E →+* Qb} (X : LocNd (lay0 D)) (Y : LocAut X) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE)
    (M : MtFam D) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h1' : 1 ≤ j') (h2' : j' ≤ D.R.m) (hμ : μ = μ') (hj : j = j') :
    HEq (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ j h1 h2) (_root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' c μ' j' h1' h2') := by
  subst hμ hj; rfl
end loc
end GlobalTheory.HeightCounting.MtIndep
namespace GlobalTheory.HeightCounting.MtIndep
section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}
theorem supr_type_v_eq_phi_submodule (hS : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup iq Y Cb) (σ' : D.ntypes.Par) (i : X.nd.Loc) :
    (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) =
    _root_.GlobalTheory.HeightCounting.MtIndep.phiSubmodule X Y A M σ' (Y.muC i) (X.nd.mu i) (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 := by
  have hc : ∀ P, (∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)) ↔
      Good X Y σ' (Y.muC i) (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
        { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P }) := by
    intro P
    have hl : Y.naut.locV i P = fun w => D.nbc.locAU (X.nd.j i) (Cb.embAV i P) w := funext (Cb.embAV_loc i P)
    have hs : Y.naut.satV i P = D.nbc.satAU (X.nd.j i) (Cb.embAV i P) := funext (Cb.embAV_sat i P)
    have hf : Y.naut.infWt i = D.nbc.infW (X.nd.j i) (D.nbc.wtAU (X.nd.j i) (Cb.embAV i P)) := Cb.embAV_inf i P
    rw [← hS.emb i P]
    unfold Good
    refine exists_congr fun Sig => and_congr_right fun _ => ?_
    unfold IsBCV BCd
    rw [hl, hs, hf]
    exact Iff.rfl
  apply le_antisymm
  · refine iSup₂_le fun P hP => ?_
    rw [hS.typeV i P]
    exact le_iSup_of_le (hS.S i P) (le_iSup_of_le (hS.irr i P) (le_iSup_of_le ((hc P).1 hP) le_rfl))
  · refine iSup_le fun S' => iSup_le fun hirr => iSup_le fun hg => ?_
    by_cases hb : (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real = ⊥
    · exact hb.le.trans bot_le
    · obtain ⟨P, hP⟩ := hS.surj i S' hirr hb
      have ht : Y.naut.typeV i P = (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real := by
        rw [hS.typeV i P, isoTyp_eq (hS.irr i P).1 hP]
      have hcl : A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := hS.S i P, irrS := hS.irr i P } =
          A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
            { (mlX M X i).wt with S := S', irrS := hirr } :=
        (A.au.iso _ _ _ _ _).2 ⟨⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩, hP⟩
      have hP' : P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)} :=
        (hc P).2 (hcl ▸ hg)
      exact le_iSup₂_of_le (f := fun P _ => Y.naut.typeV i P) P hP' ht.ge
end loc2
theorem typeV_iSup_indep_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i i' : X.nd.Loc) (σ' : D.ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big X T Sp Y Cb hS i i' σ' hmu hj
  rw [_root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i, _root_.GlobalTheory.HeightCounting.MtIndep.supr_type_v_eq_phi_submodule hS σ' i']
  have hc : Y.muC i = Y.muC i' := by
    obtain ⟨h1, h2⟩ := X.nd.j_range i
    have e := hS.muC i ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    have e' := hS.muC i' ⟨X.nd.j i - 1, by omega⟩ (by simp only; omega)
    rw [hmu] at e
    exact A.chr.e1.injective (Subtype.ext (e.trans e'.symm))
  rw [hc]
  exact _root_.GlobalTheory.HeightCounting.MtIndep.phi_submodule_heq X Y A M σ' _ _ _ _ _ hmu hj
end GlobalTheory.HeightCounting.MtIndep
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocBrOfAutSpec
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem locBr_of_autSpec_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExists
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 2000000 in
theorem locAll_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  intro hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi hO hBU big
  obtain ⟨X, T, ⟨Sp⟩⟩ := _root_.GlobalTheory.T.side_rational_eigen_data_alt hGAR GlobalTheory.HeckeStdFacts.heckeStdPlain D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hO hpsi big
  obtain ⟨Y, Cb, ⟨aut⟩⟩ := _root_.GlobalTheory.T.side_rational_level_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb hpsi big X T Sp
  obtain ⟨Br, -⟩ := _root_.GlobalTheory.HeightCounting.locBr_of_autSpec_alt D cf jE A M C tp.tup big X T Sp Y Cb aut
  have hchi := _root_.GlobalTheory.T.side_rational_character_data_alt hGAR D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  have hMt := _root_.GlobalTheory.HeightCounting.MtIndep.typeV_iSup_indep_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hexp hsplit hCheb big X T Sp Y Cb aut
  obtain ⟨Z, hbc, hrb, hmt, hss⟩ := locTy_exists D A.row A.pl X Y hBU hCheb aut.locW aut.iotaQC aut.kFbar Sp.heckeLoc_gamma_places hchi hMt
  exact ⟨{ X := X, T := T, Y := Y, C := Cb, Z := Z, B := Br, bc_tie := hbc, rbar_tie := hrb, mtpar_tie := hmt }, Sp, ⟨aut⟩, hss⟩
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocAllExistsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_rational_hecke_data_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → BlocksUnique D → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam) := by
  first | exact @_root_.GlobalTheory.HeightCounting.locAll_exists_alt | exact _root_.GlobalTheory.HeightCounting.locAll_exists_alt | (intros; apply _root_.GlobalTheory.HeightCounting.locAll_exists_alt <;> assumption)
end
end
