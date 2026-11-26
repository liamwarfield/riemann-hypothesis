module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StmtOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerHyperplaneAveragesVanish
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

variable {D : D7}

theorem psi_ne_zero' (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem heisO_injective (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {f g : WO S T → ℂ}
    (h : heisO ψ S T w f = heisO ψ S T w g) : f = g := by
  funext x
  have := congrFun h (x - w)
  simp only [heisO, sub_add_cancel] at this
  exact mul_left_cancel₀ (psi_ne_zero' ψ _) this

theorem heisO_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := by
  funext x
  simp [heisO]

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ)
    (X : WO S T → ℂ) : comb ψ S T c X = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u X) c := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem comb_sum_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ι : Type} (s : Finset ι) (r : ι → WO S T)
    (z : ι → ℂ) (X : WO S T → ℂ) :
    comb ψ S T (∑ i ∈ s, Finsupp.single (r i) (z i)) X = ∑ i ∈ s, z i • heisO ψ S T (r i) X := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_eq_linearCombination, map_sum]
  simp only [Finsupp.linearCombination_single]

theorem comb_fun_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    comb ψ S T c (0 : WO S T → ℂ) = 0 := by
  unfold comb Finsupp.sum
  exact Finset.sum_eq_zero fun u _ => by
    show c u • heisO ψ S T u 0 = 0
    rw [heisO_fun_zero, smul_zero]

theorem relOff_factor {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Sb : Finset (FinPl D)} {p f : WO S T → ℂ}
    (hR : RelOff ψ S T Sb p f) (w : WO S T) (s : Finset (WO S T)) (a e : WO S T → ℂ) (r : WO S T → WO S T)
    (hr : ∀ u ∈ s, OffPl Sb (r u))
    (hp : ∀ u ∈ s, heisO ψ S T u p = e u • heisO ψ S T w (heisO ψ S T (r u) p))
    (hf : ∀ u ∈ s, heisO ψ S T u f = e u • heisO ψ S T w (heisO ψ S T (r u) f))
    (h0 : ∑ u ∈ s, a u • heisO ψ S T u p = 0) : ∑ u ∈ s, a u • heisO ψ S T u f = 0 := by
  classical
  set c' : WO S T →₀ ℂ := ∑ u ∈ s, Finsupp.single (r u) (a u * e u) with hc'
  have key : ∀ X : WO S T → ℂ, (∀ u ∈ s, heisO ψ S T u X = e u • heisO ψ S T w (heisO ψ S T (r u) X)) →
      ∑ u ∈ s, a u • heisO ψ S T u X = heisO ψ S T w (comb ψ S T c' X) := by
    intro X hX
    rw [hc', comb_sum_single, GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hX u hu, GlobalTheory.SplitScalar.heisO_smul, smul_smul]
  have hsupp : ∀ u ∈ c'.support, OffPl Sb u := by
    intro u hu
    rw [hc'] at hu
    obtain ⟨x, hx, hx'⟩ := Finsupp.mem_support_finsetSum u hu
    have heq : u = r x := Finset.mem_singleton.1 (Finsupp.support_single_subset hx')
    rw [heq]
    exact hr x hx
  have hp0 : comb ψ S T c' p = 0 := by
    apply heisO_injective ψ S T w
    rw [← key p hp, h0, heisO_fun_zero]
  rw [key f hf, hR c' hsupp hp0, heisO_fun_zero]

theorem offPl_zero (Sb : Finset (FinPl D)) (S T : HSp D) : OffPl Sb (0 : WO S T) :=
  ⟨by ext i j; simp, fun _ _ _ _ _ _ => by simp⟩

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (z : ℂ) (X : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u z) X = z • heisO ψ S T u X := by
  unfold comb
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem isHalf_one_sub {S T : HSp D} {b : AE D} (hb2 : b * b = b) (u : WO S T) : IsHalf (1 - b) (u - b • u) := by
  intro i j
  show (1 - b) * (u i j - b * u i j) = u i j - b * u i j
  rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, ← mul_assoc, hb2, sub_self, sub_zero]

theorem heisO_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {b : AE D} (hb2 : b * b = b) (hcb : cA D b = b)
    (u u0 : WO S T) (X : WO S T → ℂ) (z : ℂ) (hX : heisO ψ S T (b • u - b • u0) X = z • X) :
    heisO ψ S T u X = ((ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * z) •
      heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) X) := by
  have hab : cA D (1 - b) * b = 0 := by rw [map_sub, map_one, hcb, sub_mul, one_mul, hb2, sub_self]
  have horth0 : symplO S T (u - b • u) (b • u - b • u0) = 0 :=
    GlobalTheory.SplitScalar.symplO_eq_zero S T hab (isHalf_one_sub hb2 u)
      (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u) (GlobalTheory.SplitScalar.isHalf_smul hb2 u0))
  have h1 : heisO ψ S T (b • u0) (heisO ψ S T (u - b • u) (heisO ψ S T (b • u - b • u0) X)) =
      ψ (symplOH S T (b • u0) (u - b • u0)) • heisO ψ S T u X := by
    rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T horth0, GlobalTheory.SplitScalar.heisO_heisO, sub_add_sub_cancel,
      add_sub_cancel]
  rw [hX, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul] at h1
  rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (psi_ne_zero' ψ _), one_smul]

theorem offPl_sub_idem {S T : HSp D} {Sb : Finset (FinPl D)} {v : FinPl D} {u : WO S T}
    (hu : OffPl (dropPl Sb v) u) : OffPl Sb (u - idem D (.inl v) • u) := by
  classical
  obtain ⟨hidem, horth, -, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  refine ⟨Matrix.ext fun i j => ?_, fun q hq ε hε i j => ?_⟩
  · have h : infPart D (u i j) = 0 := congrFun (congrFun hu.1 i) j
    show infPart D (u i j - idem D (.inl v) * u i j) = 0
    rw [map_sub, map_mul, (hfin v).1, h, zero_mul, sub_zero]
  · rw [placeIdem_eq hε]
    show idem D (.inl q) * (u i j - idem D (.inl v) * u i j) = 0
    by_cases hqv : q = v
    · rw [hqv, mul_sub, ← mul_assoc, hidem, sub_self]
    · have hq' : q ∈ dropPl Sb v := by unfold dropPl; exact Finset.mem_erase.2 ⟨hqv, hq⟩
      have h1 := hu.2 q hq' _ ((hfin q).2.2) i j
      rw [placeIdem_eq ((hfin q).2.2)] at h1
      rw [mul_sub, h1, ← mul_assoc, horth (.inl q) (.inl v) (fun h => hqv (Sum.inl.inj h)), zero_mul, sub_zero]

theorem relOff_dropPl_of_coEig : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D))
    (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨
      ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) →
    RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  classical
  intro D ψ S T Sb v _ p f hH hR c hc hcp
  have hrest : ∀ u : WO S T, OffPl (dropPl Sb v) u → OffPl Sb (u - idem D (.inl v) • u) :=
    fun u hu => offPl_sub_idem hu
  obtain ⟨hidem, -, hconj, -, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  obtain ⟨b, hb⟩ : ∃ b, b = idem D (.inl v) := ⟨_, rfl⟩
  rw [← hb] at hH hrest
  have hb2 : b * b = b := by rw [hb]; exact hidem _
  have hcb : cA D b = b := by rw [hb]; exact hconj _
  by_cases hp0 : p = 0
  · have hf0 : f = 0 := by
      have h1 := hR (Finsupp.single 0 1) (fun u hu => by
        rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]; exact offPl_zero Sb S T) (by
        rw [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul, hp0])
      rwa [comb_single, GlobalTheory.SplitScalar.heisO_zero, one_smul] at h1
    rw [hf0, comb_fun_zero]

  have hcl : ∀ l : {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l}, ∃ z : ℂ, z ≠ 0 ∧
      heisO ψ S T l.1 p = z • p ∧ heisO ψ S T l.1 f = z • f := by
    rintro ⟨l, -, z, h1, h2⟩
    refine ⟨z, fun hz => hp0 ?_, h1, h2⟩
    apply heisO_injective ψ S T l
    rw [h1, hz, zero_smul, heisO_fun_zero]
  choose cl hcl0 hclp _ using hcl
  obtain ⟨χ, hχ⟩ : ∃ χ : WO S T → {l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ,
      ∀ u l, χ u l = ψ (symplO S T l.1 u) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (WO S T → ℂ) → ({l : WO S T // IsHalf b l ∧ CoEig ψ S T p f l} → ℂ) → (WO S T → ℂ),
      ∀ X k, V X k = ∑ u ∈ c.support with χ u = k, c u • heisO ψ S T u X := ⟨_, fun _ _ => rfl⟩
  have hcomb : ∀ X, ∑ k ∈ c.support.image χ, V X k = comb ψ S T c X := by
    intro X
    simp only [hV]
    exact Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem χ hu) _
  have heig : ∀ k ∈ c.support.image χ, ∀ l, GlobalTheory.SplitScalar.heisL ψ S T l.1 (V p k) = (k l * cl l) • V p k := by
    intro k _ l
    rw [GlobalTheory.SplitScalar.heisL_apply, hV, GlobalTheory.SplitScalar.heisO_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← (Finset.mem_filter.1 hu).2, hχ, GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hclp,
      GlobalTheory.SplitScalar.heisO_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hVp : ∀ k ∈ c.support.image χ, V p k = 0 :=
    GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero _ _ _ (fun l => GlobalTheory.SplitScalar.heisL ψ S T l.1)
      (fun k l => k l * cl l) (V p) _ heig
      (fun k1 _ k2 _ h => funext fun l => mul_right_cancel₀ (hcl0 l) (congrFun h l)) (by rw [hcomb]; exact hcp)
  have hVf : ∀ k ∈ c.support.image χ, V f k = 0 := by
    intro k hk
    obtain ⟨u0, _, hu0k⟩ := Finset.mem_image.1 hk
    have hCo : ∀ u ∈ c.support.filter (fun u => χ u = k), ∃ z : ℂ,
        heisO ψ S T (b • u - b • u0) p = z • p ∧ heisO ψ S T (b • u - b • u0) f = z • f := by
      intro u hu
      have hχu := (Finset.mem_filter.1 hu).2
      rcases hH _ (GlobalTheory.SplitScalar.isHalf_sub (GlobalTheory.SplitScalar.isHalf_smul hb2 u)
          (GlobalTheory.SplitScalar.isHalf_smul hb2 u0)) with h | ⟨l, hl, hlco, hne⟩
      · exact h
      · exfalso
        apply hne
        have e1 : ψ (symplO S T l u) = ψ (symplO S T l u0) := by
          have := congrFun (hχu.trans hu0k.symm) ⟨l, hl, hlco⟩
          rwa [hχ, hχ] at this
        have hbl : ∀ x, symplO S T l (b • x) = symplO S T l x := fun x => by
          conv_lhs => rw [← hcb]
          rw [← GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ l).1 hl]
        have e2 : symplO S T l (b • u - b • u0) + symplO S T l (b • u0) = symplO S T l (b • u) := by
          rw [← GlobalTheory.LatVac.symplO_add_right, sub_add_cancel]
        rw [hbl, hbl] at e2
        have e3 := congrArg ψ e2
        rw [AddChar.map_add_eq_mul, e1] at e3
        exact mul_right_cancel₀ (psi_ne_zero' ψ _) (e3.trans (one_mul _).symm)
    choose! eco hecp hecf using hCo
    have key := relOff_factor hR (b • u0) (c.support.filter fun u => χ u = k) c
      (fun u => (ψ (symplOH S T (b • u0) (u - b • u0)))⁻¹ * eco u) (fun u => u - b • u)
      (fun u hu => hrest u (hc u (Finset.mem_filter.1 hu).1))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 p _ (hecp u hu))
      (fun u hu => heisO_decomp ψ S T hb2 hcb u u0 f _ (hecf u hu))
      (by rw [← hV]; exact hVp k hk)
    rw [hV]
    exact key
  rw [← hcomb f]
  exact Finset.sum_eq_zero hVf

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRelationsExtendToPlaceCommonEigenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (p f : WO S T → ℂ), (∀ u, IsHalf (idem D (.inl v)) u → CoEig ψ S T p f u ∨ ∃ l, IsHalf (idem D (.inl v)) l ∧ CoEig ψ S T p f l ∧ ψ (symplO S T l u) ≠ 1) → RelOff ψ S T Sb p f → RelOff ψ S T (dropPl Sb v) p f := by
  first | exact @GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | exact GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig | (intros; apply GlobalTheory.DownLift.GenSplit.relOff_dropPl_of_coEig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunAtTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.SplitScalar

def trSet (O K : Type) [CommRing O] [Field K] [Algebra O K] (r t : ℕ) (ϖ : O) (g : GL (Fin r) K) :
    Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) :=
  {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) =
    (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)}

theorem exists_finset_trSet (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O)
    (hϖ : Irreducible ϖ) {ι : Type} (Φ : ι → Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) (N : ℕ)
    (hinv : ∀ k x (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ k (x + (ϖ ^ N • z).map (algebraMap O K)) = Φ k x)
    (hsupp : ∀ k x, Φ k x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K))
    (hΩ : ∀ k x, Φ k x ≠ 0 → ∃ g, x ∈ trSet O K r t ϖ g) :
    ∃ F : Finset (GL (Fin r) K), ∀ k x, Φ k x ≠ 0 → ∃! g, g ∈ F ∧ x ∈ trSet O K r t ϖ g := by
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N
  have huniq : ∀ g g' x, x ∈ trSet O K r t ϖ g → x ∈ trSet O K r t ϖ g' → trSet O K r t ϖ g = trSet O K r t ϖ g' := by
    rintro g g' x ⟨z, hz⟩ ⟨z', hz'⟩
    ext y; constructor
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw
  let rep : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → GL (Fin r) K := fun A =>
    if h : ∃ g, trSet O K r t ϖ g = A then h.choose else 1
  have hrep : ∀ g, trSet O K r t ϖ (rep (trSet O K r t ϖ g)) = trSet O K r t ϖ g := fun g => by
    have h : ∃ g', trSet O K r t ϖ g' = trSet O K r t ϖ g := ⟨g, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K := fun y =>
    if h : ∃ g, y ∈ trSet O K r t ϖ g then h.choose else 1
  refine ⟨T.image fun y => rep (trSet O K r t ϖ (gs y)), fun k x hx => ?_⟩
  obtain ⟨z, hz⟩ := hsupp k x hx
  obtain ⟨y, hyT, z', rfl⟩ := hT x z hz
  have hy : Φ k y ≠ 0 := by rwa [hinv] at hx
  have hy' : y ∈ trSet O K r t ϖ (gs y) := by
    have h := hΩ k y hy
    simp only [gs, dif_pos h]
    exact h.choose_spec
  obtain ⟨z₀, hz₀⟩ := hy'
  have hx' : y + (ϖ ^ N • z').map (algebraMap O K) ∈ trSet O K r t ϖ (gs y) :=
    GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ k _ (by rwa [hinv])) z'
  refine ⟨rep (trSet O K r t ϖ (gs y)), ⟨Finset.mem_image_of_mem _ hyT, by rwa [hrep]⟩, ?_⟩
  rintro g ⟨hg, hxg⟩
  obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hg
  rw [hrep] at hxg
  rw [huniq _ _ _ hxg hx']

variable {D : D7}

theorem suppAt_conj' {e : Formalism.L2.Theta.AE D} {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt (cA D e) V g := fun i j => by
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hg i j

theorem suppAt_one' (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

section Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem exists_scalar (hW : IsWeilDatumO ψ S T χS χT om) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S}
    {h : GA D T} (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = s * ℓ f := by
  have he' := isSplitIdem_conj he
  obtain ⟨r, hr, H⟩ := hW.om_split (cA D e) he' g h (suppAt_conj' hg) (suppAt_conj' hh) _ _
    (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 S g) (GlobalTheory.VecInv.isDetAt_detAt _ he'.1 T h)
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') (Circle.coe_ne_zero _), fun ℓ hℓ => H ℓ fun u hu => hℓ u ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA] at hu
  exact hu

theorem scalar_eq (hW : IsWeilDatumO ψ S T χS χT om) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f₀)
    {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S}
    {h : GA D T} (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h)
    (hL : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    {x y : (Formalism.L2.Theta.AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) :
    ∀ ℓ, InvForm ψ S T e ℓ → ∀ f, IsThetaFunO ψ S T f →
      ℓ (om (g, h) f) = ((splitFacO χS χT x y : Circle) : ℂ) * ℓ f := by
  obtain ⟨s, -, hs⟩ := exists_scalar hW he hg hh
  have he' := isSplitIdem_conj he
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  obtain ⟨ℓ₀, hℓ0, hℓ⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (ψ := ψ) he
    (fun y hy hn => exists_dual_half he hdual hstc hy hn) hne (hvac.2 e he) (hvac.2 _ he')
  have h1 := hs ℓ₀ hℓ f₀ h0
  rw [GlobalTheory.VecInv.om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hL x y hx hy f₀ h0 hvac, map_smul,
    smul_eq_mul] at h1
  rw [mul_right_cancel₀ hℓ0 h1]
  exact hs

end Gen

section Lev

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem mu_val_one (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {PP : Pl D.host.E} (hP : PP ∈ L.Pg) {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (x : (Formalism.L2.Theta.AE D)ˣ) (a : Formalism.L2.Theta.AE D)
    (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ)
    (hx : (x : Formalism.L2.Theta.AE D) = e * a + (1 - e))
    (ha : (a' : Formalism.IndefR.Lev.EAf D) = toEAf D a) (hu : ∀ PP, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) = (((L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) ∧ L.eta x = 1 := by
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hs : IsIdemSum e {PP} := ⟨⟨fun _ => e, fun P h => by rw [Finset.mem_singleton.1 h]; exact he, by simp⟩, he.1.2.1⟩
  have e1 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun P => (L.chi ((j : ℕ) + 1) P)⁻¹) (hL.mu0 j) hs
    (fun P h => ⟨(L.C.isMu0 j).tame P, by rw [Finset.mem_singleton.1 h]; exact hL.chi j PP hP⟩) x a a' u hx ha
    fun P _ => hu P
  have e2 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) (hL.xi t) hs
    (fun P h => ⟨hL.xi_tame t P, by rw [Finset.mem_singleton.1 h]; exact GlobalTheory.VecInv.isRes_one (h3 PP hP)⟩) x a a' u hx ha
    fun P _ => hu P
  have e3 := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D _ _ {PP} e (fun _ => 1) hL.eta hs
    (fun P _ => ⟨GlobalTheory.VecInv.tameAt_of_unrAt (L.C.isEta.unr P), GlobalTheory.VecInv.isRes_one (L.C.isEta.unr P)⟩) x a a' u hx ha
    fun P _ => hu P
  refine ⟨?_, Subtype.ext (e3.trans (Finset.prod_eq_one fun _ _ => rfl))⟩
  have e0 : ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) = (L.mu0 ((j : ℕ) + 1) x : Circle) * (L.xi t x : Circle) := rfl
  rw [e0, e1, e2, Finset.prod_singleton, Finset.prod_singleton]
  simp

theorem not_conj (hL : L.Is μ0) (t : T0) {PP PP' : Pl D.host.E} (hP : PP ∈ L.Pg) (hP' : PP' ∈ L.Pg ∨ PP' ∈ L.Q t) :
    ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (hL.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl L.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (hL.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

end Lev

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem actAt (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {PP : Pl D.host.E} (hP : PP ∈ R.Pg) {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (hφ : IsProjAt φ PP)
    (he : IsIdemOf φ e) (red : OI v →+* kP PP)
    (hred : ∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F,
        red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) : ActAt R i t PP φ e red := by
  intro h
  obtain ⟨κ, hs, hκ⟩ := GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Vc D i) v φ e he (frCo φ (R.βV i))
    (Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h)
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.splitPlaceUnitary_integralMatrix_keeps_lattice D (Vc D i) (R.βV i) (R.ΛV i) _ (hL.βV i).choose_spec PP v φ e hφ he red hred h κ hs hκ
  refine ⟨κ, hs, h1, h2, hκ, h3, fun PP' a b => h4 PP' b (not_conj hL t hP a), fun ℓ hℓ f hf => ?_⟩
  have hvac := (hv i t).1
  have hne : R.vacP i ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn⟩ := hvac.2.norm
    have n1 := hn p hp
    rw [h0] at n1
    simp [nrm2] at n1
  have hAt := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  rw [scalar_eq (hω i t) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) hvac.2.theta hne hvac.2.lat
    he.1 hs (suppAt_one' e _) (GlobalTheory.VecInv.mem_latO_iff (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 h2
      (by rw [map_one]; exact Subgroup.one_mem _)) (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ κ)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ 1) ℓ hℓ f hf]
  obtain ⟨a, ha, hr⟩ := GlobalTheory.VecInv.exists_det_int h2
  obtain ⟨m, n⟩ := mu_val_one hL t i hP hAt (GlobalTheory.VecInv.detAt e he.1.1 _ κ) _ a _
    (GlobalTheory.VecInv.isDetAt_detAt e he.1.1 _ κ) ha hr
  congr 1
  rw [splitFacO, map_one, map_one, mul_one]
  change ((((R.toLevCh.mu t ((i : ℕ) + 1) * R.eta⁻¹) _)⁻¹ : Circle) : ℂ) = _
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, n, inv_one, mul_one, Circle.coe_inv, m, h3, Units.val_inv_eq_inv_val,
    inv_inv]

section Fib

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {e : Formalism.L2.Theta.AE D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {c : WO S T' →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (comb ψ S T' c f) :=
  theta_sum _ _ f hf fun y hy => theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he (hc y hy)) hf)

theorem form_heis (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {ℓ : (WO S T' → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T' e ℓ)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) {x y : WO S T'} (hx : IsHalf (cA D e) x) (hy : IsHalf e y) :
    ℓ (heisO ψ S T' x (heisO ψ S T' y f)) = ψ (symplO S T' x y) * ℓ (heisO ψ S T' x f) := by
  rw [heisO_comm, map_smul, smul_eq_mul,
    hℓ y hy _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin (isSplitIdem_conj he) hx) hf)]

theorem form_comb (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {ℓ : (WO S T' → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T' e ℓ)
    {c : WO S T' →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y)
    {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) {x : WO S T'} (hx : IsHalf (cA D e) x) :
    ℓ (heisO ψ S T' x (comb ψ S T' c f)) = (c.sum fun y z => z * ψ (symplO S T' x y)) * ℓ (heisO ψ S T' x f) := by
  unfold comb Finsupp.sum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heisO_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [heisO_smul, map_smul, smul_eq_mul, form_heis hψ he hℓ hf hx (hc y hy), mul_assoc]

theorem eq_of_forms (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f)
    (hg : IsThetaFunO ψ S T' g) (h : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x →
      ℓ (heisO ψ S T' x f) = ℓ (heisO ψ S T' x g)) : f = g := by
  rw [← sub_eq_zero]
  refine GlobalTheory.ThetaStalk.eq_zero_of_invariant_forms D ψ hψ S T' _ (isSplitIdem_conj he) _ (theta_sub hf hg)
    fun ℓ hℓ x hx => ?_
  rw [GlobalTheory.DualPairCheck.cA_cA] at hℓ
  rw [← heisL_apply, map_sub, map_sub, heisL_apply, heisL_apply, h ℓ hℓ x hx, sub_self]

theorem shape_of_forms (hψ : IsStdChar D ψ (-1)) (he : IsSplitIdem D e) {A : Set (WO S T')}
    (hA : ∀ z ∈ A, IsHalf (cA D e) z) {x₀ : WO S T'} {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f)
    (h1 : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x → ∀ z ∈ A,
      ℓ (heisO ψ S T' (x + z) f) = ℓ (heisO ψ S T' x f))
    (h2 : ∀ ℓ, InvForm ψ S T' e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T' x f) ≠ 0 → x - x₀ ∈ A) :
    Shape ψ S T' e A x₀ f := by
  have he' := isSplitIdem_conj he
  refine ⟨fun z hz => eq_of_forms hψ he (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' (hA z hz)) hf) hf
    fun ℓ hℓ x hx => ?_, fun y hy hAy => eq_of_forms hψ he
      (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he hy) hf) (theta_smul _ hf) fun ℓ hℓ x hx => ?_⟩
  · rw [← heisO_add_of_orth ψ S T' (half_orth he' hx (hA z hz)), h1 ℓ hℓ x hx z hz]
  · rw [form_heis hψ he hℓ hf hx hy, heisO_smul, map_smul, smul_eq_mul]
    by_cases h0 : ℓ (heisO ψ S T' x f) = 0
    · rw [h0, mul_zero, mul_zero]
    · have := hAy _ (h2 ℓ hℓ x hx h0)
      rw [show symplO S T' x y = symplO S T' (x - x₀) y + symplO S T' x₀ y by rw [symplO_sub_left, sub_add_cancel],
        AddChar.map_add_eq_mul, this, one_mul]

theorem relOff_drop {v : FinPl D} (he : IsSplitIdem D e) (hev : e + cA D e = idem D (.inl v)) {A : Set (WO S T')}
    (hA : ∀ z ∈ A, IsHalf (cA D e) z)
    (hd : ∀ x, IsHalf (cA D e) x → x ∉ A → ∃ y, IsHalf e y ∧ (∀ z ∈ A, ψ (symplO S T' z y) = 1) ∧ ψ (symplO S T' x y) ≠ 1)
    {x₀ : WO S T'} {p f : WO S T' → ℂ} (hp : Shape ψ S T' e A x₀ p) (hf : Shape ψ S T' e A x₀ f)
    {Sb : Finset (FinPl D)} (hv : v ∈ Sb) (h : RelOff ψ S T' Sb p f) : RelOff ψ S T' (dropPl Sb v) p f := by
  have he' := isSplitIdem_conj he
  refine GlobalTheory.T.heisenbergRelations_extend_to_place_commonEigen D ψ S T' Sb v hv p f (fun u hu => ?_) h
  have h1 : ∀ y : WO S T', IsHalf e y → IsHalf (idem D (.inl v)) y := fun y hy i j => by
    rw [← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]
  have h2 : ∀ y : WO S T', IsHalf (cA D e) y → IsHalf (idem D (.inl v)) y := fun y hy i j => by
    rw [← hev, ← hy i j, ← mul_assoc, add_mul, he'.1, he.2.1, zero_add]
  have hu' : e • u + cA D e • u = u := by rw [← add_smul, hev]; exact (isHalf_iff _ _).1 hu
  have ha := isHalf_smul he.1 u
  have hb := isHalf_smul he'.1 u
  by_cases c1 : ∀ z ∈ A, ψ (symplO S T' z (e • u)) = 1
  · by_cases c2 : cA D e • u ∈ A
    · left
      have hne : ψ (symplOH S T' (e • u) (cA D e • u)) ≠ 0 := fun h0 => by
        have := AddChar.map_add_eq_mul ψ (symplOH S T' (e • u) (cA D e • u)) (-symplOH S T' (e • u) (cA D e • u))
        rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
        exact one_ne_zero this
      have key : ∀ q, Shape ψ S T' e A x₀ q → heisO ψ S T' u q =
          ((ψ (symplOH S T' (e • u) (cA D e • u)))⁻¹ * ψ (symplO S T' x₀ (e • u))) • q := fun q hq => by
        have := heisO_heisO ψ S T' (e • u) (cA D e • u) q
        rw [hu', hq.1 _ c2, hq.2 _ ha c1] at this
        rw [mul_smul, this, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact ⟨_, key p hp, key f hf⟩
    · obtain ⟨y, hy, hy1, hy2⟩ := hd _ hb c2
      refine Or.inr ⟨y, h1 y hy, ⟨_, hp.2 y hy hy1, hf.2 y hy hy1⟩, psi_skew_ne ?_⟩
      rwa [symplO_smul, GlobalTheory.DualPairCheck.cA_cA, (isHalf_iff _ _).1 hy] at hy2
  · push Not at c1
    obtain ⟨z, hz, hz1⟩ := c1
    refine Or.inr ⟨z, h2 z (hA z hz), ⟨1, by rw [hp.1 z hz, one_smul], by rw [hf.1 z hz, one_smul]⟩, ?_⟩
    rwa [← (isHalf_iff _ _).1 (hA z hz), symplO_smul, GlobalTheory.DualPairCheck.cA_cA]

theorem half_idem {v : FinPl D} (he : IsSplitIdem D e) (hev : e + cA D e = idem D (.inl v)) {y : WO S T'}
    (hy : IsHalf e y) : IsHalf (idem D (.inl v)) y := fun i j => by
  rw [← hev, ← hy i j, ← mul_assoc, add_mul, he.1, mul_comm (cA D e), he.2.1, add_zero]

theorem om_inv_om (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (h : GA D T') (f : WO S T' → ℂ) :
    om (1, h⁻¹) (om (1, h) f) = f := by
  have e1 : ((1, h⁻¹) : GA D S × GA D T') * (1, h) = 1 := by rw [Prod.mk_mul_mk, mul_one, inv_mul_cancel]; rfl
  rw [← Module.End.mul_apply, ← map_mul, e1, map_one, Module.End.one_apply]

end Fib

section Coord

variable {v : FinPl D} {ϖ : OI v}

theorem inPow_add {m n : Type} {N : ℕ} {X Z : Matrix m n (Fv D.host.F v)} (hX : InPow ϖ N X) (hZ : InPow ϖ N Z) :
    InPow ϖ N (X + Z) := fun a b => by
  obtain ⟨o, ho⟩ := hX a b
  obtain ⟨o', ho'⟩ := hZ a b
  exact ⟨o + o', by rw [Matrix.add_apply, ho, ho', mul_add, map_add (f := _)]⟩

theorem inPow_neg {m n : Type} {N : ℕ} {X : Matrix m n (Fv D.host.F v)} (hX : InPow ϖ N X) : InPow ϖ N (-X) := fun a b => by
  obtain ⟨o, ho⟩ := hX a b
  exact ⟨-o, by rw [Matrix.neg_apply, ho, mul_neg, map_neg]⟩

theorem inPow_submatrix {m n m' n' : Type} {N : ℕ} (X : Matrix m n (Fv D.host.F v)) (a : m' ≃ m) (b : n' ≃ n) :
    InPow ϖ N (X.submatrix a b) ↔ InPow ϖ N X :=
  ⟨fun h i j => by simpa using h (a.symm i) (b.symm j), fun h i j => h (a i) (b j)⟩

theorem inPow_iff {r t : ℕ} (X : Matrix (Fin r ⊕ Fin t) (Fin r) (Fv D.host.F v))
    (E : Matrix (Fin r ⊕ Fin t) (Fin r) (OI v)) :
    InPow ϖ 1 (X - E.map (algebraMap (OI v) (Fv D.host.F v))) ↔
      ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) (OI v), X = (E + ϖ • z).map (algebraMap (OI v) (Fv D.host.F v)) := by
  constructor
  · intro h
    choose z hz using h
    refine ⟨Matrix.of z, Matrix.ext fun a b => ?_⟩
    have := hz a b
    rw [Matrix.sub_apply, sub_eq_iff_eq_add', pow_one] at this
    rw [this]
    simp
  · rintro ⟨z, rfl⟩ a b
    exact ⟨z a b, by simp⟩

def reGL {K : Type} [CommRing K] {r n : ℕ} (h : r = n) (g : GL (Fin r) K) : GL (Fin n) K :=
  ⟨g.val.submatrix (finCongr h).symm (finCongr h).symm, (g⁻¹).val.submatrix (finCongr h).symm (finCongr h).symm,
    by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩

variable (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (i : Fin D.R.m) {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D}
  (he : IsIdemOf φ e)
include hL he

theorem coord : GlobalTheory.PlaceTensor.IsCoord (cA D e) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True)
      (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i))) ∧ ∀ g h x,
      adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (actO (Vc D i) (Wc D i) g⁻¹ h⁻¹ x) =
        ((grpCo φ (Vc D i) (frCo φ (R.βV i)) g)⁻¹).val * adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x *
          (grpCo φ (Wc D i) (frCo φ (R.βW i)) h).val :=
  GlobalTheory.PlaceTensor.adjCo_isCoord D _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) v φ e he _ _

theorem coR_add (x y : WO (Vc D i) (Wc D i)) : coR R i φ (x + y) = coR R i φ x + coR R i φ y := by
  unfold coR co
  rw [(coord R hL i he).1.1]
  rfl

theorem coR_sub (x y : WO (Vc D i) (Wc D i)) : coR R i φ (x - y) = coR R i φ x - coR R i φ y := by
  rw [eq_sub_iff_add_eq, ← coR_add R hL i he, sub_add_cancel]

theorem coR_inj {x y : WO (Vc D i) (Wc D i)} (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y)
    (h : coR R i φ x = coR R i φ y) : x = y := by
  refine (coord R hL i he).1.2.1.injOn hx hy (Matrix.ext fun a b => ?_)
  have := congrFun (congrFun h ((rowIx (rank_V i)).symm a)) ((finCongr (rank_weight_component_eq i)).symm b)
  simpa [coR, co] using this

theorem exists_section : ∃ σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i),
    ∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X := by
  have h : ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∃ x : WO (Vc D i) (Wc D i),
      IsHalf (cA D e) x ∧ coR R i φ x = X := fun X => by
    obtain ⟨x, hx, hX⟩ := (coord R hL i he).1.2.1.surjOn
      (Set.mem_univ (X.submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm))
    refine ⟨x, hx, ?_⟩
    unfold coR co
    rw [hX]
    ext a b
    simp
  exact ⟨fun X => (h X).choose, fun X => (h X).choose_spec⟩

theorem coR_act {g : GL (Fin D.R.r) (Fv D.host.F v)} {h : GA D (Wc D i)}
    (hh : grpCo φ (Wc D i) (frCo φ (R.βW i)) h = reGL (rank_weight_component_eq i) g) (x : WO (Vc D i) (Wc D i)) :
    coR R i φ (actO (Vc D i) (Wc D i) 1 h⁻¹ x) = coR R i φ x * g.val := by
  have h1 := (coord R hL i he).2 1 h x
  have h2 : grpCo φ (Vc D i) (frCo φ (R.βV i)) 1 = 1 := by simp [grpCo]
  rw [inv_one, h2, inv_one, Units.val_one, Matrix.one_mul, hh] at h1
  unfold coR co
  rw [h1, ← Matrix.submatrix_mul_equiv _ _ _ (finCongr (rank_weight_component_eq i))]
  congr 1

omit hL he in
theorem mem_halfPow {N : ℕ} {z : WO (Vc D i) (Wc D i)} :
    z ∈ halfPow φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) e ϖ N ↔
      IsHalf (cA D e) z ∧ InPow ϖ N (coR R i φ z) :=
  and_congr Iff.rfl (inPow_submatrix _ _ _).symm

end Coord


open Classical in
theorem piece (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (hv : R.thP_vP) (i : Fin D.R.m) (t : T)
    {PP : Pl D.host.E} (hP : PP ∈ R.Pg) {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (hφ : IsProjAt φ PP)
    (he : IsIdemOf φ e) {ϖ : OI v} (hϖ : Irreducible ϖ) {Sb : Finset (FinPl D)} (hvS : v ∈ Sb)
    {f : WO (Vc D i) (Wc D i) → ℂ} (hT : TypeIn R i t Sb f) (hC : CleanIn R i t Sb f) (hO : LikeOff R i t Sb f)
    (g : GL (Fin D.R.r) (Fv D.host.F v))
    (hconst : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x x', IsHalf (cA D e) x → IsHalf (cA D e) x' →
      coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g →
      coR R i φ x' ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) x' f)) :
    ∃ F ∈ StepGen R i t (dropPl Sb v), IsThetaFunO R.ψ (Vc D i) (Wc D i) F ∧
      ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x, IsHalf (cA D e) x →
        ℓ (heisO R.ψ (Vc D i) (Wc D i) x F) =
          if coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g then ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) else 0 := by
  have hW := hω i t
  have hψ := hW.std
  have he' := isSplitIdem_conj he.1
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  have frV := (hL.βV i).choose_spec.1
  have frW := (hL.βW i).choose_spec.1
  have hf := hT.1
  have thx : ∀ {x q}, IsHalf (cA D e) x → IsThetaFunO R.ψ (Vc D i) (Wc D i) q →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (heisO R.ψ (Vc D i) (Wc D i) x q) := fun hx hq =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hq
  obtain ⟨σ, hσ⟩ := exists_section R hL i he
  obtain ⟨h, hh, hg⟩ := GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq D (Wc D i) v φ e he (frCo φ (R.βW i)) (reGL (rank_weight_component_eq i) g)
  have hh' : Formalism.L2.Theta.SuppAt e (Wc D i) h⁻¹ := fun a b => by
    have := congrFun (congrFun (off_smul_mt_inv hh) a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.sub_apply]
    linear_combination -this
  obtain ⟨s, hs0, hs⟩ := exists_scalar hW he.1 (suppAt_one' e (Vc D i)) hh'
  set E : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v) := Matrix.fromRows 1 0 with hE
  set x₀ := σ (E.map (algebraMap (OI v) (Fv D.host.F v))) with hx₀
  set A₁ := halfPow φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) e ϖ 1 with hA₁
  have hf' := hW.om_pres (1, h⁻¹) f hf
  have hdual := GlobalTheory.T.exists_separating_character_conjugate_half_split D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ 1
  obtain ⟨N, -, hN⟩ := GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ sdV sdW frV frW v φ e he ϖ hϖ _ hf'
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.finiteFourierExpansion_conjugateHalf_splitPlace D R.ψ hψ _ _ _ _ sdV sdW v φ e he (frCo φ (R.βV i)) (frCo φ (R.βW i)) ϖ hϖ 1 N hdual
    (fun X => if InPow ϖ 1 (X - adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀) then 1 else 0)
    (fun X Z hZ => if_congr ⟨fun h => by
        have := inPow_add h (inPow_neg hZ)
        rwa [add_sub_right_comm, add_neg_cancel_right] at this,
      fun h => by rw [add_sub_right_comm]; exact inPow_add h hZ⟩ rfl rfl)
  set F := comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h⁻¹) f) with hF
  have hFt : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := theta_comb hψ he.1 hc hf'
  have hB : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ y, IsHalf (cA D e) y →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) y F) =
        if y - x₀ ∈ A₁ then ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) else 0 := by
    intro ℓ hℓ y hy
    rw [hF, form_comb hψ he.1 hℓ hc hf' hy]
    by_cases h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) y (R.ωP i t (1, h⁻¹) f)) = 0
    · rw [h0, mul_zero, ite_self]
    · rw [← hcv y hy (hN ℓ hℓ y hy h0)]
      have e1 : adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) (y - x₀) =
          adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y -
            adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀ := by
        rw [eq_sub_iff_add_eq, ← (coord R hL i he).1.1, sub_add_cancel]
      have e2 : y - x₀ ∈ A₁ ↔ InPow ϖ 1 (adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y -
          adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) x₀) := by
        rw [← e1]
        exact ⟨fun h => h.2, fun h => ⟨isHalf_sub hy (hσ _).1, h⟩⟩
      simp only [e2]
      split_ifs
      · rw [one_mul]
      · rw [zero_mul]
  have hmove : ∀ ℓ, InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ x, IsHalf (cA D e) x → ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) q →
      ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) 1 h⁻¹ x) (R.ωP i t (1, h⁻¹) q)) =
        s * ℓ (heisO R.ψ (Vc D i) (Wc D i) x q) := fun ℓ hℓ x hx q hq => by
    rw [← hW.om_heis 1 h⁻¹ x q hq, hs ℓ hℓ _ (thx hx hq)]
  have hmem : ∀ x, IsHalf (cA D e) x → (actO (Vc D i) (Wc D i) 1 h⁻¹ x - x₀ ∈ A₁ ↔
      coR R i φ x ∈ trSet (OI v) (Fv D.host.F v) D.R.r D.R.t ϖ g) := fun x hx => by
    rw [hA₁, mem_halfPow, coR_sub R hL i he, coR_act R hL i he hg, hx₀, (hσ _).2, inPow_iff]
    exact and_iff_right (isHalf_sub (GlobalTheory.SplitHecke.isHalf_actO _ _ hx) (hσ _).1)
  have hback : ∀ y, actO (Vc D i) (Wc D i) 1 h⁻¹ (actO (Vc D i) (Wc D i) 1 h y) = y := fun y => by
    have := GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D (Vc D i)) h y
    rwa [inv_one] at this
  have hsh : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ F := by
    refine shape_of_forms hψ he.1 (A := A₁) (fun z hz => hz.1) hFt (fun ℓ hℓ y hy z hz => ?_) fun ℓ hℓ y hy h0 => ?_
    · have hyz := isHalf_add hy hz.1
      have e1 : y + z - x₀ ∈ A₁ ↔ y - x₀ ∈ A₁ := by
        have hz2 := ((mem_halfPow R i).1 hz).2
        rw [hA₁, mem_halfPow, mem_halfPow, add_sub_right_comm, coR_add R hL i he]
        refine ⟨fun h => ⟨isHalf_sub hy (hσ _).1, ?_⟩, fun h => ⟨isHalf_add h.1 hz.1, inPow_add h.2 hz2⟩⟩
        have := inPow_add h.2 (inPow_neg hz2)
        rwa [add_neg_cancel_right] at this
      rw [hB ℓ hℓ _ hyz, hB ℓ hℓ _ hy]
      by_cases c1 : y - x₀ ∈ A₁
      · have c2 := e1.2 c1
        rw [if_pos c1, if_pos c2]
        have a1 := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hy
        have a2 := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D (Vc D i)) h hyz
        rw [← hback y] at c1
        rw [← hback (y + z)] at c2
        rw [← hback (y + z), hmove ℓ hℓ _ a2 f hf]
        conv_rhs => rw [← hback y, hmove ℓ hℓ _ a1 f hf]
        rw [hconst ℓ hℓ _ _ a2 a1 ((hmem _ a2).1 c2) ((hmem _ a1).1 c1)]
      · rw [if_neg c1, if_neg fun c2 => c1 (e1.1 c2)]
    · by_contra hn
      exact h0 (by rw [hB ℓ hℓ y hy, if_neg hn])
  have hvp : Shape R.ψ (Vc D i) (Wc D i) e A₁ x₀ (R.vP i t) := by
    refine GlobalTheory.T.typePrime_fixedThetaVector_schrodinger_indicator D R.ψ R.θ _ _ _ _ _ _ _ _ _ _ _ _ _ sdV sdW frV frW (hv i t) PP hP v φ e hφ he ϖ hϖ x₀ (hσ _).1
      fun a b => ?_
    obtain ⟨a, rfl⟩ := (rowIx (rank_V i)).surjective a
    obtain ⟨b, rfl⟩ := (finCongr (rank_weight_component_eq i)).surjective b
    have := congrFun (congrFun (hσ (E.map (algebraMap (OI v) (Fv D.host.F v)))).2 a) b
    refine Eq.trans this ?_
    rcases a with a | a
    · simp [hE, rowIx, Matrix.one_apply, Fin.ext_iff]
    · have : D.R.r + a.val ≠ b.val := by have := b.2; omega
      simp [hE, rowIx, this]
  obtain ⟨b1, b2, b3⟩ := GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape D G Pl0 T A Ks R hω i t Sb v hvS h⁻¹ (fun a b => by rw [← he.2.1]; exact hh' a b) c
    (fun y hy => half_idem he.1 he.2.1 (hc y hy)) f hT hC hO
  have b4 : LikeOff R i t (dropPl Sb v) F :=
    ⟨hFt, relOff_drop he.1 he.2.1 (A := A₁) (fun z hz => hz.1) (fun x hx hn => hdual x hx fun h => hn ⟨hx, h⟩) hvp hsh hvS b3.2⟩
  refine ⟨R.ωP i t (1, h) F, ⟨h, F, b1, b2, b4, rfl⟩, hW.om_pres _ _ hFt, fun ℓ hℓ x hx => ?_⟩
  have e1 := hmove ℓ hℓ x hx _ (hW.om_pres (1, h) _ hFt)
  rw [om_inv_om, hB ℓ hℓ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ hx), hmove ℓ hℓ x hx f hf] at e1
  simp only [hmem x hx] at e1
  apply mul_left_cancel₀ hs0
  rw [← e1]
  split_ifs
  · rfl
  · rw [mul_zero]

theorem gen_at_type_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∃ PP ∈ R.Pg, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t Sb v hvS ⟨PP, hP, hO⟩ f hT hC hLk
  classical
  have hL := hG.core.lev
  have hω := hG.core.thP.ωP
  have hv := hG.core.thP.vP
  have hW := hω i t
  have hψ := hW.std
  have hf := hT.1
  obtain ⟨-, e₀, ⟨⟨es, hes, -⟩, -⟩, -⟩ := hv i t
  obtain ⟨v', φ, he, hφ⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ PP (hes PP (Finset.mem_union_left _ hP))
  obtain rfl : v' = v :=
    HeightOneSpectrum.ext ((((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ PP hφ).1).symm.trans hO)
  set e := es PP
  have he' := isSplitIdem_conj he.1
  obtain ⟨⟨red, hsurj, hker, -, hred⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v' φ PP hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OI v')
  have : Finite (IsLocalRing.ResidueField (OI v')) := Formalism.UG.P.glint_finite_residueField v'
  have hact := actAt R hL hω hv i t hP hφ he red hred
  obtain ⟨σ, hσ⟩ := exists_section R hL i he
  have hσx : ∀ x, IsHalf (cA D e) x → σ (coR R i φ x) = x := fun x hx => coR_inj R hL i he (hσ _).1 hx (hσ _).2
  obtain ⟨N, hN1, hN2⟩ := GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support D R.ψ hψ _ _ _ _ _ _ (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 v' φ e he ϖ hϖ f hf
  let Φ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} → Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v') → ℂ :=
    fun ℓ X => ℓ.1 (heisO R.ψ (Vc D i) (Wc D i) (σ X) f)
  have h2 := fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} =>
    GlobalTheory.T.schrodingerFunction_invariant_typePrime D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hT ϖ hϖ
  have h3 := fun ℓ : {ℓ // InvForm R.ψ (Vc D i) (Wc D i) e ℓ} =>
    GlobalTheory.T.schrodinger_hyperplane_averages_vanish D G Pl0 T A Ks R hL hω i t PP hP v' φ e hφ he red hsurj hker hact Sb hvS σ hσ ℓ.1 ℓ.2 f hf hC
  have hsupp : ∀ k X, Φ k X ≠ 0 → ∃ z : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (OI v'),
      algebraMap (OI v') (Fv D.host.F v') (ϖ ^ N) • X = z.map (algebraMap (OI v') (Fv D.host.F v')) := fun k X hX => by
    choose o ho using hN2 k.1 k.2 _ (hσ X).1 hX
    refine ⟨Matrix.of fun a b => o (rowIx (rank_V i) a) (finCongr (rank_weight_component_eq i) b), Matrix.ext fun a b => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, ← ho, ← (hσ X).2, hσx _ (hσ X).1]
    rfl
  obtain ⟨Fs, hFs⟩ := exists_finset_trSet (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ Φ N (fun k X z => by
      have e1 : σ (X + (ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v'))) =
          σ X + σ ((ϖ ^ N • z).map (algebraMap (OI v') (Fv D.host.F v'))) :=
        coR_inj R hL i he (hσ _).1 (isHalf_add (hσ _).1 (hσ _).1) (by rw [coR_add R hL i he, (hσ _).2, (hσ _).2, (hσ _).2])
      simp only [Φ]
      rw [e1, heisO_add_of_orth _ _ _ (half_orth he' (hσ _).1 (hσ _).1),
        hN1 _ ((mem_halfPow R i).2 ⟨(hσ _).1, by rw [(hσ _).2]; exact fun a b => ⟨z a b, rfl⟩⟩)]) hsupp
    fun k => GlobalTheory.parahoric_schwartz_vanish_off_translates (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ k) N (hsupp k)
      (h2 k) (h3 k)
  choose P hP1 hP2 hP3 using fun g => piece R hL hω hv i t hP hφ he hϖ hvS hT hC hLk g fun ℓ hℓ x x' hx hx' ⟨z, hz⟩ ⟨z', hz'⟩ => by
    have a1 := GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z hz
    have a2 := GlobalTheory.T.congruenceInvariant_const_on_frame_translate (OI v') (Fv D.host.F v') D.R.r D.R.t ϖ hϖ (Φ ⟨ℓ, hℓ⟩) (h2 ⟨ℓ, hℓ⟩) _ g z' hz'
    have a3 := a1.trans a2.symm
    simp only [Φ] at a3
    rwa [hσx x hx, hσx x' hx'] at a3
  have hsum : f = ∑ g ∈ Fs, P g := by
    refine eq_of_forms hψ he.1 hf (theta_sum _ _ f hf fun g _ => hP2 g) fun ℓ hℓ x hx => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heisO_sum, map_sum, Finset.sum_congr rfl fun g _ => hP3 g ℓ hℓ x hx]
    by_cases h0 : ℓ (heisO R.ψ (Vc D i) (Wc D i) x f) = 0
    · simp [h0]
    · obtain ⟨g, ⟨hg, hxg⟩, hu⟩ := hFs ⟨ℓ, hℓ⟩ (coR R i φ x) (by simp only [Φ]; rwa [hσx x hx])
      rw [Finset.sum_eq_single_of_mem g hg fun g' hg' hne => if_neg fun h => hne (hu g' ⟨hg', h⟩), if_pos hxg]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.subset_span (hP1 g)

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunAtTypePrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_generation_thetaFun_at_type_prime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∃ PP ∈ R.Pg, GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.GenSplit.gen_at_type_prime | exact GlobalTheory.DownLift.GenSplit.gen_at_type_prime | (intros; apply GlobalTheory.DownLift.GenSplit.gen_at_type_prime <;> assumption)
end
