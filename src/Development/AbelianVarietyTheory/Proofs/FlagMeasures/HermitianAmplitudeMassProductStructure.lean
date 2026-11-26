module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesTermsOrbitsLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbit
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.amp_summand_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP Λ hT hL o ho
  have hrel : MulAction.orbitRel S.St (Submodule L.O S.V) o.out Λ := by
    have h1 : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) = Quotient.mk'' Λ :=
      (Quotient.out_eq' o).trans ho
    exact Quotient.exact' h1
  obtain ⟨g, hg⟩ := hrel
  have hout : o.out = (g : S.GLV) • Λ := by rw [← hg]; rfl
  have hgm : (g : S.GLV) ∈ S.St := g.2
  obtain ⟨hT', hom, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT _ hgm
  have hmu : S.mu ((g : S.GLV) • Λ) = S.mu Λ := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hL |>.2.2 _ hgm
  have hPg : P ((g : S.GLV) • Λ) ↔ P Λ := hP Λ _ hgm
  refine ⟨hout ▸ hT', ⟨_, hgm, hout⟩, ?_, ?_⟩
  · rw [hout]; simp only [hT', true_and, hPg, hmu, hom]
  · rw [hout]; simp only [hT', true_and, hPg, hmu]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbitStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAmplitude_summand_at_term_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  first | exact @GlobalTheory.HL.amp_summand_orbit | exact GlobalTheory.HL.amp_summand_orbit | (intros; apply GlobalTheory.HL.amp_summand_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbit
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hex huniq hall
  obtain ⟨Λ, hΛ⟩ := hex
  let o₀ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk'' Λ
  have hout : S.IsTerm d o₀.out := by
    have hm : o₀.out ∈ MulAction.orbit S.St Λ :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St _) Λ)
    obtain ⟨g, hg⟩ := hm
    rw [← hg]
    exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hΛ g.1 g.2).1
  have hother : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₀ →
      ¬ S.IsTerm d o.out := by
    intro o ho ht
    obtain ⟨h, hh, e⟩ := huniq Λ o.out hΛ ht
    apply ho
    rw [← Quotient.out_eq' o]
    apply Quotient.sound'
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩
  obtain ⟨hP, hmu, hom⟩ := hall _ hout
  constructor
  · unfold GlobalTheory.HL.Frames.amp
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu, hom]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
  · unfold GlobalTheory.HL.Frames.mass
    rw [tsum_eq_single o₀]
    · rw [if_pos ⟨hout, hP⟩, hmu]; simp
    · intro o ho
      exact if_neg fun hc => hother o ho hc.1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbitStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  first | exact @GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | exact GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | (intros; apply GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijection
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijection
open scoped Classical

namespace GlobalTheory

theorem prod_sum_of_local_choices {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)]
    (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p))
    (hU : ∀ p ∈ s, (U p).Finite)
    (hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c')
    (hmem : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p)
    (hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p)
    (g : ∀ p, O p → R) :
    Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  have hT : Tq.Finite := by
    let e : Q → ∀ p : s, O p := fun c p => Φ c p
    have hfin : (Set.pi Set.univ (fun p : s => U p)).Finite :=
      Set.Finite.pi (fun p => hU p p.2)
    refine Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_
    · rintro _ ⟨c, hc, rfl⟩ p _
      exact hmem c hc p p.2
    · intro c hc c' hc' h
      exact hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)
  refine ⟨hT, ?_⟩
  let t : ∀ p, Finset (O p) := fun p => if h : p ∈ s then (hU p h).toFinset else ∅
  have ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p := by
    intro p hp o; simp [t, hp]
  rw [tsum_eq_sum (s := hT.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc; simp [hc])]
  have hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o := by
    intro p hp
    rw [tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]
    refine Finset.sum_congr rfl (fun o ho => ?_)
    rw [ht p hp] at ho; simp [ho]
  rw [Finset.prod_congr rfl hR, Finset.prod_sum]
  have hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p) :=
    Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])
  rw [hL]
  refine Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    rw [Finset.mem_pi]
    intro p hp
    exact (ht p hp _).2 (hmem c hc p hp)
  · intro c hc c' hc' h
    rw [Set.Finite.mem_toFinset] at hc hc'
    exact hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let y : ∀ p, O p := fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)
    obtain ⟨c, hc, hcy⟩ := hsurj y (fun p hp => by
      simp only [y, dif_pos hp]; exact (ht p hp _).1 (hx p hp))
    refine ⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩
    funext p hp
    rw [hcy p hp]; simp [y, hp]
  · intro c _
    exact (Finset.prod_attach s (fun p => g p (Φ c p))).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijectionStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_of_local_choices_bijection : ∀ {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)] (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p)), (∀ p ∈ s, (U p).Finite) → (∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c') → (∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p) → (∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p) → ∀ g : ∀ p, O p → R, Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  first | exact @GlobalTheory.prod_sum_of_local_choices | exact GlobalTheory.prod_sum_of_local_choices | (intros; apply GlobalTheory.prod_sum_of_local_choices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.ProdStruct

def instLf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : IsNonarchimedeanLocalField X.Fp := X.lf

def instChar0 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    {p : HeightOneSpectrum (𝓞 F)} (X : LocAt F E sig p) : CharZero X.Fp := X.char0
attribute [local instance] instLf instChar0

theorem orb_eq_iff {G α : Type*} [Group G] [MulAction G α] (H : Subgroup G) (a b : α) :
    (Quotient.mk'' a : MulAction.orbitRel.Quotient H α) = Quotient.mk'' b ↔ ∃ h ∈ H, a = h • b := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨h, hh⟩, e⟩
    exact ⟨h, hh, e.symm⟩
  · rintro ⟨h, hh, e⟩
    exact ⟨⟨h, hh⟩, e.symm⟩

theorem std_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (Λs : Submodule L.O S.V) (d₀ : S.Datum), IsLat L Λs → S.St ⊓ MulAction.stabilizer S.GLV Λs = S.K0 → S.IsTerm d₀ Λs → S.om d₀ Λs = 1 → (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • Λs) → (∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀) → ∀ (d : S.Datum) (Λ Λ' : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm d Λ' → (∃ h ∈ S.St, Λ' = h • Λ) ∧ S.mu Λ = 1 ∧ S.om d Λ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λs d₀ hlat hK hterm hom hall hdat d Λ Λ' hΛ hΛ'
  obtain ⟨h, hh, rfl⟩ := hdat d Λ hΛ
  have tr := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h⁻¹ (S.H0.inv_mem hh)
  have tr2 := GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser L r k S h hh
  have key : ∀ Λ, S.IsTerm (h • d₀) Λ → ∃ s ∈ S.St, h⁻¹ • Λ = s • Λs ∧ S.mu Λ = 1 ∧ S.om (h • d₀) Λ = 1 := by
    intro Λ hΛ
    have e := tr.2 (h • d₀) Λ hΛ
    simp only [inv_smul_smul] at e
    obtain ⟨s, hs, hsΛ⟩ := hall _ e.1
    refine ⟨s, hs, hsΛ, ?_, ?_⟩
    · rw [← e.2.2, hsΛ, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λs hlat).2.2 s hs]
      unfold Frames.mu
      rw [hK]
      simp [invVol, Subgroup.relIndex_self]
    · rw [← e.2.1, hsΛ, (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d₀ Λs hterm s hs).2.1, hom]
  obtain ⟨s, hs, e1, hmu, hom1⟩ := key Λ hΛ
  obtain ⟨s', hs', e2, -, -⟩ := key Λ' hΛ'
  refine ⟨⟨h * (s' * s⁻¹) * h⁻¹, tr2.1 _ (S.St.mul_mem hs' (S.St.inv_mem hs)), ?_⟩, hmu, hom1⟩
  have hl : Λs = s⁻¹ • h⁻¹ • Λ := by rw [e1, inv_smul_smul]
  have hl' : Λ' = h • s' • Λs := by rw [← e2, smul_inv_smul]
  rw [hl', hl]
  simp only [mul_smul]

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem isLattice_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) {Γ Γ' : G.Lt}
    (hΓ : Submodule.IsLattice E Γ) (h : G.LRel Γ Γ') : Submodule.IsLattice E Γ' := by
  obtain ⟨g, -, rfl⟩ := h
  refine ⟨hΓ.fg.map _, ?_⟩
  rw [Submodule.map_coe]
  intro s hs hlin
  let f : G.V →ₗ[E] G.V := g
  let t : Set G.V := f ⁻¹' s
  have ht : t ⊆ Γ := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hs hx
    exact (g.injective heq) ▸ hy
  have himage : f '' t = s := Set.image_preimage_eq _ g.surjective
  have hR : LinearIndepOn (𝓞 E) id t := by
    apply (linearIndepOn_id_imageₛ_iff (f := f.restrictScalars (𝓞 E)) g.injective.injOn).mp
    simpa [himage] using hlin
  have hE := hΓ.linearIndepOn t ht hR
  have := (linearIndepOn_id_imageₛ_iff (f := f) g.injective.injOn).mpr hE
  simpa [himage] using this

theorem term_of_LRel {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (hk : 4 * r + 7 ≤ k) {d : G.Dat}
    (hex : ∃ Λ₀, G.IsTerm d Λ₀) {Γ Γ' : G.Lt} (hΓ : G.IsTerm d Γ) (h : G.LRel Γ Γ') : G.IsTerm d Γ' := by
  have hl := isLattice_of_LRel G hΓ.1 h
  have e := ((GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex).2.1 Γ Γ' hΓ hl).1 h
  refine ⟨hl, fun p => ?_⟩
  obtain ⟨s, hs, hsp⟩ := e p
  rw [hsp]
  exact (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ (hΓ.2 p) s hs).1

end GlobalTheory.HL.ProdStruct

namespace GlobalTheory.HL.ProdStruct
attribute [local instance] instLf instChar0

theorem full_lattice_of_term {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)
    {d : G.Dat} {Λ : G.Lt} (hΛ : G.IsTerm d Λ) : Submodule.IsFullLattice E Λ := by
  refine { toIsLattice := hΛ.1, span_eq_top := ?_ }
  by_contra hne
  obtain ⟨φ, hφ, hzero⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  have := (A.loc p).lf
  have := (A.loc p).char0
  have := PlacesInt.nontrivial_Ep (A.loc p)
  have hspan := (TermBasic.term_basic (A.L p) r k (G.S p) (d p) (A.lat p Λ) (hΛ.2 p)).1.1.2
  let ψ : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
    ∑ i : Fin (k + 2 * r + 1), (A.loc p).ιE (φ fun j => if i = j then 1 else 0) • LinearMap.proj i
  have hψ (z : G.V) : ψ (A.bc p z) = (A.loc p).ιE (φ z) := by
    rw [φ.pi_apply_eq_sum_univ z, map_sum]
    simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul, map_mul, Places.bc]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hlat : A.lat p Λ ≤ (LinearMap.ker ψ).restrictScalars (A.L p).O := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    have hz' : φ z ∈ (⊥ : Submodule E E) := by
      rw [← hzero]
      exact Submodule.mem_map_of_mem (Submodule.subset_span hz)
    change ψ (A.bc p z) = 0
    rw [hψ, (Submodule.mem_bot E).mp hz', map_zero]
  have hker : Submodule.span (A.loc p).Ep (A.lat p Λ : Set _) ≤ LinearMap.ker ψ :=
    Submodule.span_le.mpr hlat
  rw [hspan] at hker
  apply hφ
  apply LinearMap.ext
  intro z
  have hz := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := A.bc p z)))
  rw [hψ] at hz
  exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp hz


theorem product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ P : ∀ p, Submodule (A.L p).O (G.S p).V → Prop, (∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → P p Λ → P p (h • Λ)) → {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ P p Λ}.Finite → G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (P p) ∧ G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).mass (d p) (P p) ∧ {p | (G.S p).amp (d p) (P p) ≠ 1 ∨ (G.S p).mass (d p) (P p) ≠ 1}.Finite ∧ {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk d hex P hPinv hPfin
  obtain ⟨Λ₀, hΛ₀⟩ := id hex
  have orb := GlobalTheory.T.globalHermitianFrames_terms_orbits_local A r k G hk d hex
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  have hrec := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Λ₀ (full_lattice_of_term G hΛ₀)
  have hfin := (hstd.union hrec.2.2).union hPfin
  set s := hfin.toFinset with hs_def

  have KF : ∀ p, p ∉ s → ∀ Λ Λ', (G.S p).IsTerm (d p) Λ → (G.S p).IsTerm (d p) Λ' →
      (∃ h ∈ (G.S p).St, Λ' = h • Λ) ∧ (G.S p).mu Λ = 1 ∧ (G.S p).om (d p) Λ = 1 ∧ P p Λ := by
    intro p hp Λ Λ' hΛ hΛ'
    simp only [hs_def, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hp
    obtain ⟨_, _, hK, d₀, hW, hom, _, hall, _, hdat⟩ := hs1
    have hlat : IsLat (A.L p) (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) := by
      rw [← hs2]; exact hrec.2.1 p
    have t := std_one (A.L p) r k (G.S p) _ d₀ hlat hK ⟨(1, 1), hW⟩ hom hall hdat (d p) Λ Λ' hΛ hΛ'
    exact ⟨t.1, t.2.1, t.2.2, by by_contra hc; exact hs3 ⟨Λ, hΛ, hc⟩⟩
  have L1 : ∀ p, p ∉ s → (G.S p).amp (d p) (P p) = 1 ∧ (G.S p).mass (d p) (P p) = 1 := fun p hp =>
    GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit (A.L p) r k (G.S p) (d p) (P p) ⟨_, hΛ₀.2 p⟩
      (fun Λ Λ' h1 h2 => (KF p hp Λ Λ' h1 h2).1)
      (fun Λ h1 => ⟨(KF p hp Λ Λ h1 h1).2.2.2, (KF p hp Λ Λ h1 h1).2.1, (KF p hp Λ Λ h1 h1).2.2.1⟩)
  have hmuG : ∀ Γ, G.IsTerm d Γ → G.mu Γ = ∏ p ∈ s, (G.S p).mu (A.lat p Γ) := by
    intro Γ hΓ
    rw [(GlobalTheory.T.hermitianLattice_mass_eq_finprod_local A r k G hk Γ (by first | exact full_lattice_of_term G hΓ | exact hΓ.1)).2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.1
  have homG : ∀ Γ, G.IsTerm d Γ → G.om d Γ = ∏ p ∈ s, (G.S p).om (d p) (A.lat p Γ) := by
    intro Γ hΓ
    unfold GFrames.om
    apply finprod_eq_prod_of_mulSupport_subset
    intro p hp
    by_contra hps
    exact hp (KF p hps _ _ (hΓ.2 p) (hΓ.2 p)).2.2.1
  have hPinv' : ∀ p, ∀ Λ, ∀ h ∈ (G.S p).St,
      ((G.S p).IsTerm (d p) (h • Λ) ∧ P p (h • Λ)) ↔ ((G.S p).IsTerm (d p) Λ ∧ P p Λ) := by
    intro p Λ h hh
    constructor
    · rintro ⟨h1, h2⟩
      have e := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h⁻¹ ((G.S p).St.inv_mem hh)
      rw [inv_smul_smul] at e
      exact ⟨e.1, by simpa using hPinv p h⁻¹ ((G.S p).St.inv_mem hh) _ h1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms (A.L p) r k (G.S p) (d p) _ h1 h hh).1, hPinv p h hh Λ h1 h2⟩
  let O := fun p => MulAction.orbitRel.Quotient (G.S p).St (Submodule (A.L p).O (G.S p).V)
  let Φ : Quot G.LRel → ∀ p, O p := fun c p => Quotient.mk'' (A.lat p c.out)
  let U : ∀ p, Set (O p) := fun p => {o | (G.S p).IsTerm (d p) o.out}
  let Tq : Set (Quot G.LRel) := {c | G.IsTerm d c.out}
  let gC : ∀ p, O p → ℂ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ((G.S p).mu o.out : ℂ) * (G.S p).om (d p) o.out else 0
  let gM : ∀ p, O p → ℝ≥0∞ := fun p o => if (G.S p).IsTerm (d p) o.out ∧ P p o.out then
    ENNReal.ofReal ((G.S p).mu o.out) else 0
  have hcls : ∀ Γ, G.IsTerm d Γ → ∀ p, (G.S p).IsTerm (d p) (Quotient.mk'' (A.lat p Γ) : O p).out ∧
      gC p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then
        ((G.S p).mu (A.lat p Γ) : ℂ) * (G.S p).om (d p) (A.lat p Γ) else 0) ∧
      gM p (Quotient.mk'' (A.lat p Γ)) = (if P p (A.lat p Γ) then ENNReal.ofReal ((G.S p).mu (A.lat p Γ)) else 0) := by
    intro Γ hΓ p
    have t := GlobalTheory.T.localAmplitude_summand_at_term_orbit (A.L p) r k (G.S p) (d p) (fun Λ => (G.S p).IsTerm (d p) Λ ∧ P p Λ) (hPinv' p)
      (A.lat p Γ) (hΓ.2 p) ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices A _ Γ (full_lattice_of_term G hΓ)).2.1 p) _ rfl
    simp only [and_self_left, hΓ.2 p, true_and] at t
    exact ⟨t.1, t.2.2.1, t.2.2.2⟩
  have hUfin : ∀ p ∈ s, (U p).Finite := fun p _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite (A.L p) r k (G.S p) (by omega) (d p)).2
  have hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c' := by
    intro c hc c' hc' he
    have hc1 : G.IsTerm d c.out := hc
    have hc2 : G.IsTerm d c'.out := hc'
    have hrel : G.LRel c.out c'.out := by
      rw [orb.2.1 c.out c'.out hc1 hc2.1]
      intro p
      by_cases hp : p ∈ s
      · exact (orb_eq_iff _ _ _).1 (he p hp).symm
      · exact (KF p hp _ _ (hc1.2 p) (hc2.2 p)).1
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    exact Quot.sound hrel
  have hmaps : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p := fun c hc p _ => (hcls c.out hc p).1
  have hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p := by
    intro x hx
    obtain ⟨Γ, hΓ, hloc⟩ := orb.1 (fun p => if p ∈ s then (x p).out else A.lat p Λ₀) (by
      intro p
      by_cases hp : p ∈ s
      · simp only [hp, if_true]; exact hx p hp
      · simp only [hp, if_false]; exact hΛ₀.2 p)
    have hr : G.LRel Γ (Quot.mk G.LRel Γ).out :=
      orb.2.2.1.symm ((Equivalence.eqvGen_iff orb.2.2.1).1 (Quot.eqvGen_exact (Quot.out_eq _)))
    have hct : G.IsTerm d (Quot.mk G.LRel Γ).out := term_of_LRel G hk hex hΓ hr
    have hloc2 := (orb.2.1 Γ _ hΓ hct.1).1 hr
    refine ⟨Quot.mk G.LRel Γ, hct, fun p hp => ?_⟩
    obtain ⟨h1, hh1, e1⟩ := hloc2 p
    obtain ⟨h2, hh2, e2⟩ := hloc p
    simp only [hp, if_true] at e2
    show (Quotient.mk'' (A.lat p (Quot.mk G.LRel Γ).out) : O p) = x p
    rw [e1, e2, ← mul_smul, (orb_eq_iff _ _ _).2 ⟨h1 * h2, (G.S p).St.mul_mem hh1 hh2, rfl⟩, Quotient.out_eq']
  haveI : ∀ p, Nonempty (O p) := fun p => ⟨Quotient.mk'' ⊥⟩
  have T5C := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gC
  have T5M := GlobalTheory.T.sum_prod_of_local_choices_bijection s Φ Tq U hUfin hinj hmaps hsurj gM
  have hPs : ∀ Γ, G.IsTerm d Γ → ((∀ p, P p (A.lat p Γ)) ↔ ∀ p ∈ s, P p (A.lat p Γ)) := fun Γ hΓ =>
    ⟨fun h p _ => h p, fun h p => if hp : p ∈ s then h p hp else (KF p hp _ _ (hΓ.2 p) (hΓ.2 p)).2.2.2⟩
  have hsumC : G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gC p (Φ c p) else 0 := by
    unfold GFrames.amp
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gC p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ((G.S p).mu (A.lat p c.out) : ℂ) * (G.S p).om (d p) (A.lat p c.out) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.1), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', homG _ hc', Complex.ofReal_prod, Finset.prod_mul_distrib]
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hsumM : G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∑' c, if c ∈ Tq then ∏ p ∈ s, gM p (Φ c p) else 0 := by
    unfold GFrames.mass
    apply tsum_congr
    intro c
    by_cases hc : c ∈ Tq
    · have hc' : G.IsTerm d c.out := hc
      rw [if_pos hc, show (∏ p ∈ s, gM p (Φ c p)) = ∏ p ∈ s, (if P p (A.lat p c.out) then
          ENNReal.ofReal ((G.S p).mu (A.lat p c.out)) else 0) from
          Finset.prod_congr rfl (fun p _ => (hcls c.out hc' p).2.2), Finset.prod_ite_zero]
      simp only [hc', true_and, hPs _ hc']
      split_ifs
      · rw [hmuG _ hc', ENNReal.ofReal_prod_of_nonneg]
        intro p _
        unfold Frames.mu invVol
        positivity
      · rfl
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  have hampC : ∀ p, (G.S p).amp (d p) (P p) = ∑' o : O p, if o ∈ U p then gC p o else 0 := by
    intro p
    unfold Frames.amp
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  have hampM : ∀ p, (G.S p).mass (d p) (P p) = ∑' o : O p, if o ∈ U p then gM p o else 0 := by
    intro p
    unfold Frames.mass
    apply tsum_congr
    intro o
    by_cases ho : (G.S p).IsTerm (d p) o.out
    · have : o ∈ U p := ho
      rw [if_pos this]
    · have : o ∉ U p := ho
      rw [if_neg this, if_neg (fun h => ho h.1)]
  refine ⟨?_, ?_, ?_, T5C.1⟩
  · rw [hsumC, T5C.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).1)]
    exact Finset.prod_congr rfl (fun p _ => (hampC p).symm)
  · rw [hsumM, T5M.2, finprod_eq_prod_of_mulSupport_subset _ (s := s) (fun p hp => by
      by_contra hps; exact hp (L1 p hps).2)]
    exact Finset.prod_congr rfl (fun p _ => (hampM p).symm)
  · refine s.finite_toSet.subset (fun p hp => ?_)
    by_contra hps
    rcases hp with h | h
    · exact h (L1 p hps).1
    · exact h (L1 p hps).2

end GlobalTheory.HL.ProdStruct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructureStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_amplitude_mass_product_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ P : ∀ p, Submodule (A.L p).O (G.S p).V → Prop, (∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → P p Λ → P p (h • Λ)) → {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ P p Λ}.Finite → G.amp d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (P p) ∧ G.mass d (fun Λ => ∀ p, P p (A.lat p Λ)) = ∏ᶠ p, (G.S p).mass (d p) (P p) ∧ {p | (G.S p).amp (d p) (P p) ≠ 1 ∨ (G.S p).mass (d p) (P p) ≠ 1}.Finite ∧ {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
  first | exact @GlobalTheory.HL.ProdStruct.product_structure | exact GlobalTheory.HL.ProdStruct.product_structure | (intros; apply GlobalTheory.HL.ProdStruct.product_structure <;> assumption)
end
