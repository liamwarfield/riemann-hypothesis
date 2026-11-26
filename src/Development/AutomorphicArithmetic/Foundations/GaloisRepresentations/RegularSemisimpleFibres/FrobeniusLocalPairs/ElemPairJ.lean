module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.BallLev
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ConjEntry
noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (d : Fin n → kˣ) (g : GL (Fin n) k) (i j : Fin n) :
    (((diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j * (d j : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

private theorem conj_ball {r : ValueGroupWithZero k} {d : Fin n → kˣ} (hd : ∀ i, valuation k (d i : k) = 1)
    {g : GL (Fin n) k} (hg : g ∈ ball n r) :
    (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [conj_entry]
  by_cases h : i = j
  · subst h
    have e : (d i : k)⁻¹ * (g : Matrix (Fin n) (Fin n) k) i i * (d i : k) = (g : Matrix (Fin n) (Fin n) k) i i := by
      have := (d i).ne_zero
      field_simp
    rw [e]
    exact hg i i
  · have := hg i j
    rw [Matrix.one_apply_ne h, sub_zero] at this ⊢
    rw [map_mul, map_mul, hd j, mul_one, map_inv₀, hd i, inv_one, one_mul]
    exact this

private theorem diag_ball {r : ValueGroupWithZero k} {a : GL (Fin n) k} (ha : a ∈ ball n r) {d : Fin n → kˣ}
    (hd : ∀ i, valuation k (d i : k) = 1)
    (h : ∀ i, ((a * diagT k (Fin n) d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = 1) :
    diagT k (Fin n) d ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    have e := h i
    rw [Units.val_mul, val_diagT, Matrix.mul_diagonal] at e
    have e' : (d i : k) - 1 = (d i : k) * -((a : Matrix (Fin n) (Fin n) k) i i - 1) := by
      linear_combination e
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, e', map_mul, hd i, one_mul, Valuation.map_neg]
    have := ha i i
    rwa [Matrix.one_apply_eq] at this
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero, map_zero]
    exact zero_le'

end

theorem levOf : LevOf := by
  intro k _ _ _ _ n r h0 h1 D hDc hDv
  obtain ⟨B, hB, hBo, hBc⟩ := ballSub k n r h0 h1
  obtain ⟨hBI, hBd⟩ := ballLev k n r h0 h1 B hB
  have mB : ∀ {g : GL (Fin n) k}, g ∈ B ↔ g ∈ ball n r := fun {g} => by rw [← SetLike.mem_coe, hB]
  have hconj : ∀ d ∈ D, ∀ g ∈ B, (diagT k (Fin n) d)⁻¹ * g * diagT k (Fin n) d ∈ B :=
    fun d hd g hg => mB.2 (conj_ball (hDv d hd) (mB.1 hg))
  have hconj' : ∀ d ∈ D, ∀ g ∈ B, diagT k (Fin n) d * g * (diagT k (Fin n) d)⁻¹ ∈ B := fun d hd g hg => by
    have := hconj d⁻¹ (D.inv_mem hd) g hg
    rwa [map_inv, inv_inv] at this
  have hcomm : ∀ s t : Fin n → kˣ, diagT k (Fin n) s * diagT k (Fin n) t = diagT k (Fin n) t * diagT k (Fin n) s :=
    fun s t => by rw [← map_mul, ← map_mul, mul_comm]
  let K : Subgroup (GL (Fin n) k) :=
    { carrier := {g | ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d}
      one_mem' := ⟨1, B.one_mem, 1, D.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, d, hd, rfl⟩ ⟨a', ha', d', hd', rfl⟩
        refine ⟨a * (diagT k (Fin n) d * a' * (diagT k (Fin n) d)⁻¹), B.mul_mem ha (hconj' d hd a' ha'), d * d',
          D.mul_mem hd hd', ?_⟩
        rw [map_mul]
        group
      inv_mem' := by
        rintro _ ⟨a, ha, d, hd, rfl⟩
        refine ⟨(diagT k (Fin n) d)⁻¹ * a⁻¹ * diagT k (Fin n) d, hconj d hd _ (B.inv_mem ha), d⁻¹, D.inv_mem hd, ?_⟩
        rw [map_inv]
        group }
  have hK : ∀ {g}, g ∈ K ↔ ∃ a ∈ B, ∃ d ∈ D, g = a * diagT k (Fin n) d := Iff.rfl
  have hBK : B ≤ K := fun a ha => ⟨a, ha, 1, D.one_mem, by simp⟩
  have hDK : ∀ d ∈ D, diagT k (Fin n) d ∈ K := fun d hd => ⟨1, B.one_mem, d, hd, by simp⟩
  have hK1 : ∀ g ∈ K, (∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1) → g ∈ B := by
    rintro _ ⟨a, ha, d, hd, rfl⟩ h
    exact B.mul_mem ha (mB.2 (diag_ball (mB.1 ha) (hDv d hd) h))
  have hdc : Continuous (diagT k (Fin n)) := (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin n))
  refine ⟨K, fun g => ⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.1 ha, d, hd, rfl⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact ⟨a, mB.2 ha, d, hd, rfl⟩
  · have := (hBc.prod hDc).image (f := fun p : GL (Fin n) k × (Fin n → kˣ) => p.1 * diagT k (Fin n) p.2)
      (continuous_fst.mul (hdc.comp continuous_snd))
    convert this using 1
    ext g
    constructor
    · rintro ⟨a, ha, d, hd, rfl⟩
      exact ⟨(a, d), ⟨ha, hd⟩, rfl⟩
    · rintro ⟨⟨a, d⟩, ⟨ha, hd⟩, rfl⟩
      exact ⟨a, ha, d, hd, rfl⟩
  · exact Subgroup.isOpen_mono hBK hBo
  · rintro _ ⟨a, ha, d, hd, rfl⟩
    obtain ⟨u, hu, d', hd', c, hc, e⟩ := hBI.fact a ha
    refine ⟨u, ⟨hBK hu.1, hu.2⟩, d' * d, ?_, (diagT k (Fin n) d)⁻¹ * c * diagT k (Fin n) d,
      ⟨hBK (hconj d hd c hc.1), ?_⟩, ?_⟩
    · rw [map_mul]
      exact K.mul_mem (hBK hd') (hDK d hd)
    · have := GlobalTheory.IwahoriTraceProof.conj_mem_unipBLower d⁻¹ hc.2
      rwa [map_inv, inv_inv] at this
    · rw [e, map_mul]
      group
  · intro t ht u hu
    exact hBK (hBI.up t ht u ⟨hK1 u hu.1 ((mem_unipB k).1 hu.2).2, hu.2⟩)
  · intro t ht c hc
    exact hBK (hBI.low t ht c ⟨hK1 c hc.1 (GlobalTheory.IwahoriTraceProof.mem_unipBLower.1 hc.2).2, hc.2⟩)
  · intro t
    ext g
    constructor
    · rintro ⟨_, ⟨a, ha, d, hd, rfl⟩, _, ⟨a', ha', d', hd', rfl⟩, rfl⟩
      refine ⟨a, mB.1 ha, (diagT k (Fin n) d')⁻¹ * a' * diagT k (Fin n) d', mB.1 (hconj d' hd' a' ha'),
        t * (d * d'), ⟨d * d', D.mul_mem hd hd', rfl⟩, ?_⟩
      have e := hcomm d t
      rw [map_mul, map_mul]
      calc a * diagT k (Fin n) d * diagT k (Fin n) t * (a' * diagT k (Fin n) d')
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * (a' * diagT k (Fin n) d') := by group
        _ = a * (diagT k (Fin n) t * diagT k (Fin n) d) * (a' * diagT k (Fin n) d') := by rw [e]
        _ = _ := by group
    · rintro ⟨a, ha, b, hb, _, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨a * diagT k (Fin n) d, ⟨a, mB.2 ha, d, hd, rfl⟩, b, hBK (mB.2 hb), ?_⟩
      have e := hcomm d t
      rw [map_mul]
      calc a * (diagT k (Fin n) t * diagT k (Fin n) d) * b
          = a * (diagT k (Fin n) d * diagT k (Fin n) t) * b := by rw [e]
        _ = _ := by group

end UpperTheory.Gal.InertialTypesAlt.L
end
end

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open UpperTheory.ConvolutionTheory UpperTheory.Gal.Join

namespace UpperTheory.Gal.InertialTypesAlt.L

section Local

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']

private theorem prod_aut [IsGalois k k'] {M : Type*} [CommMonoid M] (s : k' ≃ₐ[k] k') (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    (f : (k' ≃ₐ[k] k') → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank k k'), f (s ^ i) := by
  have ho : orderOf s = Module.finrank k k' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (Module.finrank k k') => s ^ (i : ℕ) := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf (by simpa [ho] using i.2) (by simpa [ho] using j.2) h)
  have hbij : Function.Bijective fun i : Fin (Module.finrank k k') => s ^ (i : ℕ) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [← Fin.prod_univ_eq_prod_range (fun i => f (s ^ i))]
  exact (Fintype.prod_bijective _ hbij _ _ fun _ => rfl).symm

private theorem iter_aut (s : k' ≃ₐ[k] k') (i : ℕ) (x : k') :
    (⇑(s : k' ≃+* k'))^[i] x = (s ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, pow_succ]
    rfl

private theorem norm_of_prod [IsGalois k k'] (s : k' ≃ₐ[k] k') (hs : ∀ τ, τ ∈ Subgroup.zpowers s) (a : k) (x : k')
    (h : algebraMap k k' a = ∏ i ∈ Finset.range (Module.finrank k k'), (⇑(s : k' ≃+* k'))^[i] x) :
    a = Algebra.norm k x := by
  apply (algebraMap k k').injective
  rw [h, Algebra.norm_eq_prod_automorphisms, prod_aut s hs]
  exact Finset.prod_congr rfl fun i _ => iter_aut s i x

end Local

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [Field k'] [ValuativeRel k'] [Algebra k k'] [ValuativeExtension k k']

private theorem val_down (a : k) (h : valuation k' (algebraMap k k' a) = 1) : valuation k a = 1 := by
  have h1 := ValuativeExtension.vle_iff_vle (A := k) (B := k') (a := a) (b := 1)
  have h2 := ValuativeExtension.vle_iff_vle (A := k) (B := k') (a := 1) (b := a)
  rw [map_one] at h1 h2
  refine le_antisymm ?_ ?_
  · rw [← map_one (valuation k)]
    exact (Valuation.Compatible.vle_iff_le (v := valuation k) _ _).1
      (h1.1 ((Valuation.Compatible.vle_iff_le (v := valuation k') _ _).2 (by rw [h, map_one])))
  · rw [← map_one (valuation k)]
    exact (Valuation.Compatible.vle_iff_le (v := valuation k) _ _).1
      (h2.1 ((Valuation.Compatible.vle_iff_le (v := valuation k') _ _).2 (by rw [h, map_one])))

private theorem val_iter (σ : k' ≃+* k') (h : ∀ x, valuation k' (σ x) = valuation k' x) (i : ℕ) (x : k') :
    valuation k' (σ^[i] x) = valuation k' x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, ih, h]

private theorem val_near {r : ValueGroupWithZero k'} (h1 : r < 1) {x : k'} (hx : valuation k' (x - 1) ≤ r) :
    valuation k' x = 1 := by
  have h := Valuation.map_one_add_of_lt (valuation k') (lt_of_le_of_lt hx h1)
  simpa using h

end Val

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem sig_eq {n : ℕ} (hn : 0 < n) (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v)
    (hw : ∀ u : PlacesOver E v, u = w) (σw s : w.1.adicCompletion E ≃+* w.1.adicCompletion E)
    (hloc : C.IsLocGal (n := n) σ w (Loc.sg σw)) (hgal : ∀ y, galFin σ v y w = s (y w))
    (x : w.1.adicCompletion E) : σw x = s x := by
  by_cases hx : x = 0
  · simp [hx]
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let e : CompletionsOver E v ≃+* w.1.adicCompletion E :=
    RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E
  have he : ∀ z, (e.symm z) w = z := fun z => e.apply_symm_apply z
  let u : (CompletionsOver E v)ˣ := Units.map (e.symm : _ →* _) (Units.mk0 x hx)
  let g : GL (Fin n) (CompletionsOver E v) := diagT (CompletionsOver E v) (Fin n) fun _ => u
  let i : Fin n := ⟨0, hn⟩
  have h1 : galFin σ v ((g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i i) w =
      σw (((g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i i) w) :=
    congrArg (fun z : GL (Fin n) (w.1.adicCompletion E) => Units.val z i i) (hloc g)
  have h2 : (g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i i = e.symm x := by
    simp only [g, val_diagT, Matrix.diagonal_apply_eq]
    rfl
  rw [h2, hgal, he] at h1
  exact h1.symm

end Glob

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.elemPairJ :
    UpperTheory.Gal.InertialTypesAlt.L.ElemPair → UpperTheory.Gal.Join.ElemPairJ := by
  intro hP F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hloc hnorm U' U hU' hU
  obtain ⟨-, -, -, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  have hw : ∀ u : PlacesOver E v, u = w := huniq v hns w
  obtain ⟨iA, iV, iF, iG, s, hs, hrk, hinc, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  have hc : ∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x := hinc
  have hse : ∀ x, σw x = s x := sig_eq hn σ w hw σw (s : _ ≃+* _) hloc hgal
  have hiter : ∀ (i : ℕ) x, (⇑σw)^[i] x = (⇑(s : w.1.adicCompletion E ≃+* w.1.adicCompletion E))^[i] x := by
    intro i x
    have : (⇑σw) = ⇑(s : w.1.adicCompletion E ≃+* w.1.adicCompletion E) := funext hse
    rw [this]
  have hN : ∀ x, (N x : v.adicCompletion F) = Algebra.norm (v.adicCompletion F) (x : w.1.adicCompletion E) := fun x => by
    refine norm_of_prod s hs _ _ ?_
    rw [hrk, ← hc, hnorm.prod]
    exact Finset.prod_congr rfl fun i _ => hiter i _
  have hnT : ∀ T, nT n N T = nrmT (v.adicCompletion F) T := fun T =>
    funext fun i => Units.ext (hN (T i))
  obtain ⟨sr1, sr2, sr3, -, sr5, sr6⟩ := smallRad (w.1.adicCompletion E) n
  obtain ⟨kr1, -, -, kr4, -, -⟩ := smallRad (v.adicCompletion F) n
  have hNc : Continuous (nT n N) := continuous_pi fun i => hnorm.cont.comp (continuous_apply i)
  have hW : {u | diagT (v.adicCompletion F) (Fin n) (nT n N u) ∈ U} ∈ nhds (1 : Fin n → (w.1.adicCompletion E)ˣ) := by
    have hcont : Continuous fun u => diagT (v.adicCompletion F) (Fin n) (nT n N u) := kr4.comp hNc
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [map_one, map_one]
    exact hU.mem_nhds U.one_mem
  obtain ⟨ra, ha0, ha1, ha⟩ := sr1 U' (hU'.mem_nhds U'.one_mem)
  obtain ⟨rb, hb0, hb1, hb⟩ := sr2 _ hW
  obtain ⟨r, hra, hrb, hr0, hr1⟩ : ∃ r, r ≤ ra ∧ r ≤ rb ∧ 0 < r ∧ r < 1 :=
    ⟨min ra rb, min_le_left _ _, min_le_right _ _, lt_min ha0 hb0, (min_le_left _ _).trans_lt ha1⟩
  have hball : ball n r ⊆ (U' : Set (C.Gw n w.1)) := ha r hra
  have hnear : ∀ u, Near r u → diagT (v.adicCompletion F) (Fin n) (nT n N u) ∈ U := fun u hu => hb r hrb u hu
  obtain ⟨r₀, h00, h01, hmain⟩ := hP F E σ hσ hp v w hw hc n r hr0 hr1
  obtain ⟨rc, hc0, hc1, hcb⟩ := kr1 U (hU.mem_nhds U.one_mem)
  obtain ⟨r', hr'a, hr'b, hr'0, hr'1⟩ : ∃ r', r' ≤ r₀ ∧ r' ≤ rc ∧ 0 < r' ∧ r' < 1 :=
    ⟨min r₀ rc, min_le_left _ _, min_le_right _ _, lt_min h00 hc0, (min_le_left _ _).trans_lt h01⟩
  have hball' : ball n r' ⊆ (U : Set (C.Gw n v)) := hcb r' hr'b
  obtain ⟨-, c, hcpos, hm⟩ := hmain r' hr'a hr'0
  obtain ⟨K', hK', -, -⟩ := ballSub (w.1.adicCompletion E) n r hr0 hr1
  obtain ⟨hK'I, hK'd⟩ := ballLev _ n r hr0 hr1 K' hK'
  have mK' : ∀ {g}, g ∈ K' ↔ g ∈ ball n r := fun {g} => by rw [← SetLike.mem_coe, hK']
  obtain ⟨D₀, hD₀, hD₀c⟩ := sr3 r hr1
  have hDc : IsCompact ((D₀.map (nT n N) : Subgroup _) : Set (Fin n → (v.adicCompletion F)ˣ)) := by
    rw [Subgroup.coe_map]
    exact hD₀c.image hNc
  have hDv : ∀ d ∈ D₀.map (nT n N), ∀ i, valuation (v.adicCompletion F) (d i : v.adicCompletion F) = 1 := by
    rintro _ ⟨u, hu, rfl⟩ i
    have h1 : valuation (w.1.adicCompletion E) (u i : w.1.adicCompletion E) = 1 :=
      val_near hr1 ((hD₀ u).1 hu i)
    refine val_down (k' := w.1.adicCompletion E) _ ?_
    change valuation (w.1.adicCompletion E) (algebraMap _ _ (N (u i) : v.adicCompletion F)) = 1
    rw [← hc, hnorm.prod, map_prod]
    exact Finset.prod_eq_one fun j _ => (val_iter σw hnorm.cyc.isom j _).trans h1
  obtain ⟨K, hK, hKI, hKd⟩ := levOf _ n r' hr'0 hr'1 _ hDc hDv
  obtain ⟨t₀, ht₀⟩ := sr5
  have hset : ∀ T : Fin n → (w.1.adicCompletion E)ˣ, {x | ∃ d ∈ D₀.map (nT n N), x = nT n N T * d} =
      nrmSet (v.adicCompletion F) r T := fun T => by
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, (hD₀ u).1 hu, by rw [← map_mul, hnT]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨nT n N u, ⟨u, (hD₀ u).2 hu, rfl⟩, by rw [← map_mul, hnT]⟩
  refine ⟨K', fun g hg => hball (mK'.1 hg), K, ?_, hK'I, hKI, fun g => ?_, (c : ℂ), t₀, ?_, ht₀, fun t ht => ?_⟩
  · intro g hg
    obtain ⟨a, ha', _, ⟨u, hu, rfl⟩, rfl⟩ := (hK g).1 hg
    exact U.mul_mem (hball' ha') (hnear u ((hD₀ u).1 hu))
  · rw [mK', mK']
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have e : ((Loc.sg σw g : GL (Fin n) (w.1.adicCompletion E)) : Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j =
        σw ((g : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) := by
      rw [map_sub]
      congr 1
      by_cases h : i = j
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
    rw [e, hnorm.cyc.isom]
  · exact_mod_cast hcpos.ne'
  · obtain ⟨-, -, hm', hnS⟩ := hm _ (sr6 t₀ t ht₀ ht)
    have e1 : el K' (t₀ * t) = (elemSet r {t₀ * t}).indicator 1 := by
      rw [el, hK'd]
      rfl
    have e2 : el K (nT n N (t₀ * t)) = (elemSet r' (nrmSet (v.adicCompletion F) r (t₀ * t))).indicator 1 := by
      rw [el, hKd, hset]
      rfl
    refine ⟨?_, ?_⟩
    · rw [e1, e2]
      exact hm'
    · rw [hKd, hset]
      exact hnS
