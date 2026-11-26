module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TefFinrank

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiRatio
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PsiMulVec
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FeIsField
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ToMatrixMulVec
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ}

abbrev Wd (e : Matrix (Fin N) (Fin N) k) : Submodule k (Fin N → k) := LinearMap.range e.mulVecLin

lemma mat_ext {b b' : Matrix (Fin N) (Fin N) k} (h : ∀ v, b *ᵥ v = b' *ᵥ v) : b = b' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma toMatrix'_mulVec' (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma W_fix {e : Matrix (Fin N) (Fin N) k} (hid : IsIdempotentElem e) {w : Fin N → k} (hw : w ∈ Wd e) :
    e *ᵥ w = w := by
  obtain ⟨v, rfl⟩ := hw
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hid.eq]

lemma W_stable {e a : Matrix (Fin N) (Fin N) k} (hc : a * e = e * a) {w : Fin N → k} (hw : w ∈ Wd e) :
    a *ᵥ w ∈ Wd e := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨a *ᵥ v, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc]⟩

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def rho (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) : A →ₐ[k] Module.End k (Wd e) where
  toFun a := (a.1.mulVecLin).restrict (fun w hw => W_stable (hA _ a.2 _ he) hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 * b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (b.1 *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec]
  map_zero' := by ext w; simp
  map_add' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 + b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (w : Fin N → k) + b.1 *ᵥ (w : Fin N → k)
    rw [Matrix.add_mulVec]
  commutes' r := by ext w; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

lemma rho_apply (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := rfl

abbrev Pe (e : Matrix (Fin N) (Fin N) k) : (Fin N → k) →ₗ[k] Wd e := LinearMap.rangeRestrict e.mulVecLin

lemma Pe_surj (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := LinearMap.surjective_rangeRestrict _

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def Th (e : Matrix (Fin N) (Fin N) k) : Module.End k (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun f := LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e)
  map_add' f g := by rw [← map_add (f := _)]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1

lemma Th_mulVec (f : Module.End k (Wd e)) (v : Fin N → k) : Th e f *ᵥ v = (f (Pe e v) : Fin N → k) := by
  show LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e) *ᵥ v = _
  exact toMatrix'_mulVec' _ v

lemma Th_inj : Function.Injective (Th (k := k) (N := N) e) := by
  intro f g h
  ext w : 1
  obtain ⟨v, rfl⟩ := Pe_surj e w
  have := congrArg (· *ᵥ v) h
  simp only [Th_mulVec] at this
  exact Subtype.ext this

variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

lemma Th_rho (a : A) : Th e (rho hA he a) = e * a.1 := by
  apply mat_ext; intro v
  rw [Th_mulVec, rho_apply]
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA _ a.2 _ he]

abbrev Fe : Subalgebra k (Module.End k (Wd e)) := (rho hA he).range

lemma map_Th_Fe : (Fe hA he).toSubmodule.map (Th e) = A.toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.1, a.2, by simp [Th_rho hA he]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho hA he ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, by simp [Th_rho hA he]⟩

lemma Fe_isField (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) : IsField (Fe hA he) := by
  have hW : ∃ v : Fin N → k, e *ᵥ v ≠ 0 := by
    by_contra h; push Not at h; exact hne (mat_ext fun v => by simp [h v])
  obtain ⟨v₀, hv₀⟩ := hW
  refine ⟨⟨0, 1, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (fun x : Fe hA he => ((x.1 (Pe e v₀) : Wd e) : Fin N → k)) h
    change 0 = e *ᵥ v₀ at this
    exact hv₀ this.symm
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show rho hA he a * rho hA he b = rho hA he b * rho hA he a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ a.2 _ b.2)
  · rintro ⟨_, a, rfl⟩ hx
    have hea : e * a.1 ≠ 0 := by
      intro h0; apply hx; apply Subtype.ext
      ext w : 1; apply Subtype.ext
      obtain ⟨v, rfl⟩ := Pe_surj e w
      show a.1 *ᵥ (e *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hA _ a.2 _ he, h0, Matrix.zero_mulVec]
    rcases hf a.1 a.2 with h0 | ⟨b, hb, hab⟩
    · exact absurd h0 hea
    refine ⟨⟨rho hA he ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    ext w : 1; apply Subtype.ext
    obtain ⟨v, rfl⟩ := Pe_surj e w
    show a.1 *ᵥ (b *ᵥ (e *ᵥ v)) = e *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hA _ hb _ he, ← mul_assoc,
      hA _ a.2 _ he, hab]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

instance Fe_tower : IsScalarTower k (Fe hA he) (Wd e) := ⟨fun _ _ _ => rfl⟩

def Psi : Module.End (Fe hA he) (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun φ := Th e (φ.restrictScalars k)
  map_add' f g := by rw [← map_add (f := _)]; rfl
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; rfl

lemma Psi_mulVec (φ : Module.End (Fe hA he) (Wd e)) (v : Fin N → k) :
    Psi hA he φ *ᵥ v = (φ (Pe e v) : Fin N → k) := Th_mulVec (φ.restrictScalars k) v

lemma Psi_inj : Function.Injective (Psi hA he) := by
  intro f g h
  have := Th_inj h
  ext w : 1
  exact congrArg (fun F : Module.End k (Wd e) => F w) this

lemma Pe_smul (a : A) (v : Fin N → k) :
    Pe e (a.1 *ᵥ v) = (⟨rho hA he a, a, rfl⟩ : Fe hA he) • Pe e v := by
  apply Subtype.ext
  show e *ᵥ (a.1 *ᵥ v) = a.1 *ᵥ (e *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA _ a.2 _ he]

def phiOf (c : Matrix (Fin N) (Fin N) k) (hc : ∀ a ∈ A, a * c = c * a) : Module.End (Fe hA he) (Wd e) where
  toFun w := ⟨c *ᵥ (w : Fin N → k), W_stable (hc e he).symm w.2⟩
  map_add' w w' := by apply Subtype.ext; exact Matrix.mulVec_add c w.1 w'.1
  map_smul' := by
    rintro ⟨_, a, rfl⟩ w
    apply Subtype.ext
    show c *ᵥ (a.1 *ᵥ (w : Fin N → k)) = a.1 *ᵥ (c *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc _ a.2]

lemma range_Psi (hid : IsIdempotentElem e) :
    LinearMap.range (Psi hA he) =
      (Subalgebra.centralizer k (A : Set (Matrix (Fin N) (Fin N) k))).toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨Psi hA he φ, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      intro a ha
      apply mat_ext; intro v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Psi_mulVec, Psi_mulVec,
        Pe_smul hA he ⟨a, ha⟩, map_smul]
      rfl
    · apply mat_ext; intro v
      simp only [LinearMap.mulLeft_apply]
      rw [← Matrix.mulVec_mulVec, Psi_mulVec]
      exact W_fix hid (φ (Pe e v)).2
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hc
    refine ⟨phiOf hA he c hc, ?_⟩
    apply mat_ext; intro v
    rw [Psi_mulVec]
    show c *ᵥ (e *ᵥ v) = (e * c) *ᵥ v
    rw [Matrix.mulVec_mulVec, hc e he]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem pi_ratio {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {e : Matrix (Fin N) (Fin N) k} (he : e ∈ A) (hid : IsIdempotentElem e) (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) :
    0 < Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∧
      Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∣ e.rank ∧
      Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
        (e.rank / Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))) ^ 2 *
          Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
  classical
  let _ : Field (Fe hA he) := (Fe_isField hA he hne hf).toField
  have hFd : Module.finrank k (Fe hA he) = Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
    rw [← map_Th_Fe hA he, ← (Submodule.equivMapOfInjective (Th e) Th_inj _).finrank_eq,
      Subalgebra.finrank_toSubmodule]
  have hD : Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
      Module.finrank k (Module.End (Fe hA he) (Wd e)) := by
    unfold cenSub
    rw [← range_Psi hA he hid, LinearMap.finrank_range_of_inj (Psi_inj hA he)]
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_end k (Fe hA he) (Wd e)
  have h2 := Module.finrank_mul_finrank k (Fe hA he) (Wd e)
  have hr : e.rank = Module.finrank k (Wd e) := rfl
  have hd0 : 0 < Module.finrank k (Fe hA he) := Module.finrank_pos
  rw [← hFd, hD, hr]
  set d := Module.finrank k (Fe hA he)
  set m := Module.finrank (Fe hA he) (Wd e)
  rw [← h2] at h1 ⊢
  refine ⟨hd0, dvd_mul_right _ _, ?_⟩
  rw [Nat.mul_div_cancel_left m hd0]
  apply Nat.eq_of_mul_eq_mul_left hd0
  rw [h1]; ring

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RankPosOfNe
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open Matrix

variable {k : Type} [Field k] {N : ℕ}

theorem rank_add_orth {a b : Matrix (Fin N) (Fin N) k} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) : (a + b).rank = a.rank + b.rank := by
  have hsup : LinearMap.range (a + b).mulVecLin = LinearMap.range a.mulVecLin ⊔ LinearMap.range b.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨a *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, ha.eq, hba, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨b *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hb.eq, hab, zero_add]
  have hinf : LinearMap.range a.mulVecLin ⊓ LinearMap.range b.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    have h1 : a *ᵥ (a *ᵥ u) = a *ᵥ u := by rw [Matrix.mulVec_mulVec, ha.eq]
    have h2 : a *ᵥ (b *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hab, Matrix.zero_mulVec]
    rw [← hv, h2] at h1
    rw [Submodule.mem_bot, ← hv, ← h1]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range a.mulVecLin) (LinearMap.range b.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  exact h

theorem idem_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => ho i hi j hj (Ne.symm hji)) (fun h => absurd hi h)]
  exact hid i hi

theorem rank_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hid' : ∀ j ∈ s, IsIdempotentElem (e j) := fun j hj => hid j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → e j * e l = 0 := fun j hj l hl h =>
      ho j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) h
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hid' ho']
    refine rank_add_orth (hid i (Finset.mem_insert_self i s)) (idem_sum_orth s e hid' ho') ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => ho j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (fun h => hi (h ▸ hj))

theorem rank_pos_of_ne {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have : Matrix.toLin' e = 0 := h0
  simpa using congrArg LinearMap.toMatrix' this

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SqSumLe
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

theorem sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]

theorem sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hne : (s.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := hne
  have hM : 1 ≤ ∑ i ∈ s.erase a, m i :=
    (hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have ih := sq_sum_le (s.erase a) m
  rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]
  have := hm a ha
  nlinarith

theorem num_fib {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

abbrev dA (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (e : Matrix (Fin N) (Fin N) k) : ℕ :=
  finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))

theorem ratio_of (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) :
    0 < dA A e ∧ dA A e ∣ e.rank ∧
      finrank k ((cenSub A).map (LinearMap.mulLeft k e)) / dA A e = (e.rank / dA A e) ^ 2 := by
  obtain ⟨h0, hd, h⟩ := pi_ratio hA.1 he.1 he.2.1 he.2.2.1 (fun a ha => pi_field hA he ha)
  exact ⟨h0, hd, by rw [h, Nat.mul_div_cancel _ h0]⟩

theorem mu_sum (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) :
    mu A = ∑ e ∈ (pi_fin hA).toFinset, (e.rank / dA A e) ^ 2 := by
  unfold mu
  rw [finsum_mem_eq_finite_toFinset_sum _ (pi_fin hA)]
  exact Finset.sum_congr rfl fun e he => (ratio_of A hA ((Set.Finite.mem_toFinset _).mp he)).2.2

theorem m_pos (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) : 1 ≤ e.rank / dA A e := by
  obtain ⟨h0, hd, -⟩ := ratio_of A hA he
  have hr := rank_pos_of_ne he.2.2.1
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_div_cancel_left _ h0]
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp at hc; omega
  · exact h

open Classical in
theorem dich_pt {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
    {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    mu (Sx D x) < mu Z ∨ ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hS := sx_cr D hZ hx hχ
  set P := (pi_fin hS).toFinset with hP
  set Q := (pi_fin hZ).toFinset with hQ
  have mP : ∀ {e}, e ∈ P ↔ e ∈ primIdem (Sx D x) := fun {e} => Set.Finite.mem_toFinset _
  have mQ : ∀ {f}, f ∈ Q ↔ f ∈ primIdem Z := fun {f} => Set.Finite.mem_toFinset _

  have hsplit : mu (Sx D x) = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
    rw [mu_sum _ hS]
    calc ∑ e ∈ P, (e.rank / dA (Sx D x) e) ^ 2
        = ∑ e ∈ P, ∑ f ∈ Q, if e * f = e then (e.rank / dA (Sx D x) e) ^ 2 else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨f₀, hf₀, hef₀⟩ := ef_exists D hZ hx hχ (mP.mp he)
          rw [Finset.sum_eq_single_of_mem f₀ (mQ.mpr hf₀) fun f hf hne => if_neg fun h =>
            hne (ef_unique D hZ hx hχ (mP.mp he) (mQ.mp hf) hf₀ h hef₀), if_pos hef₀]
      _ = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun f _ => (Finset.sum_filter _ _).symm

  have hfib : ∀ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 ≤ (f.rank / dA Z f) ^ 2 ∧
      (∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 = (f.rank / dA Z f) ^ 2 →
        f ∈ primIdem (Sx D x) ∧ dA (Sx D x) f ≤ dA Z f) := by
    intro f hf
    have hf' := mQ.mp hf
    have hmem : ∀ e ∈ P.filter (fun e => e * f = e), e ∈ primIdem (Sx D x) ∧ e * f = e := fun e he =>
      ⟨mP.mp (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    have hfs := fib_sum D hZ hx hχ hf'
    obtain ⟨hdF, hdvF, -⟩ := ratio_of Z hZ hf'
    have hsum : f.rank / dA Z f * dA Z f =
        ∑ e ∈ P with e * f = e, e.rank / dA (Sx D x) e * dA (Sx D x) e := by
      rw [Nat.div_mul_cancel hdvF]
      conv_lhs => rw [← hfs]
      rw [rank_sum_orth _ _ (fun e he => (hmem e he).1.2.1)
        (fun e he e' he' hne => pi_orth hS (hmem e he).1 (hmem e' he').1 hne)]
      exact Finset.sum_congr rfl fun e he => (Nat.div_mul_cancel (ratio_of _ hS (hmem e he).1).2.1).symm
    obtain ⟨hle, heq⟩ := num_fib (P.filter (fun e => e * f = e)) (fun e => e.rank / dA (Sx D x) e)
      (fun e => dA (Sx D x) e) (f.rank / dA Z f) (dA Z f) hdF (fun e he => m_pos _ hS (hmem e he).1)
      (fun e he => dim_le D hZ hx hχ (hmem e he).1 hf' (hmem e he).2) hsum
    refine ⟨hle, fun h => ?_⟩
    have hne : (P.filter (fun e => e * f = e)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hfs
      exact hf'.2.2.1 hfs.symm
    obtain ⟨e, he⟩ := hne
    obtain ⟨hsing, hde⟩ := heq h ⟨e, he⟩ e he
    have hef : e = f := by rw [← hfs, hsing, Finset.sum_singleton]
    subst hef
    exact ⟨(hmem e he).1, hde⟩

  have hle : mu (Sx D x) ≤ mu Z := by
    rw [hsplit, mu_sum _ hZ]
    exact Finset.sum_le_sum fun f hf => (hfib f hf).1
  by_cases hlt : mu (Sx D x) < mu Z
  · exact Or.inl hlt
  right
  have heq : mu (Sx D x) = mu Z := le_antisymm hle (not_lt.mp hlt)
  rw [hsplit, mu_sum _ hZ] at heq
  have hall := (Finset.sum_eq_sum_iff_of_le fun f hf => (hfib f hf).1).mp heq
  exact zn_of_eq D hZ hx hχ fun f hf => (hfib f (mQ.mpr hf)).2 (hall f (mQ.mpr hf))

variable (k) in
theorem dich : PositivityTheory.RgUd.TP.Desc.Piece.Dich k := by
  intro N q Z hZ χ D τ x₀ hx₀
  exact dich_pt D hZ hx₀.1 hx₀.2.1

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
