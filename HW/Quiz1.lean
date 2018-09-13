-- Matthew Normansell (man9ej)

def and_assoc_r
  { P Q R : Prop }
  (pfPQ_R: (P ∧ Q) ∧ R) :
    (P ∧ (Q ∧ R)) :=
      begin
      have pfPQ := and.elim_left pfPQ_R,
      have pfR := and.elim_right pfPQ_R,
      have pfP := and.elim_left pfPQ,
      have pfQ := and.elim_right pfPQ,
      have pfQR := and.intro (pfQ) (pfR),
      have pfP_QR :=and.intro pfP pfQR,
      exact pfP_QR
      end

#check and_assoc_r
