;; activate model generation
(set-option :produce-models true)
(set-option :opt.priority lex)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool)
(declare-fun G2 () Bool)
(declare-fun G3 () Bool)
(declare-fun G4 () Bool)
(declare-fun G5 () Bool)
(declare-fun G7 () Bool)
(declare-fun G8 () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R4 () Bool)
(declare-fun R3 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 R2 )))
(assert (=> G3 (or R4  )))
(assert (=> G5 (or R3 )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G2 )) (=> R1 G1 )))
(assert (and (= R2 (and G3 )) (=> R2 G1 )))
(assert (and (= R3 (and G8 )) (=> R3 G5 )))
(assert (and (= R4 (and G4 G5 G7 )) (=> R4 G3 )))

