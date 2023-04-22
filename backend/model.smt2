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
(declare-fun G6 () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R3 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 R2 )))
(assert (=> G3 (or R3  )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G2 )) (=> R1 G1 )))
(assert (and (= R2 (and G3 )) (=> R2 G1 )))
(assert (and (= R3 (and G4 G5 G6 )) (=> R3 G3 )))

;;%%%%
;Mandatory goals
;%%%%
(assert G1)

;;%%%%
;Precedence relationships
;%%%%

;;%%
;;Optimization:
;;%%
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)
