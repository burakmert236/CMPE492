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
(declare-fun G9 () Bool)
(declare-fun G11 () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R3 () Bool)
(declare-fun R4 () Bool)
(declare-fun CCL1 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 R2 )))
(assert (=> G3 (or R3  )))
(assert (=> G7 (or R4  )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G3 )) (=> R1 G1 )))
(assert (and (= R2 (and G2 )) (=> R2 G1 )))
(assert (and (= R3 (and G4 G5 )) (=> R3 G3 )))
(assert (and (= R4 (and G8 G9 )) (=> R4 G7 )))

;;%%%%
;Mandatory goals
;%%%%

;;%%%%
;Implemented goals
;%%%%

;;%%%%
;Precedence relationships
;%%%%

;;%%%%
;Contributions
;%%%%
(assert (= CCL1 (and G1 G7)))
(assert-soft (not CCL1) :weight 10 :id PCC)

;;%%%%
;Goal Attributes
;%%%%
(assert-soft (not G1) :weight 1 :id cost)
(assert-soft (not G1) :weight 1 :id value)
(assert-soft (not G2) :weight 1 :id cost)
(assert-soft (not G2) :weight 1 :id value)
(assert-soft (not G3) :weight 1 :id cost)
(assert-soft (not G3) :weight 1 :id value)
(assert-soft (not G4) :weight 1 :id cost)
(assert-soft (not G4) :weight 1 :id value)
(assert-soft (not G5) :weight 1 :id cost)
(assert-soft (not G5) :weight 1 :id value)
(assert-soft (not G7) :weight 1 :id cost)
(assert-soft (not G7) :weight 1 :id value)
(assert-soft (not G8) :weight 1 :id cost)
(assert-soft (not G8) :weight 1 :id value)
(assert-soft (not G9) :weight 1 :id cost)
(assert-soft (not G9) :weight 1 :id value)

;;%%%%
;Exclusion
;%%%%
(assert (not (and G8 G5)))

;;%%%%
;Leaf Nodes
;%%%%
(assert-soft (not G2 ) :id sat_tasks)
(assert-soft (not G3 ) :id sat_tasks)

;;%%%%
;Root Nodes
;%%%%
(assert-soft (not G1 ) :id unsat_requirements)
(assert-soft (not G4 ) :id unsat_requirements)
(assert-soft (not G5 ) :id unsat_requirements)
(assert-soft (not G7 ) :id unsat_requirements)
(assert-soft (not G8 ) :id unsat_requirements)
(assert-soft (not G9 ) :id unsat_requirements)
(assert-soft (not G11 ) :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(declare-fun cost.auto () Real)
(assert (= cost.auto (- cost 0)))
(declare-fun value.auto () Real)
(assert (= value.auto (- value 0)))


(minimize cost.auto)
(maximize value.auto)
(maximize NCC)
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)
