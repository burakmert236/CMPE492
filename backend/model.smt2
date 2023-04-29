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
(declare-fun G8 () Bool)
(declare-fun G9 () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R4 () Bool)
(declare-fun R3 () Bool)
(declare-fun VCL1 () Bool)
(declare-fun CCL1 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 )))
(assert (=> G3 (or R3 )))
(assert (=> G4 (or R4  )))
(assert (=> G5 (or R2 )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G3 )) (=> R1 G1 )))
(assert (and (= R2 (and G8 )) (=> R2 G5 )))
(assert (and (= R3 (and G9 )) (=> R3 G3 )))
(assert (and (= R4 (and G5 G6 )) (=> R4 G4 )))

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
(assert (= VCL1 (and G1 G4)))
(assert-soft (not VCL1) :weight 7 :id PVC)
(assert (= CCL1 (and G2 G1)))
(assert-soft (not CCL1) :weight 1 :id NCC)

;;%%%%
;Goal Attributes
;%%%%
(assert-soft (not G1) :weight 3 :id cost)
(assert-soft (not G1) :weight 1 :id value)
(assert-soft (not G2) :weight 1 :id cost)
(assert-soft (not G2) :weight 5 :id value)
(assert-soft (not G3) :weight 1 :id cost)
(assert-soft (not G3) :weight 1 :id value)
(assert-soft (not G3) :weight 2 :id effort)
(assert-soft (not G4) :weight 1 :id cost)
(assert-soft (not G4) :weight 1 :id value)
(assert-soft (not G5) :weight 1 :id cost)
(assert-soft (not G5) :weight 1 :id value)
(assert-soft (not G6) :weight 1 :id cost)
(assert-soft (not G6) :weight 1 :id value)
(assert-soft (not G8) :weight 1 :id cost)
(assert-soft (not G8) :weight 1 :id value)
(assert-soft (not G9) :weight 1 :id cost)
(assert-soft (not G9) :weight 1 :id value)

;;%%%%
;Leaf Nodes
;%%%%
(assert-soft (not G6 ) :id sat_tasks)
(assert-soft (not G8 ) :id sat_tasks)
(assert-soft (not G9 ) :id sat_tasks)

;;%%%%
;Root Nodes
;%%%%
(assert-soft (not G1 ) :id unsat_requirements)
(assert-soft (not G2 ) :id unsat_requirements)
(assert-soft (not G4 ) :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)
