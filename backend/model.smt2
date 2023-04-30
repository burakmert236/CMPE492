;; activate model generation
(set-option :produce-models true)
(set-option :opt.priority box)

;;%%%%
;Declaration of Goal, Assumption and Refinement Propostions
;%%%%
(declare-fun G1 () Bool)
(declare-fun G2 () Bool)
(declare-fun G3 () Bool)
(declare-fun G4 () Bool)
(declare-fun G5 () Bool)
(declare-fun R1 () Bool)
(declare-fun R2 () Bool)
(declare-fun R3 () Bool)

;;%%%%
;Close-world
;%%%%
(assert (=> G1 (or R1 R2 )))
(assert (=> G4 (or R3  )))

;;%%%%
;Refinement-Goal relationships
;%%%%
(assert (and (= R1 (and G2 )) (=> R1 G1 )))
(assert (and (= R2 (and G3 )) (=> R2 G1 )))
(assert (and (= R3 (and G1 G5 )) (=> R3 G4 )))

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

;;%%%%
;Leaf Nodes
;%%%%
(assert-soft (not G2 ) :id sat_tasks)
(assert-soft (not G3 ) :id sat_tasks)
(assert-soft (not G5 ) :id sat_tasks)

;;%%%%
;Root Nodes
;%%%%
(assert-soft (not G4 ) :id unsat_requirements)

;;%%
;;Optimization:
;;%%
(declare-fun cost.auto () Real)
(assert (= cost.auto (- cost 0)))
(declare-fun value.auto () Real)
(assert (= value.auto (- value 0)))


(minimize (+ cost.auto value.auto))

(maximize (+ NCC PVC))
(minimize unsat_requirements)
(minimize sat_tasks)
(check-sat)
(get-objectives)
(load-objective-model 1)
(get-model)
(exit)
