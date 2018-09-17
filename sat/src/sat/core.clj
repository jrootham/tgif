(ns sat.core
  (:gen-class)
  (:require [clojure.set :refer [intersection difference union]])
  (:require [clojure.string :as str])
)

(defn parse-clause [line]
	(loop [literals (str/split line #" ") sat-true #{} sat-false #{}] 
		(if (empty? literals)

			{:sat-true sat-true :sat-false sat-false}

			(let 
				[
					this-one (first literals)
					remaining (rest literals)
				]

				(if (str/starts-with? this-one "~")
					(recur remaining sat-true (conj sat-false (subs this-one 1)))
					(recur remaining (conj sat-true this-one) sat-false)
				)
			)		
		)
	)
)

(defn get-cnf []
	(loop [line (read-line) result ()] 
		(if line
			(if (or (str/starts-with? line "~ ") (str/blank? line))
				(recur (read-line) result)
				(recur (read-line) (cons (parse-clause line) result)) 
			) 

			result
		)	
	)
)

(defn simplify [raw-cnf]
	(loop [clause-list raw-cnf result ()]
		(if (empty? clause-list)
			result
			(let 
				[
					clause (first clause-list)
					input-sat-true (get clause :sat-true)
					input-sat-false (get clause :sat-false)
					tautology (intersection input-sat-true input-sat-false)
					sat-true (difference input-sat-true tautology)
					sat-false (difference input-sat-false tautology)
				]
				(if (and (empty? sat-true) (empty? sat-false))
					(recur (rest clause-list) result)
					(recur (rest clause-list) (cons {:sat-true sat-true :sat-false sat-false} result))
				)
			)
		)
	)
)

(defn get-size [raw-cnf]
	(loop [clause-list raw-cnf literal-set #{}]
		(if (empty? clause-list)
			(count literal-set)
			(let
				[
					clause (first clause-list)					
					sat-true (get clause :sat-true)
					sat-false (get clause :sat-false)
				]
				(recur (rest clause-list) (union literal-set (union sat-true sat-false)))
			)
		)
	)
)

(declare scan-cnf)

(defn make-side [sat-set jump-level]
	{:sat-set sat-set :jump-level jump-level}
)

(defn make-clause [sat-true sat-false level-true level-false]
	{:true-side (make-side sat-true level-true) :false-side (make-side sat-false level-false)}
)

(defn make-cnf [raw-cnf infinity]
	(loop [clause-list raw-cnf result ()]
		(if (empty? clause-list)
			result
			(let
				[
					clause (first clause-list)					
					sat-true (get clause :sat-true)
					sat-false (get clause :sat-false)
				]
				(recur (rest clause-list) (cons (make-clause sat-true sat-false infinity infinity) result))
			)
		)
	)
)

(defn unit? [sat-true sat-false]
	(= 1 (+ (count sat-true) (count sat-false)))
)

(def empty-answer {:true-side #{} :false-side #{}})

(defn update-answer [assert-literals old-answer]
	{
		:true-side (union (get assert-literals :true-side) (get old-answer :true-side))
		:false-side (union (get assert-literals :false-side) (get old-answer :false-side))
	}
)

(defn get-try [cnf]
	(let
		[
			clause (first cnf)
			sat-true (get (get clause :true-side) :sat-set)
		]
		(if (empty? sat-true)
			(first (get (get clause :false-side) :sat-set))
			(first sat-true)
		)
	)
)

(defn first-try [options cnf]
	{:true-side #{(get-try cnf)} :false-side #{}}
)

(defn second-try [options cnf]
	{:true-side #{} :false-side #{(get-try cnf)}}
)

(defn descend [options infinity level cnf accumulator stats]
	(let
		[
			true-set (get accumulator :true-set)
			false-set (get accumulator :false-set)
			true-unit (get accumulator :true-unit)
			false-unit (get accumulator :false-unit)
			diff-true (difference true-set false-set)
			diff-false (difference false-set true-set)
			assert-true (union (difference true-set false-set) true-unit)
			assert-false (union (difference false-set true-set) false-unit)
		]
		(if (and (empty? assert-true) (empty? assert-false))
			(let
				[
					new-level (+ level 1)
					assert-literals (first-try options cnf)
					result (scan-cnf options infinity cnf new-level assert-literals stats)
				]
				(if (get result :sat)
					result
					(scan-cnf options infinity cnf new-level (second-try options cnf) stats)
				)
			)
			(scan-cnf options infinity cnf level {:true-side assert-true :false-side assert-false} stats)
		)
	)
)

(defn end-scan [options infinity sat level cnf assert-literals accumulator stats]
	(if sat
		(if (empty? cnf)
			{:sat true :answer (update-answer assert-literals empty-answer) :stats stats}
			(if (empty? (intersection (get accumulator :true-unit) (get accumulator :false-unit)))
				(let [result (descend options infinity level cnf accumulator stats)]
					(if (get result :sat)
						{:sat true :answer (update-answer assert-literals (get result :answer)) :stats stats}
						result
					)
				)
				{:sat false :level level :stats stats}
			)
		)
		{:sat false :level level :stats stats}
	)
)

(defn reduce-clause [options cnf sat level clause assert-true assert-false accumulator stats]
	(let 
		[
			sat-true (get (get clause :true-side) :sat-set)
			sat-false (get (get clause :false-side) :sat-set)
			new-sat-true (difference sat-true assert-false)
			new-sat-false (difference sat-false assert-true)
		]
		(if (and (empty? new-sat-true) (empty? new-sat-false))
			(let 
				[
					tmp-level (get (get clause (get (get options :which-first) :jump)) :jump-level)
					new-level (min level tmp-level)
				]
				{:sat false :level new-level :cnf () :accumulator {} :stats stats}
			)
			(let
				[
					level-true (get (get clause :true-side) :jump-level)
					level-false (get (get clause :false-side) :jump-level)
					new-level-true level-true
					new-level-false level-false
					true-set (union (get accumulator :true-set) new-sat-true)
					false-set (union (get accumulator :false-set) new-sat-false)
					true-unit (union (get accumulator :true-unit) (if (unit? sat-true sat-false) sat-true #{}))
					false-unit (union (get accumulator :false-unit) (if (unit? sat-true sat-false) sat-false #{}))
				]
				{
					:sat sat
					:level level
					:cnf (cons (make-clause new-sat-true new-sat-false new-level-true new-level-false) cnf)
					:accumulator
						{
							:true-set true-set
							:false-set false-set
							:true-unit true-unit
							:false-unit false-unit
						}
					:stats stats
				}
			)
		)
	)
)

(defn do-clause [options sat level clause cnf assert-literals accumulator stats]
	(let
		[
			sat-true (get (get clause :true-side) :sat-set)
			sat-false (get (get clause :false-side) :sat-set)
			assert-true (get assert-literals :true-side)
			assert-false (get assert-literals :false-side)
		]
		(if (and 
				(empty? (intersection assert-true sat-true))
				(empty? (intersection assert-false sat-false))
			)
			(reduce-clause options cnf sat level clause assert-true assert-false accumulator stats)
			{:sat sat :level level :cnf cnf :accumulator accumulator :stats stats}
		)
	)
)

(defn extract [clause]
	(let 
		[	
			true-side (get (get clause :true-side) :sat-set)
			false-side (get (get clause :false-side) :sat-set)
		]
		{:true-side true-side :false-side false-side}
	)
)

(defn display-cnf [cnf]
	(println (map extract cnf))
)

(defn scan-cnf [options infinity base-cnf level assert-literals start-stats]
	(loop 
		[
			clause-list base-cnf 
			sat true
			jump-level infinity
			cnf ()
			accumulator {:true-set #{} :false-set #{} :true-unit #{} :false-unit #{}} 
			stats start-stats
		]
		(if (empty? clause-list)
			(end-scan options infinity sat level cnf assert-literals accumulator stats)
			(let
				[
					clause (first clause-list)					
					clause-result (do-clause options sat level clause cnf assert-literals accumulator stats)
					new-sat (get clause-result :sat)
					new-level (get clause-result :level)
					new-cnf (get clause-result :cnf)
					new-accumulator (get clause-result :accumulator)
					new-stats (get clause-result :stats)
				]
				(recur (rest clause-list) new-sat new-level new-cnf new-accumulator new-stats)
			)
		)
	)
)

(defn -main
	"SAT solver"
	[& args]
	(let 
		[
			raw-cnf (simplify (get-cnf))
			infinity (+ 1 (get-size raw-cnf))
			options {:which-first {:first true :second false :jump :false-side}}
		]
		(println (scan-cnf options infinity (make-cnf raw-cnf infinity) 0 {:true-side #{} :false-side #{}} {}))
	)
)

