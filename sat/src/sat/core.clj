(ns sat.core
  (:gen-class)
  (:require [clojure.set :refer [intersection difference union]])
  (:require [clojure.string :as str])
)

(defn set-add [the-set member]
	(union the-set (set (list member)))
)

(defn fill-clause [literals sat-true sat-false]
	(if (empty? literals)

		(cons sat-true (list sat-false))

		(let 
			[
				this-one (first literals)
				remaining (rest literals)
			]

			(if (str/starts-with? this-one "~")
				(fill-clause remaining sat-true (set-add sat-false (subs this-one 1)))
				(fill-clause remaining (set-add sat-true this-one) sat-false)
			)
		)		
	)
)

(defn parse-clause [line]
	(fill-clause (str/split line #" ") (set nil) (set nil))
)

(defn get-cnf [result]
	(let [line (read-line)] 
		(if line
			(if (or (str/starts-with? line "~ ") (str/blank? line))
				(get-cnf result)
				(cons (parse-clause line) (get-cnf result)) 
			) 
			result
		)	
	)
)

(defn -main
  "SAT solver"
  [& args]
  (println (get-cnf nil))
)

