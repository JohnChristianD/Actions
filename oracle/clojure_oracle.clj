(defn sigmoid [z]
  (/ 1.0 (+ 1.0 (Math/exp (- z)))))

(defn lstm [x h c]
  (let [z (+ x h)
        f (sigmoid z)
        i (sigmoid z)
        o (sigmoid z)
        g (Math/tanh z)
        c2 (+ (* f c) (* i g))
        h2 (* o (Math/tanh c2))]
    [h2 c2]))

(doseq [[x h c] [[0.2 -0.1 0.3] [1.0 0.2 -0.4] [-0.7 0.5 0.1]]]
  (let [[lh lc] (lstm x h c)]
    (println (format "%.12f,%.12f,%.12f,%.12f,%.12f"
                     x h c lh lc))))
