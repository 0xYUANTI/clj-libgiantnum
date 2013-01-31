;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tree-based arithmetic and Compressed Representations of Giant Numbers.
;;; http://arxiv.org/abs/1301.0114
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_* Declarations =====================================================
(ns clj-giant.core
  (:use clojure.test))

(declare B O I)
(declare T V W)

;;;_* Code =============================================================
;;;_ * Generic operations ----------------------------------------------
(defprotocol N
  "A representation-independent abstraction of natural numbers."
  (eq [x y] "Structural equality.")
  (e  [x]   "The empty sequence of binary digits.")
  (o  [x]   "Add 0 to a binary string.")
  (o' [x]   "Remove 0 from a binary string.")
  (i  [x]   "Add 1 to a binary string.")
  (i' [x]   "Remove 1 from a binary string.")
  (o_ [x]   "True iff binary string ends with a 0."))

(defn e_ [x] (eq x (e x)))
(defn i_ [x] (not (or (e_ x) (o_ x))))

(defn s
  "Successor."
  [x]
  (cond
   (e_ x) (o x)
   (o_ x) (i (o' x))
   (i_ x) (o (s (i' x)))))

(defn s'
  "Predecessor."
  [x]
  (cond
   (eq x (o (e x))) (e x)
   (i_ x)           (o (i' x))
   (o_ x)           (i (s' (o' x)))))

(defn all-from [x] (iterate s x))

(defn add [x y]
  (cond
   (e_ x)               y
   (e_ y)               x
   (and (o_ x) (o_ y))  (i (add (o' x) (o' y)))
   (and (o_ x) (i_ y))  (o (s (add (o' x) (i' y))))
   (and (i_ x) (o_ y))  (o (s (add (i' x) (o' y))))
   (and (i_ x) (i_ y))  (i (s (add (i' x) (i' y))))))

(defn sub [x y]
  (cond
   (e_ y)              x
   (and (o_ x) (o_ y)) (s' (o (sub (o' x) (o' y))))
   (and (o_ x) (i_ y)) (s' (s' (o (sub (o' x) (i' y)))))
   (and (i_ x) (o_ y)) (o (sub (i' x) (o' y)))
   (and (i_ x) (i_ y)) (s' (o (sub (i' x) (i' y))))))

(defn cmp [x y]
  (letfn [(down [ord] (if (= ord 0) -1 ord))
          (up   [ord] (if (= ord 0) +1 ord))]
    (cond
     (and (e_ x) (e_ y)) 0
     (e_ x)              -1
     (e_ y)              +1
     (and (o_ x) (o_ y)) (cmp (o' x) (o' y))
     (and (i_ x) (i_ y)) (cmp (i' x) (i' y))
     (and (o_ x) (i_ y)) (down (cmp (o' x) (i' y)))
     (and (i_ x) (o_ y)) (up   (cmp (i' x) (o' y))))))

(defn min2 [x y] (if (= -1 (cmp x y)) x y))
(defn max2 [x y] (if (= -1 (cmp x y)) y x))

(defn mul [x y]
  (letfn [(m [x y]
            (cond
             (e_ x) y
             (o_ x) (o (m (o' x) y))
             (i_ x) (s (add y (o (m (i' x) y))))))]
    (cond
     (e_ x) (e x)
     (e_ y) (e x)
     :else  (s (m (s' x) (s' y))))))

(defn db [x] (s' (o x)))
(defn hf [x] (s (i' x)))

(defn pow [x y]
  (cond
   (e_ y) (o (e x))
   (o_ y) (mul x (pow (mul x x) (o' y)))
   (i_ y) (mul (mul x x) (pow (mul x x) (i' y)))))

(defn exp2 [x]
  (cond
   (e_ x) (o (e x))
   :else  (db (exp2 (s' x)))))

(defn leftshift [x y] (mul (exp2 x) y))

(defn div-and-rem [x y]
  (letfn [(try-to-double [x y k]
            (if (= -1 (cmp x y))
              (s' k)
              (recur x (db y) (s k))))
          (divstep [n m]
            (let [q (try-to-double n m (e n))
                  p (mul (exp2 q) m)]
              [q (sub n p)]))]
    (cond
     (= -1 (cmp x y))
     [(e x) x]
     (not (e_ y))
     (let [[qt rm] (divstep x y)
           [z r]   (div-and-rem rm y)
           q       (add (exp2 qt) z)]
       [q r]))))

(defn divide    [n m] (first  (div-and-rem n m)))
(defn remainder [n m] (second (div-and-rem n m)))

;;;_ * Misc instances --------------------------------------------------
(extend-type Long
  N
  (eq [x y] (= x y))

  (e  [_]   0)
  (o_ [x]   (odd? x))

  (o  [x]   (+ (* 2 x) 1))
  (o' [x]   (cond (and (odd? x) (> x 0)) (/ (- x 1) 2)))

  (i  [x]   (+ (* 2 x) 2))
  (i' [x]   (cond (and (even? x) (> x 0)) (/ (- x 2) 2))))

(defrecord Bee [ctor arg]
  N
  (eq [x y] (= x y))

  (e  [_]   (B))

  (o  [x]   (O x))
  (i  [x]   (I x))

  (o' [x]   (case (:ctor x) :O (:arg x)))
  (i' [x]   (case (:ctor x) :I (:arg x)))

  (o_ [x]   (= (:ctor x) :O)))

(defn B []  (Bee. :B nil))
(defn O [B] (Bee. :O B))
(defn I [B] (Bee. :I B))

(deftest arith-test
  (is (= (mul 10 5)                50))
  (is (= (exp2 5)                  32))
  (is (= (add (O (B)) (I (O (B)))) (O (I (B))))))

;;;_ * Trees -----------------------------------------------------------
(defrecord Tee [ctor arg1 arg2]
  N
  (eq [x y] (= x y))

  (e [_] (T))

  (o [x]
    (case (:ctor x)
      :T (V (T) ())
      :V (V (s (:arg1 x)) (:arg2 x))
      :W (V (T) (cons (:arg1 x) (:arg2 x)))))

  (i [x]
    (case (:ctor x)
      :T (W (T) ())
      :V (W (T) (cons (:arg1 x) (:arg2 x)))
      :W (W (s (:arg1 x)) (:arg2 x))))

  (o' [x]
    (assert (= :V (:ctor x)))
    (if (= (T) (:arg1 x))
      (if (= () (:arg2 x))
        (T)
        (W (first (:arg2 x)) (rest (:arg2 x))))
      (V (s' (:arg1 x)) (:arg2 x))))

  (i' [x]
    (assert (= :W (:ctor x)))
    (if (= (T) (:arg1 x))
      (if (= () (:arg2 x))
        (T)
        (V (first (:arg2 x)) (rest (:arg2 x))))
      (W (s' (:arg1 x)) (:arg2 x))))

  (o_ [x] (= :V (:ctor x))))

(defn T []     (Tee. :T nil nil))
(defn V [T Ts] (Tee. :V T   Ts))
(defn W [T Ts] (Tee. :W T   Ts))

(defn exp2' [x]
  (if (= :T (:ctor x))
    (V (T) ())
    (s (V (s' x) ()))))

(defn vmul [n y]
  (cond
   (= (T) n)        y
   (= (T) y)        (V (s' n) ())
   (= :V (:ctor y)) (V (add (s' n) (:arg1 y)) (:arg2 y))
   (= :W (:ctor y)) (V (s' n) (cons (:arg1 y) (:arg2 y)))))

(defn leftshift' [n y]
  (if (= (T) y)
    (T)
    (cond
     (o_ y) (s (vmul n     (s' y)))
     (i_ y) (s (vmul (s n) (s' y))))))

(defn view
  "View an X as a Y."
  [x y]
  (cond
   (e_ x) (e y)
   (o_ x) (o (view (o' x) y))
   (i_ x) (i (view (i' x) y))))

(defn t [x] (view x (T)))
(defn b [x] (view x (B)))
(defn n [x] (view x 0))

(deftest view-test
  (is (= (t 42)
         (W (V (T) ()) (list (T) (T) (T)))))
  (is (= (b (t 42))
         (I (I (O (I (O (B))))))))
  (is (= (n (b (t 42)))
         42)))

(deftest tee-test
  (is (= (t 5)
         (V (T) (list (T)))))
  (is (= (exp2' (t 5))
         (W (T) (list (V (V (T) ()) ())))))
  (is (= (n (exp2' (t 5)))
         32))
  (is (= (t 10)
         (W (V (T) ()) (list (T)))))
  (is (= (leftshift' (t 10) (t 1))
         (W (T) (list (W (T) (list (V (T) ())))))))
  (is (= (n (leftshift' (t 10) (t 1)))
         1024)))

;;;_ * Numbers ---------------------------------------------------------
(defn fermat [n] (s (exp2' (exp2' n))))

(deftest fermat-test
  (is (= (fermat (t 11))
         (V (T) (list (T) (V (T) (list (W (T) (list (V (T) ()))))))))))


(defn mersenne [p] (s' (exp2' p)))

(defn prime45    [] (t 43112609))
(defn mersenne45 [] (mersenne (prime45))) ;2^43112609 - 1

(deftest mersenne-test
  (is (= (mersenne (t 127))
         (V (W (V (T) (list (T))) ()) ()))) ;Long overflows :)
  (is (= (mersenne45)
         (V (W (T) (list (V (V (T) ()) ())
                         (T) (T) (T)
                         (W (T) ())
                         (V (T) ())
                         (T)
                         (W (T) ())
                         (W (T) ())
                         (T)
                         (V (T) ())
                         (T) (T)))
            ()))))


(defn perfect [p]
  (let [q (s' (s' p))]
    (s (V q (list q)))))

(defn perfect45 [] (perfect (t prime45)))

(deftest perfect-test
  ;; TODO
  )

;;;_ * Collections -----------------------------------------------------
(defprotocol Collections
  "Convert between natural numbers and lists by using the bijection
   f(x, y) = 2^x(2*y + 1)."
  (c   [x y])
  (c'  [x])
  (c'' [x]))

;; Default implementation:
(extend-type Object
  Collections
  (c   [x y] (mul (exp2 x) (o y)))
  (c'  [x]   (when (not (e_ x)) (if (o_ x) (e x) (s (c' (hf x))))))
  (c'' [x]   (when (not (e_ x)) (if (o_ x) (o' x) (c'' (hf x))))))


(defn to-list [x]
  (cond
   (e_ x) []
   :else  (cons (c' x) (to-list (c'' x)))))

(defn from-list [xs witness]
  (cond
   (empty? xs) (e witness)
   :else       (c (first xs) (from-list (rest xs) witness))))


(defn scanl [f z xs]
  (reverse (reduce (fn [acc x] (cons (f (first acc) x) acc)) (list z) xs)))


(defn list2mset [ns witness] (rest (scanl add (e witness) ns)))

(defn mset2list [ms witness] (map sub ms (cons (e witness) ms)))

(defn list2set [xs witness] (map s' (list2mset (map s xs) witness)))

(defn set2list [xs witness] (map s' (mset2list (map s xs) witness)))

(defn to-mset [x witness] (list2mset (to-list x) witness))

(defn from-mset [ms witness] (from-list (mset2list ms witness) witness))

(defn to-set [x witness] (list2set (to-list x) witness))

(defn from-set [ns witness] (from-list (set2list ns witness) witness))


(extend-type Tee
  Collections
  (c  [n y] (s (vmul n (s' (o y)))))

  (c' [z]
    (cond
     (o_ z) (T)
     :else  (let [q (s' z)]
              (assert (= :V (:ctor q)))
              (s (:arg1 q)))))

  (c'' [z]
    (cond
     (o_ z) (o' z)
     :else (let [q (s' z)
                 f (fn [xs]
                     (if (empty? xs)
                       (T)
                       (s (i' (W (first xs) (rest xs))))))]
             (assert (= :V (:ctor q)))
             (f (:arg2 q))))))

(deftest from-set-test
  (is (= (from-set (map t '(1 100 123 234)) (T))
         (W (V (T) ())
            (list (V (T) (list (T) (W (T) ()) (T)))
                  (T)
                  (V (T) (list (V (T) ()) (T)))
                  (T)
                  (V (T) (list (W (T) ()) (T) (T))))))))

;;;_ * Bitwise ---------------------------------------------------------

;; TODO

;;;_ * Isomorphisms ----------------------------------------------------

;; TODO

;;;_ * Computations ----------------------------------------------------
(defprotocol SpecialComputation
  (dual       [x])
  (bitsize    [x])
  (repsize    [x])
  (deconz     [x])
  (conz       [xy])
  (ocount     [x])
  (icount     [x])
  (otrim      [x])
  (itrim      [x])
  (otimes     [x y])
  (itimes     [x y])
  (to-list'   [x])
  (from-list' [xs witness]))

(extend-type Object
  SpecialComputation
  (dual [x]
    (cond
     (e_ x) (e x)
     (o_ x) i (dual (o' x))
     (i_ x) o (dual (i' x))))

  (bitsize [x]
    (cond
     (e_ x) (e x)
     (o_ x) (s (bitsize (o' x)))
     (i_ x) (s (bitsize (i' x)))))

  (repsize [x] (bitsize x))

  (deconz [z]
    (cond
     (o_ z)
     (let [x0 (s' (ocount z))
           y  (otrim z)
           x (if (e_ y) (s' (o x0)) x0)]
       [x y])

     (i_ z)
     (let [x0 (s' (icount z))
           y (itrim z)
           x (if (e_ y) (s' (i x0)) x0)]
       [x y])))

  (conz [[x y]]
    (cond
     (and (e_ x) (e_ y)) (s (e x))
     (and (o_ x) (e_ y)) (itimes (s (i' (s x))) (e x))
     (and (i_ x) (e_ y)) (otimes (s (o' (s x))) (e x))
     (o_ y)              (itimes (s x) y)
     (i_ y)              (otimes (s x) y)))

  (ocount [x]
    (cond
     (o_ x) (s (ocount (o' x)))
     :else  (e x)))

  (icount [x]
    (cond
     (i_ x) (s (icount (i' x)))
     :else  (e x)))

  (otrim [x]
    (o_ x) (otrim (o' x))
    :else  x)

  (itrim [x]
    (i_ x) (itrim (i' x))
    :else  x)

  (otimes [x y]
    (cond
     (e_ x) y
     :else  (otimes (s' x) (o y))))

  (itimes [x y]
    (cond
     (e_ x) y
     :else  (itimes (s' x) (i y))))

  (to-list' [x]
    (cond
     (e_ x) ()
     :else  (let [[hd tl] (decons x)]
              (cons hd (to-list' tl)))))

  (from-list' [xs witness]
    (cond
     (empty? xs) (e witness)
     :else       (conz [(first xs) (from-list' (rest xs) witness)]))))

(extend-type Tee
  SpecialComputation
  (bitsize [x]
    (let [add1 (fn [x y] (s (add x y)))]
      (case (:ctor x)
        :T (T)
        :V (s (reduce add1 (:arg1 x) (:arg2 x)))
        :W (s (reduce add1 (:arg1 x) (:arg2 x))))))

  (dual [x]
    (case (:ctor x)
      :T (T)
      :V (W (:arg1 x) (:arg2 x))
      :W (V (:arg1 x) (:arg2 x))))

  (repsize [x]
    (case (:ctor x)
      :T (T)
      :V (s (reduce add (T) (map tsize (cons (:arg1 x) (:arg2 x)))))
      :W (s (reduce add (T) (map tsize (cons (:arg1 x) (:arg2 x)))))))

  (deconz [x]


    )

  (conz [[x y]]


    ))

;;;_ * Benchmarks ------------------------------------------------------

;; TODO

;;;_* Emacs ============================================================
;;; Local Variables:
;;; allout-layout: t
;;; End:
