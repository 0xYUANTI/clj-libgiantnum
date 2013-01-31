;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tree-based arithmetic and Compressed Representations of Giant Numbers.
;;; http://arxiv.org/abs/1301.0114
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;_* Declarations =====================================================
(ns clj-giant.core
  (:use clojure.test))

(declare B O I)
(declare T V W)
(declare vmul)
(declare scanl)
(declare t b n)

;;;_* Code =============================================================
;;;_ * Generic arithmetic ----------------------------------------------
;;;_  * Protocol -------------------------------------------------------
(defprotocol N
  "A representation-independent abstraction of natural numbers."
  (eq          [x y] "Structural equality.")
  (e           [x]   "The empty sequence of binary digits.")
  (o           [x]   "Add 0 to a binary string.")
  (o'          [x]   "Remove 0 from a binary string.")
  (i           [x]   "Add 1 to a binary string.")
  (i'          [x]   "Remove 1 from a binary string.")
  (o_          [x]   "True iff binary string ends with a 0.")

  (e_          [x]   "Zero?")
  (i_          [x]   "Even?")
  (s           [x]   "Successor")
  (s'          [x]   "Predecessor")

  (all-from    [x]   "")
  (add         [x y] "")
  (sub         [x y] "")
  (cmp         [x y] "")
  (min2        [x y] "")
  (max2        [x y] "")
  (mul         [x y] "")
  (db          [x]   "")
  (hf          [x]   "")
  (pow         [x y] "")
  (exp2        [x]   "")
  (leftshift   [x y] "")
  (div-and-rem [x y] "")
  (divide      [x y] "")
  (remainder   [x y] ""))

(def N-defaults
  {:eq
   (fn [x y] (= x y))

   :e_
   (fn [x] (eq x (e x)))

   :i_
   (fn [x] (not (or (e_ x) (o_ x))))

   :s
   (fn [x]
     (cond
      (e_ x) (o x)
      (o_ x) (i (o' x))
      (i_ x) (o (s (i' x)))))

   :s'
   (fn [x]
     (cond
      (eq x (o (e x))) (e x)
      (i_ x)           (o (i' x))
      (o_ x)           (i (s' (o' x)))))

   :all-from
   (fn [x] (iterate s x))

   :add
   (fn [x y]
     (cond
      (e_ x)               y
      (e_ y)               x
      (and (o_ x) (o_ y))  (i (add (o' x) (o' y)))
      (and (o_ x) (i_ y))  (o (s (add (o' x) (i' y))))
      (and (i_ x) (o_ y))  (o (s (add (i' x) (o' y))))
      (and (i_ x) (i_ y))  (i (s (add (i' x) (i' y))))))

   :sub
   (fn [x y]
     (cond
      (e_ y)              x
      (and (o_ x) (o_ y)) (s' (o (sub (o' x) (o' y))))
      (and (o_ x) (i_ y)) (s' (s' (o (sub (o' x) (i' y)))))
      (and (i_ x) (o_ y)) (o (sub (i' x) (o' y)))
      (and (i_ x) (i_ y)) (s' (o (sub (i' x) (i' y))))))

   :cmp
   (fn [x y]
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

   :min2
   (fn [x y] (if (= -1 (cmp x y)) x y))

   :max2
   (fn [x y] (if (= -1 (cmp x y)) y x))

   :mul
   (fn [x y]
     (letfn [(m [x y]
               (cond
                (e_ x) y
                (o_ x) (o (m (o' x) y))
                (i_ x) (s (add y (o (m (i' x) y))))))]
       (cond
        (e_ x) (e x)
        (e_ y) (e x)
        :else  (s (m (s' x) (s' y))))))

   :db
   (fn [x] (s' (o x)))

   :hf
   (fn [x] (s (i' x)))

   :pow
   (fn [x y]
     (cond
      (e_ y) (o (e x))
      (o_ y) (mul x (pow (mul x x) (o' y)))
      (i_ y) (mul (mul x x) (pow (mul x x) (i' y)))))

   :exp2
   (fn [x]
     (cond
      (e_ x) (o (e x))
      :else  (db (exp2 (s' x)))))

   :leftshift
   (fn [x y] (mul (exp2 x) y))

   :div-and-rem
   (fn [x y]
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

   :divide
   (fn [x y] (first  (div-and-rem x y)))

   :remainder
   (fn [x y] (second (div-and-rem x y)))})

;;;_  * Instances ------------------------------------------------------
;;;_   * Integers ------------------------------------------------------
(extend Long
  N
  (assoc N-defaults
    :e  (fn [_] 0)
    :o_ (fn [x] (odd? x))
    :o  (fn [x] (+ (* 2 x) 1))
    :o' (fn [x] (cond (and (odd? x) (> x 0)) (/ (- x 1) 2)))
    :i  (fn [x] (+ (* 2 x) 2))
    :i' (fn [x] (cond (and (even? x) (> x 0)) (/ (- x 2) 2)))))

(deftest int-test
  (is (= (mul 10 5) 50))
  (is (= (exp2 5)   32)))

;;;_   * Bijective Base 2 ----------------------------------------------
(defrecord Bee [ctor arg])

(extend Bee
  N
  (assoc N-defaults
    :e  (fn [_] (B))
    :o  (fn [x] (O x))
    :i  (fn [x] (I x))
    :o' (fn [x] (case (:ctor x) :O (:arg x)))
    :i' (fn [x] (case (:ctor x) :I (:arg x)))
    :o_ (fn [x] (= (:ctor x) :O))))

(defn B []  (Bee. :B nil))
(defn O [B] (Bee. :O B))
(defn I [B] (Bee. :I B))

(deftest bb2-test
  (is (= (add (O (B)) (I (O (B)))) (O (I (B))))))

;;;_   * Trees ---------------------------------------------------------
(defrecord Tee [ctor arg1 arg2])

(extend Tee
  N
  (assoc N-defaults
    :e
    (fn [_] (T))

    :o
    (fn [x]
      (case (:ctor x)
        :T (V (T) ())
        :V (V (s (:arg1 x)) (:arg2 x))
        :W (V (T) (cons (:arg1 x) (:arg2 x)))))

    :i
    (fn [x]
      (case (:ctor x)
        :T (W (T) ())
        :V (W (T) (cons (:arg1 x) (:arg2 x)))
        :W (W (s (:arg1 x)) (:arg2 x))))

    :o'
    (fn [x]
      (assert (= :V (:ctor x)))
      (if (= (T) (:arg1 x))
        (if (= () (:arg2 x))
          (T)
          (W (first (:arg2 x)) (rest (:arg2 x))))
        (V (s' (:arg1 x)) (:arg2 x))))

    :i'
    (fn [x]
      (assert (= :W (:ctor x)))
      (if (= (T) (:arg1 x))
        (if (= () (:arg2 x))
          (T)
          (V (first (:arg2 x)) (rest (:arg2 x))))
        (W (s' (:arg1 x)) (:arg2 x))))

    :o_
    (fn [x] (= :V (:ctor x)))

    :exp2
    (fn [x]
      (if (= :T (:ctor x))
        (V (T) ())
        (s (V (s' x) ()))))

    :leftshift
    (fn [x y]
      (if (= (T) y)
        (T)
        (cond
         (o_ y) (s (vmul x     (s' y)))
         (i_ y) (s (vmul (s x) (s' y))))))))

(defn T []     (Tee. :T nil nil))
(defn V [T Ts] (Tee. :V T   Ts))
(defn W [T Ts] (Tee. :W T   Ts))

(defn vmul [n y]
  (cond
   (= (T) n)        y
   (= (T) y)        (V (s' n) ())
   (= :V (:ctor y)) (V (add (s' n) (:arg1 y)) (:arg2 y))
   (= :W (:ctor y)) (V (s' n) (cons (:arg1 y) (:arg2 y)))))

(deftest tee-test
  (is (= (t 5)
         (V (T) (list (T)))))
  (is (= (exp2 (t 5))
         (W (T) (list (V (V (T) ()) ())))))
  (is (= (n (exp2 (t 5)))
         32))
  (is (= (t 10)
         (W (V (T) ()) (list (T)))))
  (is (= (leftshift (t 10) (t 1))
         (W (T) (list (W (T) (list (V (T) ())))))))
  (is (= (n (leftshift (t 10) (t 1)))
         1024)))

;;;_  * Views ----------------------------------------------------------
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

;;;_ * Numbers ---------------------------------------------------------
(defn fermat [n] (s (exp2 (exp2 n))))

(deftest fermat-test
  (is (= (fermat (t 11))
         (V (T) (list (T) (V (T) (list (W (T) (list (V (T) ()))))))))))


(defn mersenne [p] (s' (exp2 p)))

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
;;;_  * Protocol -------------------------------------------------------
(defprotocol Collections
  "Convert between natural numbers and lists by using the bijection
   f(x, y) = 2^x(2*y + 1)."
  (c         [x y])
  (c'        [x])
  (c''       [x])
  (to-list   [x])
  (from-list [witness xs])
  (list2mset [witness ns])
  (mset2list [witness ms])
  (list2set  [witness xs])
  (set2list  [witness xs])
  (to-mset   [witness x])
  (from-mset [witness ms])
  (to-set    [witness x])
  (from-set  [witness ns]))

(def Collections-defaults
  {:c
   (fn [x y] (mul (exp2 x) (o y)))

   :c'
   (fn [x] (when (not (e_ x)) (if (o_ x) (e x) (s (c' (hf x))))))

   :c''
   (fn [x] (when (not (e_ x)) (if (o_ x) (o' x) (c'' (hf x)))))

   :to-list
   (fn [x]
     (cond
      (e_ x) []
      :else  (cons (c' x) (to-list (c'' x)))))

   :from-list
   (fn [witness xs]
     (cond
      (empty? xs) (e witness)
      :else       (c (first xs) (from-list witness (rest xs)))))

   :list2mset
   (fn [witness ns] (rest (scanl add (e witness) ns)))

   :mset2list
   (fn [witness ms] (map sub ms (cons (e witness) ms)))

   :list2set
   (fn [witness xs] (map s' (list2mset witness (map s xs))))

   :set2list
   (fn [witness xs] (map s' (mset2list witness (map s xs))))

   :to-mset
   (fn [witness x] (list2mset witness (to-list x)))

   :from-mset
   (fn [witness ms] (from-list witness (mset2list witness ms)))

   :to-set
   (fn [witness x] (list2set witness (to-list x)))

   :from-set
   (fn [witness ns] (from-list witness (set2list witness ns)))})

(defn scanl [f z xs]
  (reverse (reduce (fn [acc x] (cons (f (first acc) x) acc)) (list z) xs)))

;;;_  * Instances ------------------------------------------------------
(extend Bee Collections Collections-defaults)

(extend Long Collections Collections-defaults)

(extend Tee
  Collections
  (assoc Collections-defaults
    :c
    (fn [n y] (s (vmul n (s' (o y)))))

    :c'
    (fn [z]
      (cond
       (o_ z) (T)
       :else  (let [q (s' z)]
                (assert (= :V (:ctor q)))
                (s (:arg1 q)))))

    :c''
    (fn [z]
      (cond
       (o_ z) (o' z)
       :else (let [q (s' z)
                   f (fn [xs]
                       (if (empty? xs)
                         (T)
                         (s (i' (W (first xs) (rest xs))))))]
               (assert (= :V (:ctor q)))
               (f (:arg2 q)))))))

(deftest from-set-test
  (is (= (from-set (T) (map t '(1 100 123 234)))
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
;;;_  * Protocol -------------------------------------------------------
(defprotocol SpecialComputation
  (dual       [x])
  (bitsize    [x])
  (repsize    [x])
  (deconz     [x])
  (conz       [witness xy])
  (ocount     [x])
  (icount     [x])
  (otrim      [x])
  (itrim      [x])
  (otimes     [x y])
  (itimes     [x y])
  (to-list'   [x])
  (from-list' [witness xs]))

(def SpecialComputation-defaults
  {:dual
   (fn [x]
     (cond
      (e_ x) (e x)
      (o_ x) i (dual (o' x))
      (i_ x) o (dual (i' x))))

   :bitsize
   (fn [x]
     (cond
      (e_ x) (e x)
      (o_ x) (s (bitsize (o' x)))
      (i_ x) (s (bitsize (i' x)))))

   :repsize
   (fn [x] (bitsize x))

   :deconz
   (fn [z]
     (cond
      (o_ z)
      (let [x0 (s' (ocount z))
            y  (otrim z)
            x  (if (e_ y) (s' (o x0)) x0)]
        [x y])

      (i_ z)
      (let [x0 (s' (icount z))
            y  (itrim z)
            x  (if (e_ y) (s' (i x0)) x0)]
        [x y])))

   :conz
   (fn [witness [x y]]
     (cond
      (and (e_ x) (e_ y)) (s (e x))
      (and (o_ x) (e_ y)) (itimes (s (i' (s x))) (e x))
      (and (i_ x) (e_ y)) (otimes (s (o' (s x))) (e x))
      (o_ y)              (itimes (s x) y)
      (i_ y)              (otimes (s x) y)))

   :ocount
   (fn [x]
     (cond
      (o_ x) (s (ocount (o' x)))
      :else  (e x)))

   :icount
   (fn [x]
     (cond
      (i_ x) (s (icount (i' x)))
      :else  (e x)))

   :otrim
   (fn [x]
     (cond
      (o_ x) (otrim (o' x))
      :else  x))

   :itrim
   (fn [x]
     (cond
      (i_ x) (itrim (i' x))
      :else  x))

   :otimes
   (fn [x y]
     (cond
      (e_ x) y
      :else  (otimes (s' x) (o y))))

   :itimes
   (fn [x y]
     (cond
      (e_ x) y
      :else  (itimes (s' x) (i y))))

   :to-list'
   (fn [x]
     (cond
      (e_ x) ()
      :else  (let [[hd tl] (deconz x)]
               (cons hd (to-list' tl)))))

   :from-list'
   (fn [witness xs]
     (cond
      (empty? xs) (e witness)
      :else       (conz witness [(first xs) (from-list' witness (rest xs))])))})

;;;_  * Instances ------------------------------------------------------
(extend Bee SpecialComputation SpecialComputation-defaults)

(extend Long SpecialComputation SpecialComputation-defaults)

(extend Tee
  SpecialComputation
  (assoc SpecialComputation-defaults
    :bitsize
    (fn [x]
      (let [add1 (fn [x y] (s (add x y)))]
        (case (:ctor x)
          :T (T)
          :V (s (reduce add1 (:arg1 x) (:arg2 x)))
          :W (s (reduce add1 (:arg1 x) (:arg2 x))))))

    :dual
    (fn [x]
      (case (:ctor x)
        :T (T)
        :V (W (:arg1 x) (:arg2 x))
        :W (V (:arg1 x) (:arg2 x))))

    :repsize
    (fn [x]
      (case (:ctor x)
        :T (T)
        :V (s (reduce add (T) (map repsize (cons (:arg1 x) (:arg2 x)))))
        :W (s (reduce add (T) (map repsize (cons (:arg1 x) (:arg2 x)))))))

    :deconz
    (fn [x]
      (case (:ctor x)
        :V (if (empty? (:arg2 x))
             [(s' (o (:arg1 x))) (T)]
             [(:arg1 x) (W (first (:arg2 x)) (rest (:arg2 x)))])
        :W (if (empty? (:arg2 x))
             [(s' (i (:arg1 x))) (T)]
             [(:arg1 x) (V (first (:arg2 x)) (rest (:arg2 x)))])))

    :conz
    (fn [[x y]]
      (cond
       (and (= x (T))  (= y (T))) (V (T) ())
       (and (o_ x)     (= y (T))) (W (i' (s x)) ())
       (and (i_ x)     (= y (T))) (V (o' (s x)) ())
       (= (:ctor y) V) (W x (cons (:arg1 y) (:arg2 y)))
       (= (:ctor y) W) (V x (cons (:arg1 y) (:arg2 y)))))))

(deftest list-test
  (is (= (map to-list' (range 21))
         '(() (0) (1) (2) (0 0) (0 1) (3) (4) (0 2) (0 0 0) (1 0) (1 1)
           (0 0 1) (0 3) (5) (6) (0 4) (0 0 2) (1 2) (1 0 0) (0 0 0 0))))
  (is (= (map #(from-list' 1 %) (map to-list' (range 21)))
         '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))))

;;;_ * Benchmarks ------------------------------------------------------

;; TODO

;;;_* Emacs ============================================================
;;; Local Variables:
;;; allout-layout: t
;;; End:
