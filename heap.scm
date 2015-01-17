;; API
;;

;; Create a heap for a given comparison function PRED
;; and optionally provide a guess at the final size of the heap
(define (make-heap* pred #!key (size-guess 20))
  (make-heap (make-vector (max 1 size-guess) heap-null-value) 0 pred))

;; Returns #t when the heap is empty.
(define (heap-empty? heap)
  (= 0 (heap-size heap)))

;; test for the heap null value
(define (heap-null-value? v)
  (eq? v heap-null-value))

;; Add an element to the heap
(define (heap-add! heap el)
  (cond 
   ((heap-empty? heap)
	(heap-expand-by-one heap el))
   (#t 
	(let ((n (heap-size heap))
		  (pred (heap-pred heap))
		  (data #f))
	  (heap-expand-by-one heap el)
	  (set! data (heap-data heap))
	  (let loop 
		  ((n n))
		(let* ((root? (heap-root? n))
			   (val (vector-ref data n))
			   (pn (heap-parent n))
			   (parent-val (if root? #f (vector-ref data pn)))) 
		  (cond 
		   ((heap-root? n) heap)
		   ((pred val parent-val)
			(vector-set! data pn val)
			(vector-set! data n parent-val)
			(loop pn))
		   (#t heap))))))))

;; Take the top of the heap off.
;; Returns a heap-null-value when the heap is empty.
;; to extract the values sorted by pred, pop the heap
;; until it is empty.
(define (heap-pop! heap)
  (if (heap-empty? heap)
	  heap-null-value
	  (let* ((return-value (heap-ref heap 0))
			 (data (heap-data heap))
			 (new-size (- (heap-size heap) 1))
			 (last-val (vector-ref data new-size)))
		   (heap-size-set! heap new-size)
		   (vector-set! data new-size heap-null-value)
		   (vector-set! data 0 last-val)
		   (heap-adjust! heap 0)
		   return-value)))

;; Implementation 

;; friends don't let friends let nil occupy all types heap-null-value
;; is a value which signals the absence of a value in a heap 
(define heap-null-value (gensym 'heap-null-value))


;; the heap type
(define-type heap data size pred)

;; double the current maximum size of the heap
(define (heap-double-max-size heap)
  (let* ((old-data (heap-data heap))
		 (n-items (heap-size heap))
		 (new-data (make-vector (* 2 (vector-length old-data)) heap-null-value)))
	(heap-data-set! heap
	 new-data)
	(let loop 
		((i 0))
	  (cond 
	   ((< i n-items)
		(vector-set! new-data i (vector-ref old-data i))
		(loop (+ i 1)))
	   (#t new-data)))
	heap))

;; expand the current heap size by one, placing val in the last node
;; double the size of the heap if needed.
(define (heap-expand-by-one heap val)
  (let* ((max-size (vector-length (heap-data heap)))
		 (current-size (heap-size heap))
		 (new-size (+ 1 current-size)))
	(if (> new-size max-size)
		(begin 
		  (heap-double-max-size heap)
		  (heap-expand-by-one heap val))
		(let ((old-size (heap-size heap)))
		  (heap-size-set! heap (+ 1 old-size))
		  (vector-set! (heap-data heap) old-size val)))))

;; give index of the left child of i
(define (heap-left i)
  (+ 1 (* 2 i)))

;; give the index of the right child of i
(define (heap-right i)
  (+ 2 (* 2 i)))

;; give the index of i's parent
(define (heap-parent i)
  (cond 
   ((odd? i) (quotient (- i 1) 2))
   ((even? i) (quotient (- i 2) 2))))

;; Return #t when i is the root of the heap
(define (heap-root? i)
  (= i 0))

;; Give the node value at N of the heap HEAP
(define (heap-ref heap n)
  (let ((data (heap-data heap))) 
	(if (>= n (heap-size heap))
		heap-null-value
		(vector-ref data n))))

;; give the value to the left of the node n
(define (heap-ref-left heap n)
  (heap-ref heap (heap-left n)))

;; give the value to the right of the node n
(define (heap-ref-right heap n)
  (heap-ref heap (heap-right n)))

;; #t when the n is a leaf of the heap tree
(define (heap-leaf? heap n)
  (and    
   (heap-null-value? (heap-ref heap (heap-left n)))
   (heap-null-value? (heap-ref heap (heap-right n)))))

;; Given a position in the heap, give the position of the smaller of
;; its children if either are smaller than the value at n.
;; give false if the node is a leaf or if both children are larger.
(define (heap-smaller-child-or-false heap n)
  (let ((val (heap-ref heap n))
		(pred (heap-pred heap))
		(left-val (heap-ref-left heap n))
		(right-val (heap-ref-right heap n))
		(smaller-child #f))
	(if (and (not (heap-null-value? left-val)) 
			 (not (pred val left-val)))
		(begin 
		  (set! smaller-child (heap-left n))
		  (set! val left-val)))
	(if (and (not (heap-null-value? right-val))
			 (not (pred val right-val)))
		(set! smaller-child (heap-right n)))
	smaller-child))

;; Adjust the heap starting at n to ensure the heap's invariants hold
(define (heap-adjust! heap n)
  (cond 
   ((heap-leaf? heap n) heap)
   (#t 
	(let ((m-or-false (heap-smaller-child-or-false heap n)))
	  (cond
	   (m-or-false
		(let* ((m m-or-false)
			   (val (heap-ref heap n))
			   (swap-val (heap-ref heap m))
			   (data (heap-data heap)))
		  (vector-set! data n swap-val)
		  (vector-set! data m val)
		  (heap-adjust! heap m)))
	   (#t heap))))))


