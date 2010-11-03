;;;; Copyright (c) 2010 Nikodemus Siivola <nikodemus@sb-studio.net>
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(in-package :pileup)

;;; Tombstone for the heap vector. The only place where this really matters
;;; is at 0.
(defconstant +empty+ '+empty+)

(defun make-heap-vector (size)
  (declare (array-index size))
  (let ((vector (make-array (1+ size))))
    (setf (aref vector 0) +empty+)
    vector))

(declaim (inline make-heap make-heap-using-fast-pred))
(defstruct (heap
             (:constructor make-heap
                           (predicate &key ((:name %name)) ((:size %size) 12) ((:key %key))
                                      &aux (%vector (make-heap-vector %size))
                                           (%predicate predicate)
                                           (fast-pred
                                            (locally
                                                #+sbcl
                                                (declare (sb-ext:muffle-conditions
                                                          sb-ext:compiler-note))
                                                (if %key
                                                    (lambda (x y)
                                                      (declare (function %key %predicate)
                                                               (optimize (speed 3)
                                                                         (debug 0)
                                                                         (safety 0)))
                                                      (let ((xx (funcall %key x))
                                                            (yy (funcall %key y)))
                                                        (funcall %predicate xx yy)))
                                                    %predicate)))))
             (:constructor make-heap-using-fast-pred
                           (%predicate fast-pred &key ((:name %name)) ((:size %size) 12)
                                                 &aux (%vector (make-heap-vector %size))))
             (:copier nil)
             (:predicate nil))
  "A thread-safe binary heap.

Heap operations which need the heap to remain consistent heap lock it. Users
can also group multiple heap operations into atomic units using
WITH-LOCKED-HEAP.

Thread-safety is implemented using a single lock per heap. While Pileup heaps
are fine for threaded use, a more specialized solution is recommended when the
heap is highly contested between multiple threads.

Important: Pileup heaps are not asynch-unwind safe: asynchronous interrupts
causing non-local exits may leave the heap in an inconsistent state or lose
data. Do not use INTERRUPT-THREAD or asychronous timeouts with Pileup.

All slot names in HEAP are internal to the PILEUP package, so it is safe to
subclass using eg. DEFSTRUCT :INCLUDE, as long as only the exported operations
are used to accessor or modify heap state."
  (%name nil)
  ;; One longer than SIZE: we keep the min element in both 0 and 1. Using
  ;; 1-based addressing makes heap calculations simpler, and keeping a
  ;; separate reference in 0 allows HEAP-MIN to be lockless.
  ;;
  ;; Using adjustable arrays would make the code simpler, but because the
  ;; loops for maintaining the heap-property don't need to adjust the vectors
  ;; we'd be paying for the increased access overheap in just the wrong place.
  ;;
  ;; The name is uglified with % because VECTOR is a symbol in CL, and we
  ;; don't want to have clashes with user code subclassing this structure, who
  ;; might also want to use that name.
  (%vector (required-argument :vector) :type simple-vector)
  (%count 0 :type array-index)
  (%size (required-argument :%size) :type array-index)
  (%predicate (required-argument :predicate) :type function :read-only t)
  (%key nil :type (or null function) :read-only t)
  ;; Combination of KEY and PREDICATE.
  (fast-pred (required-argument :fast-pred) :type function :read-only t)
  (lock #+sbcl (sb-thread:make-mutex :name "Heap Lock")
        #-sbcl (bordeaux-threads:make-lock :name "Heap Lock")
        :read-only t)
  (state :clean :type (member :clean :dirty :traverse)))

(define-compiler-macro make-heap (&whole whole predicate &rest initargs)
  (let ((no-key t))
    ;; Check that no KEY is being used.
    (doplist (key val initargs)
      (when (or (eq :key key) (not (keywordp key)))
        (setf no-key nil)))
    ;; Calling variadic functions like #'< is generally a whole lot slower than
    ;; calling them with a known number of arguments. Once :ELEMENT-TYPE is
    ;; added we can also inform the predicate about it here.
    ;;
    ;; At least for compilers like SBCL the FAST-PRED lambda in the constructor
    ;; does the same job for cases where KEY is provided.
    (if (and no-key
             (consp predicate)
             (starts-with 'function predicate)
             (member (second predicate) '(< <= > >=)))
        (with-gensyms (x y)
          `(make-heap-using-fast-pred ,predicate
                                 (lambda (,x ,y)
                                   (declare (optimize (speed 3)
                                                      (debug 0)
                                                      (safety 0)))
                                   #+sbcl
                                   (declare (sb-ext:muffle-conditions sb-ext:compiler-note))
                                   (funcall ,predicate ,x ,y))
                                 ,@initargs))
        whole)))

(setf (documentation 'make-heap 'function)
      "Constructs a HEAP.

The PREDICATE determines the ordering of the heap. It must be a function of two
arguments, returning true if the first argument should be closer to top of the
heap than the second. If a predicate signals an error and causes a non-local
exit from a heap operation, it may leave the heap in an inconsistent state and
cause a subsequent heap operation to signal an error.

If KEY is not NIL, it must be a function of one argument, and is used to
extract values for use by PREDICATE for comparison.

The NAME can be used to optionally specify a name for the heap: it affects only
printing of the heap.

The SIZE is the size of the storage initially reserved for the heap.
Specifying size is not necessary: the heap will grow as necessary, but a
reasonable estimate can improve performance by eliminating unnecessary copying
by allocation sufficient storage immediately.")

;;; KLUDGE: For prettier arglist in the docs.
(defun heap-name (heap)
  "Returns the name of the heap. Heap name affects only printed
representation of the heap. Can be changed using SETF unlike other heap
properties."
  (heap-%name heap))
(defun (setf heap-name) (name heap)
  (setf (heap-%name heap) name))

;;; KLUDGE: For prettier arglist in the docs.
(defun heap-predicate (heap)
  "Returns the heap predicate, a function of two arguments, returning true if
the first argument should be closer to te top of the heap than the second."
  (heap-%predicate heap))

;;; KLUDGE: For prettier arglist in the docs.
(defun heap-key (heap)
  "Returns the heap key, a function one argument used to extract values for
use by the heap predicate. Heap key may also be NIL, meaning heap elements are
used directly by the heap predicate."
  (heap-%key heap))

(declaim (inline heap-count))
(defun heap-count (heap)
  "Returns the number of objects in the heap."
  (heap-%count heap))

(declaim (inline heap-size))
(defun heap-size (heap)
  "Returns the reserved size of the heap. Note, this is not the same as the
number of elements in the heap: see HEAP-COUNT for comparison."
  (heap-%size heap))

(declaim (inline heap-empty-p))
(defun heap-empty-p (heap)
  "Returns true if the heap is empty, that is iff HEAP-COUNT is zero."
  (zerop (heap-count heap)))

(defmethod print-object ((heap heap) stream)
  (flet ((pretty-fun (fun)
           (or (when (functionp fun)
                 (nth-value 2 (function-lambda-expression fun)))
               fun)))
    (print-unreadable-object (heap stream :type t :identity t)
     (format stream "~@[~S ~]count: ~S predicate: ~S~@[ key: ~S~]"
             (heap-name heap)
             (heap-count heap)
             (pretty-fun (heap-predicate heap))
             (pretty-fun (heap-key heap))))))

(defmacro with-locked-heap ((heap) &body body)
  "Executes BODY with HEAP locked. Heap operations which implicitly lock the
heap are: HEAP-INSERT, HEAP-POP, HEAP-DELETE, and MAP-HEAP. Allows grouping
multiple heap operations into atomic units."
  #+sbcl
  `(sb-thread:with-recursive-lock ((heap-lock ,heap))
     ,@body)
  #-sbcl
  `(bordeaux-threads:with-recursive-lock-held ((heap-lock ,heap))
     ,@body))

(defconstant heap-size-limit (- array-dimension-limit 1)
  "Exclusive upper limit for heap size, based on ARRAY-DIMENSION-LIMIT.
When an insertion is attempted and the heap cannot grow any further, an error
is signaled.")

(defconstant max-heap-size (- heap-size-limit 1))

(defun check-heap-clean (heap what &optional allow-traverse)
  (ecase (heap-state heap)
    (:clean t)
    (:dirty
     (error "Heap dirty on entry to ~S: ~S"
            what heap))
    (:traverse
     (unless allow-traverse
       (error "Cannot ~S while ~S is in progress: ~S"
              what 'map-heap heap)))))

(defun heap-insert (elt heap)
  "Insert ELT to HEAP. Returns ELT.

Locks the heap during its operation unless the current thread is already
holding the heap lock via WITH-LOCKED-HEAP."
  (declare (heap heap))
  (with-locked-heap (heap)
    (check-heap-clean heap 'heap-insert)
    (let* ((vector (heap-%vector heap))
           (fast-pred (heap-fast-pred heap))
           (size (heap-size heap))
           (count (heap-count heap)))
      ;; Sanity-check the heap element: if the predicate will signal an error
      ;; on receiving it, it is better to know about it before we mess up the
      ;; heap state.
      (funcall fast-pred elt elt)
      ;; Make space if necessary.
      (when (= count size)
        (when (= size max-heap-size)
          (error "Cannot grow heap vector: at maximum size."))
        (let* ((new-size (min (* 2 size) max-heap-size))
               (new (make-array (1+ new-size))))
          (setf vector (replace new vector)
                (heap-%size heap) new-size
                (heap-%vector heap) vector)))
      ;; Mark the heap dirty, and insert the element at the end of the vector.
      (setf (heap-state heap) :dirty
            (aref vector (incf count)) elt
            (heap-%count heap) count)
      ;; Restore heap property.
      (loop with child = count
            while (> child 1)
            do (let* ((parent (truncate child 2))
                      (parent-data (aref vector parent))
                      (child-data (aref vector child)))
                 (cond ((funcall fast-pred parent-data child-data)
                        (return))
                       (t
                        (setf (aref vector child) parent-data
                              (aref vector parent) child-data
                              child parent)))))
      ;; Put reference to min to 0 too. Heap is now clean.
      (setf (aref vector 0) (aref vector 1)
            (heap-state heap) :clean)
      elt)))

(defun heap-top (heap)
  "Returns the element at the top of the HEAP without removing it, and a
secondary value of T. Should the heap be empty, both the primary and the
secondary values are NIL."
  (let ((elt (aref (heap-%vector heap) 0)))
    (if (eq +empty+ elt)
        (values nil nil)
        (values elt t))))

(defun heap-pop (heap)
  "Removes and returns the element at the top of the HEAP and a secondary value of T.
Should the heap be empty, both the primary and the secondary values are NIL.

Locks the heap during its operation unless the current thread is already
holding the heap lock via WITH-LOCKED-HEAP."
  (declare (heap heap))
  (with-locked-heap (heap)
    (check-heap-clean heap 'heap-pop)
    (cond ((heap-empty-p heap)
           (values nil nil))
          (t
           (values (%heap-delete 1 heap) t)))))

;;; Delete heap element identified by vector index.
(defun %heap-delete (index heap)
  (let* ((vector (heap-%vector heap))
         (count (heap-count heap))
         (victim (aref vector index))
         (bottom (aref vector count))
         (fast-pred (heap-fast-pred heap))
         (recoverable t))
    (unwind-protect
         (progn
           ;; Move BOTTOM in place of VICTIM. Order is important here: if
           ;; INDEX=COUNT we want to be left with +EMPTY+.
           (setf (heap-state heap) :dirty
                 (aref vector index) bottom
                 (aref vector count) +empty+
                 (heap-%count heap) (decf count))
           ;; Restore heap property.
           ;; Step 1: from deleted element to end
           (loop with parent = index
                 while (< parent count)
                 do (let* ((local parent)
                           (local-data (aref vector parent))
                           (parent-data local-data)
                           (left (* 2 parent))
                           (right (+ left 1))
                           (left-data nil)
                           (right-data nil))
                      (unless (or (> left count)
                                  (funcall fast-pred parent-data
                                           (setf left-data (aref vector left))))
                        (setf local left
                              local-data left-data))
                      (unless (or (> right count)
                                  (funcall fast-pred local-data
                                           (setf right-data (aref vector right))))
                        (setf local right
                              local-data right-data))
                      (if (= local parent)
                          (return)
                          (setf (aref vector parent) local-data
                                (aref vector local) parent-data
                                parent local
                                recoverable nil))))
           ;; Step 2: fix towards the head.
           (cond ((= index 1)
                  ;; Deleted the topmost element: copy it to V[0]
                  (setf (aref vector 0) (aref vector 1)))
                 ((= index (1+ count))
                  ;; Deleted the last element: nothing to do.
                  )
                 (t
                  ;; Deleted something from middle: fix heap property
                  ;; towards the head.
                  (loop with child = index
                        while (> child 1)
                        do (let* ((parent (truncate child 2))
                                  (parent-data (aref vector parent))
                                  (child-data (aref vector child)))
                             (cond ((funcall fast-pred parent-data child-data)
                                    (return))
                                   (t
                                    (setf (aref vector child) parent-data
                                          (aref vector parent) child-data
                                          child parent
                                          recoverable nil)))))))
           ;; Clean again
           (setf (heap-state heap) :clean))
      ;; If we're not clean, try to recover on unwind.
      (unless (eq :clean (heap-state heap))
        (setf (heap-%count heap) (incf count))
        (if recoverable
            ;; We didn't actually swap any elements yet, so we can restore
            ;; the whole heap.
            (setf (aref vector count) bottom
                  (aref vector index) victim
                  (heap-state heap) :clean)
            ;; Can't recover, but at least put VICTIM back -- recovery of
            ;; sorts is still possible using unordered MAP-HEAP.
            (setf (aref vector count) victim))))
    victim))

(defun heap-delete (elt heap &key count)
  "Removes elements of the HEAP EQL to ELT. Returns T if one or more elements
were found and removed, NIL otherwise.

If COUNT is NIL (the default), removes all elements EQL to ELT, otherwise at
most the indicated number.

Locks the heap during its operation unless the current thread is already
holding the heap lock via WITH-LOCKED-HEAP."
  (declare (type heap heap))
  (with-locked-heap (heap)
    (check-heap-clean heap 'heap-delete)
    (let* ((todo (cond ((not count) -1)
                       ((minusp count) 0)
                       (t count)))
           (count (heap-count heap))
           (vector (heap-%vector heap))
           (fast-pred (heap-fast-pred heap)))
      (unless (or (zerop count) (zerop todo))
        (let ((fringe (make-heap (lambda (x y)
                                   (funcall fast-pred (aref vector x) (aref vector y))))))
          ;; Grab the lock now so we don't need to do that repeatedly.
          (with-locked-heap (fringe)
            (heap-insert 1 fringe)
            (loop until (heap-empty-p fringe)
                  do (let* ((parent (heap-pop fringe))
                            (parent-elt (aref vector parent)))
                       (cond ((eql elt parent-elt)
                              ;; Got it. Now delete them all.
                              (loop do (%heap-delete parent heap)
                                       (decf todo)
                                    while (and (/= 0 todo) (eql elt (aref vector parent))))
                              (return-from heap-delete t))
                             ((funcall fast-pred elt parent-elt)
                              ;; Searched past it.
                              (return-from heap-delete nil))
                             (t
                              (let* ((left (* 2 parent))
                                     (right (1+ left)))
                                (unless (> left count)
                                  (heap-insert left fringe))
                                (unless (> right count)
                                  (heap-insert right fringe)))))))))))))

(defun map-heap (function heap &key (ordered t))
  "Calls FUNCTION for each element in heap. Returns the heap.

If ORDERED is true \(the default), processes the elements in heap order from
top down.

If ORDERED is false, uses unordered traversal. Unordered traversal is faster
and also works on heaps that have been corrupted by eg. the heap predicate
performing a non-local exit from a heap operation.

Attempts to insert or delete elements to the heap from FUNCTION will cause
an error to be signalled.

Locks the heap during its operation unless the current thread is already
holding the heap lock via WITH-LOCKED-HEAP."
  (declare (heap heap))
  (with-locked-heap (heap)
    (let ((count (heap-count heap))
          (old-state (heap-state heap)))
      (when ordered
        (check-heap-clean heap 'map-heap t))
      (unwind-protect
           (unless (zerop count)
             ;; Mark the heap as traversed
             (setf (heap-state heap) :traverse)
             (let ((vector (heap-%vector heap)))
               (if ordered
                   ;; ORDERED = T traversal. Keep fringe in another heap
                   ;; to maintain order.
                   (let* ((fast-pred (heap-fast-pred heap))
                          (fringe (make-heap
                                   (lambda (x y)
                                     (funcall fast-pred (aref vector x) (aref vector y))))))
                     ;; Grab the lock now so we don't need to do that repeatedly.
                     (with-locked-heap (fringe)
                       (heap-insert 1 fringe)
                       (loop until (heap-empty-p fringe)
                             do (let* ((parent (heap-pop fringe))
                                       (left (* 2 parent))
                                       (right (1+ left)))
                                  (funcall function (aref vector parent))
                                  (unless (> left count)
                                    (heap-insert left fringe))
                                  (unless (> right count)
                                    (heap-insert right fringe))))
                       (heap-size fringe)))
                   ;; ORDERED = NIL traversal. Just iterate over the vector.
                   (loop for i from 1 upto count
                         do (funcall function (aref vector i))))))
        ;; Restore the old state: either :CLEAN, or another :TRAVERSE.
        (setf (heap-state heap) old-state))))
  heap)

