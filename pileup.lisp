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

(declaim (inline make-heap))
(defstruct (heap
             (:constructor make-heap (predicate &key name ((:size %size) 12)
                                                &aux (vector
                                                      (let ((vector (make-array (1+ %size))))
                                                        (setf (aref vector 0) +empty+)
                                                        vector))))
             (:copier nil))
  "A binary heap."
  ;; One longer than SIZE: we keep the min element in both 0 and 1. Using
  ;; 1-based addressing makes heap calculations simpler, and keeping a
  ;; separate reference in 0 allows HEAP-MIN to be lockless.
  ;;
  ;; Using adjustable arrays would make the code simpler, but because the
  ;; loops for maintaining the heap-property don't need to adjust the vectors
  ;; we'd be paying for the increased access overheap in just the wrong place.
  (vector (required-argument) :type simple-vector)
  (%count 0 :type array-index)
  (%size (required-argument) :type array-index)
  (predicate (required-argument) :type function :read-only t)
  (lock #+sbcl (sb-thread:make-mutex :name "Heap Lock")
        #-sbcl (bordeaux-threads:make-lock :name "Heap Lock")
        :read-only t)
  ;; True while the heap property is being fixed up. Used to detect if predicate
  ;; causes recursive entry into heap routines. Similarly a predicate that causes
  ;; a non-local exit can leave the heap dirty.
  (dirty nil)
  (name nil :read-only t))

(setf (documentation 'make-heap 'function)
      "Constructs a binary heap.

PREDICATE determines the ordering of the heap. It must be a function of two
arguments, returning true if the first argument should be closer to top of the
heap than the second. If a predicate signals an error and causes a non-local
exit from a heap operation, it may leave the heap in an inconsistent state and
cause a subsequent heap operation to signal an error.

NAME can be used to optionally specify a name for the heap: it affects only
printing of the heap.

SIZE is the size of the storage initially reserved for the heap -- specifying
it is not necessary: the heap will grow as necessary, but a reasonable
estimate can improve performance.")

(setf (documentation 'heap-name 'function)
      "Name of the heap. Only affects printed representation of the heap.")

(setf (documentation 'heap-predicate 'function)
      "Heap predicate. A function of two arguments, returning true if the first
argument should be closer to te top of the heap than the second.")

(setf (documentation 'heap-p 'function)
      "Returns true if the argument is a heap.")

(declaim (inline heap-count))
(defun heap-count (heap)
  "Returns the number of objects in the heap."
  (heap-%count heap))

(declaim (inline heap-size))
(defun heap-size (heap)
  "Returns the reserved size of the heap."
  (heap-%size heap))

(declaim (inline heap-empty-p))
(defun heap-empty-p (heap)
  "Returns true if the heap is empty."
  (zerop (heap-count heap)))

(defmethod print-object ((heap heap) stream)
  (print-unreadable-object (heap stream :type t :identity t)
    (format stream "~@[~S ~]count: ~S predicate: ~S"
            (heap-name heap)
            (heap-count heap)
            (let ((pred (heap-predicate heap)))
              (or (when (functionp pred)
                    (nth-value 2 (function-lambda-expression pred)))
                  pred)))))

(defmacro with-locked-heap ((heap) &body body)
  "Executes BODY with HEAP locked. Heap operations which implicitly lock the
heap are: HEAP-INSERT, HEAP-POP, and HEAP-DELETE. Allows grouping multiple
heap operations into atomic units."
  #+sbcl
  `(sb-thread:with-recursive-lock ((heap-lock ,heap))
     ,@body)
  #-sbcl
  `(bordeaux-threads:with-recursive-lock-held ((heap-lock ,heap))
     ,@body))

(defconstant heap-size-limit (- array-dimension-limit 1)
  "Exclusive upper limit for heap size.")

(defconstant max-heap-size (- heap-size-limit 1))

(defun heap-insert (elt heap)
  "Insert ELT to HEAP. Returns ELT."
  (declare (heap heap))
  (with-locked-heap (heap)
    (when (heap-dirty heap)
      (error "Heap dirty on entry to HEAP-INSERT."))
    (let* ((vector (heap-vector heap))
           (pred (heap-predicate heap))
           (size (heap-size heap))
           (count (heap-count heap)))
      ;; Make space if necessary.
      (when (= count size)
        (when (= size max-heap-size)
          (error "Cannot grow heap vector: at maximum size."))
        (let* ((new-size (min (* 2 size) max-heap-size))
               (new (make-array (1+ new-size))))
          (setf vector (replace new vector)
                (heap-%size heap) new-size
                (heap-vector heap) vector)))
      ;; Mark the heap dirty, and insert the element at the end of the vector.
      (setf (heap-dirty heap) t
            (aref vector (incf count)) elt
            (heap-%count heap) count)
      ;; Restore heap property.
      (loop with child = count
            while (> child 1)
            do (let* ((parent (truncate child 2))
                      (parent-data (aref vector parent))
                      (child-data (aref vector child)))
                 (cond ((funcall pred parent-data child-data)
                        (return))
                       (t
                        (setf (aref vector child) parent-data
                              (aref vector parent) child-data
                              child parent)))))
      ;; Put reference to min to 0 too. Heap is now clean.
      (setf (aref vector 0) (aref vector 1)
            (heap-dirty heap) nil)
      elt)))

(defun heap-peek (heap)
  "Returns the element at the top of the HEAP, and a secondary value of T.
Should the heap be empty, both the primary and the secondary values are NIL."
  (let ((elt (aref (heap-vector heap) 0)))
    (if (eq +empty+ elt)
        (values nil nil)
        (values elt t))))

(defun heap-pop (heap)
  "Removes and returns the element at the top of the HEAP and a secondary value of T.
Should the heap be empty, both the primary and the secondary values are NIL."
  (declare (heap heap))
  (with-locked-heap (heap)
    (when (heap-dirty heap)
      (error "Heap dirty on entry to HEAP-POP."))
    (cond ((heap-empty-p heap)
           (values nil nil))
          (t
           (values (%heap-delete 1 heap) t)))))

;;; Delete heap element identified by vector index.
(defun %heap-delete (index heap)
  (let* ((vector (heap-vector heap))
         (count (heap-count heap))
         (victim (aref vector index))
         (bottom (aref vector count))
         (pred (heap-predicate heap)))
    ;; Move BOTTOM in place of VICTIM.
    (setf (heap-dirty heap) t
          (aref vector count) +empty+
          (aref vector index) bottom
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
                           (funcall pred parent-data
                                    (setf left-data (aref vector left))))
                 (setf local left
                       local-data left-data))
               (unless (or (> right count)
                           (funcall pred local-data
                                    (setf right-data (aref vector right))))
                 (setf local right
                       local-data right-data))
               (if (= local parent)
                   (return)
                   (setf (aref vector parent) local-data
                         (aref vector local) parent-data
                         parent local))))
    (if (= index 1)
        ;; Deleted the topmost element: copy it to V[0]
        (setf (aref vector 0) (aref vector 1))
        ;; Deleted something from middle: fix heap property
        ;; towards the head.
        (loop with child = index
              while (> child 1)
              do (let* ((parent (truncate child 2))
                        (parent-data (aref vector parent))
                        (child-data (aref vector child)))
                   (cond ((funcall pred parent-data child-data)
                          (return))
                         (t
                          (setf (aref vector child) parent-data
                                (aref vector parent) child-data
                                child parent))))))
    ;; Clean again
    (setf (heap-dirty heap) nil)
    victim))

(defun heap-delete (elt heap)
  "If ELT is in HEAP, removes it. Returns T if one or more references to ELT
were found and removed, NIL otherwise"
  (declare (type heap heap))
  (with-locked-heap (heap)
    (when (heap-dirty heap)
      (error "Heap dirty on entry to HEAP-DELETE."))
    (let* ((count (heap-count heap))
           (vector (heap-vector heap))
           (pred (heap-predicate heap)))
      (unless (zerop count)
        (let ((fringe (make-heap (lambda (x y)
                                   (funcall pred (aref vector x) (aref vector y))))))
          (declare (dynamic-extent))
          ;; Grab the lock now so we don't need to do that repeatedly.
          (with-locked-heap (fringe)
            (heap-insert 1 fringe)
            (loop until (heap-empty-p fringe)
                  do (let* ((parent (heap-pop fringe))
                            (parent-elt (aref vector parent)))
                       (cond ((eql elt parent-elt)
                              ;; Got it. Now delete them all.
                              (loop do (%heap-delete parent heap)
                                    while (eql elt (aref vector parent))))
                             ((funcall pred elt parent-elt)
                              ;; Searched past it.
                              (return-from heap-delete t))
                             (t
                              (let* ((left (* 2 parent))
                                     (right (1+ left)))
                                (unless (> left count)
                                  (heap-insert left fringe))
                                (unless (> right count)
                                  (heap-insert right fringe)))))))))))))

(defun map-heap (function heap)
  "Calls FUNCTION for each element in heap from top down, following the heap order."
  (declare (heap heap))
  (with-locked-heap (heap)
    (when (heap-dirty heap)
      (error "Heap dirty on entry to MAP-HEAP"))
    (let ((count (heap-count heap)))
      (unless (zerop count)
        (let* ((vector (heap-vector heap))
               (pred (heap-predicate heap))
               ;; Another heap to help us maintain order during traversal.
               (fringe (make-heap (lambda (x y)
                                    (funcall pred (aref vector x) (aref vector y))))))
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
            (heap-size fringe)))))))

