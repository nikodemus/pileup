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

(defpackage :pileup-tests
  (:use :cl :pileup :hu.dwim.stefil)
  (:export
   #:pileup-tests))

(in-package :pileup-tests)

(defsuite (test-pileup :in root-suite) ()
  (run-child-tests))

(in-suite test-pileup)

(deftest heap-type ()
  (is (heap-p (make-heap #'<)))
  (is (not (heap-p (cons t t))))
  (is (subtypep 'heap 'structure-object))
  (is (< heap-size-limit array-dimension-limit)))

(deftest heap-basics ()
  (let ((heap (make-heap #'< :name "test" :size 128)))
    (is (heap-empty-p heap))
    (is (zerop (heap-count heap)))
    (is (= 128 (heap-size heap)))
    (is (eq #'< (heap-predicate heap)))
    (is (equal "test" (heap-name heap)))
    (heap-insert 0 heap)
    (is (not (heap-empty-p heap)))
    (dotimes (i 127)
      (heap-insert i heap))
    (heap-insert -1 heap)
    (is (= 129 (heap-count heap)))
    (is (= 256 (heap-size heap)))
    (is (= -1 (heap-top heap)))
    (heap-insert 100 heap)
    (is (< 130 (heap-size heap)))
    (is (= 130 (heap-count heap)))
    (is (= -1 (heap-top heap)))
    (is (= -1 (heap-pop heap)))
    (is (= 0 (heap-pop heap)))
    (is (= 0 (heap-top heap)))
    (is (< 129 (heap-size heap)))
    (is (= 128 (heap-count heap)))
    (dotimes (i 127)
      (when (= i 100)
        (is (= 100 (heap-pop heap))))
      (is (= i (heap-pop heap))))
    (is (= 0 (heap-count heap)))
    (is (heap-empty-p heap))))

(deftest heap-stress ()
  (let ((heap (make-heap #'>)))
    (loop repeat 10000
         do (heap-insert (random 1.0) heap))
    (is (= 10000 (heap-count heap)))
    (let ((prev 1.0)
          (oops 0))
      (loop repeat 10000
            do (let ((this (heap-pop heap)))
                 (unless (>= prev this)
                   (incf oops))
                 (setf prev this)))
      (is (zerop oops))
      (is (heap-empty-p heap)))))

(deftest heap-traverse ()
  (let ((heap (make-heap #'>)))
    (dotimes (i 128)
      (heap-insert i heap))
    (let ((x 128))
      (map-heap (lambda (i)
                  (decf x)
                  (is (eql i x)))
                heap)
      (is (zerop x))
      (is (= 128 (heap-count heap))))
    ;; Now break the heap by inserting a bad element.
    (ignore-errors
      (heap-insert "ding" heap))
    (is (eq :dirty (pileup::heap-state heap)))
    ;; Unordered map to the rescue.
    (let ((new (make-heap #'>)))
      (map-heap (lambda (i)
                  (when (integerp i)
                    (heap-insert i new)))
                heap
                :ordered nil)
      (setf heap new))
    (let ((x 128))
      (map-heap (lambda (i)
                  (decf x)
                  (is (eql i x)))
                heap)
      (is (zerop x))
      (is (= 128 (heap-count heap))))))
