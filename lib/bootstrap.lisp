(defmacro while (expr &body body)
  (let ((n (gensym)))
    `(labels ((,n ()
                (if ,expr
                  (progn ,@body (,n))
                  nil)))
       (,n))))

(defun 1+ (n)
  (+ n 1))

(defun 1- (n)
  (- n 1))

(defun length (l)
  (labels ((len (acc l)
                (if l
                  (len (1+ acc) (cdr l))
                  acc)))
           (len 0 l)))

(defun not (e)
  (if e nil t))

(defun caar (l) (car (car l)))
(defun cadr (l) (car (cdr l)))
(defun cdar (l) (cdr (car l)))
(defun cddr (l) (cdr (cdr l)))
