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

(defun reverse (l)
  (labels ((impl (acc l)
                 (if l
                   (impl (cons (car l) acc) (cdr l))
                   acc)))
    (impl '() l)))

(defun > (l)
  (apply #'< (reverse l)))
(defun >= (l)
  (apply #'<= (reverse l)))

(defun assoc (k alist)
  (labels ((searcher (k alist)
                     (if alist
                       (if (and (car alist) (eql k (caar alist)))
                         (car alist)
                         (searcher k (cdr alist)))
                       nil)))
    (searcher k alist)))
