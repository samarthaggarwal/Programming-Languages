let rec fib n = match n with 0->1 | 1->1 | n->n*(fib n-1);;
fib 5;;
