int main2(int m,int p,int q){
  int x;

  x=q;

  
  /*@

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant x <= \at(q, Pre);

    loop assigns x;

  */
  while (x>0) {
      x = x-1;
  }

  /*@ assert 1; */
}