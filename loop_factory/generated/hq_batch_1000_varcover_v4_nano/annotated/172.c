int main1(int a,int n,int p){
  int l, i, v, e, d, m, w;

  l=10;
  i=0;
  v=5;
  e=i;
  d=p;
  m=i;
  w=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == 5 + 3*i;
    loop invariant m == 4*i;
    loop invariant (i % 2 == 0) ==> (d == p + 2*i);
    loop invariant (i % 2 == 1) ==> (d == -p + 2*i - 2);
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, d, m, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+3;
      d = d+4;
      m = m+4;
      d = m-d;
      i = i+1;
  }

}