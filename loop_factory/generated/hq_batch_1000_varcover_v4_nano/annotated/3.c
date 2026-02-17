int main1(int k,int m,int q){
  int l, i, v, x, d, n, y, a, c;

  l=36;
  i=1;
  v=5;
  x=-5;
  d=m;
  n=-3;
  y=k;
  a=l;
  c=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i > 0;
    loop invariant i <= 2*l;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == 36;
    loop assigns i;
    loop variant l - i;
  */
  while (i<l) {
      i = i*2;
  }

}