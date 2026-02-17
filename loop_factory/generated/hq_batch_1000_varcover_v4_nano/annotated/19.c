int main1(int m,int n,int q){
  int l, i, v, e;

  l=42;
  i=0;
  v=i;
  e=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 2*i;
    loop invariant i <= l;
    loop invariant l == 42;
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+2;
      i = i+1;
  }

}