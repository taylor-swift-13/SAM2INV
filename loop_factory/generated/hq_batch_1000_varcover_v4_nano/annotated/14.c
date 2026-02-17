int main1(int a,int m,int p){
  int l, i, v, j, n, e, b;

  l=11;
  i=0;
  v=-4;
  j=m;
  n=p;
  e=m;
  b=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == -4 + i * j;
    loop invariant l == 11;
    loop invariant j == m;
    loop invariant m == \at(m, Pre);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+j;
      i = i+1;
  }

}