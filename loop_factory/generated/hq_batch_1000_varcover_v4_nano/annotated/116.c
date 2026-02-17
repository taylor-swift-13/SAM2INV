int main1(int k,int m,int p){
  int l, i, v, e, q, d;

  l=69;
  i=0;
  v=l;
  e=l;
  q=2;
  d=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant e == 69 + 35*i*i - 33*i;
    loop invariant q == 2 + 70*i;
    loop invariant v == l;
    loop assigns e, q, i;
  */
  while (i<l) {
      e = e+q;
      q = q+v;
      q = q+1;
      i = i+1;
  }

}