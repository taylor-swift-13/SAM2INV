int main1(int a,int m,int q){
  int l, i, v, k;

  l=80;
  i=0;
  v=q;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v == q + 2*i;
    loop invariant k == m + i*i + i*q + 5*i;
    loop assigns i, v, k;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      k = k+v;
      k = k+5;
      v = v+1;
      i = i+1;
  }

}