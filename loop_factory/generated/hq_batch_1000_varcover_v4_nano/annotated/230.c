int main1(int b,int p,int q){
  int l, i, v, a, n, z;

  l=42;
  i=0;
  v=l;
  a=4;
  n=0;
  z=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant v == l + i;
    loop invariant a == 4 + l*i + i*(i+1)/2;
    loop invariant n == i*(p + 1);
    loop assigns v, a, n, i;
  */
  while (i<l) {
      v = v+1;
      a = a+v;
      n = n+z;
      n = n+1;
      i = i+1;
  }

}