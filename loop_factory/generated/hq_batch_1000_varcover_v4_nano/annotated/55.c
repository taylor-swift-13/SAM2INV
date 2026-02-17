int main1(int a,int b,int q){
  int l, i, v, x, d;

  l=54;
  i=0;
  v=5;
  x=2;
  d=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant i % 3 == 0;
    loop invariant v == 5 - 2*i;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+x+d;
      i = i+3;
  }

}