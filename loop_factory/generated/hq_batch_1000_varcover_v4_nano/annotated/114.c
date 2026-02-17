int main1(int a,int b,int m){
  int l, i, v, y;

  l=41;
  i=l;
  v=b;
  y=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == b + 2*y*(l - i);
    loop invariant l == 41;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+y+y;
      i = i-1;
  }

}