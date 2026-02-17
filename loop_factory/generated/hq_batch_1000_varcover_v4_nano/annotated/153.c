int main1(int k,int n,int p){
  int l, i, v, t, b, f;

  l=30;
  i=l;
  v=6;
  t=l;
  b=3;
  f=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 6 + 5*(l - i);
    loop invariant b == 3 + 5*(l - i) - 3*( (l/7) - (i/7) );
    loop invariant 0 <= i && i <= l;
    loop invariant l == 30;
    loop assigns v, b, i;
    loop variant i;
  */
  while (i>0) {
      v = v+5;
      b = b+1;
      if ((i%7)==0) {
          b = b+1;
      }
      else {
          b = b+4;
      }
      i = i-1;
  }

}