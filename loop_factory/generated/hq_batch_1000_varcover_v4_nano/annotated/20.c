int main1(int k,int m,int n){
  int l, i, v, r, g, b, s;

  l=k+19;
  i=l;
  v=m;
  r=2;
  g=l;
  b=-4;
  s=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == k + 19;
    loop invariant v >= m;
    loop invariant (m <= l) ==> (v <= l);
    loop assigns v;
    loop variant l - v;
  */
  while (v<l) {
      if (v<l) {
          v = v+1;
      }
  }

}