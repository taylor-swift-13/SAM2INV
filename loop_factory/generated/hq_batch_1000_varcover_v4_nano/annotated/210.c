int main1(int m,int n,int q){
  int l, i, v, d, r, a;

  l=54;
  i=l;
  v=n;
  d=q;
  r=6;
  a=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 54;
    loop invariant (n >= 0) ==> (v >= 0);
    loop invariant (n <= 0) ==> (v <= 0);
    loop assigns v, i;
  */
  while (i>0) {
      v = v*2;
      i = i/2;
  }

}