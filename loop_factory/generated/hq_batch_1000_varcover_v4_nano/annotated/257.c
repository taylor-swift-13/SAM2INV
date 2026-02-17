int main1(int a,int k,int m){
  int l, i, v, w, u, x;

  l=32;
  i=1;
  v=i;
  w=0;
  u=1;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 32;
    loop invariant i <= l;
    loop invariant i > 0;
    loop invariant w == 0;
    loop invariant v % i == 0;
    loop invariant v >= i;
    loop assigns v, w;
  */
while (i<l) {
      v = v*2;
      w = w/2;
      v = v+i;
  }

}