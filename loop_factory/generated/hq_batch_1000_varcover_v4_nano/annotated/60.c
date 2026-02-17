int main1(int m,int n,int p){
  int l, i, v, z, y, g, f, j;

  l=(p%13)+17;
  i=l;
  v=-2;
  z=8;
  y=-6;
  g=0;
  f=n;
  j=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == (p % 13) + 17;
    loop invariant 0 <= i && i <= l;
    loop invariant v < 0;
    loop invariant v % 2 == 0;
    loop invariant i > 0 ==> v < 0;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v*4;
      i = i/2;
  }

}