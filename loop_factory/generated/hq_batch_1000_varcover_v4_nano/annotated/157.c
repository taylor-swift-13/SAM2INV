int main1(int b,int n,int p){
  int l, i, v, z, r, o, s, w, a, y;

  l=60;
  i=l;
  v=n;
  z=n;
  r=n;
  o=p;
  s=-5;
  w=-4;
  a=-3;
  y=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant (i == l) ==> (v == n);
    loop invariant (i == l) ==> (z == n);
    loop assigns v, z, i;
  */
  while (i>0) {
      v = v*2+1;
      z = z*v+1;
      i = i/2;
  }

}