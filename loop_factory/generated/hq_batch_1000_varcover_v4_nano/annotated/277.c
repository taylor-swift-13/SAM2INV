int main1(int a,int k,int m,int n){
  int l, i, v, u, g, y, q, h, o, d;

  l=46;
  i=0;
  v=n;
  u=6;
  g=m;
  y=4;
  q=-2;
  h=a;
  o=k;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant (i == 0) ==> (v == n);
    loop invariant (i == 0) ==> (u == 6);
    loop assigns v, u, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2+2;
      u = u*v+2;
      i = i+1;
  }

}