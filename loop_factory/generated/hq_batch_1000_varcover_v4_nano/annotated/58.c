int main1(int b,int n,int p){
  int l, i, v, r, e, t, z, q, h;

  l=78;
  i=0;
  v=n;
  r=6;
  e=-2;
  t=l;
  z=3;
  q=p;
  h=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == n);
    loop invariant l == 78;
    loop assigns v, i;
  */
  while (i<l) {
      v = v*3+3;
      i = i+1;
  }

}