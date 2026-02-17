int main1(int b,int n,int p){
  int l, i, v, g, t, s;

  l=56;
  i=0;
  v=i;
  g=i;
  t=l;
  s=i;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v >= 0;

    loop invariant g >= 0;

    loop invariant (i > 0) ==> (v >= 3);

    loop invariant (i > 0) ==> (g >= 3);

    loop assigns v, g, i;

  */
  while (i<l) {
      v = v*3+3;
      g = g*v+3;
      i = i+1;
  }

}