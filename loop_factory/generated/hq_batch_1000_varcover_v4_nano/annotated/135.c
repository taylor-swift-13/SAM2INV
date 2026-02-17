int main1(int m,int n,int q){
  int l, i, v, r, d, a, t;

  l=(m%8)+16;
  i=l;
  v=i;
  r=l;
  d=5;
  a=m;
  t=n;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant r >= 0;

    loop invariant r <= l;

    loop invariant v >= 0;

    loop invariant i < l ==> v == r*r + r;

    loop assigns v, r, i;

    loop variant i;

  */
  while (i>0) {
      v = v*2;
      r = r/2;
      v = r*r;
      v = v+r;
      i = i-1;
  }

}