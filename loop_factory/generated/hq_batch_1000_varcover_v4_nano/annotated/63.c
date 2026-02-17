int main1(int b,int n,int q){
  int l, i, v, p, e, d, t, u;

  l=49;
  i=0;
  v=q;
  p=-1;
  e=l;
  d=n;
  t=1;
  u=-5;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant l == 49;

    loop invariant v % 2 == \at(q, Pre) % 2;

    loop assigns v, i;

  */
  while (i<l) {
      v = v*3+2;
      i = i+1;
  }

}