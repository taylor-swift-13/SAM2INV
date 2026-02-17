int main1(int a,int k,int m){
  int l, i, v, e, h, t, j, w;

  l=37;
  i=l;
  v=m;
  e=l;
  h=-6;
  t=m;
  j=0;
  w=i;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v >= m;

    loop invariant 2*(e - l) == (v - m) * (v + m + 7);

    loop assigns v, e, i;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      e = e+v;
      e = e+3;
      i = i/2;
  }

}