int main1(int k,int n,int q){
  int l, i, v, z, d, m, w, j, b, x;

  l=18;
  i=l;
  v=l;
  z=4;
  d=k;
  m=q;
  w=0;
  j=-6;
  b=-3;
  x=-6;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == l + (l*(l+1))/2 - (i*(i+1))/2;

    loop invariant v <= l + (l*(l+1))/2;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+i;
      i = i-1;
  }

}