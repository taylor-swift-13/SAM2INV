int main1(int a,int m,int n){
  int l, i, v, s, u, p, k;

  l=38;
  i=l;
  v=m;
  s=8;
  u=i;
  p=l;
  k=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == m + 3*(l - i);

    loop invariant u == 5*l - 4*i;

    loop invariant m == \at(m, Pre);

    loop assigns v, u, i;

    loop variant i;

  */
  while (i>0) {
      v = v+3;
      u = u+4;
      i = i-1;
  }

}