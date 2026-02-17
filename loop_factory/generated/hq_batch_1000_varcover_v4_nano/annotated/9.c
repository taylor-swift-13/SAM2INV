int main1(int k,int n,int q){
  int l, i, v, u, t, e, w, j;

  l=65;
  i=0;
  v=n;
  u=8;
  t=2;
  e=l;
  w=-6;
  j=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == n;
    loop invariant u == 8;
    loop invariant t == 2;
    loop invariant l == 65;
    loop invariant e == v + u + t || e == l;
    loop assigns e, i;
    loop variant l - i;
  */
  while (i<l) {
      e = v+u+t;
      i = i+1;
  }

}