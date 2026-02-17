int main1(int k,int n,int q){
  int l, i, v, u, g;

  l=58;
  i=0;
  v=2;
  u=n;
  g=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == i + 2;
    loop invariant u == n + (i*i + 5*i)/2;
    loop invariant g == n + i*(i-1)/2;
    loop assigns i, v, u, g;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      u = u+v;
      g = g+i;
      i = i+1;
  }

}