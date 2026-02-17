int main1(int k,int m,int p){
  int l, i, v, n, o;

  l=50;
  i=0;
  v=k;
  n=8;
  o=i;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == k + i;

    loop invariant n == i*i + i*(2*k + 1) + 8;

    loop invariant l == 50;

    loop assigns i, v, n;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      n = n+v;
      n = n+v;
      i = i+1;
  }

}