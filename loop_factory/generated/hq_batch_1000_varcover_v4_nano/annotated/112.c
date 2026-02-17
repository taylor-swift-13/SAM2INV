int main1(int a,int k,int q){
  int l, i, v, n;

  l=(k%15)+18;
  i=0;
  v=i;
  n=a;

  
  /*@

    loop invariant l == (k % 15) + 18;

    loop invariant n == a;

    loop invariant v == i*(2*n + 1);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+n+n;
      v = v+1;
      i = i+1;
  }

}