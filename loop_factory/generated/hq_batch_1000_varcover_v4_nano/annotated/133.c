int main1(int b,int n,int q){
  int l, i, v, o;

  l=(b%7)+14;
  i=0;
  v=n;
  o=n;

  
  /*@

    loop invariant v == n + i*(i+1)/2;

    loop invariant o == n - i;

    loop invariant 0 <= i <= l;

    loop invariant l == (b % 7) + 14;

    loop assigns v, o, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      o = o-1;
      v = v+i;
      i = i+1;
  }

}