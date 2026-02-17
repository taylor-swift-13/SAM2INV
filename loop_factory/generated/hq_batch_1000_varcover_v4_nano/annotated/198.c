int main1(int a,int k,int m){
  int l, i, v, d;

  l=9;
  i=0;
  v=k;
  d=m;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v == k + 2*d*i;

    loop invariant d == m;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+d+d;
      i = i+1;
  }

}