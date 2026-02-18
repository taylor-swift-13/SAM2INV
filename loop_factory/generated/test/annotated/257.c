int main1(int k,int m){
  int l, i, v, p;

  l=27;
  i=0;
  v=l;
  p=k;

  
  /*@

    loop invariant v - 5*p == 27 - 5*k;

    loop invariant v >= 27;

    loop invariant p >= k;

    loop invariant l == 27;

    loop invariant m == \at(m, Pre);

    loop invariant v == 27 + 5*(p - k);

    loop invariant k == \at(k, Pre);

    loop invariant v == l + 5*(p - k);

    loop invariant v <= l;

    loop assigns v, p;

  */
  while (v<l) {
      if (v<l) {
          v = v+1;
      }
      v = v+4;
      p = p+1;
  }

}