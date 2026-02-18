int main1(int a,int k,int m,int q){
  int l, i, v, b, p;

  l=k-1;
  i=l;
  v=k;
  b=-1;
  p=-5;

  
  /*@

    loop invariant l == k - 1;

    loop invariant i <= l;

    loop invariant v >= k;

    loop invariant b == 2*v - 2*k - 1;

    loop invariant i <= k - 1;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);


    loop invariant i <= \at(k,Pre) - 1;

    loop invariant (\at(k,Pre) > 0) ==> i >= 0;

    loop invariant (\at(k,Pre) >= 0) ==> v >= \at(k,Pre);

    loop invariant (\at(k,Pre) <= 0) ==> v <= \at(k,Pre);

    loop invariant (\at(k,Pre) >= 0) ==> b >= -1;

    loop invariant (\at(k,Pre) <= 0) ==> b <= -1;

    loop assigns v, b, i;

    loop variant i;

  */
  while (i>0) {
      v = v*2;
      b = b+v;
      i = i/2;
  }

}