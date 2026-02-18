int main1(int k,int m,int n,int p){
  int l, i, v;

  l=k+11;
  i=0;
  v=k;

  
  /*@

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant l == k + 11;


    loop invariant v >= k;

    loop invariant k == \at(k,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant p == \at(p,Pre);


    loop invariant 0 <= i;

    loop invariant (l >= 0) ==> (i <= l);

    loop invariant (i == 0) ==> (v == k);

    loop invariant i >= 0;

    loop invariant (k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre));

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v;
      v = v+i;
      i = i+1;
  }

}