int main1(int k,int m,int n,int p){
  int l, i, v, u;

  l=9;
  i=l;
  v=8;
  u=-5;

  
  /*@

    loop invariant v + 2*i == 26;

    loop invariant u == i - 14;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v - 2*(l - i) == 8;

    loop invariant u == i - l - 5;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v == 26 - 2*i;

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop assigns v, u, i;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      u = u-1;
      v = v+1;
      i = i-1;
  }

}