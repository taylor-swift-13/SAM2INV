int main1(int a,int k,int m,int p){
  int l, i, v, z;

  l=76;
  i=l;
  v=-3;
  z=k;

  
  /*@

    loop invariant v + z == \at(k, Pre) - 3;

    loop invariant i + v == 73;

    loop invariant i >= 0;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant z - i == k - 76;

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= 76;

    loop invariant v == 73 - i;

    loop invariant z == i + k - 76;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && p == \at(p, Pre);

    loop invariant a == \at(a, Pre) &&
                   k == \at(k, Pre) &&
                   m == \at(m, Pre) &&
                   p == \at(p, Pre) &&
                   v + i == l - 3 &&
                   z == k - l + i &&
                   i >= 0 &&
                   i <= l;

    loop invariant z == k - 76 + i;

    loop invariant l == 76;

    loop assigns v, z, i;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      z = z-1;
      i = i-1;
  }

}