int main1(int a,int k,int m,int p){
  int l, i, v, z;

  l=76;
  i=l;
  v=-3;
  z=k;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 76;

    loop invariant v == 73 - i;

    loop invariant l == 76;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && p == \at(p, Pre);

    loop invariant i + v == l - 3;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant v + i == l - 3;

    loop invariant v + i == 73;

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      i = i-1;
  }

}