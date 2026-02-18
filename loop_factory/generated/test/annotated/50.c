int main1(int a,int k,int m,int p){
  int l, i, v;

  l=31;
  i=0;
  v=4;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant a == \at(a, Pre) &&
                 k == \at(k, Pre) &&
                 m == \at(m, Pre) &&
                 p == \at(p, Pre) &&
                 l == 31 &&
                 0 <= i &&
                 i <= l;

    loop invariant l == 31;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant v % 4 == 0;

    loop invariant v >= 4;

    loop invariant v % 2 == 0;

    loop invariant 0 <= i && i <= l;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      i = i+1;
  }

}