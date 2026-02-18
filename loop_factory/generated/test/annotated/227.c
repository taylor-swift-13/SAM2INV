int main1(int m,int p){
  int l, i, v;

  l=41;
  i=0;
  v=8;

  
  /*@

    loop invariant i % 2 == 0;

    loop invariant 0 <= i;

    loop invariant 8 <= v <= l - 7;

    loop invariant v <= 8 + i/2;

    loop invariant p == \at(p, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant i <= l + 1;

    loop invariant 8 <= v <= 34;

    loop invariant p == \at(p,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant l == 41;

    loop invariant v == 8 + i/2;


    loop invariant (i % 2) == 0;

    loop invariant v >= 8;

    loop invariant v <= l - 7;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if (v+7<l) {
          v = v+1;
      }
      i = i+2;
  }

}