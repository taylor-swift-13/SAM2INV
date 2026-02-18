int main1(int a,int m,int p,int q){
  int l, i, v;

  l=(a%12)+20;
  i=0;
  v=0;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v >= 0;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v % 2 == 0;

    loop invariant l == (a % 12) + 20;

    loop invariant l == (\at(a,Pre) % 12) + 20;

    loop invariant 0 <= i;

    loop invariant a == \at(a,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant q == \at(q,Pre);

    loop invariant 0 <= i && i <= l;

    loop invariant (v % 2) == 0;

    loop invariant l == (\at(a, Pre) % 12) + 20;

    loop assigns i, v;

  */
  while (i<l) {
      if ((i%5)==0) {
          v = v*v;
      }
      else {
          v = v+i;
      }
      v = v+v;
      i = i+1;
  }

}