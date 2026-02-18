int main1(int b,int m,int n,int p){
  int l, i, v;

  l=n-7;
  i=0;
  v=4;

  
  /*@

    loop invariant l == n - 7;

    loop invariant 0 <= i;


    loop invariant 4 <= v;

    loop invariant v >= 4 + i*(i-1)/2;

    loop invariant l == \at(n,Pre) - 7;


    loop invariant n == \at(n,Pre);

    loop invariant b == \at(b,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant v >= 4;

    loop invariant v - i >= 3;

    loop invariant v >= i;

    loop invariant l == \at(n,Pre) - 7 && i >= 0 && v >= 4 &&
                   b == \at(b,Pre) && m == \at(m,Pre) && n == \at(n,Pre) && p == \at(p,Pre);

    loop assigns i, v;

  */
  while (i<l) {
      if (v+6<l) {
          v = v+v;
      }
      v = v+i;
      i = i+1;
  }

}