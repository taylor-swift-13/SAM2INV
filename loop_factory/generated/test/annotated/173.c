int main1(int b,int m,int n,int p){
  int l, i, v;

  l=n-7;
  i=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == n - 7;
    loop invariant i >= 0;
    loop invariant v % 2 == 0;
    loop invariant v >= 4;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i;
    loop invariant v >= i;
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == \at(n,Pre) - 7;
    loop invariant b == \at(b,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant v >= 2*i + 4;
    loop invariant m == \at(m,Pre);
    loop assigns i, v;
  */
while (i<l) {
      if (v+6<l) {
          v = v+v;
      }
      v = v+i;
      v = v+v;
      i = i+1;
  }

}