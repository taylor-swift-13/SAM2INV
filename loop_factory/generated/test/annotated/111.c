int main1(int a,int b,int k,int p){
  int l, i, v;

  l=b;
  i=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant (l <= 0) || (i <= l);
    loop invariant v >= \at(k, Pre);

    loop invariant l == \at(b, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);

    loop invariant l == b;
    loop invariant v >= k;
    loop invariant (v - k) % 8 == 0;

    loop invariant l == \at(b,Pre);

    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant p == \at(p,Pre);
    loop assigns i, v;
    loop variant l - i;
  */
while (i<l) {
      if ((i%8)==0) {
          v = v+i;
      }
      i = i+1;
  }

}