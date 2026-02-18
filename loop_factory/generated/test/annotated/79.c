int main1(int b,int k,int p,int q){
  int l, i, v;

  l=b+18;
  i=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v >= 2*i + 2;
    loop invariant v % 2 == 0;
    loop invariant l == \at(b,Pre) + 18;

    loop invariant b == \at(b,Pre) && k == \at(k,Pre) && p == \at(p,Pre) && q == \at(q,Pre);
    loop invariant 0 <= i;
    loop invariant i <= l || l <= 0;
    loop invariant l == b + 18;
    loop invariant i >= 0;

    loop invariant v % 4 == 2;
    loop assigns v, i;
  */
while (i<l) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

}