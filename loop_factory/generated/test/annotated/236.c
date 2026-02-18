int main1(int k,int q){
  int l, i, v;

  l=k+8;
  i=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == k + 8;

    loop invariant 0 <= i;
    loop invariant (v - i) % 2 == 1;
    loop invariant v >= 1;
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant 1 + i <= v;
    loop invariant v <= 1 + 3*i;
    loop invariant k == \at(k,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant v >= 1 + i;
    loop invariant v >= i + 1;
    loop invariant v - i >= 1;
    loop invariant ((v - i) % 2 == 1);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (v+6<l) {
          v = v+2;
      }
      v = v+1;
      i = i+1;
  }

}