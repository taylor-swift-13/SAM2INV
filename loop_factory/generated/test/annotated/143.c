int main1(int b,int m,int p,int q){
  int l, i, v;

  l=b+12;
  i=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == b + 12;
    loop invariant v == 4 + i*(i+1)/2;
    loop invariant 0 <= i;

    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant v == 4 + i + i * (i - 1) / 2;
    loop invariant b == \at(b,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant l == \at(b,Pre) + 12;
    loop invariant (l < 0) || (i <= l);
    loop assigns i, v;
  */
  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+1;
  }

}