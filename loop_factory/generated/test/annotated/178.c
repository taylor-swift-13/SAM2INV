int main1(int b,int m,int p,int q){
  int l, i, v, u;

  l=56;
  i=0;
  v=1;
  u=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 56;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant i % 4 == 0;
    loop invariant u == \at(q, Pre) + i/4;
    loop invariant v == (i/4)*(i/4) + 2*\at(q,Pre)*(i/4) + 1;
    loop invariant 4*u - i == 4*\at(q,Pre);
    loop invariant 16*v == i*i + 8*\at(q,Pre)*i + 16;
    loop invariant b == \at(b,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant 0 <= i;
    loop invariant v == (i/4)*(i/4) + 2*\at(q, Pre)*(i/4) + 1;
    loop invariant u == \at(q,Pre) + i/4;
    loop invariant v == (i/4)*(i/4) + 2 * \at(q,Pre) * (i/4) + 1;
    loop invariant q == \at(q,Pre);
    loop invariant u == \at(q,Pre) + (i/4);
    loop assigns v, u, i;
  */
  while (i<l) {
      v = v+u+u;
      v = v+1;
      u = u+1;
      i = i+4;
  }

}