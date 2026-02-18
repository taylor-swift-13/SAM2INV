int main1(int b,int k,int p,int q){
  int l, i, v, c;

  l=80;
  i=0;
  v=l;
  c=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant i % 4 == 0;
    loop invariant c - i == k;
    loop invariant 4*v - 3*i == 4*l;
    loop invariant l == 80;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i <= l;
    loop invariant c == k + i;
    loop invariant v == l + 3 * (i/4);
    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant c - k == i;
    loop invariant 4*(v - 80) == 3*i;
    loop invariant v == 80 + 3 * (i / 4);
    loop invariant c == k + 4 * (i / 4);
    loop invariant k == \at(k, Pre) && b == \at(b, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop assigns v, c, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+3;
      c = c+3;
      c = c+1;
      i = i+4;
  }

}