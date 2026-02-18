int main1(int b,int k,int m,int p){
  int l, i, v, h, y;

  l=64;
  i=0;
  v=k;
  h=-2;
  y=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant y == m + i * k;

    loop invariant b == \at(b, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant v == k;
    loop invariant l == 64;
    loop invariant h == -2 + i * m + i + (k + 1) * i * (i - 1) / 2;
    loop invariant 0 <= i && i <= l;
    loop invariant y == m + v*i;
    loop invariant h == -2 + i*(m+1) + (v+1)*i*(i-1)/2;
    loop invariant 0 <= i;
    loop invariant y == m + i * v;
    loop invariant h == -2 + i * m + (((v+1) * i * (i - 1)) / 2) + i;
    loop invariant y == \at(m, Pre) + i * v;

    loop invariant v == \at(k, Pre);
    loop assigns h, y, i;
    loop variant l - i;
  */
  while (i<l) {
      h = h+y;
      y = y+v;
      h = h+i;
      h = h+1;
      i = i+1;
  }

}