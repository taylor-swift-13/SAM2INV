int main1(int a,int b,int m,int q){
  int h, z, l, s, n, v, r, p;

  h=55;
  z=h;
  l=0;
  s=0;
  n=h;
  v=b;
  r=h;
  p=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant h == 55;
  loop invariant z == h;
  loop invariant z >= 3;
  loop invariant l >= 0;
  loop invariant s <= h;
  loop invariant s + l <= h + 1;
  loop invariant (l == 0 ==> s == 0);
  loop invariant (l > 0 ==> s == h - l + 1);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns l, s;
*/
while (z-3>=0) {
      s = h-l;
      l = l+1;
  }

}
