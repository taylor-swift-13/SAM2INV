int main1(int a,int n,int p){
  int l, h, v, c;

  l=8;
  h=0;
  v=3;
  c=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 0;
  loop invariant v >= 3;
  loop invariant v % 3 == 0;

  loop invariant c >= p;
  loop invariant a == \at(a, Pre);
  loop invariant l == 8;
  loop invariant (c - p) % 3 == 0;
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop assigns c, v;
*/
while (1) {
      c = c+v;
      v = v+3;
      c = c+3;
      c = c+h;
  }

}
