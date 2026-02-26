int main1(int a,int n){
  int r, c, v;

  r=44;
  c=r;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == a + ((44 - c)/4) * (1 + r);
  loop invariant 0 <= c <= 44;
  loop invariant v >= a;
  loop invariant (v - a) % (1 + r) == 0;
  loop invariant 4*(v - a) == 45*(44 - c);
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c <= 44;
  loop invariant c >= 0;
  loop invariant v == a + (r + 1) * ((44 - c) / 4);
  loop invariant r == 44;
  loop invariant c % 4 == 0;
  loop invariant 4*(v - a) == (1 + r) * (r - c);
  loop invariant 0 <= c <= r;
  loop assigns v, c;
*/
while (c>=4) {
      v = v+1;
      v = v+r;
      c = c-4;
  }

}
