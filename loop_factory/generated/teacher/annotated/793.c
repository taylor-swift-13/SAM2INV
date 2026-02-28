int main1(int a,int q){
  int h, b, c, r;

  h=(q%7)+16;
  b=h;
  c=b;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (q % 7) + 16;
  loop invariant b == h;
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant (c == h && r == c) || r == 2*c - 3;
  loop invariant c >= h;
  loop invariant r >= c;
  loop invariant c >= b;
  loop invariant (c - b) % 3 == 0;
  loop invariant r >= b;
  loop invariant c >= 0;
  loop invariant h == ((\at(q,Pre) % 7) + 16);
  loop invariant 0 <= c - b;
  loop invariant r <= 2*c - 3;
  loop invariant 10 <= b <= 22;
  loop assigns c, r;
*/
while (b>=2) {
      r = c;
      c = c+2;
      c = c+1;
      r = r+c;
  }

}
