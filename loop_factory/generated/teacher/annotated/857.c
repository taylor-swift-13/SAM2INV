int main1(int k,int q){
  int x, o, b, r;

  x=36;
  o=0;
  b=6;
  r=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre) && q == \at(q, Pre) && r == 1;
  loop invariant b == 6 + 4*o && o <= x && o >= 0;
  loop invariant o <= x;
  loop invariant o >= 0;
  loop invariant b - 6 == 4*o;
  loop invariant r == 1;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == 6 + 2*(r+1)*o;
  loop invariant x == 36;
  loop invariant b == 6 + 4*o;
  loop invariant o >= 0 && o <= x;
  loop invariant b == 6 + o*(2 + 2*r);
  loop invariant o <= x && k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant b == 6 + o * (2 + 2 * r);
  loop invariant 0 <= o;
  loop invariant b <= 6 + x * (2 + 2 * r);
  loop invariant b == 6 + (2 + 2*r) * o;
  loop assigns b, o;
*/
while (1) {
      if (o>=x) {
          break;
      }
      b = b+2;
      o = o+1;
      b = b+r+r;
  }

}
