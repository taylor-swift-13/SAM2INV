int main1(){
  int g60p, in, e3, b;
  g60p=1+3;
  in=0;
  e3=g60p;
  b=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g60p == 1+3;
  loop invariant in == 0;
  loop invariant in < g60p/2;
  loop invariant (b + 5) % 4 == 0;
  loop invariant 0 <= in;
  loop invariant in <= g60p - 3;
  loop invariant in >= 0;
  loop invariant b >= -5;
  loop assigns b, e3;
*/
while (in<=g60p-3) {
      if (in<g60p/2) {
          e3 += b;
      }
      else {
          e3 += 1;
      }
      b = b + g60p;
  }
}