int main1(){
  int a, cs, yxo, sy, i, wm0;
  a=1+11;
  cs=0;
  yxo=0;
  sy=0;
  i=0;
  wm0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= cs <= a;
  loop invariant 0 <= i <= cs;
  loop invariant 0 <= sy <= cs;
  loop invariant 0 <= wm0 <= cs;
  loop invariant 0 <= yxo <= 2*cs;
  loop invariant yxo >= i + sy;
  loop invariant wm0 + yxo + i + sy == 2 * cs;
  loop invariant 0 <= i <= 1;
  loop assigns cs, i, sy, wm0, yxo;
*/
while (cs<a) {
      if (!(!(cs%11==0))) {
          if (cs%9==0) {
              i = i + 1;
          }
          else {
              if (cs%6==0) {
                  sy += 1;
              }
              else {
                  yxo++;
              }
          }
      }
      else {
          wm0 = wm0 + 1;
      }
      yxo++;
      cs++;
  }
}