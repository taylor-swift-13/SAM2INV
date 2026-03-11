int main1(){
  int tz, uj, jsi, vb, jme, uto;
  tz=1;
  uj=0;
  jsi=0;
  vb=0;
  jme=0;
  uto=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tz == 1;
  loop invariant 0 <= uto;
  loop invariant uto <= uj;
  loop invariant jsi >= uj;
  loop invariant jme <= (uj + 39) / 40;
  loop invariant 0 <= uj <= tz;
  loop invariant 0 <= vb;
  loop invariant 0 <= jme;
  loop invariant jme + vb + jsi + uto == 2 * uj;
  loop invariant jme <= (uj / 40) + 1;
  loop invariant vb  <= (uj / 24);
  loop invariant 0 <= jsi;
  loop invariant uto >= 0;
  loop assigns uto, jme, vb, jsi, uj;
*/
while (uj<tz) {
      if (!(!(uj%8==0))) {
          if (uj%5==0) {
              jme++;
          }
          else {
              if (uj%3==0) {
                  vb = vb + 1;
              }
              else {
                  jsi += 1;
              }
          }
      }
      else {
          uto += 1;
      }
      uj++;
      jsi += 1;
  }
/*@
  assert !(uj<tz) &&
         (tz == 1);
*/


  int __aux_12=0;
  while (__aux_12 < 2) { __aux_12 = __aux_12 + 1; }
}