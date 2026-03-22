int main1(int d){
  int k0, o, dz6, u70, sya;
  k0=d;
  o=0;
  dz6=0;
  u70=3;
  sya=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sya == 5 * o;
  loop invariant dz6 >= 3 * o;
  loop invariant (k0 < 0) || (0 <= o && o <= k0);
  loop invariant o >= 0;
  loop invariant u70 == 3 + 5 * o * (o - 1) / 2;
  loop invariant dz6 == 3 * o + 5 * (o - 1) * o * (o - 2) / 6;
  loop invariant k0 == d;
  loop invariant u70 == 3 + (5 * o * (o - 1)) / 2;
  loop invariant dz6 == 3 * o + (5 * (o - 1) * o * (o - 2)) / 6;
  loop invariant 0 <= o;
  loop invariant sya >= 0;
  loop invariant dz6 >= 0;
  loop invariant u70 >= 3;
  loop invariant ((u70 - 3) % 5) == 0;
  loop invariant dz6 <= o * u70;
  loop assigns dz6, u70, sya, o;
*/
while (1) {
      dz6 += u70;
      u70 = u70 + sya;
      sya = sya + 5;
      o = o + 1;
      if (o>=k0) {
          break;
      }
  }
}