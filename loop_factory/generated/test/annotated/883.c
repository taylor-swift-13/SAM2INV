int main1(){
  int k0, lu0u, hr, os8;
  k0=1+12;
  lu0u=0;
  hr=0;
  os8=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= os8;
  loop invariant 0 <= lu0u <= k0;
  loop invariant hr == lu0u * os8 + (lu0u * (lu0u + 3)) / 2;
  loop invariant os8 == 5 - lu0u;
  loop assigns lu0u, hr, os8;
*/
while (lu0u<k0&&os8>0) {
      lu0u = lu0u + 1;
      hr += os8;
      hr += 1;
      os8--;
  }
}