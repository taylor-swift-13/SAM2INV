int main1(int z){
  int c29, o, t, wz;
  c29=21;
  o=0;
  t=0;
  wz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == t % c29;
  loop invariant 0 <= t;
  loop invariant 0 <= wz;
  loop invariant wz <= t * (c29 - 1);
  loop assigns o, t, wz;
*/
while (1) {
      if (!(t < z)) {
          break;
      }
      o = (o + 1) % c29;
      t += 1;
      wz = wz + o;
  }
}