int main1(){
  int z1u, btt, wp3i, ks7, wl;
  z1u=1+13;
  btt=0;
  wp3i=btt;
  ks7=0;
  wl=btt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wl == z1u * btt;
  loop invariant ks7 == z1u * (((btt - 1) * btt * (2 * btt - 1)) / 6);
  loop invariant wp3i == 0;
  loop invariant 0 <= btt;
  loop invariant btt <= z1u;
  loop assigns ks7, wp3i, btt, wl;
*/
while (btt < z1u) {
      ks7 = ks7 + btt*wl;
      wp3i = wp3i*2;
      btt = btt + 1;
      wl += z1u;
  }
}