int main1(){
  int xv, c9, tf6q, z, d9, ca3;
  xv=(1%7)+9;
  c9=1;
  tf6q=c9;
  z=4;
  d9=0;
  ca3=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tf6q > 0;
  loop invariant ca3 > 0;
  loop invariant xv == 10;
  loop invariant 0 <= d9 <= xv;
  loop invariant 4 <= z;
  loop invariant 3 <= ca3;
  loop assigns z, tf6q, d9, ca3;
*/
while (d9<xv) {
      z = z*ca3;
      tf6q = tf6q*ca3+4;
      d9++;
      ca3 = ca3*4+(d9%7)+2;
  }
}