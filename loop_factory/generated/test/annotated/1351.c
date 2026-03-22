int main1(){
  int olje, g, n4, gy, i0b, f;
  olje=1*2;
  g=(1%60)+60;
  n4=(1%9)+2;
  gy=0;
  i0b=0;
  f=olje;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i0b;
  loop invariant i0b < n4;
  loop invariant gy >= 0;
  loop invariant f >= olje;
  loop invariant g >= n4*gy + i0b;
  loop assigns f, gy, i0b;
*/
while (1) {
      if (g<=n4*gy+i0b) {
          break;
      }
      if (i0b==n4-1) {
          i0b = 0;
          gy += 1;
      }
      else {
          i0b += 1;
      }
      f = (gy)+(f);
  }
}