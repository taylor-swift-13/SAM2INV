int main1(int y){
  int sb, m7, d7h;
  sb=0;
  m7=(y%20)+10;
  d7h=(y%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m7 == ((\at(y, Pre) % 20) + 10) - ((sb + 1) / 2);
  loop invariant d7h == ((\at(y, Pre) % 15) + 8) - (sb / 2);
  loop invariant sb >= 0;
  loop invariant m7 + d7h + sb == ((\at(y, Pre) % 20) + 10) + ((\at(y, Pre) % 15) + 8);
  loop assigns sb, m7, d7h;
*/
while (m7>0&&d7h>0) {
      if (!(!(sb%2==0))) {
          m7 = m7 - 1;
      }
      else {
          d7h -= 1;
      }
      sb = sb + 1;
  }
}