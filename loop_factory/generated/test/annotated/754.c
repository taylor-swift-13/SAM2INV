int main1(){
  int t9, cz, xey, qfc, hbu;
  t9=(1%20)+1;
  cz=(1%25)+1;
  xey=0;
  qfc=0;
  hbu=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t9 % 2 == 0;
  loop invariant xey >= 0;
  loop invariant hbu >= 12;
  loop invariant qfc == 0;
  loop invariant xey < t9;
  loop invariant 0 <= cz <= 2;
  loop invariant t9 >= 2;
  loop invariant t9 * cz <= 4;
  loop assigns xey, cz, t9, hbu, qfc;
*/
while (cz!=0) {
      if (cz%2==1) {
          xey = xey + t9;
          cz = cz - 1;
      }
      else {
      }
      t9 = 2*t9;
      cz = cz/2;
      hbu = ((cz%6))+(hbu);
      qfc = qfc*4;
  }
}