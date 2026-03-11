int main1(){
  int z, zr, mv, a, j7, eh;
  z=1*5;
  zr=0;
  mv=21;
  a=0;
  j7=1;
  eh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a + mv == 21;
  loop invariant j7 == zr + 1;
  loop invariant 0 <= mv;
  loop invariant zr <= z;
  loop invariant 0 <= zr;
  loop invariant 0 <= a;
  loop invariant 0 <= eh;
  loop invariant eh <= j7;
  loop assigns a, eh, j7, mv, zr;
*/
while (1) {
      if (!(mv>0&&zr<z)) {
          break;
      }
      if (mv<=j7) {
          eh = mv;
      }
      else {
          eh = j7;
      }
      zr += 1;
      j7 += 1;
      a = a + eh;
      mv = mv - eh;
  }
}