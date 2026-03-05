int main1(){
  int v50h, e4, z6ft;
  v50h=15;
  e4=3;
  z6ft=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e4 <= v50h;
  loop invariant v50h == 15;
  loop invariant ((e4 == 3 && z6ft == 7) || (e4 >= 4 && z6ft == 4));
  loop assigns e4, z6ft;
*/
while (e4<v50h) {
      z6ft = e4%5;
      if (e4>=z6ft) {
          z6ft = (e4-z6ft)%5;
          z6ft = z6ft+z6ft-z6ft;
      }
      else {
          z6ft += z6ft;
      }
      e4 = e4 + 1;
      z6ft += 4;
  }
}