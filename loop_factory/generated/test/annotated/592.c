int main1(){
  int izo, oy, wqm;
  izo=0;
  oy=(1%20)+10;
  wqm=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= oy;
  loop invariant 0 <= wqm;
  loop invariant 0 <= izo;
  loop invariant oy + wqm == 20 - izo;
  loop invariant oy == 11 - ((izo + 1) / 2);
  loop assigns izo, oy, wqm;
*/
while (1) {
      if (!(oy>0&&wqm>0)) {
          break;
      }
      if (!(!(izo%2==0))) {
          oy -= 1;
      }
      else {
          wqm = wqm - 1;
      }
      izo += 1;
  }
}