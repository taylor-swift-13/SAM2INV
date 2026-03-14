int main1(){
  int cq, mm, q92;
  cq=0;
  mm=(1%20)+10;
  q92=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q92 >= 0;
  loop invariant cq >= 0;
  loop invariant mm == 11 - ((cq + 1) / 2);
  loop invariant q92 == 9 - (cq / 2);
  loop assigns mm, q92, cq;
*/
while (mm>0&&q92>0) {
      if (cq%2==0) {
          mm = mm - 1;
      }
      else {
          q92 -= 1;
      }
      cq += 1;
  }
}