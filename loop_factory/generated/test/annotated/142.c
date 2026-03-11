int main1(){
  int q7, rmid, w53;
  q7=37;
  rmid=0;
  w53=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rmid <= q7;
  loop invariant q7 == 37;
  loop invariant (rmid == 0 ==> w53 == 11) && (rmid > 0 ==> w53 == 0);
  loop assigns w53, rmid;
*/
while (rmid<q7) {
      w53 = q7-rmid;
      w53 = w53 - w53;
      rmid += 1;
  }
}