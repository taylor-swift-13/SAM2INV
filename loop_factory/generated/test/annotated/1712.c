int main1(){
  int ey, rn, hbgq, pp8;
  ey=1*2;
  rn=0;
  hbgq=rn;
  pp8=rn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hbgq == 4 * rn;
  loop invariant pp8 == 0;
  loop invariant ey == 2;
  loop invariant 0 <= rn <= ey;
  loop assigns rn, hbgq, pp8;
*/
while (rn < ey) {
      rn += 1;
      hbgq = hbgq + 3;
      pp8 = (pp8+hbgq)+(-(hbgq));
      hbgq++;
  }
}