int main1(int s){
  int q1, r1, xcyp;
  q1=80;
  r1=0;
  xcyp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xcyp;
  loop invariant xcyp <= q1;
  loop invariant r1 == xcyp % 5;
  loop invariant ((s - \at(s,Pre) - (xcyp*(xcyp+1))/2) % 4) == 0;
  loop assigns r1, xcyp, s;
*/
while (1) {
      if (!(xcyp<q1)) {
          break;
      }
      r1 = (r1+1)%5;
      xcyp += 1;
      s = (s+xcyp)%4;
  }
}