int main1(int z,int e){
  int rto, yg;
  rto=e+16;
  yg=rto+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rto == \at(e, Pre) + 16;
  loop invariant rto == e + 16;
  loop invariant ((yg - (rto + 5)) % 2 == 0);
  loop invariant -1 <= (yg - rto) <= 5;
  loop assigns yg;
*/
for (; yg>=rto+1; yg -= 2) {
  }
}