int main1(){
  int bl, jcyt, pt, iy, qz8, qc;
  bl=41;
  jcyt=6;
  pt=0;
  iy=jcyt;
  qz8=0;
  qc=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qz8 <= bl;
  loop invariant (qz8 == 0) ==> (pt == 0 && iy == jcyt && qc == 3);
  loop invariant 0 <= pt;
  loop invariant 0 <= iy;
  loop invariant qc % 3 == 0;
  loop invariant (qz8 == 0) || (qz8 == bl);
  loop invariant qc > 0;
  loop invariant pt <= 2;
  loop invariant iy <= 18;
  loop assigns pt, iy, qc, qz8;
*/
while (qz8<=bl-1) {
      pt = pt*qc+2;
      iy = iy*qc;
      qz8 = bl;
      if ((jcyt%2)==0) {
          qc += qc;
      }
      else {
          qc = qc%8;
      }
  }
}