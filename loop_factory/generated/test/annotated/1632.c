int main1(int h){
  int z6, uk, qnv;
  z6=0;
  uk=58;
  qnv=29;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uk + z6 == 58;
  loop invariant qnv >= 0;
  loop invariant uk == 4*qnv - 58;
  loop assigns uk, qnv, z6;
*/
while (qnv>0) {
      uk -= 4;
      qnv = qnv - 1;
      z6 += 4;
  }
}