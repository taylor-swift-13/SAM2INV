int main1(int l){
  int tn, bns, z3, w;
  tn=(l%19)+13;
  bns=tn;
  z3=4;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z3 == 4 + l*w;
  loop invariant w >= 0;
  loop assigns w, z3;
*/
while (w<tn) {
      w += 1;
      z3 += l;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tn <= bns;
  loop invariant bns == \at(l, Pre) % 19 + 13;
  loop invariant tn >= bns;
  loop assigns tn;
*/
while (1) {
      tn++;
      if (tn>=bns) {
          break;
      }
  }
}