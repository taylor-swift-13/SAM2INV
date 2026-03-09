int main1(int t){
  int hqj, wi, vt, j12;
  hqj=61;
  wi=hqj;
  vt=0;
  j12=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre);
  loop invariant vt == 7 * (wi - hqj);
  loop invariant j12 == vt + 7;
  loop invariant vt == 7*(wi - 61);
  loop assigns j12, vt, wi;
*/
while (wi<hqj) {
      j12 = j12 + 7;
      vt = vt + 7;
      wi += 1;
  }
}