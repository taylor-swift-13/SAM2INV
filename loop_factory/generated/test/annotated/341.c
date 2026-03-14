int main1(int e,int f){
  int pg, qn2, jq, lx;
  pg=f;
  qn2=2;
  jq=0;
  lx=pg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jq;
  loop invariant qn2 == 2 + e * jq;
  loop invariant lx == pg + jq*(jq+1)/2;
  loop invariant pg == \at(f,Pre);
  loop invariant e == \at(e,Pre);
  loop assigns qn2, jq, lx;
*/
while (jq<=pg-1) {
      qn2 = qn2 + e;
      jq = jq + 1;
      lx = lx + jq;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jq;
  loop invariant pg == f;
  loop invariant pg == \at(f,Pre);
  loop assigns jq, qn2, e;
*/
while (jq<=pg-1) {
      jq = jq + 1;
      qn2 = qn2 + e;
      e = e+pg-lx;
  }
}