int main1(int k,int o){
  int e2r, qn, go1;
  e2r=61;
  qn=e2r;
  go1=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant go1 + qn == 58;
  loop invariant e2r == 61;
  loop invariant qn >= 0;
  loop invariant qn <= 61;
  loop assigns go1, qn;
*/
for (; qn>=1; qn -= 1) {
      go1 += 1;
  }
}