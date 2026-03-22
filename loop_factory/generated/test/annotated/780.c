int main1(int t,int j){
  int kp, crj, w, fb;
  kp=185;
  crj=1;
  w=1;
  fb=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 1;
  loop invariant kp == 185;
  loop invariant j == \at(j, Pre);
  loop invariant crj >= 1;
  loop invariant fb >= j;
  loop invariant (crj == 1) ==> (fb == j);
  loop assigns fb, crj;
*/
while (1) {
      if (!(crj<=kp/2)) {
          break;
      }
      fb = fb*fb+w;
      crj = crj*2;
  }
}