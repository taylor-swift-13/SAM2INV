int main1(int x){
  int pms2, pclm, hf3, ssa;
  pms2=40;
  pclm=0;
  hf3=(x%40)+2;
  ssa=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ssa > 0) ==> (hf3 == ((ssa + (40 / ssa)) / 2));
  loop invariant pclm == 0;
  loop invariant pms2 == 40;
  loop invariant x == \at(x, Pre);
  loop assigns ssa, hf3, x;
*/
while (1) {
      if (!(hf3!=ssa)) {
          break;
      }
      ssa = hf3;
      hf3 = (hf3+pms2/hf3)/2;
      x += pclm;
  }
}