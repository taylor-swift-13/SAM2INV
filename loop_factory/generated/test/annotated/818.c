int main1(int i,int h){
  int sg, bc, lx, v3g;
  sg=h;
  bc=1;
  lx=0;
  v3g=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sg == \at(h, Pre);
  loop invariant v3g == 1;
  loop invariant lx == 0;
  loop invariant (bc == 1) || (bc == sg);
  loop invariant sg == h;
  loop assigns v3g, bc;
*/
while (1) {
      if (!(bc<=sg-1)) {
          break;
      }
      v3g = v3g+lx*bc;
      bc = sg;
  }
}