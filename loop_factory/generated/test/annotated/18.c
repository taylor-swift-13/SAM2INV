int main1(int v){
  int xo, i;
  xo=0;
  i=-9057;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xo == 0;
  loop invariant v == \at(v, Pre);
  loop invariant i <= -9057;
  loop assigns i, v;
*/
while (i+5<0) {
      i = i+i+3;
      i = i + 3;
      v = v + xo;
  }
}