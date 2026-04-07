int main1(int g){
  int jj, f7yt, y4j, oj6;
  jj=5;
  f7yt=0;
  y4j=0;
  oj6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre) + f7yt * oj6;
  loop invariant y4j == oj6;
  loop invariant 0 <= f7yt;
  loop invariant f7yt <= jj;
  loop invariant g == \at(g, Pre);
  loop assigns g, f7yt, y4j;
*/
while (f7yt < jj) {
      y4j = oj6;
      f7yt++;
      g = g + y4j;
  }
}