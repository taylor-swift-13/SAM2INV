int main1(int b){
  int byr, vh, l, sb;
  byr=55;
  vh=0;
  l=4;
  sb=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 4 + vh*(vh - 1)/2;
  loop invariant sb >= -3;
  loop invariant vh <= byr;
  loop invariant 0 <= vh;
  loop invariant byr == 55;
  loop invariant (vh == 0) ==> (sb == -3);
  loop assigns sb, l, vh;
*/
while (1) {
      sb = sb*sb;
      l += vh;
      vh = vh + 1;
      if (vh>=byr) {
          break;
      }
  }
}