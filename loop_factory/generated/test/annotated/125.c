int main1(int g,int t){
  int hp, c8, s, j8, ia;
  hp=t*5;
  c8=0;
  s=0;
  j8=2;
  ia=c8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 6*ia == s*(2*hp - s + 3);
  loop invariant s % 3 == 0;
  loop invariant 0 <= s;
  loop assigns s, ia, j8;
*/
while (s<=hp-1) {
      j8 = hp-s;
      s = s + 3;
      ia += j8;
  }
}