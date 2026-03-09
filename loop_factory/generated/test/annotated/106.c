int main1(int j,int w){
  int r, s5, bbq;
  r=-4;
  s5=(j%20)+10;
  bbq=(j%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s5 + bbq + r + 4 == (j % 20) + 10 + (j % 15) + 8;
  loop invariant s5 + bbq == (j % 20) + (j % 15) + 14 - r;
  loop invariant r >= -4;
  loop invariant s5 + bbq == (\at(j, Pre)%20) + (\at(j, Pre)%15) + 14 - r;
  loop invariant s5 <= ((\at(j, Pre) % 20) + 10);
  loop invariant bbq <= ((\at(j, Pre) % 15) + 8);
  loop assigns s5, bbq, r;
*/
for (; s5>0&&bbq>0; r = r + 1) {
      if (r%2==0) {
          s5--;
      }
      else {
          bbq--;
      }
  }
}