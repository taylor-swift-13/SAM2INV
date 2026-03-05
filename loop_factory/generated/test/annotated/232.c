int main1(){
  int m5u6, bh8e;
  m5u6=1+16;
  bh8e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m5u6 == 17;
  loop invariant bh8e % 2 == 0;
  loop invariant 0 <= bh8e;
  loop invariant bh8e <= 6;
  loop assigns bh8e;
*/
while (bh8e<m5u6) {
      bh8e = (bh8e+1)%6;
      bh8e += 1;
  }
}