int main1(){
  int zc81, p5, m6, p5l;
  zc81=1-6;
  p5=0;
  m6=(1%28)+10;
  p5l=zc81;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m6 - p5 + p5l == 6;
  loop invariant m6 == 11 - p5*(p5 - 1)/2;
  loop invariant p5l == zc81 + p5*(p5 + 1)/2;
  loop invariant p5 >= 0;
  loop invariant p5 <= 5;
  loop assigns m6, p5, p5l;
*/
while (m6>p5) {
      m6 = m6 - p5;
      p5 = (1)+(p5);
      p5l = p5l + p5;
  }
}