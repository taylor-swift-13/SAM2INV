int main1(){
  int qefv, p, w6n, g6l, j2y4;
  qefv=1;
  p=qefv;
  w6n=p;
  g6l=p;
  j2y4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j2y4 == 0;
  loop invariant g6l == w6n;
  loop invariant w6n == 1;
  loop invariant qefv == 1;
  loop invariant (1 <= p && p <= qefv);
  loop assigns g6l, j2y4, p;
*/
while (1) {
      if (!(p < qefv)) {
          break;
      }
      g6l = (g6l+g6l)+(-(w6n));
      j2y4 = j2y4+j2y4-j2y4;
      p++;
  }
}