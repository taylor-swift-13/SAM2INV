int main1(int j,int d){
  int qg, b, qh;
  qg=0;
  b=(j%28)+10;
  qh=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == (\at(j,Pre) % 28) + 10 - qg*(qg-1)/2;
  loop invariant j == \at(j,Pre) + 6*(qg/4) + (qg%4)*((qg%4)+1)/2;
  loop invariant qg >= 0;
  loop assigns b, qg, j, d;
*/
while (1) {
      if (!(b>qg)) {
          break;
      }
      b -= qg;
      qg = (1)+(qg);
      j = j+(qg%4);
      d = d*d+qh;
  }
}