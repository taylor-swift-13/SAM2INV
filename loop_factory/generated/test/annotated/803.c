int main1(int k,int q){
  int dndb, hh, l3bx, yv;
  dndb=(k%31)+9;
  hh=0;
  l3bx=dndb;
  yv=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dndb == (k % 31) + 9;
  loop invariant 0 <= hh;
  loop invariant l3bx >= dndb;
  loop invariant dndb == (\at(k,Pre) % 31) + 9;
  loop invariant yv <= -4;
  loop invariant (hh == 0) ==> (l3bx == dndb && yv == -4);
  loop invariant (hh > 0) ==> ((l3bx + 2) % 3 == 0);
  loop assigns l3bx, yv, hh;
*/
while (1) {
      l3bx = l3bx*3+4;
      yv = yv*l3bx+4;
      hh++;
      if (hh>=dndb) {
          break;
      }
  }
}