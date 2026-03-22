int main1(){
  int e42e, ik, yyx, rczo, wtdz;
  e42e=(1%60)+60;
  ik=(1%9)+2;
  yyx=0;
  rczo=0;
  wtdz=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wtdz >= 10;
  loop invariant 0 <= rczo <= ik-1;
  loop invariant yyx >= 0;
  loop invariant e42e == 61;
  loop invariant 3*yyx + rczo <= e42e;
  loop invariant ik == 3;
  loop assigns rczo, yyx, wtdz;
*/
while (e42e>ik*yyx+rczo) {
      if (rczo==ik-1) {
          rczo = 0;
          yyx += 1;
      }
      else {
          rczo += 1;
      }
      wtdz += yyx;
  }
}