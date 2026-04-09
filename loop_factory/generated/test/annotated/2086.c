int main1(int q){
  int pv, ho, lg7, x;
  pv=34;
  ho=0;
  lg7=-4;
  x=pv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ho;
  loop invariant ho <= pv;
  loop invariant lg7 == -4;
  loop invariant ( (x >= pv) ==> (x - pv == ho) ) && ( (x <= pv) ==> (pv - x == ho) );
  loop invariant pv == 34;
  loop invariant (pv >= q) ==> (x - q == pv - q - ho);
  loop invariant (pv <= q) ==> (x - q == pv - q + ho);
  loop invariant ((\at(q,Pre) <= pv) ==> (\at(q,Pre) <= x && x <= pv)) &&
                 ((pv <= \at(q,Pre)) ==> (pv <= x && x <= \at(q,Pre)));
  loop assigns x, ho, lg7;
*/
while (ho < pv && x != q) {
      x = x + (x < q ? 1 : -1);
      ho += 1;
      lg7 = lg7+x-x;
  }
}