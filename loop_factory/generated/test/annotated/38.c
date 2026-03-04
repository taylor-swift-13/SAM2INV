int main1(){
  int hhsh, v9, qh;
  hhsh=1;
  v9=0;
  qh=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qh == 5 + (v9*(v9 + 5))/2;
  loop invariant 0 <= v9;
  loop invariant v9 <= hhsh;
  loop invariant hhsh == 1;
  loop invariant qh == 5 + (v9*v9 + 5*v9) / 2;
  loop invariant 0 <= v9 <= hhsh;
  loop invariant v9 >= 0;
  loop invariant qh >= 5;
  loop invariant qh == 5 + 3*v9 + v9*(v9 - 1) / 2;
  loop assigns qh, v9;
*/
while (v9<hhsh) {
      qh += 2;
      v9++;
      qh = qh + v9;
  }
}