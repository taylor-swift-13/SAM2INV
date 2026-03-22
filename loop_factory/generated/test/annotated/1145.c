int main1(int x){
  int ko, t6, iq, so;
  ko=0;
  t6=0;
  iq=0;
  so=(x%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t6 == iq;
  loop invariant iq == ko;
  loop invariant so <= ((\at(x, Pre)) % 18) + 5;
  loop assigns so, t6, iq, ko, x;
*/
while (so>=1) {
      so -= 1;
      t6 = t6+x*x;
      iq = iq+x*x;
      ko = ko+x*x;
      x += so;
  }
}