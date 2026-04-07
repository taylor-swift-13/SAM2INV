int main1(int m){
  int ug, ie, igd, g7;
  ug=(m%15)+20;
  ie=0;
  igd=-4;
  g7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g7 == m * (igd + 4);
  loop invariant ug == (\at(m, Pre) % 15) + 20;
  loop invariant ((ie == 0) ==> (g7 == 0));
  loop invariant (ie == 0) || (ie == ug);
  loop invariant (igd == -4) || (igd == -3);
  loop invariant (ie != 0) ==> (g7 == m);
  loop invariant (ie == 0) ==> (igd == -4);
  loop invariant ug == (m % 15) + 20;
  loop invariant ((igd == -4 && ie == 0 && g7 == 0) ||
                    (igd == -3 && ie == ug && g7 == m));
  loop assigns g7, igd, ie;
*/
while (ie < ug) {
      g7 = g7 * (ie + 1) + m;
      igd += 1;
      ie = ug;
  }
}