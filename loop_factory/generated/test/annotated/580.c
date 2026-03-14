int main1(){
  int o2, mi, di, a;
  o2=1;
  mi=1;
  di=0;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o2 == 1;
  loop invariant (di >= 0);
  loop invariant (mi == (1 << di));
  loop invariant (a >= 0);
  loop invariant di <= 1;
  loop invariant (di == 0) ==> (mi == 1 && a == 0);
  loop assigns di, mi, a;
*/
while (mi<=o2) {
      di++;
      mi = 2*mi;
      a = a*4+(mi%7)+0;
  }
}