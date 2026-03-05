int main1(int g,int i){
  int ea, rve, e;
  ea=10;
  rve=ea;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ea == 10;
  loop invariant rve == ea;
  loop invariant i == \at(i, Pre);
  loop invariant e == 0 || e == ea + 1;
  loop invariant (g - \at(g, Pre)) % (ea + 1) == 0;
  loop invariant g >= \at(g, Pre);
  loop assigns e, g;
*/
while (rve>=3) {
      e = ea-e;
      e += 1;
      g = g + e;
  }
}