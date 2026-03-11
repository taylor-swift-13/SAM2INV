int main1(int p){
  int c6v, w, om, a7g;
  c6v=p;
  w=0;
  om=c6v;
  a7g=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c6v == \at(p, Pre);
  loop invariant a7g == 4;
  loop invariant c6v == p;
  loop invariant om == c6v;
  loop invariant (w == 0) || (w == c6v);
  loop assigns a7g, w;
*/
while (w<=c6v-1) {
      a7g = a7g+om*w;
      w = c6v;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a7g == 4;
  loop invariant c6v == \at(p, Pre);
  loop invariant om >= \at(p, Pre);
  loop assigns om, w;
*/
while (1) {
      if (!(om<=a7g-1)) {
          break;
      }
      om++;
      w += p;
  }
}