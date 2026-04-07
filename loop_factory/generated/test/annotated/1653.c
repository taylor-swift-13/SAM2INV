int main1(int p){
  int e, pp, m;
  e=p;
  pp=-4;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(p, Pre);
  loop invariant m == 7*(pp + 4);
  loop invariant p == \at(p, Pre) + (pp + 4) * (pp - 3) / 2;
  loop assigns p, pp, m;
*/
while (pp<=e-1) {
      pp += 1;
      m = m + 7;
      p += pp;
  }
}