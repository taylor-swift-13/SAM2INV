int main1(){
  int x1, vi, pm, y0;
  x1=64;
  vi=1;
  pm=0;
  y0=vi;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y0 <= x1;
  loop invariant ((y0 == 1 && pm == 0) || (pm == y0*y0));
  loop invariant y0 >= 1;
  loop invariant (vi == x1) || (vi == 1 && y0 == 1 && pm == 0 && x1 == 64);
  loop assigns y0, pm, vi;
*/
while (vi<=x1-1) {
      y0++;
      pm = y0*y0;
      vi = x1;
  }
}